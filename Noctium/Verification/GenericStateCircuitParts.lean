import Noctium.Backend.NativeExpected

namespace Noctium.Verification.GenericStateCircuitParts
open Backend.Native

abbrev OutputFrame := AliasEnvironment × List (Term × Nat) × List Term
abbrev ReturnFrame := List Normalized × List Normalized

/-- One source condition per native field group, in the accepted plan's
operation order. Unconditional groups have no source condition. -/
def activityGuardSources (plan : Backend.Impact.Plan) : List (Option (Expr .bool)) :=
  if plan.activityGuards.isEmpty then
    plan.operations.flatMap fun operation => List.replicate operation.fieldGroups.length none
  else
    plan.operations.zip plan.activityGuards |>.flatMap fun (operation, guard) =>
      List.replicate operation.fieldGroups.length guard

def normalizeActivityGuard (entry : Entrypoint) (aliases : AliasEnvironment) :
    Option (Expr .bool) → Except Diagnostic Normalized := fun source =>
  match source with
  | none => pure {term := .constant 1}
  | some guard => (normalize aliases guard).mapError
      (fun message => {span := entry.span, message})

def inputRequirements (entry : Entrypoint) (plan : Backend.Impact.Plan) : List InputRequirement :=
  entry.circuit.inputs.map (fun input =>
    {identifier := "%input_" ++ input.name, visibility := input.visibility, ty := input.ty}) ++
  (plan.reads.drop ((entry.circuit.inputs.filter (·.visibility == .«public»)).length)).map
    (fun read => {identifier := "%input_" ++ read.name, visibility := .«public», ty := read.ty})

def initialAliases (entry : Entrypoint) (plan : Backend.Impact.Plan) : AliasEnvironment :=
  (inputRequirements entry plan).map
    (fun input => (input.identifier.drop 7 |>.toString, .input input.identifier))

def normalizeOutput (aliases : AliasEnvironment) (output : Output) : Except Diagnostic Normalized :=
  (normalize aliases output.value).mapError (fun message => {span := output.span, message})

def appendOutput (output : Output) (frame : OutputFrame) : Except Diagnostic OutputFrame := do
  let result ← normalizeOutput frame.1 output
  pure ((output.name, result.term) :: frame.1,
    frame.2.1 ++ result.bounds, frame.2.2 ++ result.assertions)

def outputFold (frame : OutputFrame) (outputs : List Output) : Except Diagnostic OutputFrame :=
  outputs.foldlM (fun frame output => appendOutput output frame) frame

def normalizeOutputs (aliases : AliasEnvironment) (outputs : List Output) :
    Except Diagnostic OutputFrame := outputFold (aliases, [], []) outputs

@[simp] theorem outputFold_nil (frame : OutputFrame) : outputFold frame [] = .ok frame := rfl

theorem outputFold_cons (frame : OutputFrame) (output : Output) (rest : List Output) :
    outputFold frame (output :: rest) =
      (appendOutput output frame).bind (fun next => outputFold next rest) := rfl

private theorem bind_ok {α β : Type} {first : Except ε α} {next : α → Except ε β}
    {result : β} : (first >>= next) = .ok result ↔
    ∃ value, first = .ok value ∧ next value = .ok result := by
  cases first <;> simp [Bind.bind, Except.bind]

theorem normalizeOutputs_loop (aliases : AliasEnvironment) (outputs : List Output) :
    (forIn outputs (aliases, [], []) fun output frame => do
      let result ← normalizeOutput frame.1 output
      pure (ForInStep.yield ((output.name, result.term) :: frame.1,
        frame.2.1 ++ result.bounds, frame.2.2 ++ result.assertions))) =
      normalizeOutputs aliases outputs := by
  simp [normalizeOutputs, outputFold, appendOutput]

/-- Exact projections of the production ledger-call expected constructor. -/
theorem expectedEntrypoint_parts (state : List StateDecl) (entry : Entrypoint)
    (expected : Expected) (accepted : expectedEntrypoint state entry = .ok expected) :
    ∃ (plan : Backend.Impact.Plan) (outputFrame : OutputFrame)
      (aliases : List (String × Term))
      (inputState : List InputRequirement × List Term × List (Term × Nat) × Nat)
      (conditions guards : List Normalized)
      (constraintCollection guardCollection : List Term × List (Term × Nat) × List Term)
      (operationFrame : List (List Term) × List (Term × Nat) × List Term)
      (returns : ReturnFrame) (activity : List Normalized),
      Backend.Impact.lower state entry = .ok plan ∧
      normalizeOutputs
        (entry.circuit.inputs.map (fun input =>
          (input.name, if entry.callInputs.contains input.name then
            Input.callArgumentTerm input else Input.sourceTerm input)) ++
          (plan.reads.drop (Backend.Impact.publicInputReadCount entry.circuit.inputs)).flatMap
            fun read => read.bindings.map fun (name, _) =>
              (name, Term.input ("%input_" ++ name)))
        entry.circuit.outputs = .ok outputFrame ∧
      (forIn ((plan.reads.drop (Backend.Impact.publicInputReadCount entry.circuit.inputs)).flatMap
          Backend.Impact.Read.scalarReads) outputFrame.1
        fun (read : Backend.Impact.Read) (aliases : AliasEnvironment) => do
        let guard : Option Normalized ← read.guard.mapM fun guard =>
          (normalize aliases guard).mapError
            (fun message => ({span := entry.span, message} : Diagnostic))
        match read.ty with
        | .bytes length =>
          let chunks := Backend.Impact.Read.bindings read |>.map fun ((name, _) : String × Ty) =>
            let input := Term.input ("%input_" ++ name)
            guard.map (fun (value : Normalized) =>
              Term.select value.term input (.constant 0)) |>.getD input
          pure (ForInStep.yield
            ((read.name, bytesFromChunksTerm length chunks.reverse) :: aliases))
        | .jubjubScalar =>
          pure (ForInStep.yield ((read.name,
            .unary "jubjub_scalar_from_native" (Term.input ("%input_" ++ read.name))) :: aliases))
        | .jubjubPoint =>
          let xName := (Backend.Impact.Read.bindings read)[0]!.1
          let yName := (Backend.Impact.Read.bindings read)[1]!.1
          let x := Term.input ("%input_" ++ xName)
          let y := Term.input ("%input_" ++ yName)
          let x := guard.map (fun (value : Normalized) =>
            Term.select value.term x (.constant 0)) |>.getD x
          let y := guard.map (fun (value : Normalized) =>
            Term.select value.term y (.constant 1)) |>.getD y
          pure (ForInStep.yield
            ((read.name, .binary "from_coordinates_jubjub" x y) :: aliases))
        | _ => pure (ForInStep.yield aliases)) = .ok aliases ∧
      (forIn (plan.reads.drop (Backend.Impact.publicInputReadCount entry.circuit.inputs))
        (((entry.circuit.inputs.filter fun input =>
            !entry.callInputs.contains input.name).flatMap Input.requirements) ++
          (plan.reads.drop (Backend.Impact.publicInputReadCount entry.circuit.inputs)).flatMap
            fun read => read.bindings.map fun (name, ty) =>
              (match ty with
              | .jubjubScalar =>
                {identifier := "%input_" ++ name, visibility := .«public», ty := .native,
                  canonicalJubjubScalar := true}
              | .opaqueBytes | .opaqueString =>
                {identifier := "%input_" ++ name, visibility := .«public», ty := .native}
              | _ => {identifier := "%input_" ++ name, visibility := .«public», ty}),
          [], [],
          ((entry.circuit.inputs.filter fun input => !entry.callInputs.contains input.name).flatMap
            Input.requirements).length) fun (read : Backend.Impact.Read)
            (state : List InputRequirement × List Term × List (Term × Nat) × Nat) => do
          match read.guard with
          | some guard => do
            let result : Normalized ←
              (normalize aliases guard).mapError
                (fun message => ({span := entry.span, message} : Diagnostic))
            let (assertions, bounds) ← forIn (Backend.Impact.Read.inactiveDefaultConstraints read)
                (state.2.1 ++ result.assertions, state.2.2.1 ++ result.bounds)
                fun condition state => do
                  let result ← (normalize aliases condition).mapError
                    (fun message => ({span := entry.span, message} : Diagnostic))
                  pure (ForInStep.yield
                    (state.1 ++ result.assertions ++ [result.term], state.2 ++ result.bounds))
            pure (ForInStep.yield
              (state.1.zipIdx.map fun ((input, position) : InputRequirement × Nat) =>
                (if state.2.2.2 ≤ position && position < state.2.2.2 +
                    (Backend.Impact.Read.bindings read).length then
                  {input with activityGuard := some result.term} else input),
                assertions, bounds, state.2.2.2 + (Backend.Impact.Read.bindings read).length))
          | _ => do
            let (assertions, bounds) ← forIn (Backend.Impact.Read.inactiveDefaultConstraints read)
                (state.2.1, state.2.2.1) fun condition state => do
                  let result ← (normalize aliases condition).mapError
                    (fun message => ({span := entry.span, message} : Diagnostic))
                  pure (ForInStep.yield
                    (state.1 ++ result.assertions ++ [result.term], state.2 ++ result.bounds))
            pure (ForInStep.yield
              (state.1, assertions, bounds, state.2.2.2 +
                (Backend.Impact.Read.bindings read).length))
        ) = .ok inputState ∧
      entry.circuit.constraints.mapM (normalize aliases) = .ok conditions ∧
      plan.guards.mapM (normalize aliases) = .ok guards ∧
      (Except.mapError (fun message => ({span := entry.span, message} : Diagnostic)) do
        let results ← entry.circuit.constraints.mapM (normalize aliases)
        pure (results.map (·.term), results.flatMap (·.bounds), results.flatMap (·.assertions))) =
          .ok constraintCollection ∧
      (Except.mapError (fun message => ({span := entry.span, message} : Diagnostic)) do
        let results ← plan.guards.mapM (normalize aliases)
        pure (results.map (·.term), results.flatMap (·.bounds), results.flatMap (·.assertions))) =
          .ok guardCollection ∧
      collectOperations entry.span aliases plan.operations outputFrame.2.1 = .ok operationFrame ∧
      (forIn entry.returns ([], []) fun (output : Output) (state : ReturnFrame) => do
        if output.ty == Ty.bytes 0 then do
          let emptyReturn ← (normalize aliases output.value).mapError
            (fun message => ({span := output.span, message} : Diagnostic))
          let fields ← output.nativeReturnFields.mapError
            (fun message => ({span := output.span, message} : Diagnostic))
          let returnResults ← forIn fields state.1 fun field returnResults => do
            let value ← (normalize aliases field).mapError
              (fun message => ({span := output.span, message} : Diagnostic))
            pure (ForInStep.yield (returnResults ++ [value]))
          pure (ForInStep.yield (returnResults, state.2 ++ [emptyReturn]))
        else do
          let fields ← output.nativeReturnFields.mapError
            (fun message => ({span := output.span, message} : Diagnostic))
          let returnResults ← forIn fields state.1 fun field returnResults => do
            let value ← (normalize aliases field).mapError
              (fun message => ({span := output.span, message} : Diagnostic))
            pure (ForInStep.yield (returnResults ++ [value]))
          pure (ForInStep.yield (returnResults, state.2))) = .ok returns ∧
      (activityGuardSources plan).mapM (normalizeActivityGuard entry aliases) = .ok activity ∧
      expected.inputs = inputState.1 ∧
      expected.groups = operationFrame.1 ∧
      expected.returns = returns.1.map (·.term) ∧
      expected.mode = .ledgerCall ∧
      expected.rawInputs = entry.callArguments.flatMap Input.callArgumentRequirements ∧
      expected.groupGuards = activity.map (·.term) ∧
      expected.assertions = conditions.flatMap (fun item => item.assertions ++ [item.term]) ++
        outputFrame.2.2 ++ inputState.2.1 ++
        guards.flatMap (fun item => item.assertions ++ [item.term]) ++ operationFrame.2.2 ++
        (returns.1 ++ returns.2).flatMap (·.assertions) ++ activity.flatMap (·.assertions) ∧
      expected.bounds = operationFrame.2.1 ++ constraintCollection.2.1 ++ inputState.2.2.1 ++
        guardCollection.2.1 ++ (returns.1 ++ returns.2).flatMap (·.bounds) ++
        activity.flatMap (·.bounds) := by
  unfold expectedEntrypoint at accepted
  simp only [bind_ok] at accepted
  rcases accepted with ⟨plan, lowered, outputFrame, outputAccepted,
    aliases, aliasesAccepted, inputState, inputStateAccepted,
    constraintCollection, constraintCollectionAccepted,
    conditions, conditionsAccepted, guardCollection, guardCollectionAccepted,
    guards, guardsAccepted, operationFrame, operationAccepted, produced⟩
  rcases produced with ⟨returns, returnsAccepted, activity, activityAccepted, expectedAccepted⟩
  have outputProjection :
      normalizeOutputs
        (entry.circuit.inputs.map (fun input =>
          (input.name, if entry.callInputs.contains input.name then
            Input.callArgumentTerm input else Input.sourceTerm input)) ++
          (plan.reads.drop (Backend.Impact.publicInputReadCount entry.circuit.inputs)).flatMap
            fun read => read.bindings.map fun (name, _) =>
              (name, Term.input ("%input_" ++ name)))
        entry.circuit.outputs = .ok outputFrame := by
    rw [← normalizeOutputs_loop]
    simpa only [readInputAliases_eq, convert_eq_mapError,
      normalizeOutput, Except.mapError] using outputAccepted
  have aliasesFoldExact := by
    simpa only [convert_eq_mapError] using aliasesAccepted
  have inputStateExact := by
    rw [readInputRequirements_eq] at inputStateAccepted
    simpa only [convert_eq_mapError] using inputStateAccepted
  have returnsExact := by
    simpa only [convert_eq_mapError] using returnsAccepted
  have activityExact :
      (activityGuardSources plan).mapM (normalizeActivityGuard entry aliases) = .ok activity := by
    simp only [convert_eq_mapError] at activityAccepted
    rw [← activityAccepted]
    unfold activityGuardSources
    congr 1
  have constraintValues := (convert_ok _ _ _).mp conditionsAccepted
  have guardValues := (convert_ok _ _ _).mp guardsAccepted
  have constraintCollectionExact :
      (Except.mapError (fun message => ({span := entry.span, message} : Diagnostic)) do
        let results ← entry.circuit.constraints.mapM (normalize aliases)
        pure (results.map (·.term), results.flatMap (·.bounds), results.flatMap (·.assertions))) =
          .ok constraintCollection := by
    rw [collect_eq] at constraintCollectionAccepted
    simpa only [convert_eq_mapError] using
      constraintCollectionAccepted
  have guardCollectionExact :
      (Except.mapError (fun message => ({span := entry.span, message} : Diagnostic)) do
        let results ← plan.guards.mapM (normalize aliases)
        pure (results.map (·.term), results.flatMap (·.bounds), results.flatMap (·.assertions))) =
          .ok guardCollection := by
    rw [collect_eq] at guardCollectionAccepted
    simpa only [convert_eq_mapError] using
      guardCollectionAccepted
  let produced : Expected := {
      mode := .ledgerCall
      inputs := inputState.1
      rawInputs := entry.callArguments.flatMap Input.callArgumentRequirements
      groups := operationFrame.1
      groupGuards := activity.map (·.term)
      returns := returns.1.map (·.term)
      assertions := conditions.flatMap (fun result => result.assertions ++ [result.term]) ++
        outputFrame.2.2 ++ inputState.2.1 ++
        guards.flatMap (fun result => result.assertions ++ [result.term]) ++
        operationFrame.2.2 ++ (returns.1 ++ returns.2).flatMap (·.assertions) ++
        activity.flatMap (·.assertions)
      bounds := operationFrame.2.1 ++ constraintCollection.2.1 ++ inputState.2.2.1 ++
        guardCollection.2.1 ++ (returns.1 ++ returns.2).flatMap (·.bounds) ++
        activity.flatMap (·.bounds)}
  change Except.ok produced = Except.ok expected at expectedAccepted
  have expectedExact : expected = produced := (Except.ok.inj expectedAccepted).symm
  subst expected
  refine ⟨plan, outputFrame, aliases, inputState, conditions, guards, constraintCollection,
    guardCollection, operationFrame, returns, activity, lowered, outputProjection,
    aliasesFoldExact, inputStateExact, ?_, ?_, constraintCollectionExact,
    guardCollectionExact, operationAccepted, returnsExact, activityExact,
    ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · simp only [constraintValues]
  · simp only [guardValues]
  · simp [produced]
  · simp [produced]
  · simp [produced]
  · simp [produced]
  · simp [produced]
  · simp [produced]
  · simp [produced]
  · simp [produced]

/-- The checked native call header comes from the source argument order. -/
theorem expectedEntrypoint_rawInputs (state : List StateDecl) (entry : Entrypoint)
    (expected : Expected) (accepted : expectedEntrypoint state entry = .ok expected) :
    expected.rawInputs = entry.callArguments.flatMap Input.callArgumentRequirements := by
  obtain ⟨_, _, _, _, _, _, _, _, _, _, _, _, _,
    _, _, _, _, _, _, _, _, _, _, _, _, _, raw, _, _, _⟩ :=
    expectedEntrypoint_parts state entry expected accepted
  exact raw

private theorem mapM_indexed {α β ε : Type} {f : α → Except ε β}
    {sources : List α} {results : List β}
    (accepted : sources.mapM f = .ok results) (index : Nat) :
    sources[index]?.mapM f = .ok results[index]? := by
  induction sources generalizing results index with
  | nil =>
    cases accepted
    rfl
  | cons source rest ih =>
    simp only [List.mapM_cons, bind_ok] at accepted
    obtain ⟨head, headAccepted, tail, tailAccepted, result⟩ := accepted
    cases result
    cases index with
    | zero => simp [Option.mapM, headAccepted, Functor.map, Except.map]
    | succ n => exact ih tailAccepted n

/-- The expected Impact guard at every ordinal comes from normalization of
the source condition at that same field-group ordinal in the actual plan. -/
theorem expectedEntrypoint_activityGuard_at (state : List StateDecl) (entry : Entrypoint)
    (expected : Expected) (accepted : expectedEntrypoint state entry = .ok expected) :
    ∃ plan aliases, Backend.Impact.lower state entry = .ok plan ∧
      ∀ index : Nat,
        ((activityGuardSources plan)[index]?.mapM (normalizeActivityGuard entry aliases)).map
          (Option.map (·.term)) = .ok expected.groupGuards[index]? := by
  obtain ⟨plan, _, aliases, _, _, _, _, _, _, _, activity, lowered, _, _, _, _, _, _, _,
    _, _, normalized, _, _, _, _, _, expectedTerms, _, _⟩ :=
    expectedEntrypoint_parts state entry expected accepted
  refine ⟨plan, aliases, lowered, fun index => ?_⟩
  rw [mapM_indexed normalized index, expectedTerms, List.getElem?_map]
  rfl

end Noctium.Verification.GenericStateCircuitParts
