import Noctium.Backend.NativeExpected
import Noctium.Verification.ScalarCircuit

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

private abbrev InputState := List InputRequirement × List Term × List (Term × Nat) × Nat

/-- Normalize a list of inactive defaults and accumulate their assertions. -/
private def inactiveDefaultResultsFor (entry : Entrypoint) (aliases : AliasEnvironment)
    (conditions : List (Expr .bool)) (initial : List Term × List (Term × Nat)) :
    Except Diagnostic (List Term × List (Term × Nat)) :=
  forIn conditions initial
    fun condition state => do
      let result ← (normalize aliases condition).mapError
        (fun message => {span := entry.span, message})
      pure (ForInStep.yield
        (state.1 ++ result.assertions ++ [result.term], state.2 ++ result.bounds))

/-- Normalize the read's inactive defaults and accumulate their assertions. -/
private def inactiveDefaultResults (entry : Entrypoint) (aliases : AliasEnvironment)
    (read : Backend.Impact.Read) (initial : List Term × List (Term × Nat)) :
    Except Diagnostic (List Term × List (Term × Nat)) :=
  inactiveDefaultResultsFor entry aliases
    (Backend.Impact.Read.inactiveDefaultConstraints read) initial

/-- One iteration of the expected constructor's public-read descriptor fold.
Guarded reads update only the activity guard on the assigned input slots. -/
private def inputStateStep (entry : Entrypoint) (aliases : AliasEnvironment)
    (read : Backend.Impact.Read) (state : InputState) :
    Except Diagnostic (ForInStep InputState) := do
  match read.guard with
  | some guard => do
    let result : Normalized ← (normalize aliases guard).mapError
      (fun message => {span := entry.span, message})
    let (assertions, bounds) ← inactiveDefaultResults entry aliases read
      (state.2.1 ++ result.assertions, state.2.2.1 ++ result.bounds)
    pure (ForInStep.yield
      (state.1.zipIdx.map fun ((input, position) : InputRequirement × Nat) =>
        if state.2.2.2 ≤ position && position < state.2.2.2 +
            (Backend.Impact.Read.bindings read).length then
          {input with activityGuard := some result.term} else input,
        assertions, bounds, state.2.2.2 + (Backend.Impact.Read.bindings read).length))
  | _ => do
    let (assertions, bounds) ← inactiveDefaultResults entry aliases read
      (state.2.1, state.2.2.1)
    pure (ForInStep.yield
      (state.1, assertions, bounds,
        state.2.2.2 + (Backend.Impact.Read.bindings read).length))

def inputRequirementCore (input : InputRequirement) : String × Visibility × Ty × Bool :=
  (input.identifier, input.visibility, input.ty, input.canonicalJubjubScalar)

private theorem inputRequirementCore_guardedZipIdx (inputs : List InputRequirement)
    (start count : Nat) (guard : Term) :
    (inputs.zipIdx.map fun ((input, position) : InputRequirement × Nat) =>
      if start ≤ position && position < start + count then
        {input with activityGuard := some guard} else input).map inputRequirementCore =
      inputs.map inputRequirementCore := by
  have updatePreserves :
      (inputs.zipIdx.map fun ((input, position) : InputRequirement × Nat) =>
        inputRequirementCore (if start ≤ position && position < start + count then
          {input with activityGuard := some guard} else input)) =
        inputs.zipIdx.map fun ((input, _) : InputRequirement × Nat) =>
          inputRequirementCore input := by
    apply List.map_congr_left
    intro pair member
    rcases pair with ⟨input, position⟩
    by_cases active : start ≤ position && position < start + count
    · simp [active, inputRequirementCore]
    · simp [active, inputRequirementCore]
  calc
    (inputs.zipIdx.map fun ((input, position) : InputRequirement × Nat) =>
      if start ≤ position && position < start + count then
        {input with activityGuard := some guard} else input).map inputRequirementCore =
        inputs.zipIdx.map (fun ((input, position) : InputRequirement × Nat) =>
          inputRequirementCore (if start ≤ position && position < start + count then
            {input with activityGuard := some guard} else input)) := by
        simp only [List.map_map, Function.comp_def]
    _ = inputs.zipIdx.map fun ((input, _) : InputRequirement × Nat) =>
          inputRequirementCore input := updatePreserves
    _ = inputs.map inputRequirementCore := by
      calc
        inputs.zipIdx.map (fun (pair : InputRequirement × Nat) => inputRequirementCore pair.1) =
            (inputs.zipIdx.map (Prod.map inputRequirementCore id)).map Prod.fst := by simp
        _ = (inputs.map inputRequirementCore).zipIdx.map Prod.fst := by
          rw [List.map_zipIdx (f := inputRequirementCore) (l := inputs) (k := 0)]
        _ = inputs.map inputRequirementCore := by simp

private def forInStepValue {α : Type} : ForInStep α → α
  | .yield value => value
  | .done value => value

private theorem list_forIn_preserves_projection
    {α β γ ε : Type} {items : List α} {initial final : β}
    (project : β → γ) (step : α → β → Except ε (ForInStep β))
    (stepPreserves : ∀ item state result,
      step item state = .ok result →
        project (forInStepValue result) = project state)
    (accepted : forIn items initial step = .ok final) :
    project final = project initial := by
  induction items generalizing initial final with
  | nil =>
    simp only [List.forIn_nil] at accepted
    cases accepted
    rfl
  | cons item rest ih =>
    rw [List.forIn_cons] at accepted
    cases stepResult : step item initial with
    | error message =>
      simp [stepResult, Bind.bind, Except.bind] at accepted
    | ok result =>
      simp only [stepResult, Bind.bind, Except.bind] at accepted
      cases result with
      | yield next =>
        calc
          project final = project next := ih accepted
          _ = project initial := stepPreserves item initial (.yield next) stepResult
      | done next =>
        have nextEq : next = final := Except.ok.inj accepted
        subst final
        exact stepPreserves item initial (.done next) stepResult

private theorem list_forIn_preserves_projection_supported
    {α β γ ε : Type} {items : List α} {initial final : β}
    (supported : α → Prop) (project : β → γ)
    (step : α → β → Except ε (ForInStep β))
    (allSupported : ∀ item ∈ items, supported item)
    (stepPreserves : ∀ item, supported item → ∀ state result,
      step item state = .ok result →
        project (forInStepValue result) = project state)
    (accepted : forIn items initial step = .ok final) :
    project final = project initial := by
  induction items generalizing initial final with
  | nil =>
    simp only [List.forIn_nil] at accepted
    cases accepted
    rfl
  | cons item rest ih =>
    rw [List.forIn_cons] at accepted
    cases stepResult : step item initial with
    | error message =>
      simp [stepResult, Bind.bind, Except.bind] at accepted
    | ok result =>
      simp only [stepResult, Bind.bind, Except.bind] at accepted
      have itemSupported : supported item := allSupported item (by simp)
      have restSupported : ∀ next ∈ rest, supported next := by
        intro next member
        exact allSupported next (by simp [member])
      cases result with
      | yield next =>
        calc
          project final = project next := ih restSupported accepted
          _ = project initial := stepPreserves item itemSupported initial
            (.yield next) stepResult
      | done next =>
        have nextEq : next = final := Except.ok.inj accepted
        subst final
        exact stepPreserves item itemSupported initial (.done next) stepResult

def initialAliases (entry : Entrypoint) (plan : Backend.Impact.Plan) : AliasEnvironment :=
  (inputRequirements entry plan).map
    (fun input => (input.identifier.drop 7 |>.toString, .input input.identifier))

/-- Seed aliases used while normalizing a generic entrypoint's circuit outputs.
The circuit inputs keep their source or call-argument terms. Post-public reads
start as their physical public input bindings. -/
def entrypointSeedAliases (entry : Entrypoint) (plan : Backend.Impact.Plan) :
    AliasEnvironment :=
  entry.circuit.inputs.map (fun input =>
    (input.name, if entry.callInputs.contains input.name then
      Input.callArgumentTerm input else Input.sourceTerm input)) ++
    (plan.reads.drop (Backend.Impact.publicInputReadCount entry.circuit.inputs)).flatMap
      fun read => read.bindings.map fun (name, _) =>
        (name, Term.input ("%input_" ++ name))

/-- One iteration of the expected constructor's post-output read-alias fold. -/
def readAliasStep (entry : Entrypoint) (read : Backend.Impact.Read)
    (aliases : AliasEnvironment) : Except Diagnostic (ForInStep AliasEnvironment) := do
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
  | _ => pure (ForInStep.yield aliases)

def scalarAliasReadType (ty : Ty) : Prop :=
  ty = .native ∨ ty = .bool ∨ ∃ width, ty = .uint width

private theorem readAliasStep_preserves_scalar (entry : Entrypoint)
    (read : Backend.Impact.Read) (aliases : AliasEnvironment)
    (supported : scalarAliasReadType read.ty) (result : ForInStep AliasEnvironment)
    (accepted : readAliasStep entry read aliases = .ok result) :
    forInStepValue result = aliases := by
  rcases supported with native | boolean | ⟨width, unsigned⟩
  · cases guardResult : (read.guard.mapM fun guard =>
        (normalize aliases guard).mapError
          (fun message => ({span := entry.span, message} : Diagnostic))) with
    | error message =>
      simp only [readAliasStep, guardResult, Bind.bind, Except.bind] at accepted
      cases accepted
    | ok guard =>
      cases result with
      | yield next =>
        simp only [readAliasStep, native, guardResult, Bind.bind, Except.bind] at accepted
        injection accepted with nextEq
        injection nextEq with valuesEq
        exact valuesEq.symm
      | done next =>
        simp only [readAliasStep, native, guardResult, Bind.bind, Except.bind] at accepted
        cases accepted
  · cases guardResult : (read.guard.mapM fun guard =>
        (normalize aliases guard).mapError
          (fun message => ({span := entry.span, message} : Diagnostic))) with
    | error message =>
      simp only [readAliasStep, guardResult, Bind.bind, Except.bind] at accepted
      cases accepted
    | ok guard =>
      cases result with
      | yield next =>
        simp only [readAliasStep, boolean, guardResult, Bind.bind, Except.bind] at accepted
        injection accepted with nextEq
        injection nextEq with valuesEq
        exact valuesEq.symm
      | done next =>
        simp only [readAliasStep, boolean, guardResult, Bind.bind, Except.bind] at accepted
        cases accepted
  · cases guardResult : (read.guard.mapM fun guard =>
        (normalize aliases guard).mapError
          (fun message => ({span := entry.span, message} : Diagnostic))) with
    | error message =>
      simp only [readAliasStep, guardResult, Bind.bind, Except.bind] at accepted
      cases accepted
    | ok guard =>
      cases result with
      | yield next =>
        simp only [readAliasStep, unsigned, guardResult, Bind.bind, Except.bind] at accepted
        injection accepted with nextEq
        injection nextEq with valuesEq
        exact valuesEq.symm
      | done next =>
        simp only [readAliasStep, unsigned, guardResult, Bind.bind, Except.bind] at accepted
        cases accepted

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

private def returnFrameStep (aliases : AliasEnvironment) (output : Output)
    (state : ReturnFrame) : Except Diagnostic (ForInStep ReturnFrame) := do
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
    pure (ForInStep.yield (returnResults, state.2))

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
      normalizeOutputs (entrypointSeedAliases entry plan) entry.circuit.outputs =
        .ok outputFrame ∧
      forIn ((plan.reads.drop (Backend.Impact.publicInputReadCount entry.circuit.inputs)).flatMap
          Backend.Impact.Read.scalarReads) outputFrame.1 (readAliasStep entry) = .ok aliases ∧
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
            Input.requirements).length) (inputStateStep entry aliases)) = .ok inputState ∧
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
      forIn entry.returns ([], []) (returnFrameStep aliases) = .ok returns ∧
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
        (entrypointSeedAliases entry plan) entry.circuit.outputs = .ok outputFrame := by
    rw [← normalizeOutputs_loop]
    simpa only [entrypointSeedAliases, readInputAliases_eq, convert_eq_mapError,
      normalizeOutput, Except.mapError] using outputAccepted
  have aliasesFoldExact := by
    simpa only [readAliasStep, convert_eq_mapError] using aliasesAccepted
  have inputStateExact := by
    rw [readInputRequirements_eq] at inputStateAccepted
    simpa only [convert_eq_mapError] using inputStateAccepted
  have returnsExact := by
    simpa only [returnFrameStep, convert_eq_mapError] using returnsAccepted
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

/-- Supported post-public scalar reads leave the output frame aliases intact. -/
private theorem readAliasFold_preserves_outputFrame (entry : Entrypoint)
    (plan : Backend.Impact.Plan) (aliases : AliasEnvironment)
    (outputFrame : OutputFrame)
    (scalarReads : ∀ read ∈
      (plan.reads.drop (Backend.Impact.publicInputReadCount entry.circuit.inputs)).flatMap
        Backend.Impact.Read.scalarReads,
      scalarAliasReadType read.ty)
    (accepted : forIn ((plan.reads.drop
        (Backend.Impact.publicInputReadCount entry.circuit.inputs)).flatMap
        Backend.Impact.Read.scalarReads) outputFrame.1 (readAliasStep entry) = .ok aliases) :
    aliases = outputFrame.1 := by
  exact list_forIn_preserves_projection_supported
    (supported := fun read : Backend.Impact.Read => scalarAliasReadType read.ty)
    (project := id) (step := readAliasStep entry) scalarReads
    (by
      intro read supported current result stepAccepted
      exact readAliasStep_preserves_scalar entry read current supported result stepAccepted)
    accepted

private theorem inactiveDefaultResultsFor_preserves (entry : Entrypoint)
    (aliases : AliasEnvironment) (conditions : List (Expr .bool))
    (initial final : List Term × List (Term × Nat))
    (accepted : inactiveDefaultResultsFor entry aliases conditions initial = .ok final) :
    (∀ term ∈ initial.1, term ∈ final.1) ∧
    (∀ bound ∈ initial.2, bound ∈ final.2) := by
  induction conditions generalizing initial final with
  | nil =>
    simp [inactiveDefaultResultsFor] at accepted
    cases accepted
    exact ⟨by intro term member; exact member, by intro bound member; exact member⟩
  | cons condition rest ih =>
    unfold inactiveDefaultResultsFor at accepted
    rw [List.forIn_cons] at accepted
    cases normalized : (normalize aliases condition).mapError
        (fun message => ({span := entry.span, message} : Diagnostic) ) with
    | error message => simp [normalized, Bind.bind, Except.bind] at accepted
    | ok value =>
      simp only [normalized, Bind.bind, Except.bind] at accepted
      have restAccepted := accepted
      obtain ⟨assertionsPreserved, boundsPreserved⟩ :=
        ih (initial := (initial.1 ++ value.assertions ++ [value.term],
          initial.2 ++ value.bounds)) (final := final) restAccepted
      constructor
      · intro term member
        exact assertionsPreserved term (List.mem_append_left _
          (List.mem_append_left _ member))
      · intro bound member
        exact boundsPreserved bound (List.mem_append_left _ member)

private theorem inactiveDefaultResultsFor_selected_exists (entry : Entrypoint)
    (aliases : AliasEnvironment) (conditions : List (Expr .bool))
    (initial final : List Term × List (Term × Nat)) (condition : Expr .bool)
    (conditionMember : condition ∈ conditions)
    (accepted : inactiveDefaultResultsFor entry aliases conditions initial = .ok final) :
    ∃ result, normalize aliases condition = .ok result ∧
      (∀ bound ∈ result.bounds, bound ∈ final.2) ∧
      (∀ term ∈ result.assertions ++ [result.term], term ∈ final.1) := by
  induction conditions generalizing initial final with
  | nil => simp at conditionMember
  | cons head rest ih =>
    unfold inactiveDefaultResultsFor at accepted
    rw [List.forIn_cons] at accepted
    cases headNormalized : (normalize aliases head).mapError
        (fun message => ({span := entry.span, message} : Diagnostic)) with
    | error message => simp [headNormalized, Bind.bind, Except.bind] at accepted
    | ok headResult =>
      simp only [headNormalized, Bind.bind, Except.bind] at accepted
      rcases List.mem_cons.mp conditionMember with same | later
      · have conditionEq : head = condition := same.symm
        subst head
        have normalized : normalize aliases condition = .ok headResult := by
          cases raw : normalize aliases condition with
          | error message => simp [raw, Except.mapError] at headNormalized
          | ok value =>
            have valueEq : value = headResult := by
              simpa [raw, Except.mapError] using headNormalized
            exact congrArg (fun item : Normalized =>
              (Except.ok item : Except String Normalized)) valueEq
        have boundsMember : ∀ bound ∈ headResult.bounds,
            bound ∈ (initial.2 ++ headResult.bounds) := by
          intro bound member
          exact List.mem_append_right _ member
        have assertionMembers : ∀ term ∈ headResult.assertions ++ [headResult.term],
            term ∈ (initial.1 ++ headResult.assertions ++ [headResult.term]) := by
          intro term member
          simp only [List.mem_append, List.mem_singleton] at member
          rcases member with assertionMember | termEq
          · exact List.mem_append_left _ (List.mem_append_right _ assertionMember)
          · subst term
            exact List.mem_append_right _ (by simp)
        have restPreserved := inactiveDefaultResultsFor_preserves entry aliases rest
          (initial.1 ++ headResult.assertions ++ [headResult.term],
            initial.2 ++ headResult.bounds) final accepted
        have boundsInFinal : ∀ bound ∈ headResult.bounds, bound ∈ final.2 := by
          intro bound member
          exact restPreserved.2 bound (boundsMember bound member)
        have assertionsInFinal : ∀ term ∈ headResult.assertions ++ [headResult.term],
            term ∈ final.1 := by
          intro term member
          exact restPreserved.1 term (assertionMembers term member)
        exact ⟨headResult, normalized, boundsInFinal, assertionsInFinal⟩
      · exact ih (initial := (initial.1 ++ headResult.assertions ++ [headResult.term],
          initial.2 ++ headResult.bounds)) (final := final) (conditionMember := later)
          (accepted := accepted)

private theorem inactiveDefaultResults_selected_exists (entry : Entrypoint)
    (aliases : AliasEnvironment) (read : Backend.Impact.Read)
    (initial final : List Term × List (Term × Nat)) (condition : Expr .bool)
    (conditionMember : condition ∈
      Backend.Impact.Read.inactiveDefaultConstraints read)
    (accepted : inactiveDefaultResults entry aliases read initial = .ok final) :
    ∃ result, normalize aliases condition = .ok result ∧
      (∀ bound ∈ result.bounds, bound ∈ final.2) ∧
      (∀ term ∈ result.assertions ++ [result.term], term ∈ final.1) := by
  exact inactiveDefaultResultsFor_selected_exists entry aliases
    (Backend.Impact.Read.inactiveDefaultConstraints read) initial final condition
    conditionMember (by simpa [inactiveDefaultResults] using accepted)

private theorem inputStateStep_yields (entry : Entrypoint) (aliases : AliasEnvironment)
    (read : Backend.Impact.Read) (current : InputState) (step : ForInStep InputState)
    (accepted : inputStateStep entry aliases read current = .ok step) :
    ∃ next, step = .yield next := by
  unfold inputStateStep at accepted
  cases guardEq : read.guard with
  | none =>
    simp only [guardEq, Bind.bind, Except.bind] at accepted
    cases defaultsEq : inactiveDefaultResults entry aliases read
        (current.2.1, current.2.2.1) with
    | error message => simp [defaultsEq] at accepted
    | ok values =>
      simp only [defaultsEq] at accepted
      refine ⟨(current.1, values.1, values.2,
        current.2.2.2 + (Backend.Impact.Read.bindings read).length), ?_⟩
      exact (Except.ok.inj accepted).symm
  | some guard =>
    simp only [guardEq, Bind.bind, Except.bind] at accepted
    cases normalizedEq : (normalize aliases guard).mapError
        (fun message => ({span := entry.span, message} : Diagnostic)) with
    | error message => simp [normalizedEq] at accepted
    | ok normalizedValue =>
      simp only [normalizedEq] at accepted
      cases defaultsEq : inactiveDefaultResults entry aliases read
          (current.2.1 ++ normalizedValue.assertions,
            current.2.2.1 ++ normalizedValue.bounds) with
      | error message => simp [defaultsEq] at accepted
      | ok values =>
        simp only [defaultsEq] at accepted
        refine ⟨(current.1.zipIdx.map fun ((input, position) : InputRequirement × Nat) =>
          if current.2.2.2 ≤ position && position < current.2.2.2 +
              (Backend.Impact.Read.bindings read).length then
            {input with activityGuard := some normalizedValue.term} else input,
          values.1, values.2, current.2.2.2 +
            (Backend.Impact.Read.bindings read).length), ?_⟩
        exact (Except.ok.inj accepted).symm

private theorem inputStateStep_preserves (entry : Entrypoint) (aliases : AliasEnvironment)
    (read : Backend.Impact.Read) (current next : InputState)
    (accepted : inputStateStep entry aliases read current = .ok (.yield next)) :
    (∀ term ∈ current.2.1, term ∈ next.2.1) ∧
    (∀ bound ∈ current.2.2.1, bound ∈ next.2.2.1) := by
  unfold inputStateStep at accepted
  cases guardEq : read.guard with
  | none =>
    simp only [guardEq, Bind.bind, Except.bind] at accepted
    cases defaultsEq : inactiveDefaultResults entry aliases read
        (current.2.1, current.2.2.1) with
    | error message => simp [defaultsEq] at accepted
    | ok values =>
      simp only [defaultsEq] at accepted
      have nextEq : (current.1, values.1, values.2,
          current.2.2.2 + (Backend.Impact.Read.bindings read).length) = next := by
        injection (Except.ok.inj accepted)
      subst next
      have preserved := inactiveDefaultResultsFor_preserves entry aliases
        (Backend.Impact.Read.inactiveDefaultConstraints read)
        (current.2.1, current.2.2.1) values (by
          simpa [inactiveDefaultResults] using defaultsEq)
      exact preserved
  | some guard =>
    simp only [guardEq, Bind.bind, Except.bind] at accepted
    cases normalizedEq : (normalize aliases guard).mapError
        (fun message => ({span := entry.span, message} : Diagnostic)) with
    | error message => simp [normalizedEq] at accepted
    | ok normalizedValue =>
      simp only [normalizedEq] at accepted
      cases defaultsEq : inactiveDefaultResults entry aliases read
          (current.2.1 ++ normalizedValue.assertions,
            current.2.2.1 ++ normalizedValue.bounds) with
      | error message => simp [defaultsEq] at accepted
      | ok values =>
        simp only [defaultsEq] at accepted
        have nextEq : (current.1.zipIdx.map fun ((input, position) : InputRequirement × Nat) =>
            if current.2.2.2 ≤ position && position < current.2.2.2 +
                (Backend.Impact.Read.bindings read).length then
              {input with activityGuard := some normalizedValue.term} else input,
            values.1, values.2, current.2.2.2 +
              (Backend.Impact.Read.bindings read).length) = next := by
          injection (Except.ok.inj accepted)
        subst next
        have preserved := inactiveDefaultResultsFor_preserves entry aliases
          (Backend.Impact.Read.inactiveDefaultConstraints read)
          (current.2.1 ++ normalizedValue.assertions,
            current.2.2.1 ++ normalizedValue.bounds) values (by
              simpa [inactiveDefaultResults] using defaultsEq)
        constructor
        · intro term member
          exact preserved.1 term (List.mem_append_left _ member)
        · intro bound member
          exact preserved.2 bound (List.mem_append_left _ member)

private theorem inputStateStep_selected_exists (entry : Entrypoint) (aliases : AliasEnvironment)
    (read : Backend.Impact.Read) (current next : InputState) (condition : Expr .bool)
    (conditionMember : condition ∈
      Backend.Impact.Read.inactiveDefaultConstraints read)
    (accepted : inputStateStep entry aliases read current = .ok (.yield next)) :
    ∃ result, normalize aliases condition = .ok result ∧
      (∀ bound ∈ result.bounds, bound ∈ next.2.2.1) ∧
      (∀ term ∈ result.assertions ++ [result.term], term ∈ next.2.1) := by
  unfold inputStateStep at accepted
  cases guardEq : read.guard with
  | none =>
    simp only [guardEq, Bind.bind, Except.bind] at accepted
    cases defaultsEq : inactiveDefaultResults entry aliases read
        (current.2.1, current.2.2.1) with
    | error message => simp [defaultsEq] at accepted
    | ok values =>
      simp only [defaultsEq] at accepted
      have nextEq : (current.1, values.1, values.2,
          current.2.2.2 + (Backend.Impact.Read.bindings read).length) = next := by
        injection (Except.ok.inj accepted)
      subst next
      obtain ⟨result, normalized, boundsMember, assertionMembers⟩ :=
        inactiveDefaultResults_selected_exists entry aliases read
          (current.2.1, current.2.2.1) values condition conditionMember
          (by simpa [inactiveDefaultResults] using defaultsEq)
      exact ⟨result, normalized, boundsMember, assertionMembers⟩
  | some guard =>
    simp only [guardEq, Bind.bind, Except.bind] at accepted
    cases normalizedGuardEq : (normalize aliases guard).mapError
        (fun message => ({span := entry.span, message} : Diagnostic)) with
    | error message => simp [normalizedGuardEq] at accepted
    | ok normalizedGuard =>
      simp only [normalizedGuardEq] at accepted
      cases defaultsEq : inactiveDefaultResults entry aliases read
          (current.2.1 ++ normalizedGuard.assertions,
            current.2.2.1 ++ normalizedGuard.bounds) with
      | error message => simp [defaultsEq] at accepted
      | ok values =>
        simp only [defaultsEq] at accepted
        have nextEq : (current.1.zipIdx.map fun ((input, position) : InputRequirement × Nat) =>
            if current.2.2.2 ≤ position && position < current.2.2.2 +
                (Backend.Impact.Read.bindings read).length then
              {input with activityGuard := some normalizedGuard.term} else input,
            values.1, values.2, current.2.2.2 +
              (Backend.Impact.Read.bindings read).length) = next := by
          injection (Except.ok.inj accepted)
        subst next
        obtain ⟨result, normalized, boundsMember, assertionMembers⟩ :=
          inactiveDefaultResults_selected_exists entry aliases read
            (current.2.1 ++ normalizedGuard.assertions,
              current.2.2.1 ++ normalizedGuard.bounds) values condition conditionMember
            (by simpa [inactiveDefaultResults] using defaultsEq)
        exact ⟨result, normalized, boundsMember, assertionMembers⟩

private theorem inputStateFold_preserves (entry : Entrypoint) (aliases : AliasEnvironment)
    (reads : List Backend.Impact.Read) (initial final : InputState)
    (accepted : forIn reads initial (inputStateStep entry aliases) = .ok final) :
    (∀ term ∈ initial.2.1, term ∈ final.2.1) ∧
    (∀ bound ∈ initial.2.2.1, bound ∈ final.2.2.1) := by
  induction reads generalizing initial final with
  | nil =>
    simp [List.forIn_nil] at accepted
    cases accepted
    exact ⟨by intro term member; exact member, by intro bound member; exact member⟩
  | cons read rest ih =>
    rw [List.forIn_cons] at accepted
    cases stepAccepted : inputStateStep entry aliases read initial with
    | error message => simp [stepAccepted, Bind.bind, Except.bind] at accepted
    | ok step =>
      simp only [stepAccepted, Bind.bind, Except.bind] at accepted
      obtain ⟨next, stepEq⟩ := inputStateStep_yields entry aliases read initial step stepAccepted
      subst step
      have nextAccepted : forIn rest next (inputStateStep entry aliases) = .ok final := accepted
      obtain ⟨assertionsPreserved, boundsPreserved⟩ := inputStateStep_preserves
        entry aliases read initial next stepAccepted
      obtain ⟨assertionsInFinal, boundsInFinal⟩ :=
        ih (initial := next) (final := final) nextAccepted
      constructor
      · intro term member
        exact assertionsInFinal term (assertionsPreserved term member)
      · intro bound member
        exact boundsInFinal bound (boundsPreserved bound member)

private theorem inputStateFold_selected_exists (entry : Entrypoint)
    (aliases : AliasEnvironment) (reads : List Backend.Impact.Read)
    (initial final : InputState) (read : Backend.Impact.Read) (condition : Expr .bool)
    (readMember : read ∈ reads)
    (conditionMember : condition ∈ Backend.Impact.Read.inactiveDefaultConstraints read)
    (accepted : forIn reads initial (inputStateStep entry aliases) = .ok final) :
    ∃ result, normalize aliases condition = .ok result ∧
      (∀ bound ∈ result.bounds, bound ∈ final.2.2.1) ∧
      (∀ term ∈ result.assertions ++ [result.term], term ∈ final.2.1) := by
  induction reads generalizing initial final with
  | nil => simp at readMember
  | cons head rest ih =>
    rw [List.forIn_cons] at accepted
    cases stepAccepted : inputStateStep entry aliases head initial with
    | error message => simp [stepAccepted, Bind.bind, Except.bind] at accepted
    | ok step =>
      simp only [stepAccepted, Bind.bind, Except.bind] at accepted
      obtain ⟨next, stepEq⟩ := inputStateStep_yields entry aliases head initial step stepAccepted
      subst step
      rcases List.mem_cons.mp readMember with same | later
      · have readEq : head = read := same.symm
        subst head
        obtain ⟨result, normalized, boundsMember, assertionMembers⟩ :=
          inputStateStep_selected_exists entry aliases read initial next condition
            conditionMember stepAccepted
        obtain ⟨assertionsPreserved, boundsPreserved⟩ :=
          inputStateFold_preserves entry aliases rest next final accepted
        exact ⟨result, normalized,
          (fun bound member => boundsPreserved bound (boundsMember bound member)),
          (fun term member => assertionsPreserved term (assertionMembers term member))⟩
      · exact ih (initial := next) (final := final) (readMember := later)
          (accepted := accepted)

/-- A checked expected entrypoint retains normalized plan guards in its
assertions and bounds. For Native, Bool, and UInt read scalars, the post-read
alias fold leaves the normalized output frame unchanged. -/
theorem expectedEntrypoint_guards (state : List StateDecl) (entry : Entrypoint)
    (expected : Expected) (plan : Backend.Impact.Plan)
    (lowered : Backend.Impact.lower state entry = .ok plan)
    (accepted : expectedEntrypoint state entry = .ok expected)
    (scalarReads : ∀ read ∈
      (plan.reads.drop (Backend.Impact.publicInputReadCount entry.circuit.inputs)).flatMap
        Backend.Impact.Read.scalarReads,
      scalarAliasReadType read.ty) :
    ∃ (outputFrame : OutputFrame) (guards : List Normalized),
      normalizeOutputs (entrypointSeedAliases entry plan) entry.circuit.outputs =
        .ok outputFrame ∧
      plan.guards.mapM (normalize outputFrame.1) = .ok guards ∧
      (∀ term ∈ guards.flatMap (fun item => item.assertions ++ [item.term]),
        term ∈ expected.assertions) ∧
      (∀ bound ∈ guards.flatMap (·.bounds), bound ∈ expected.bounds) := by
  obtain ⟨partsPlan, outputFrame, aliases, inputState, conditions, guards,
      constraintCollection, guardCollection, operationFrame, returns, activity,
      planAccepted, outputsAccepted, aliasesAccepted, inputStateAccepted,
      conditionsAccepted, guardsAccepted, constraintCollectionAccepted,
      guardCollectionAccepted, operationAccepted, returnsAccepted, activityAccepted,
      inputsShape, groupsShape, returnsShape, modeShape, rawInputsShape,
      groupGuardsShape, assertionsShape, boundsShape⟩ :=
    expectedEntrypoint_parts state entry expected accepted
  have samePlan : partsPlan = plan := Except.ok.inj (planAccepted.symm.trans lowered)
  subst partsPlan
  have aliasesEq : aliases = outputFrame.1 :=
    readAliasFold_preserves_outputFrame entry plan aliases outputFrame scalarReads aliasesAccepted
  have normalizedGuards : plan.guards.mapM (normalize outputFrame.1) = .ok guards := by
    simpa only [← aliasesEq] using guardsAccepted
  have assertionMembers : ∀ term ∈ guards.flatMap
      (fun item => item.assertions ++ [item.term]), term ∈ expected.assertions := by
    intro term member
    rw [assertionsShape]
    simp [List.mem_append, member]
  have guardCollectionEq :
      (guards.map (·.term), guards.flatMap (·.bounds),
        guards.flatMap (·.assertions)) = guardCollection := by
    have collected := guardCollectionAccepted
    simp only [guardsAccepted, Bind.bind, Except.bind, Except.mapError] at collected
    exact Except.ok.inj collected
  have guardCollectionBounds :
      guardCollection.2.1 = guards.flatMap (·.bounds) := by
    rw [← guardCollectionEq]
  have boundMembers : ∀ bound ∈ guards.flatMap (·.bounds),
      bound ∈ expected.bounds := by
    intro bound member
    rw [boundsShape, guardCollectionBounds]
    simp [List.mem_append, member]
  exact ⟨outputFrame, guards, outputsAccepted, normalizedGuards,
    assertionMembers, boundMembers⟩

/-- A checked expected entrypoint retains every normalized inactive default
from a selected post-public read in its assertions and bounds. -/
theorem expectedEntrypoint_inactiveDefault (state : List StateDecl) (entry : Entrypoint)
    (expected : Expected) (plan : Backend.Impact.Plan)
    (lowered : Backend.Impact.lower state entry = .ok plan)
    (accepted : expectedEntrypoint state entry = .ok expected)
    (scalarReads : ∀ read ∈
      (plan.reads.drop (Backend.Impact.publicInputReadCount entry.circuit.inputs)).flatMap
        Backend.Impact.Read.scalarReads,
      scalarAliasReadType read.ty)
    (read : Backend.Impact.Read) (condition : Expr .bool)
    (readMember : read ∈
      plan.reads.drop (Backend.Impact.publicInputReadCount entry.circuit.inputs))
    (conditionMember : condition ∈ Backend.Impact.Read.inactiveDefaultConstraints read) :
    ∃ (outputFrame : OutputFrame) (result : Normalized),
      normalizeOutputs (entrypointSeedAliases entry plan) entry.circuit.outputs =
        .ok outputFrame ∧
      normalize outputFrame.1 condition = .ok result ∧
      (∀ bound ∈ result.bounds, bound ∈ expected.bounds) ∧
      (∀ term ∈ result.assertions ++ [result.term], term ∈ expected.assertions) := by
  obtain ⟨partsPlan, outputFrame, aliases, inputState, conditions, guards,
      constraintCollection, guardCollection, operationFrame, returns, activity,
      planAccepted, outputsAccepted, aliasesAccepted, inputStateAccepted,
      conditionsAccepted, guardsAccepted, constraintCollectionAccepted,
      guardCollectionAccepted, operationAccepted, returnsAccepted, activityAccepted,
      inputsShape, groupsShape, returnsShape, modeShape, rawInputsShape,
      groupGuardsShape, assertionsShape, boundsShape⟩ :=
    expectedEntrypoint_parts state entry expected accepted
  have samePlan : partsPlan = plan := Except.ok.inj (planAccepted.symm.trans lowered)
  subst partsPlan
  have aliasesEq : aliases = outputFrame.1 :=
    readAliasFold_preserves_outputFrame entry plan aliases outputFrame scalarReads aliasesAccepted
  let postReads := plan.reads.drop
    (Backend.Impact.publicInputReadCount entry.circuit.inputs)
  let initialInputs := (entry.circuit.inputs.filter fun input =>
    !entry.callInputs.contains input.name).flatMap Input.requirements
  let readRequirements := postReads.flatMap fun (read : Backend.Impact.Read) =>
    read.bindings.map fun (name, ty) =>
      (match ty with
      | Ty.jubjubScalar =>
        ({identifier := "%input_" ++ name, visibility := .«public», ty := Ty.native,
          canonicalJubjubScalar := true} : InputRequirement)
      | Ty.opaqueBytes | Ty.opaqueString =>
        ({identifier := "%input_" ++ name, visibility := .«public», ty := Ty.native} : InputRequirement)
      | _ => ({identifier := "%input_" ++ name, visibility := .«public», ty} : InputRequirement))
  let initialState : InputState :=
    (initialInputs ++ readRequirements, [], [], initialInputs.length)
  have loopAccepted : forIn postReads initialState (inputStateStep entry aliases) =
      .ok inputState := by
    change forIn postReads initialState (inputStateStep entry aliases) = .ok inputState
      at inputStateAccepted
    exact inputStateAccepted
  obtain ⟨result, normalized, boundMembers, assertionMembers⟩ :=
    inputStateFold_selected_exists entry aliases postReads initialState inputState
      read condition readMember conditionMember loopAccepted
  have normalizedFrame : normalize outputFrame.1 condition = .ok result := by
    simpa only [← aliasesEq] using normalized
  have expectedBoundMembers : ∀ bound ∈ result.bounds, bound ∈ expected.bounds := by
    intro bound member
    rw [boundsShape]
    simp [List.mem_append, boundMembers bound member]
  have expectedAssertionMembers :
      ∀ term ∈ result.assertions ++ [result.term], term ∈ expected.assertions := by
    intro term member
    rw [assertionsShape]
    simp [List.mem_append, assertionMembers term member]
  exact ⟨outputFrame, result, outputsAccepted, normalizedFrame,
    expectedBoundMembers, expectedAssertionMembers⟩

/-- The checked Impact group schedule comes from normalizing each operation
of the exact accepted plan. The same output frame supplies the scalar aliases
and the expected relation retains all operation bounds and assertions. -/
theorem expectedEntrypoint_operations (state : List StateDecl) (entry : Entrypoint)
    (expected : Expected) (plan : Backend.Impact.Plan)
    (lowered : Backend.Impact.lower state entry = .ok plan)
    (accepted : expectedEntrypoint state entry = .ok expected)
    (scalarReads : ∀ read ∈
      (plan.reads.drop (Backend.Impact.publicInputReadCount entry.circuit.inputs)).flatMap
        Backend.Impact.Read.scalarReads,
      scalarAliasReadType read.ty) :
    ∃ (outputFrame : OutputFrame) (bounds : List (Term × Nat)) (assertions : List Term),
      normalizeOutputs (entrypointSeedAliases entry plan) entry.circuit.outputs =
        .ok outputFrame ∧
      collectOperations entry.span outputFrame.1 plan.operations outputFrame.2.1 =
        .ok (expected.groups, bounds, assertions) ∧
      (∀ bound ∈ bounds, bound ∈ expected.bounds) ∧
      (∀ assertion ∈ assertions, assertion ∈ expected.assertions) := by
  obtain ⟨actualPlan, outputFrame, aliases, _, _, _, _, _, operationFrame, _, _,
    planAccepted, outputsAccepted, aliasesAccepted, _, _, _, _, _, operationAccepted, _, _,
    _, groupsShape, _, _, _, _, assertionsShape, boundsShape⟩ :=
    expectedEntrypoint_parts state entry expected accepted
  have samePlan := Except.ok.inj (planAccepted.symm.trans lowered)
  subst actualPlan
  have aliasesEq :=
    readAliasFold_preserves_outputFrame entry plan aliases outputFrame scalarReads aliasesAccepted
  refine ⟨outputFrame, operationFrame.2.1, operationFrame.2.2, outputsAccepted, ?_, ?_, ?_⟩
  · rw [groupsShape, ← aliasesEq]
    exact operationAccepted
  · intro bound member
    rw [boundsShape]
    simp [member]
  · intro assertion member
    rw [assertionsShape]
    simp [member]

private theorem returnFrameStep_scalar (aliases : AliasEnvironment) (output : Output)
    (frame : ReturnFrame) (scalarType : ScalarNormalization.ScalarType output.ty) :
    returnFrameStep aliases output frame = (do
      let normal ← normalizeOutput aliases output
      pure (.yield (frame.1 ++ [normal], frame.2))) := by
  obtain ⟨field, fieldShape, normalizeField⟩ :=
    ScalarNormalization.scalarOutputField aliases output.value scalarType
  have notBytesZero : (output.ty == .bytes 0) = false := by
    cases output with
    | mk name ty value span => cases scalarType <;> rfl
  simp only [returnFrameStep, notBytesZero, Bool.false_eq_true, ite_false,
    Output.nativeReturnFields, fieldShape, normalizeOutput, List.forIn_cons,
    List.forIn_nil, normalizeField, Pure.pure, Except.pure, Except.mapError,
    Bind.bind, Except.bind]
  cases normalize aliases output.value <;> rfl

private theorem scalar_return_frame (aliases : AliasEnvironment) (outputs : List Output)
    (frame final : ReturnFrame)
    (scalar : ∀ output ∈ outputs, Nonempty (ScalarNormalization.ScalarType output.ty))
    (accepted : forIn outputs frame (returnFrameStep aliases) = .ok final) :
    ∃ normalized,
      outputs.mapM (fun output => normalize aliases output.value) = .ok normalized ∧
      final = (frame.1 ++ normalized, frame.2) := by
  induction outputs generalizing frame final with
  | nil =>
    simp only [List.forIn_nil, Pure.pure, Except.pure, Except.ok.injEq] at accepted
    subst final
    exact ⟨[], rfl, by simp⟩
  | cons output rest ih =>
    obtain ⟨scalarType⟩ := scalar output (by simp)
    rw [List.forIn_cons, returnFrameStep_scalar aliases output frame scalarType] at accepted
    unfold normalizeOutput at accepted
    cases head : normalize aliases output.value with
    | error message => simp [head, Bind.bind, Except.bind, Except.mapError] at accepted
    | ok value =>
      have remaining : forIn rest (frame.1 ++ [value], frame.2)
          (returnFrameStep aliases) = .ok final := by
        simpa [head, Bind.bind, Except.bind, Except.mapError, Pure.pure, Except.pure] using accepted
      obtain ⟨tail, tailChecked, finalShape⟩ := ih _ _
        (fun item member => scalar item (List.mem_cons_of_mem _ member)) remaining
      exact ⟨value :: tail, by simp [List.mapM_cons, head, tailChecked, Bind.bind, Except.bind, Pure.pure, Except.pure],
        by simpa only [List.append_assoc, List.singleton_append] using finalShape⟩

/-- Each admitted scalar source return accounts for one expected return term.
Its normalization uses the exact output frame and retains checked requirements. -/
theorem expectedEntrypoint_scalar_returns (state : List StateDecl) (entry : Entrypoint)
    (expected : Expected) (plan : Backend.Impact.Plan)
    (lowered : Backend.Impact.lower state entry = .ok plan)
    (accepted : expectedEntrypoint state entry = .ok expected)
    (scalarReads : ∀ read ∈
      (plan.reads.drop (Backend.Impact.publicInputReadCount entry.circuit.inputs)).flatMap
        Backend.Impact.Read.scalarReads,
      scalarAliasReadType read.ty)
    (scalarReturns : ∀ output ∈ entry.returns, Nonempty (ScalarNormalization.ScalarType output.ty)) :
    ∃ (outputFrame : OutputFrame) (normalized : List Normalized),
      normalizeOutputs (entrypointSeedAliases entry plan) entry.circuit.outputs =
        .ok outputFrame ∧
      entry.returns.mapM (fun output => normalize outputFrame.1 output.value) = .ok normalized ∧
      expected.returns = normalized.map (·.term) ∧
      (∀ bound ∈ normalized.flatMap (·.bounds), bound ∈ expected.bounds) ∧
      (∀ term ∈ normalized.flatMap (·.assertions), term ∈ expected.assertions) := by
  obtain ⟨actualPlan, outputFrame, aliases, _, _, _, _, _, _, returns, _,
    planAccepted, outputsAccepted, aliasesAccepted, _, _, _, _, _, _, returnsAccepted, _,
    _, _, returnsShape, _, _, _, assertionsShape, boundsShape⟩ :=
    expectedEntrypoint_parts state entry expected accepted
  have samePlan := Except.ok.inj (planAccepted.symm.trans lowered)
  subst actualPlan
  have aliasesEq :=
    readAliasFold_preserves_outputFrame entry plan aliases outputFrame scalarReads aliasesAccepted
  obtain ⟨normalized, checked, exactReturns⟩ :=
    scalar_return_frame aliases entry.returns ([], []) returns scalarReturns returnsAccepted
  subst returns
  refine ⟨outputFrame, normalized, outputsAccepted,
    by simpa only [aliasesEq] using checked, by simpa using returnsShape, ?_, ?_⟩
  · intro bound member
    rw [boundsShape]
    simp [member]
  · intro term member
    rw [assertionsShape]
    simp [member]

/-- The accepted expected constructor retains the actual normalized source
circuit outputs and constraints. Supported post-public scalar read aliases
leave the output frame's aliases unchanged. Output bounds enter expected
bounds through the initial bound prefix passed to the production operation
collector. -/
theorem expectedEntrypoint_sourceCircuitRequirements
    (state : List StateDecl) (entry : Entrypoint) (expected : Expected)
    (plan : Backend.Impact.Plan)
    (lowered : Backend.Impact.lower state entry = .ok plan)
    (accepted : expectedEntrypoint state entry = .ok expected)
    (scalarReads : ∀ read ∈
      (plan.reads.drop (Backend.Impact.publicInputReadCount entry.circuit.inputs)).flatMap
        Backend.Impact.Read.scalarReads,
      scalarAliasReadType read.ty) :
    ∃ (outputFrame : OutputFrame) (conditions : List Normalized),
      normalizeOutputs (entrypointSeedAliases entry plan) entry.circuit.outputs =
        .ok outputFrame ∧
      entry.circuit.constraints.mapM (normalize outputFrame.1) = .ok conditions ∧
      (∀ bound ∈ outputFrame.2.1, bound ∈ expected.bounds) ∧
      (∀ assertion ∈ outputFrame.2.2, assertion ∈ expected.assertions) ∧
      (∀ bound ∈ conditions.flatMap (·.bounds), bound ∈ expected.bounds) ∧
      (∀ term ∈ conditions.flatMap (fun item => item.assertions ++ [item.term]),
        term ∈ expected.assertions) := by
  obtain ⟨partsPlan, outputFrame, aliases, inputState, conditions, guards,
      constraintCollection, guardCollection, operationFrame, returns, activity,
      planAccepted, outputsAccepted, aliasesAccepted, inputStateAccepted,
      conditionsAccepted, guardsAccepted, constraintCollectionAccepted,
      guardCollectionAccepted, operationAccepted, returnsAccepted, activityAccepted,
      inputsShape, groupsShape, returnsShape, modeShape, rawInputsShape,
      groupGuardsShape, assertionsShape, boundsShape⟩ :=
    expectedEntrypoint_parts state entry expected accepted
  have samePlan : partsPlan = plan := Except.ok.inj (planAccepted.symm.trans lowered)
  subst partsPlan
  have aliasesEq : aliases = outputFrame.1 :=
    readAliasFold_preserves_outputFrame entry plan aliases outputFrame scalarReads aliasesAccepted
  have normalizedConditions :
      entry.circuit.constraints.mapM (normalize outputFrame.1) = .ok conditions := by
    simpa only [← aliasesEq] using conditionsAccepted
  have constraintCollectionEq :
      (conditions.map (·.term), conditions.flatMap (·.bounds),
        conditions.flatMap (·.assertions)) = constraintCollection := by
    have collected := constraintCollectionAccepted
    simp only [conditionsAccepted, Bind.bind, Except.bind, Except.mapError] at collected
    exact Except.ok.inj collected
  have conditionBoundsEq :
      constraintCollection.2.1 = conditions.flatMap (·.bounds) := by
    exact (congrArg Prod.fst (congrArg Prod.snd constraintCollectionEq)).symm
  have operationBoundsPrefix :
      ∀ bound ∈ outputFrame.2.1, bound ∈ operationFrame.2.1 := by
    unfold collectOperations at operationAccepted
    simp only [bind_ok] at operationAccepted
    obtain ⟨pieces, piecesAccepted, resultAccepted⟩ := operationAccepted
    have resultEq := Except.ok.inj resultAccepted
    have boundsEq :
        outputFrame.2.1 ++ pieces.flatMap (fun piece => piece.2.1) = operationFrame.2.1 :=
      congrArg Prod.fst (congrArg Prod.snd resultEq)
    intro bound member
    rw [← boundsEq]
    exact List.mem_append_left _ member
  have outputBoundMembers : ∀ bound ∈ outputFrame.2.1, bound ∈ expected.bounds := by
    intro bound member
    rw [boundsShape]
    simp [List.mem_append, operationBoundsPrefix bound member]
  have outputAssertionMembers : ∀ assertion ∈ outputFrame.2.2,
      assertion ∈ expected.assertions := by
    intro assertion member
    rw [assertionsShape]
    simp [List.mem_append, member]
  have conditionBoundMembers : ∀ bound ∈ conditions.flatMap (·.bounds),
      bound ∈ expected.bounds := by
    intro bound member
    rw [boundsShape, conditionBoundsEq]
    simp [List.mem_append, member]
  have conditionAssertionMembers :
      ∀ term ∈ conditions.flatMap (fun item => item.assertions ++ [item.term]),
        term ∈ expected.assertions := by
    intro term member
    rw [assertionsShape]
    simp [List.mem_append, member]
  exact ⟨outputFrame, conditions, outputsAccepted, normalizedConditions,
    outputBoundMembers, outputAssertionMembers, conditionBoundMembers,
    conditionAssertionMembers⟩

/-- Every post-public Native, Bool, or UInt read descriptor appears in the
accepted expected input list. The projection omits activityGuard because the
expected constructor fills that field for guarded reads after making the
descriptor from its binding. -/
theorem expectedEntrypoint_scalarReadDescriptor
    (state : List StateDecl) (entry : Entrypoint) (expected : Expected)
    (accepted : expectedEntrypoint state entry = .ok expected)
    (plan : Backend.Impact.Plan)
    (planAccepted : Backend.Impact.lower state entry = .ok plan)
    (read : Backend.Impact.Read) (name : String) (ty : Ty)
    (postPublic : read ∈ plan.reads.drop
      (Backend.Impact.publicInputReadCount entry.circuit.inputs))
    (singleton : read.bindings = [(name, ty)])
    (supported : ty = .native ∨ ty = .bool ∨ ∃ width, ty = .uint width) :
    ∃ requirement, requirement ∈ expected.inputs ∧
      inputRequirementCore requirement = ("%input_" ++ name, .«public», ty, false) := by
  obtain ⟨actualPlan, _, aliases, inputState, _, _, _, _, _, _, _,
      lowerAccepted, _, _, inputStateAccepted, _, _, _, _, _, _, _, inputShape, _, _, _, _, _, _⟩ :=
    expectedEntrypoint_parts state entry expected accepted
  have planEq : actualPlan = plan := Except.ok.inj (lowerAccepted.symm.trans planAccepted)
  subst actualPlan
  let initialInputs := (entry.circuit.inputs.filter fun input =>
      !entry.callInputs.contains input.name).flatMap Input.requirements
  let postReads := plan.reads.drop
    (Backend.Impact.publicInputReadCount entry.circuit.inputs)
  let readRequirements := postReads.flatMap fun (read : Backend.Impact.Read) =>
    read.bindings.map fun (name, ty) =>
      (match ty with
      | Ty.jubjubScalar =>
        ({identifier := "%input_" ++ name, visibility := .«public», ty := Ty.native,
          canonicalJubjubScalar := true} : InputRequirement)
      | Ty.opaqueBytes | Ty.opaqueString =>
        ({identifier := "%input_" ++ name, visibility := .«public», ty := Ty.native} : InputRequirement)
      | _ => ({identifier := "%input_" ++ name, visibility := .«public», ty} : InputRequirement))
  let initialState : InputState :=
    (initialInputs ++ readRequirements, [], [], initialInputs.length)
  have loopAccepted : forIn postReads initialState (inputStateStep entry aliases) =
      .ok inputState := by
    change forIn postReads initialState (inputStateStep entry aliases) = .ok inputState
      at inputStateAccepted
    exact inputStateAccepted
  have corePreserved : inputState.1.map inputRequirementCore =
      initialState.1.map inputRequirementCore := by
    refine list_forIn_preserves_projection
      (items := postReads) (initial := initialState) (final := inputState)
      (project := fun inputState : List InputRequirement × List Term ×
        List (Term × Nat) × Nat => inputState.1.map inputRequirementCore)
      (step := inputStateStep entry aliases)
      (by
        intro read current result stepAccepted
        cases result with
        | done next =>
          unfold inputStateStep at stepAccepted
          cases guardEq : read.guard with
          | none =>
            simp only [guardEq, Bind.bind, Except.bind] at stepAccepted
            cases defaults : inactiveDefaultResults entry aliases read
                (current.2.1, current.2.2.1) with
            | error message => simp [defaults] at stepAccepted
            | ok values =>
              simp only [defaults] at stepAccepted
              change Except.ok (ForInStep.yield
                (current.1, values.1, values.2, current.2.2.2 +
                  (Backend.Impact.Read.bindings read).length)) =
                Except.ok (ForInStep.done next) at stepAccepted
              cases stepAccepted
          | some guardTerm =>
            simp only [guardEq, Bind.bind, Except.bind] at stepAccepted
            cases normalizedEq : (normalize aliases guardTerm).mapError
                (fun message => ({span := entry.span, message} : Diagnostic)) with
            | error message => simp [normalizedEq] at stepAccepted
            | ok normalizedValue =>
              simp only [normalizedEq] at stepAccepted
              cases defaults : inactiveDefaultResults entry aliases read
                  (current.2.1 ++ normalizedValue.assertions,
                    current.2.2.1 ++ normalizedValue.bounds) with
              | error message => simp [defaults] at stepAccepted
              | ok values =>
                simp only [defaults] at stepAccepted
                change Except.ok (ForInStep.yield
                  (current.1.zipIdx.map fun ((input, position) : InputRequirement × Nat) =>
                    if current.2.2.2 ≤ position && position < current.2.2.2 +
                        (Backend.Impact.Read.bindings read).length then
                      {input with activityGuard := some normalizedValue.term} else input,
                    values.1, values.2, current.2.2.2 +
                      (Backend.Impact.Read.bindings read).length)) =
                  Except.ok (ForInStep.done next) at stepAccepted
                cases stepAccepted
        | yield next =>
          unfold inputStateStep at stepAccepted
          cases guardEq : read.guard with
          | none =>
            simp only [guardEq, Bind.bind, Except.bind] at stepAccepted
            cases defaults : inactiveDefaultResults entry aliases read
                (current.2.1, current.2.2.1) with
            | error message => simp [defaults] at stepAccepted
            | ok values =>
              simp only [defaults] at stepAccepted
              change Except.ok (ForInStep.yield
                (current.1, values.1, values.2, current.2.2.2 +
                  (Backend.Impact.Read.bindings read).length)) =
                Except.ok (ForInStep.yield next) at stepAccepted
              have stateEq : (current.1, values.1, values.2, current.2.2.2 +
                  (Backend.Impact.Read.bindings read).length) = next := by
                injection stepAccepted with yieldEq
                injection yieldEq with stateEq
              cases stateEq
              simp [forInStepValue]
          | some guardTerm =>
            simp only [guardEq, Bind.bind, Except.bind] at stepAccepted
            cases normalizedEq : (normalize aliases guardTerm).mapError
                (fun message => ({span := entry.span, message} : Diagnostic)) with
            | error message => simp [normalizedEq] at stepAccepted
            | ok normalizedValue =>
              simp only [normalizedEq] at stepAccepted
              cases defaults : inactiveDefaultResults entry aliases read
                  (current.2.1 ++ normalizedValue.assertions,
                    current.2.2.1 ++ normalizedValue.bounds) with
              | error message => simp [defaults] at stepAccepted
              | ok values =>
                simp only [defaults] at stepAccepted
                change Except.ok (ForInStep.yield
                  (current.1.zipIdx.map fun ((input, position) : InputRequirement × Nat) =>
                    if current.2.2.2 ≤ position && position < current.2.2.2 +
                        (Backend.Impact.Read.bindings read).length then
                      {input with activityGuard := some normalizedValue.term} else input,
                    values.1, values.2, current.2.2.2 +
                      (Backend.Impact.Read.bindings read).length)) =
                  Except.ok (ForInStep.yield next) at stepAccepted
                have stateEq : (current.1.zipIdx.map fun ((input, position) : InputRequirement × Nat) =>
                    if current.2.2.2 ≤ position && position < current.2.2.2 +
                        (Backend.Impact.Read.bindings read).length then
                      {input with activityGuard := some normalizedValue.term} else input,
                    values.1, values.2, current.2.2.2 +
                      (Backend.Impact.Read.bindings read).length) = next := by
                  injection stepAccepted with yieldEq
                  injection yieldEq with stateEq
                cases stateEq
                simpa only [forInStepValue] using
                  inputRequirementCore_guardedZipIdx current.1 current.2.2.2
                    (Backend.Impact.Read.bindings read).length normalizedValue.term)
      loopAccepted
  let target : InputRequirement :=
    {identifier := "%input_" ++ name, visibility := .«public», ty}
  have readRequirementMember : target ∈ readRequirements := by
    unfold readRequirements
    apply List.mem_flatMap.mpr
    refine ⟨read, postPublic, ?_⟩
    rw [singleton]
    rcases supported with native | boolean | ⟨width, uint⟩
    · subst ty
      simp [target]
    · subst ty
      simp [target]
    · subst ty
      simp [target]
  have targetMember : target ∈ initialState.1 := by
    simp [initialState, readRequirementMember]
  have coreMember : inputRequirementCore target ∈
      inputState.1.map inputRequirementCore := by
    rw [corePreserved]
    exact List.mem_map_of_mem targetMember
  obtain ⟨requirement, requirementMember, coreEq⟩ := List.mem_map.mp coreMember
  refine ⟨requirement, ?_, ?_⟩
  · rw [inputShape]
    exact requirementMember
  · simpa [target, inputRequirementCore] using coreEq

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
