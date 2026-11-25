import Noctium.Verification.GenericStateLedgerAllocation
import Noctium.Verification.GenericStateConverseResult
import Noctium.Verification.GenericStateConverseWitnessFrame
import Noctium.Verification.GenericStateConverseCandidateEnvironment
import Noctium.Verification.GenericStateOutputCompleteness
import Noctium.Verification.GenericStateOperationCompleteness
import Noctium.Verification.ScalarCircuitLowering
import Noctium.Verification.ScalarExpressionLowering
import Noctium.Verification.GenericStateExpressionEnvironment
import Noctium.Verification.GenericStateLedgerIdentifiers

namespace Noctium.Verification.GenericStateLedgerWitness
open Lean Backend NativeRelation NativeRelationJson ScalarLowering ScalarNormalization
open Backend.Native GenericStateCircuitParts

/-- Output aliases are absent from the source environment while circuit outputs
are evaluated. Pushing one therefore preserves lookup meanings for that env. -/
theorem lowerAliasAgreement_cons_unused (hash : Hash)
    (inputs witness : NativeRelation.Assignment)
    (normalAliases : Backend.Native.AliasEnvironment)
    (lowerAliases : List (String × String))
    (values : EvalEnv) (name : String) (term : Backend.Native.Term) (text : String)
    (agreement : LowerAliasAgreement hash inputs witness normalAliases lowerAliases values)
    (unused : values.lookup name = none) :
    LowerAliasAgreement hash inputs witness ((name, term) :: normalAliases)
      ((name, text) :: lowerAliases) values := by
  intro found ty raw value lookup typed
  by_cases same : found = name
  · subst found
    rw [unused] at lookup
    contradiction
  · obtain ⟨oldTerm, oldNormal, oldMeaning⟩ := agreement found ty raw value lookup typed
    have different : (found == name) = false := by simp [same]
    refine ⟨oldTerm, ?_, ?_⟩
    · simp [List.lookup_cons, different, oldNormal]
    · simpa [List.lookup_cons, different] using oldMeaning

/-- A later fresh SSA assignment preserves every operand already in scope. -/
theorem LowerAliasAgreement.of_frame (hash : Hash)
    (inputs before after : NativeRelation.Assignment)
    (normalAliases : Backend.Native.AliasEnvironment)
    (lowerAliases : List (String × String)) (values : EvalEnv) (next : Nat)
    (agreement : LowerAliasAgreement hash inputs before normalAliases lowerAliases values)
    (aliasesScoped : ∀ name text, (name, text) ∈ lowerAliases -> TextScope next text)
    (inputIdentifiers : ∀ name, validIdentifier ("%input_" ++ name) = true)
    (frame : ∀ name, InScope next name -> after name = before name) :
    LowerAliasAgreement hash inputs after normalAliases lowerAliases values := by
  intro name ty raw value lookup typed
  obtain ⟨term, normal, meaning⟩ := agreement name ty raw value lookup typed
  let text := lowerAliases.lookup name |>.getD ("%input_" ++ name)
  have textScope : TextScope next text := by
    cases found : lowerAliases.lookup name with
    | some value =>
      obtain ⟨beforeNames, afterNames, equal, _⟩ := List.lookup_eq_some_iff.mp found
      have member : (name, value) ∈ lowerAliases := by
        rw [equal]
        simp
      simpa [text, found] using aliasesScoped name value member
    | none =>
      have textEqual : text = "%input_" ++ name := by simp [text, found]
      rw [textEqual]
      apply TextScope.validReference next ("%input_" ++ name) (inputIdentifiers name)
      exact Or.inl ⟨name, rfl⟩
  have meaningAfter := OperandMeaning.of_frame hash inputs before after next text term
    (by simpa only [text] using meaning) textScope frame
  exact ⟨term, normal, by simpa only [text] using meaningAfter⟩

/-- Frame transport only needs identifier validity when an observed source
value has no SSA alias and therefore falls back to its external input id. -/
theorem LowerAliasAgreement.of_frame_observed (hash : Hash)
    (inputs before after : NativeRelation.Assignment)
    (normalAliases : Backend.Native.AliasEnvironment)
    (lowerAliases : List (String × String)) (values : EvalEnv) (next : Nat)
    (agreement : LowerAliasAgreement hash inputs before normalAliases lowerAliases values)
    (aliasesScoped : ∀ name text, (name, text) ∈ lowerAliases -> TextScope next text)
    (frame : ∀ name, InScope next name -> after name = before name) :
    LowerAliasAgreement hash inputs after normalAliases lowerAliases values := by
  intro name ty raw value lookup typed
  obtain ⟨term, normal, meaning⟩ := agreement name ty raw value lookup typed
  let text := lowerAliases.lookup name |>.getD ("%input_" ++ name)
  obtain ⟨operand, parsed, read⟩ := meaning
  have parsedText : decodeOperand (toJson text) = .ok operand := by
    simpa only [text] using parsed
  have meaningText : OperandMeaning hash inputs before text term :=
    ⟨operand, parsedText, read⟩
  have textScope := ScalarLowering.TextScope.lookup_default next lowerAliases name
    operand parsedText aliasesScoped
  have meaningAfter := OperandMeaning.of_frame hash inputs before after next text term
    meaningText textScope frame
  exact ⟨term, normal, by simpa only [text] using meaningAfter⟩

theorem LowerAliasAgreement.normalAliases_ext (hash : Hash)
    (inputs witness : NativeRelation.Assignment)
    (before after : Backend.Native.AliasEnvironment)
    (lowerAliases : List (String × String)) (values : EvalEnv)
    (agreement : LowerAliasAgreement hash inputs witness before lowerAliases values)
    (same : ∀ name ty raw value, values.lookup name = some raw -> raw.as ty = some value ->
      after.lookup name = before.lookup name) :
    LowerAliasAgreement hash inputs witness after lowerAliases values := by
  intro name ty raw value lookup typed
  obtain ⟨term, oldNormal, meaning⟩ := agreement name ty raw value lookup typed
  refine ⟨term, ?_, meaning⟩
  rw [same name ty raw value lookup typed]
  exact oldNormal

theorem LowerAliasAgreement.environment_ext (hash : Hash)
    (inputs witness : NativeRelation.Assignment)
    (normalAliases : Backend.Native.AliasEnvironment)
    (lowerAliases : List (String × String)) (before after : EvalEnv)
    (agreement : LowerAliasAgreement hash inputs witness normalAliases lowerAliases before)
    (same : ∀ name, before.lookup name = after.lookup name) :
    LowerAliasAgreement hash inputs witness normalAliases lowerAliases after := by
  intro name ty raw value lookup typed
  apply agreement name ty raw value _ typed
  rw [same name]
  exact lookup

/-- Input-only aliases survive any SSA prefix that keeps the external input
bindings fixed. The empty lower alias stack reads each value by its input id. -/
theorem LowerAliasAgreement.input_frame (hash : Hash)
    (inputs before after : NativeRelation.Assignment)
    (normalAliases : Backend.Native.AliasEnvironment) (values : EvalEnv)
    (agreement : LowerAliasAgreement hash inputs before normalAliases [] values)
    (identifiers : ∀ name, validIdentifier ("%input_" ++ name) = true)
    (frame : ∀ name, after ("%input_" ++ name) = before ("%input_" ++ name)) :
    LowerAliasAgreement hash inputs after normalAliases [] values := by
  intro name ty raw value lookup typed
  obtain ⟨term, normal, meaning⟩ := agreement name ty raw value lookup typed
  have referenceParsed : decodeOperand (toJson ("%input_" ++ name)) =
      .ok (.reference ("%input_" ++ name)) :=
    (ScalarInstructionEncoding.OperandEncoding.reference _ (identifiers name)).decode
  have operandSame : ∃ operand,
      decodeOperand (toJson ("%input_" ++ name)) = .ok operand ∧
      operand.read before = interpret hash inputs term := meaning
  rcases operandSame with ⟨operand, parsed, oldRead⟩
  have operandEqual : operand = .reference ("%input_" ++ name) :=
    Except.ok.inj (parsed.symm.trans referenceParsed)
  subst operand
  refine ⟨term, normal, ?_⟩
  apply OperandMeaning.reference hash inputs after _ (identifiers name) term
  simp only [Operand.read.eq_def, frame name]
  exact oldRead

/-- Lower one successful condition in any ledger alias stack. Unlike the
standalone-circuit wrapper, this keeps computed output aliases in scope. -/
theorem lowerExpr_assert_complete (ctx : EvalContext) (hash : Hash)
    (implementation : HashAgreement ctx hash)
    (complete : ∀ ty (expression : Expr ty), ExprComplete expression)
    (inputs witness : NativeRelation.Assignment) (state : Zkir.LowerState)
    (aliases : Backend.Native.AliasEnvironment) (values : EvalEnv)
    (types : TypeEnv) (condition : Expr .bool)
    (valid : condition.validate {poseidon2 := true} types = .ok ())
    (evaluated : condition.eval ctx values = .ok true)
    (sourceAliases : AliasAgreement hash inputs aliases values)
    (lowerAliases : LowerAliasAgreement hash inputs witness aliases state.aliases values)
    (meaning : LowerStateMeaning hash witness state)
    (budget : (Zkir.lowerExpr condition >>= fun text =>
      Zkir.emit "assert" [("cond", toJson text)]).run state |>.2.next ≤
        (Native.maxInstructions * Native.maxVectorLength)) :
    ∃ result finalState,
      (do let text ← Zkir.lowerExpr condition
          Zkir.emit "assert" [("cond", toJson text)]).run state = ((), finalState) ∧
      LowerStateMeaning hash result finalState ∧
      LowerAliasAgreement hash inputs result aliases finalState.aliases values ∧
      (∀ name, result ("%input_" ++ name) = witness ("%input_" ++ name)) := by
  have expressionBudget : (Zkir.lowerExpr condition).run state |>.2.next ≤
      (Native.maxInstructions * Native.maxVectorLength) := by
    exact ScalarAllocation.bind_middle_budget (Zkir.lowerExpr condition)
      (fun text => Zkir.emit "assert" [("cond", toJson text)]) state
      (by intro text; exact ScalarAllocation.emit_preserves _ _) _ budget
  obtain ⟨step⟩ := complete .bool condition ctx hash implementation inputs witness
    state aliases values types true valid evaluated sourceAliases lowerAliases meaning
    expressionBudget
  have readOne : ∃ operand,
      decodeOperand (toJson step.text) = .ok operand ∧
      operand.read step.finalWitness = one := by
    obtain ⟨operand, parsed, read⟩ := step.operandMeaning
    refine ⟨operand, parsed, ?_⟩
    rw [read, step.represents.2.2]
    simp [number, scalar_one]
  have runEq :
      (Zkir.lowerExpr condition >>= fun text =>
          Zkir.emit "assert" [("cond", toJson text)]).run state =
        ((), (Zkir.emit "assert" [("cond", toJson step.text)]).run step.finalState).2 := by
    change ((fun text => Zkir.emit "assert" [("cond", toJson text)])
      ((Zkir.lowerExpr condition).run state).1).run
      ((Zkir.lowerExpr condition).run state).2 = _
    rw [step.run]
  refine ⟨step.finalWitness, ((Zkir.emit "assert" [("cond", toJson step.text)]).run step.finalState).2,
    ?_, ?_, ?_, ?_⟩
  · exact runEq
  · exact ScalarCircuitLowering.emit_assert hash step.finalWitness step.finalState
      step.stateMeaning step.text step.textScope readOne
  · change LowerAliasAgreement hash inputs step.finalWitness aliases
      step.finalState.aliases values
    exact step.aliasAgreement
  · intro name
    exact step.frame _ (Or.inl ⟨name, rfl⟩)

private theorem listMapM_preserves (expressions : List (Expr .native)) :
    ScalarAllocation.PreservesFrame (expressions.mapM Zkir.lowerExpr) := by
  induction expressions with
  | nil => exact ScalarAllocation.pure_preserves _
  | cons expression expressions ih =>
    simp only [List.mapM_cons]
    apply ScalarAllocation.bind_preserves _ _
      (ScalarAllocation.lowerExpr_preserves expression)
    intro _
    exact ih

/-- Lower an ordered field vector using the actual scalar expression lowerer.
The invariant keeps existing aliases and every `%input_` binding in scope. -/
theorem lowerExprs_complete (ctx : EvalContext) (hash : Hash)
    (implementation : HashAgreement ctx hash)
    (complete : ∀ ty (expression : Expr ty), ExprComplete expression)
    (inputs initialWitness : NativeRelation.Assignment) (initialState : Zkir.LowerState)
    (aliases : Backend.Native.AliasEnvironment) (values : EvalEnv) (types : TypeEnv)
    (expressions : List (Expr .native))
    (valid : ∀ expression ∈ expressions,
      expression.validate {poseidon2 := true} types = .ok ())
    (evaluated : ∀ expression ∈ expressions,
      ∃ value, expression.eval ctx values = .ok value)
    (sourceAliases : AliasAgreement hash inputs aliases values)
    (lowerAliases : LowerAliasAgreement hash inputs initialWitness aliases
      initialState.aliases values)
    (meaning : LowerStateMeaning hash initialWitness initialState)
    (inputFrame : ScalarCircuitLowering.InputFrame inputs initialWitness)
    (budget : (expressions.mapM Zkir.lowerExpr).run initialState |>.2.next ≤
      (Native.maxInstructions * Native.maxVectorLength)) :
    ∃ texts finalWitness finalState,
      (expressions.mapM Zkir.lowerExpr).run initialState = (texts, finalState) ∧
      LowerStateMeaning hash finalWitness finalState ∧
      LowerAliasAgreement hash inputs finalWitness aliases finalState.aliases values ∧
      ScalarCircuitLowering.InputFrame inputs finalWitness ∧
      ∀ text ∈ texts, ScalarLowering.TextScope finalState.next text := by
  induction expressions generalizing initialWitness initialState with
  | nil =>
    refine ⟨[], initialWitness, initialState, rfl, meaning, lowerAliases,
      inputFrame, ?_⟩
    simp
  | cons expression expressions ih =>
    let tail := expressions.mapM Zkir.lowerExpr
    have tailFrame : ScalarAllocation.PreservesFrame tail := listMapM_preserves expressions
    let finishText : String → StateM Zkir.LowerState (List String) := fun text =>
      tail >>= fun texts => pure (text :: texts)
    have finishTextFrame : ∀ text, ScalarAllocation.PreservesFrame (finishText text) := by
      intro text
      exact ScalarAllocation.bind_preserves _ _ tailFrame
        (fun _ => ScalarAllocation.pure_preserves _)
    have wholeBudget : ((Zkir.lowerExpr expression >>= finishText).run initialState).2.next ≤
        (Native.maxInstructions * Native.maxVectorLength) := by
      simpa only [List.mapM_cons, bind_assoc, pure_bind, tail, finishText] using budget
    have firstBudget := ScalarAllocation.bind_middle_budget
      (Zkir.lowerExpr expression) finishText initialState finishTextFrame
      (Native.maxInstructions * Native.maxVectorLength) wholeBudget
    obtain ⟨value, expressionEval⟩ := evaluated expression (by simp)
    obtain ⟨step⟩ := complete .native expression ctx hash implementation inputs
      initialWitness initialState aliases values types value
      (valid expression (by simp)) expressionEval sourceAliases lowerAliases meaning firstBudget
    have continueBudget : (finishText step.text).run step.finalState |>.2.next ≤
        (Native.maxInstructions * Native.maxVectorLength) := by
      change ((Zkir.lowerExpr expression >>= finishText).run initialState).2.next ≤ _ at wholeBudget
      simp only [StateT.run_bind] at wholeBudget
      rw [step.run] at wholeBudget
      exact wholeBudget
    have tailBudget : tail.run step.finalState |>.2.next ≤ Native.maxInstructions * Native.maxVectorLength :=
      ScalarAllocation.bind_middle_budget tail
        (fun texts => pure (step.text :: texts)) step.finalState
        (by intro texts; exact ScalarAllocation.pure_preserves _) (Native.maxInstructions * Native.maxVectorLength)
        (by simpa only [finishText] using continueBudget)
    have nextFrame : ScalarCircuitLowering.InputFrame inputs step.finalWitness := by
      intro name
      exact (step.frame _ (Or.inl ⟨name, rfl⟩)).trans (inputFrame name)
    obtain ⟨texts, finalWitness, finalState, runTail, finalMeaning,
      finalAliases, finalFrame, finalScopes⟩ := ih step.finalWitness step.finalState
      (fun item member => valid item (List.mem_cons_of_mem expression member))
      (fun item member => evaluated item (List.mem_cons_of_mem expression member))
      step.aliasAgreement step.stateMeaning nextFrame tailBudget
    have fullRun : (((expression :: expressions).mapM Zkir.lowerExpr).run initialState) =
        (step.text :: texts, finalState) := by
      have listRun : (expression :: expressions).mapM Zkir.lowerExpr =
          Zkir.lowerExpr expression >>= fun text =>
            expressions.mapM Zkir.lowerExpr >>= fun rest => pure (text :: rest) := by
        simp only [List.mapM_cons]
      have tailRun : (tail >>= fun rest => pure (step.text :: rest)).run
          step.finalState = (step.text :: texts, finalState) := by
        rw [StateT.run_bind, runTail]
        rfl
      rw [listRun, StateT.run_bind, step.run]
      exact tailRun
    have scopes : ∀ text ∈ step.text :: texts,
        TextScope finalState.next text := by
      intro text member
      rcases List.mem_cons.mp member with equal | tailMember
      · subst text
        have tailMonotone := tailFrame step.finalState
        rw [runTail] at tailMonotone
        exact step.textScope.mono tailMonotone.next
      · exact finalScopes text tailMember
    refine ⟨step.text :: texts, finalWitness, finalState, fullRun, finalMeaning,
      finalAliases, finalFrame, scopes⟩

/-- Lower the actual ordered Impact field vector and bind it as one group. -/
theorem lowerFieldsImpact_complete (ctx : EvalContext) (hash : Hash)
    (implementation : HashAgreement ctx hash)
    (complete : ∀ ty (expression : Expr ty), ExprComplete expression)
    (inputs initialWitness : NativeRelation.Assignment) (initialState : Zkir.LowerState)
    (aliases : Backend.Native.AliasEnvironment) (values : EvalEnv) (types : TypeEnv)
    (expressions : List (Expr .native))
    (valid : ∀ expression ∈ expressions,
      expression.validate {poseidon2 := true} types = .ok ())
    (evaluated : ∀ expression ∈ expressions,
      ∃ value, expression.eval ctx values = .ok value)
    (sourceAliases : AliasAgreement hash inputs aliases values)
    (lowerAliases : LowerAliasAgreement hash inputs initialWitness aliases
      initialState.aliases values)
    (meaning : LowerStateMeaning hash initialWitness initialState)
    (inputFrame : ScalarCircuitLowering.InputFrame inputs initialWitness)
    (budget : ((expressions.mapM Zkir.lowerExpr) >>= fun texts =>
      Zkir.bindPublic texts).run initialState |>.2.next ≤ Native.maxInstructions * Native.maxVectorLength) :
    ∃ finalWitness finalState,
      ((expressions.mapM Zkir.lowerExpr) >>= fun texts =>
        Zkir.bindPublic texts).run initialState = ((), finalState) ∧
      LowerStateMeaning hash finalWitness finalState ∧
      LowerAliasAgreement hash inputs finalWitness aliases finalState.aliases values ∧
      ScalarCircuitLowering.InputFrame inputs finalWitness := by
  have expressionBudget := ScalarAllocation.bind_middle_budget
    (expressions.mapM Zkir.lowerExpr) (fun texts => Zkir.bindPublic texts)
    initialState (by intro texts; exact ScalarAllocation.bindPublic_preserves _)
    (Native.maxInstructions * Native.maxVectorLength) budget
  obtain ⟨texts, finalWitness, expressionState, expressionRun, finalMeaning,
    finalAliases, finalFrame, scopes⟩ := lowerExprs_complete ctx hash implementation
      complete inputs initialWitness initialState aliases values types expressions
      valid evaluated sourceAliases lowerAliases meaning inputFrame expressionBudget
  have actualRun : ((expressions.mapM Zkir.lowerExpr) >>= fun texts =>
      Zkir.bindPublic texts).run initialState =
      ((), (Zkir.bindPublic texts).run expressionState |>.2) := by
    rw [StateT.run_bind, expressionRun]
    rfl
  refine ⟨finalWitness, (Zkir.bindPublic texts).run expressionState |>.2,
    actualRun, ?_, ?_, finalFrame⟩
  · exact ScalarCircuitLowering.emit_impact hash finalWitness expressionState
      finalMeaning texts (by intro text member; exact scopes text member)
  · change LowerAliasAgreement hash inputs finalWitness aliases
      ((Zkir.bindPublic texts).run expressionState).2.aliases values
    exact finalAliases

private def lowerOutputBody (output : Output) : StateM Zkir.LowerState Unit := do
  let text ← Zkir.lowerExpr output.value
  modify fun state => {state with aliases := (output.name, text) :: state.aliases}

private def lowerOutputLoop (outputs : List Output) : StateM Zkir.LowerState Unit :=
  forIn outputs PUnit.unit (fun output _ => do
    lowerOutputBody output
    pure (.yield PUnit.unit))

private theorem lowerOutputBody_preserves (output : Output) :
    ScalarAllocation.PreservesFrame (lowerOutputBody output) := by
  dsimp only [lowerOutputBody]
  apply ScalarAllocation.bind_preserves _ _ (ScalarAllocation.lowerExpr_preserves _)
  intro text
  exact ScalarAllocation.modify_preserves _ (by
    intro state
    change ScalarAllocation.Frame state
      {state with aliases := (output.name, text) :: state.aliases}
    exact ⟨by simp, by simp⟩)

private theorem lowerOutputLoop_preserves (outputs : List Output) :
    ScalarAllocation.PreservesFrame (lowerOutputLoop outputs) := by
  dsimp only [lowerOutputLoop]
  apply ScalarAllocation.forIn_preserves
  intro output accumulator
  apply ScalarAllocation.bind_preserves _ _ (lowerOutputBody_preserves output)
  intro _
  exact ScalarAllocation.pure_preserves _

private theorem lowerOutputLoop_cons (output : Output) (outputs : List Output) :
    lowerOutputLoop (output :: outputs) =
      lowerOutputBody output >>= fun _ => lowerOutputLoop outputs := by
  simp only [lowerOutputLoop]
  rw [List.forIn_cons]
  simp only [bind_assoc, pure_bind]

private theorem bind_ok {α β : Type} {first : Except ε α}
    {next : α → Except ε β} {result : β} :
    (first >>= next) = .ok result ↔
      ∃ value, first = .ok value ∧ next value = .ok result := by
  cases first <;> simp [Bind.bind, Except.bind]

private theorem normalizeOutput_ok (aliases : Backend.Native.AliasEnvironment)
    (output : Output) (normalized : Backend.Native.Normalized)
    (accepted : normalizeOutput aliases output = .ok normalized) :
    Backend.Native.normalize aliases output.value = .ok normalized := by
  unfold normalizeOutput at accepted
  cases checked : Backend.Native.normalize aliases output.value with
  | error message => simp [checked, Except.mapError] at accepted
  | ok found =>
    simp [checked, Except.mapError] at accepted
    subst normalized
    rfl

private theorem evalOutput_value (ctx : EvalContext) (values : EvalEnv)
    (output : Output) (pair : String × Value)
    (accepted : evalOutput ctx values output = .ok pair) :
    ∃ value, output.value.eval ctx values = .ok value ∧
      pair = (output.name, Value.pack output.ty value) := by
  unfold evalOutput at accepted
  simp only [bind_ok] at accepted
  rcases accepted with ⟨value, evaluated, shape⟩
  cases shape
  exact ⟨value, evaluated, rfl⟩

private def lowerReadBody (read : Impact.Read) : StateM Zkir.LowerState Unit := do
  let output := "%input_" ++ read.name
  Zkir.emit "public_input"
    [("guard", Json.null), ("type", toJson ("Scalar<BLS12-381>" : String)),
      ("output", toJson output)]
  Zkir.constrainType read.ty output

private theorem lowerReadBody_preserves (read : Impact.Read) :
    ScalarAllocation.PreservesFrame (lowerReadBody read) := by
  dsimp only [lowerReadBody]
  apply ScalarAllocation.bind_preserves _ _ (ScalarAllocation.emit_preserves _ _)
  intro ignored
  exact ScalarAllocation.constrainType_preserves _ _

private def lowerReadLoop (reads : List Impact.Read) : StateM Zkir.LowerState Unit :=
  forIn reads PUnit.unit (fun read _ => do
    lowerReadBody read
    pure (.yield PUnit.unit))

private theorem lowerReadLoop_preserves (reads : List Impact.Read) :
    ScalarAllocation.PreservesFrame (lowerReadLoop reads) := by
  dsimp only [lowerReadLoop]
  apply ScalarAllocation.forIn_preserves
  intro read accumulator
  apply ScalarAllocation.bind_preserves _ _ (lowerReadBody_preserves read)
  intro _
  exact ScalarAllocation.pure_preserves _

private theorem lowerReadLoop_cons (read : Impact.Read) (reads : List Impact.Read) :
    lowerReadLoop (read :: reads) = lowerReadBody read >>= fun _ => lowerReadLoop reads := by
  simp only [lowerReadLoop]
  rw [List.forIn_cons]
  simp only [bind_assoc, pure_bind]

/-- A ledger read is emitted as an input and type-constrained. This mirrors
the actual body directly and deliberately emits no standalone impact group. -/
theorem lowerReadBody_complete (hash : Hash) (inputs witness : NativeRelation.Assignment)
    (state : Zkir.LowerState) (aliases : Backend.Native.AliasEnvironment)
    (values : EvalEnv) (read : Impact.Read) (value : read.ty.Denote)
    (canonical : Canonical read.ty value)
    (binding : inputs ("%input_" ++ read.name) = scalar (number read.ty value))
    (identifier : validIdentifier ("%input_" ++ read.name) = true)
    (lowerAliases : LowerAliasAgreement hash inputs witness aliases state.aliases values)
    (meaning : LowerStateMeaning hash witness state)
    (inputFrame : ScalarCircuitLowering.InputFrame inputs witness)
    (budget : (lowerReadBody read).run state |>.2.next ≤ Native.maxInstructions * Native.maxVectorLength) :
    ∃ finalWitness finalState,
      (lowerReadBody read).run state = ((), finalState) ∧
      LowerStateMeaning hash finalWitness finalState ∧
      ScalarCircuitLowering.InputFrame inputs finalWitness ∧
      LowerAliasAgreement hash inputs finalWitness aliases finalState.aliases values ∧
      finalState.aliases = state.aliases := by
  let input : Input := ⟨read.name, read.ty, .public, {}⟩
  have emitRun : (Zkir.emit "public_input"
      [("guard", Json.null), ("type", toJson ("Scalar<BLS12-381>" : String)),
        ("output", toJson ("%input_" ++ read.name))]).run state =
      ((), (Zkir.emit "public_input"
        [("guard", Json.null), ("type", toJson ("Scalar<BLS12-381>" : String)),
          ("output", toJson ("%input_" ++ read.name))]).run state).2 := by
    rfl
  let emittedState := (Zkir.emit "public_input"
      [("guard", Json.null), ("type", toJson ("Scalar<BLS12-381>" : String)),
        ("output", toJson ("%input_" ++ read.name))]).run state |>.2
  have emitMeaning : LowerStateMeaning hash witness emittedState := by
    have publicVisibility : (Visibility.public == Visibility.public) = true := by decide
    simpa only [emittedState, input, publicVisibility, if_true] using
      ScalarCircuitLowering.emit_input hash witness state meaning input identifier
  have typeBudget : (Zkir.constrainType read.ty ("%input_" ++ read.name)).run emittedState |>.2.next ≤
      (Native.maxInstructions * Native.maxVectorLength) := by
    change (do
      Zkir.emit "public_input"
        [("guard", Json.null), ("type", toJson ("Scalar<BLS12-381>" : String)),
          ("output", toJson ("%input_" ++ read.name))]
      Zkir.constrainType read.ty ("%input_" ++ read.name)).run state |>.2.next ≤ _ at budget
    rw [StateT.run_bind, emitRun] at budget
    exact budget
  have termMeaning : OperandMeaning hash inputs witness ("%input_" ++ read.name)
      (.input ("%input_" ++ read.name)) := by
    apply OperandMeaning.reference hash inputs witness _ identifier _
    simp only [interpret_input]
    exact inputFrame read.name
  have inputScope : TextScope emittedState.next ("%input_" ++ read.name) := by
    apply TextScope.validReference emittedState.next _ identifier
    exact Or.inl ⟨read.name, rfl⟩
  obtain ⟨extended⟩ := ScalarCircuitLowering.constrain_type_complete hash inputs witness
    emittedState read.ty value ("%input_" ++ read.name) (.input ("%input_" ++ read.name))
    canonical (by simpa only [interpret_input] using binding) emitMeaning termMeaning inputScope typeBudget
  let finalState := (Zkir.constrainType read.ty ("%input_" ++ read.name)).run emittedState |>.2
  have finalFrame : ScalarCircuitLowering.InputFrame inputs extended.witness := by
    intro name
    exact (extended.frame _ (Or.inl ⟨name, rfl⟩)).trans (inputFrame name)
  have aliasesEq : finalState.aliases = state.aliases := by
    change finalState.aliases = emittedState.aliases
    rw [extended.aliases]
  have finalAliases : LowerAliasAgreement hash inputs extended.witness aliases finalState.aliases values := by
    rw [aliasesEq]
    apply LowerAliasAgreement.of_frame_observed hash inputs witness extended.witness aliases
      state.aliases values emittedState.next lowerAliases emitMeaning.aliases
    intro name scope
    exact extended.frame name scope
  refine ⟨extended.witness, finalState, ?_, ?_, finalFrame, finalAliases, aliasesEq⟩
  · change (do
      Zkir.emit "public_input"
        [("guard", Json.null), ("type", toJson ("Scalar<BLS12-381>" : String)),
          ("output", toJson ("%input_" ++ read.name))]
      Zkir.constrainType read.ty ("%input_" ++ read.name)).run state = _
    rw [StateT.run_bind, emitRun]
    rfl
  · exact extended.meaning

/-- Lower the production ledger-read fold in transcript order, carrying the
same source aliases and input frame through each public read constraint. -/
theorem lowerReadLoop_complete (hash : Hash) (inputs initialWitness : NativeRelation.Assignment)
    (initialState : Zkir.LowerState) (aliases : Backend.Native.AliasEnvironment)
    (values : EvalEnv) (reads : List Impact.Read)
    (facts : ∀ read ∈ reads, ∃ value, Canonical read.ty value ∧
      inputs ("%input_" ++ read.name) = scalar (number read.ty value))
    (identifiers : ∀ read ∈ reads, validIdentifier ("%input_" ++ read.name) = true)
    (lowerAliases : LowerAliasAgreement hash inputs initialWitness aliases
      initialState.aliases values)
    (meaning : LowerStateMeaning hash initialWitness initialState)
    (inputFrame : ScalarCircuitLowering.InputFrame inputs initialWitness)
    (budget : (lowerReadLoop reads).run initialState |>.2.next ≤ Native.maxInstructions * Native.maxVectorLength) :
    ∃ finalWitness finalState,
      (lowerReadLoop reads).run initialState = ((), finalState) ∧
      LowerStateMeaning hash finalWitness finalState ∧
      ScalarCircuitLowering.InputFrame inputs finalWitness ∧
      LowerAliasAgreement hash inputs finalWitness aliases finalState.aliases values ∧
      finalState.aliases = initialState.aliases := by
  induction reads generalizing initialWitness initialState with
  | nil =>
    refine ⟨initialWitness, initialState, ?_, meaning, inputFrame, lowerAliases, rfl⟩
    rfl
  | cons read reads ih =>
    have tailFrame : ScalarAllocation.PreservesFrame (lowerReadLoop reads) :=
      lowerReadLoop_preserves reads
    have wholeBudget : ((lowerReadBody read >>= fun _ => lowerReadLoop reads).run
        initialState).2.next ≤ Native.maxInstructions * Native.maxVectorLength := by
      simpa only [lowerReadLoop_cons] using budget
    have bodyBudget := ScalarAllocation.bind_middle_budget
      (lowerReadBody read) (fun _ => lowerReadLoop reads) initialState
      (fun _ => tailFrame) (Native.maxInstructions * Native.maxVectorLength) wholeBudget
    obtain ⟨value, canonical, binding⟩ := facts read (by simp)
    obtain ⟨middleWitness, middleState, bodyRun, middleMeaning, middleFrame,
      middleAliases, bodyAliasesEq⟩ := lowerReadBody_complete hash inputs initialWitness initialState
      aliases values read value canonical binding (identifiers read (by simp))
      lowerAliases meaning inputFrame bodyBudget
    have tailBudget : (lowerReadLoop reads).run middleState |>.2.next ≤
        (Native.maxInstructions * Native.maxVectorLength) := by
      change ((lowerReadBody read >>= fun _ => lowerReadLoop reads).run
        initialState).2.next ≤ _ at wholeBudget
      simp only [StateT.run_bind] at wholeBudget
      rw [bodyRun] at wholeBudget
      exact wholeBudget
    obtain ⟨finalWitness, finalState, tailRun, finalMeaning, finalFrame,
      finalAliases, tailAliasesEq⟩ := ih middleWitness middleState
      (fun item member => facts item (List.mem_cons_of_mem read member))
      (fun item member => identifiers item (List.mem_cons_of_mem read member))
      middleAliases middleMeaning middleFrame tailBudget
    have wholeRun : (lowerReadLoop (read :: reads)).run initialState =
        ((), finalState) := by
      rw [lowerReadLoop_cons, StateT.run_bind, bodyRun]
      exact tailRun
    exact ⟨finalWitness, finalState, wholeRun, finalMeaning, finalFrame, finalAliases,
      tailAliasesEq.trans bodyAliasesEq⟩

private def lowerGuardBody (condition : Expr .bool) : StateM Zkir.LowerState Unit := do
  let text ← Zkir.lowerExpr condition
  Zkir.emit "assert" [("cond", toJson text)]

private def lowerGuardLoop (conditions : List (Expr .bool)) : StateM Zkir.LowerState Unit :=
  forIn conditions PUnit.unit (fun condition _ => do
    lowerGuardBody condition
    pure (.yield PUnit.unit))

private theorem lowerGuardBody_preserves (condition : Expr .bool) :
    ScalarAllocation.PreservesFrame (lowerGuardBody condition) := by
  dsimp only [lowerGuardBody]
  exact ScalarAllocation.bind_preserves _ _ (ScalarAllocation.lowerExpr_preserves _)
    (fun _ => ScalarAllocation.emit_preserves _ _)

private theorem lowerGuardLoop_preserves (conditions : List (Expr .bool)) :
    ScalarAllocation.PreservesFrame (lowerGuardLoop conditions) := by
  dsimp only [lowerGuardLoop]
  apply ScalarAllocation.forIn_preserves
  intro condition accumulator
  apply ScalarAllocation.bind_preserves _ _ (lowerGuardBody_preserves condition)
  intro _
  exact ScalarAllocation.pure_preserves _

private theorem lowerGuardLoop_cons (condition : Expr .bool) (conditions : List (Expr .bool)) :
    lowerGuardLoop (condition :: conditions) =
      lowerGuardBody condition >>= fun _ => lowerGuardLoop conditions := by
  simp only [lowerGuardLoop]
  rw [List.forIn_cons]
  simp only [bind_assoc, pure_bind]

private theorem validateConstraints_members {types : TypeEnv} {span : SourceSpan}
    {conditions : List (Expr .bool)}
    (valid : validateConstraints {poseidon2 := true} types span conditions = .ok ()) :
    ∀ condition ∈ conditions,
      condition.validate {poseidon2 := true} types = .ok () := by
  induction conditions with
  | nil => simp
  | cons condition rest ih =>
    cases checked : condition.validate {poseidon2 := true} types with
    | error message => simp [validateConstraints, checked] at valid
    | ok checkedUnit =>
      cases checkedUnit
      simp only [validateConstraints, checked] at valid
      intro found member
      rcases List.mem_cons.mp member with same | member
      · cases same
        exact checked
      · exact ih valid found member

/-- Lower actual Impact guards with their successful source evaluations. -/
theorem lowerGuardLoop_complete (ctx : EvalContext) (hash : Hash)
    (implementation : HashAgreement ctx hash)
    (complete : ∀ ty (expression : Expr ty), ExprComplete expression)
    (inputs initialWitness : NativeRelation.Assignment) (initialState : Zkir.LowerState)
    (aliases : Backend.Native.AliasEnvironment) (values : EvalEnv) (types : TypeEnv)
    (conditions : List (Expr .bool))
    (valid : ∀ condition ∈ conditions,
      condition.validate {poseidon2 := true} types = .ok ())
    (evaluated : ∀ condition ∈ conditions,
      condition.eval ctx values = .ok true)
    (sourceAliases : AliasAgreement hash inputs aliases values)
    (lowerAliases : LowerAliasAgreement hash inputs initialWitness aliases
      initialState.aliases values)
    (meaning : LowerStateMeaning hash initialWitness initialState)
    (inputFrame : ScalarCircuitLowering.InputFrame inputs initialWitness)
    (budget : (lowerGuardLoop conditions).run initialState |>.2.next ≤ Native.maxInstructions * Native.maxVectorLength) :
    ∃ finalWitness finalState,
      (lowerGuardLoop conditions).run initialState = ((), finalState) ∧
      LowerStateMeaning hash finalWitness finalState ∧
      ScalarCircuitLowering.InputFrame inputs finalWitness ∧
      LowerAliasAgreement hash inputs finalWitness aliases finalState.aliases values := by
  induction conditions generalizing initialWitness initialState with
  | nil =>
    refine ⟨initialWitness, initialState, ?_, meaning, inputFrame, lowerAliases⟩
    rfl
  | cons condition conditions ih =>
    have tailFrame : ScalarAllocation.PreservesFrame (lowerGuardLoop conditions) :=
      lowerGuardLoop_preserves conditions
    have wholeBudget : ((lowerGuardBody condition >>= fun _ => lowerGuardLoop conditions).run
        initialState).2.next ≤ Native.maxInstructions * Native.maxVectorLength := by
      simpa only [lowerGuardLoop_cons] using budget
    have bodyBudget := ScalarAllocation.bind_middle_budget
      (lowerGuardBody condition) (fun _ => lowerGuardLoop conditions) initialState
      (fun _ => tailFrame) (Native.maxInstructions * Native.maxVectorLength) wholeBudget
    obtain ⟨middleWitness, middleState, bodyRun, middleMeaning, middleAliases,
      extensionFrame⟩ := lowerExpr_assert_complete ctx hash implementation complete inputs
      initialWitness initialState aliases values types condition (valid condition (by simp))
      (evaluated condition (by simp)) sourceAliases lowerAliases meaning bodyBudget
    have guardRun : (lowerGuardBody condition).run initialState = ((), middleState) := by
      simpa only [lowerGuardBody] using bodyRun
    have middleFrame : ScalarCircuitLowering.InputFrame inputs middleWitness := by
      intro name
      exact (extensionFrame name).trans (inputFrame name)
    have tailBudget : (lowerGuardLoop conditions).run middleState |>.2.next ≤
        (Native.maxInstructions * Native.maxVectorLength) := by
      change ((lowerGuardBody condition >>= fun _ => lowerGuardLoop conditions).run
        initialState).2.next ≤ _ at wholeBudget
      rw [StateT.run_bind, guardRun] at wholeBudget
      exact wholeBudget
    obtain ⟨finalWitness, finalState, tailRun, finalMeaning, finalFrame,
      finalAliases⟩ := ih middleWitness middleState
      (fun item member => valid item (List.mem_cons_of_mem condition member))
      (fun item member => evaluated item (List.mem_cons_of_mem condition member))
      middleAliases middleMeaning middleFrame tailBudget
    have wholeRun : (lowerGuardLoop (condition :: conditions)).run initialState =
        ((), finalState) := by
      rw [lowerGuardLoop_cons, StateT.run_bind, guardRun]
      exact tailRun
    exact ⟨finalWitness, finalState, wholeRun, finalMeaning, finalFrame, finalAliases⟩

private def lowerOperationBody (operation : Impact.Op) : StateM Zkir.LowerState Unit := do
  let fields ← operation.fields.mapM Zkir.lowerExpr
  Zkir.bindPublic fields

private def lowerOperationLoop (operations : List Impact.Op) : StateM Zkir.LowerState Unit :=
  forIn operations PUnit.unit (fun operation _ => do
    lowerOperationBody operation
    pure (.yield PUnit.unit))

private theorem lowerOperationBody_preserves (operation : Impact.Op) :
    ScalarAllocation.PreservesFrame (lowerOperationBody operation) := by
  dsimp only [lowerOperationBody]
  exact ScalarAllocation.bind_preserves _ _ (listMapM_preserves operation.fields)
    (fun _ => ScalarAllocation.bindPublic_preserves _)

private theorem lowerOperationLoop_preserves (operations : List Impact.Op) :
    ScalarAllocation.PreservesFrame (lowerOperationLoop operations) := by
  dsimp only [lowerOperationLoop]
  apply ScalarAllocation.forIn_preserves
  intro operation accumulator
  apply ScalarAllocation.bind_preserves _ _ (lowerOperationBody_preserves operation)
  intro _
  exact ScalarAllocation.pure_preserves _

private theorem lowerOperationLoop_cons (operation : Impact.Op)
    (operations : List Impact.Op) :
    lowerOperationLoop (operation :: operations) =
      lowerOperationBody operation >>= fun _ => lowerOperationLoop operations := by
  simp only [lowerOperationLoop]
  rw [List.forIn_cons]
  simp only [bind_assoc, pure_bind]

private theorem mapM_member {α β : Type} {function : α → Except String β}
    {values : List α} {results : List β}
    (success : values.mapM function = .ok results) (result : β)
    (member : result ∈ results) :
    ∃ value ∈ values, function value = .ok result := by
  induction values generalizing results with
  | nil => cases success; simp at member
  | cons value rest ih =>
    simp only [List.mapM_cons, bind_ok] at success
    rcases success with ⟨first, firstResult, tail, tailResult, equal⟩
    cases equal
    rcases List.mem_cons.mp member with equal | member
    · subst first
      exact ⟨value, by simp, firstResult⟩
    · obtain ⟨found, foundMember, foundResult⟩ := ih tailResult member
      exact ⟨found, List.mem_cons_of_mem _ foundMember, foundResult⟩

private theorem evalFields_values (ctx : EvalContext) (values : EvalEnv)
    (expressions : List (Expr .native)) (fields : List Scalar)
    (success : GenericStateOps.evalFields ctx values expressions = .ok fields) :
    ∀ expression ∈ expressions, ∃ value, expression.eval ctx values = .ok value := by
  induction expressions generalizing fields with
  | nil => cases success; simp
  | cons expression expressions ih =>
    unfold GenericStateOps.evalFields at success
    simp only [List.mapM_cons, bind_ok] at success
    rcases success with ⟨head, headEval, tail, tailEval, equal⟩
    cases equal
    have expressionEval : ∃ value, expression.eval ctx values = .ok value := by
      cases evaluated : expression.eval ctx values with
      | error message => simp [evaluated, Functor.map, Except.map] at headEval
      | ok value => exact ⟨value, rfl⟩
    intro found member
    rcases List.mem_cons.mp member with equal | member
    · subst found
      exact expressionEval
    · exact ih tail tailEval found member

private theorem lookup_member {items : List (String × α)} {name : String} {value : α}
    (lookup : items.lookup name = some value) : (name, value) ∈ items := by
  obtain ⟨before, after, equal, _⟩ := List.lookup_eq_some_iff.mp lookup
  rw [equal]
  simp

private theorem initialAliases_lookup_input (entry : Entrypoint)
    (plan : Impact.Plan) (input : Input) (member : input ∈ entry.circuit.inputs) :
    (GenericStateCircuitParts.initialAliases entry plan).lookup input.name =
      some (.input ("%input_" ++ input.name)) := by
  rw [GenericStateAliases.initialAliases_eq]
  have circuitLookup := ScalarNormalization.aliases_lookup entry.circuit.inputs
    input.name ⟨input, member, rfl⟩
  simp only [ScalarNormalization.circuitAliases] at circuitLookup ⊢
  rw [List.lookup_append, circuitLookup]
  rfl

private theorem lookup_reverse_append (outputs before after : EvalEnv)
    (unique : (outputs.map Prod.fst).Nodup) (name : String) :
    ((outputs.reverse ++ before) ++ after).lookup name =
      ((outputs ++ before) ++ after).lookup name := by
  simp only [List.lookup_append]
  rw [GenericStateOutputOrder.lookup_reverse_unique outputs unique name]

/-- Add decoded read values to the source environment. Their normal aliases and
SSA operands both resolve to the same preserved `%input_` assignment. -/
theorem LowerAliasAgreement.append_reads (hash : Hash)
    (inputs witness : NativeRelation.Assignment)
    (normalAliases : Backend.Native.AliasEnvironment)
    (lowerAliases : List (String × String)) (values : EvalEnv)
    (reads : List Impact.Read)
    (agreement : LowerAliasAgreement hash inputs witness normalAliases lowerAliases values)
    (normalRead : ∀ read ∈ reads,
      normalAliases.lookup read.name = some (.input ("%input_" ++ read.name)))
    (lowerReadAbsent : ∀ read ∈ reads, lowerAliases.lookup read.name = none)
    (identifiers : ∀ read ∈ reads,
      validIdentifier ("%input_" ++ read.name) = true)
    (inputFrame : ∀ name, witness ("%input_" ++ name) = inputs ("%input_" ++ name)) :
    LowerAliasAgreement hash inputs witness normalAliases lowerAliases
      (values ++ GenericStateInputValues.decodeReads reads inputs) := by
  intro name ty raw value lookup typed
  cases beforeLookup : values.lookup name with
  | some old =>
    have oldLookup : values.lookup name = some raw := by
      simp [List.lookup_append, beforeLookup] at lookup
      have equal : old = raw := lookup
      simpa [equal] using beforeLookup
    exact agreement name ty raw value oldLookup typed
  | none =>
    have readLookup : (GenericStateInputValues.decodeReads reads inputs).lookup name = some raw := by
      simp only [List.lookup_append, beforeLookup] at lookup
      exact lookup
    obtain ⟨read, readMember, pairEqual⟩ := List.mem_map.mp
      (lookup_member readLookup : (name, raw) ∈ GenericStateInputValues.decodeReads reads inputs)
    have nameEqual : read.name = name := congrArg Prod.fst pairEqual
    subst name
    have readTerm := normalRead read readMember
    have noLowerRead := lowerReadAbsent read readMember
    have operand : OperandMeaning hash inputs witness
        ("%input_" ++ read.name) (.input ("%input_" ++ read.name)) :=
      OperandMeaning.reference hash inputs witness _ (identifiers read readMember)
        (.input ("%input_" ++ read.name)) (by
          simp only [interpret_input]
          exact inputFrame read.name)
    refine ⟨.input ("%input_" ++ read.name), readTerm, ?_⟩
    simpa [noLowerRead] using operand

private def lowerCircuitInputBody (input : Input) : StateM Zkir.LowerState Unit := do
  let output := "%input_" ++ input.name
  Zkir.emit (if input.visibility == .«public» then "public_input" else "private_input")
    [("guard", Json.null), ("type", toJson ("Scalar<BLS12-381>" : String)),
      ("output", toJson output)]
  Zkir.constrainType input.ty output

private def lowerCircuitInputLoop (inputs : List Input) : StateM Zkir.LowerState Unit :=
  forIn inputs PUnit.unit (fun input _ => do
    lowerCircuitInputBody input
    pure (.yield PUnit.unit))

private theorem lowerCircuitInputBody_preserves (input : Input) :
    ScalarAllocation.PreservesFrame (lowerCircuitInputBody input) := by
  dsimp only [lowerCircuitInputBody]
  exact ScalarAllocation.bind_preserves _ _ (ScalarAllocation.emit_preserves _ _)
    (fun _ => ScalarAllocation.constrainType_preserves _ _)

private theorem lowerCircuitInputLoop_preserves (inputs : List Input) :
    ScalarAllocation.PreservesFrame (lowerCircuitInputLoop inputs) := by
  dsimp only [lowerCircuitInputLoop]
  apply ScalarAllocation.forIn_preserves
  intro input accumulator
  apply ScalarAllocation.bind_preserves _ _ (lowerCircuitInputBody_preserves input)
  intro _
  exact ScalarAllocation.pure_preserves _

private theorem lowerCircuitInputBody_complete (hash : Hash)
    (inputs : NativeRelation.Assignment) (input : Input) (value : input.ty.Denote)
    (canonical : Canonical input.ty value)
    (binding : inputs ("%input_" ++ input.name) = scalar (number input.ty value))
    (identifier : validIdentifier ("%input_" ++ input.name) = true) :
    ScalarCircuitLowering.Completes hash inputs (lowerCircuitInputBody input) := by
  apply ScalarCircuitLowering.completes_bind hash inputs _ _
    (ScalarAllocation.emit_preserves _ _)
  · intro _
    exact ScalarAllocation.constrainType_preserves _ _
  · simpa only [Zkir.nativeType_eq] using
      ScalarCircuitLowering.completes_emit_input hash inputs input identifier
  · intro _
    exact ScalarCircuitLowering.completes_input_type hash inputs input value canonical
      binding identifier

private theorem lowerCircuitInputLoop_complete (hash : Hash)
    (circuit : Circuit) (values : EvalEnv) (inputs : NativeRelation.Assignment)
    (admitted : CanonicalInputs circuit values inputs)
    (identifiers : ∀ input ∈ circuit.inputs,
      validIdentifier ("%input_" ++ input.name) = true) :
    ScalarCircuitLowering.Completes hash inputs (lowerCircuitInputLoop circuit.inputs) := by
  let body : Input → StateM Zkir.LowerState Unit := lowerCircuitInputBody
  have frames : ∀ input, ScalarAllocation.PreservesFrame (body input) :=
    lowerCircuitInputBody_preserves
  have construction : ∀ input ∈ circuit.inputs,
      ScalarCircuitLowering.Completes hash inputs (body input) := by
    intro input member
    obtain ⟨value, lookup, canonical⟩ := admitted.complete input member
    exact lowerCircuitInputBody_complete hash inputs input value canonical
      (admitted.binding input member value lookup) (identifiers input member)
  simpa only [lowerCircuitInputLoop, body] using
    ScalarCircuitLowering.completes_forIn hash inputs circuit.inputs PUnit.unit body
      frames construction

private def lowerCircuitConditionBody (condition : Expr .bool) :
    StateM Zkir.LowerState Unit := do
  let text ← Zkir.lowerExpr condition
  Zkir.emit "assert" [("cond", toJson text)]

private def lowerCircuitConditionLoop (conditions : List (Expr .bool)) :
    StateM Zkir.LowerState Unit :=
  forIn conditions PUnit.unit (fun condition _ => do
    lowerCircuitConditionBody condition
    pure (.yield PUnit.unit))

private theorem lowerCircuitConditionBody_preserves (condition : Expr .bool) :
    ScalarAllocation.PreservesFrame (lowerCircuitConditionBody condition) := by
  dsimp only [lowerCircuitConditionBody]
  exact ScalarAllocation.bind_preserves _ _ (ScalarAllocation.lowerExpr_preserves _)
    (fun _ => ScalarAllocation.emit_preserves _ _)

private theorem lowerCircuitConditionLoop_preserves (conditions : List (Expr .bool)) :
    ScalarAllocation.PreservesFrame (lowerCircuitConditionLoop conditions) := by
  dsimp only [lowerCircuitConditionLoop]
  apply ScalarAllocation.forIn_preserves
  intro condition accumulator
  apply ScalarAllocation.bind_preserves _ _ (lowerCircuitConditionBody_preserves condition)
  intro _
  exact ScalarAllocation.pure_preserves _

private theorem lowerCircuitConditionLoop_complete (ctx : EvalContext) (hash : Hash)
    (implementation : HashAgreement ctx hash)
    (complete : ∀ ty (expression : Expr ty), ExprComplete expression)
    (circuit : Circuit) (values : EvalEnv) (inputs : NativeRelation.Assignment)
    (admitted : CanonicalInputs circuit values inputs)
    (identifiers : ∀ input ∈ circuit.inputs,
      validIdentifier ("%input_" ++ input.name) = true)
    (constraintsValid : validateConstraints {poseidon2 := true}
      (circuit.inputs.map (fun input => (input.name, input.ty))) circuit.span
      circuit.constraints = .ok ())
    (constraintsRun : runConstraints ctx values circuit.constraints = .ok ()) :
    ScalarCircuitLowering.Completes hash inputs
      (lowerCircuitConditionLoop circuit.constraints) := by
  have conditionFacts := ScalarCircuitLowering.constraints_members ctx circuit values
    constraintsValid constraintsRun
  let body : Expr .bool → StateM Zkir.LowerState Unit := lowerCircuitConditionBody
  have frames : ∀ condition, ScalarAllocation.PreservesFrame (body condition) :=
    lowerCircuitConditionBody_preserves
  have construction : ∀ condition ∈ circuit.constraints,
      ScalarCircuitLowering.Completes hash inputs (body condition) := by
    intro condition member
    simpa only [body, lowerCircuitConditionBody] using
      ScalarCircuitLowering.completes_condition ctx hash implementation complete
        circuit values inputs admitted identifiers condition
        (conditionFacts condition member).1 (conditionFacts condition member).2
  simpa only [lowerCircuitConditionLoop, body] using
    ScalarCircuitLowering.completes_forIn hash inputs circuit.constraints PUnit.unit
      body frames construction

private def lowerLedgerPrelude (circuit : Circuit) : StateM Zkir.LowerState Unit := do
  lowerCircuitInputLoop circuit.inputs
  lowerCircuitConditionLoop circuit.constraints

private theorem lowerLedgerPrelude_preserves (circuit : Circuit) :
    ScalarAllocation.PreservesFrame (lowerLedgerPrelude circuit) := by
  dsimp only [lowerLedgerPrelude]
  exact ScalarAllocation.bind_preserves _ _
    (lowerCircuitInputLoop_preserves circuit.inputs)
    (fun _ => lowerCircuitConditionLoop_preserves circuit.constraints)

/-- The actual input and circuit-assertion prefix constructs a checked
instruction state while leaving the alias stack empty for output lowering. -/
theorem lowerLedgerPrelude_complete (ctx : EvalContext) (hash : Hash)
    (implementation : HashAgreement ctx hash)
    (complete : ∀ ty (expression : Expr ty), ExprComplete expression)
    (circuit : Circuit) (values : EvalEnv) (inputs : NativeRelation.Assignment)
    (admitted : CanonicalInputs circuit values inputs)
    (identifiers : ∀ input ∈ circuit.inputs,
      validIdentifier ("%input_" ++ input.name) = true)
    (validation : circuit.validate {poseidon2 := true} = .ok ())
    (result : EvalEnv) (source : circuit.run ctx values = .ok result) :
    ScalarCircuitLowering.Completes hash inputs (lowerLedgerPrelude circuit) := by
  obtain ⟨constraintValidation, _⟩ :=
    ScalarNormalization.circuit_validation_parts circuit validation
  obtain ⟨constraintSuccess, _⟩ :=
    ScalarNormalization.circuit_run_steps ctx circuit values result source
  have inputComplete := lowerCircuitInputLoop_complete hash circuit values inputs
    admitted identifiers
  have conditionComplete := lowerCircuitConditionLoop_complete ctx hash implementation
    complete circuit values inputs admitted identifiers constraintValidation constraintSuccess
  exact ScalarCircuitLowering.completes_bind hash inputs
    (lowerCircuitInputLoop circuit.inputs)
    (fun _ => lowerCircuitConditionLoop circuit.constraints)
    (lowerCircuitInputLoop_preserves circuit.inputs)
    (fun _ => lowerCircuitConditionLoop_preserves circuit.constraints)
    inputComplete (fun _ => conditionComplete)

private def lowerLedgerAfterGuards (plan : Impact.Plan) :
    StateM Zkir.LowerState Unit := do
  lowerOperationLoop plan.operations
  Zkir.emit "output" [("vals", toJson ([] : List String))]

private def lowerLedgerAfterReads (plan : Impact.Plan) :
    StateM Zkir.LowerState Unit := do
  lowerGuardLoop plan.guards
  lowerLedgerAfterGuards plan

private def lowerLedgerAfterOutput (entry : Entrypoint) (plan : Impact.Plan) :
    StateM Zkir.LowerState Unit := do
  let publicCount := (entry.circuit.inputs.filter
    (·.visibility == .«public»)).length
  lowerReadLoop (plan.reads.drop publicCount)
  lowerLedgerAfterReads plan

private def lowerLedgerAfterPrelude (entry : Entrypoint) (plan : Impact.Plan) :
    StateM Zkir.LowerState Unit := do
  lowerOutputLoop entry.circuit.outputs
  lowerLedgerAfterOutput entry plan

private def lowerLedgerBodyStages (entry : Entrypoint) (plan : Impact.Plan) :
    StateM Zkir.LowerState Unit := do
  lowerLedgerPrelude entry.circuit
  lowerLedgerAfterPrelude entry plan

/-- This decomposition is definitionally the production body, including the
actual order of circuit inputs, outputs, ledger reads, guards, opcode groups,
and the empty contract return instruction. -/
theorem lowerEntrypointBody_eq_stages (entry : Entrypoint) (plan : Impact.Plan) :
    Zkir.lowerEntrypointBody entry plan = lowerLedgerBodyStages entry plan := by
  unfold Zkir.lowerEntrypointBody lowerLedgerBodyStages lowerLedgerAfterPrelude
    lowerLedgerAfterOutput lowerLedgerAfterReads lowerLedgerAfterGuards
    lowerLedgerPrelude lowerCircuitInputLoop
    lowerCircuitInputBody lowerCircuitConditionLoop lowerCircuitConditionBody
    lowerOutputLoop lowerOutputBody lowerReadLoop
    lowerReadBody lowerGuardLoop lowerGuardBody lowerOperationLoop lowerOperationBody
  simp only [Zkir.nativeType_eq, bind_assoc, pure_bind]

private theorem lowerLedgerAfterGuards_preserves (plan : Impact.Plan) :
    ScalarAllocation.PreservesFrame (lowerLedgerAfterGuards plan) := by
  dsimp only [lowerLedgerAfterGuards]
  exact ScalarAllocation.bind_preserves _ _
    (lowerOperationLoop_preserves plan.operations)
    (fun _ => ScalarAllocation.emit_preserves _ _)

private theorem lowerLedgerAfterReads_preserves (plan : Impact.Plan) :
    ScalarAllocation.PreservesFrame (lowerLedgerAfterReads plan) := by
  dsimp only [lowerLedgerAfterReads]
  exact ScalarAllocation.bind_preserves _ _ (lowerGuardLoop_preserves plan.guards)
    (fun _ => lowerLedgerAfterGuards_preserves plan)

private theorem lowerLedgerAfterOutput_preserves (entry : Entrypoint)
    (plan : Impact.Plan) :
    ScalarAllocation.PreservesFrame (lowerLedgerAfterOutput entry plan) := by
  dsimp only [lowerLedgerAfterOutput]
  exact ScalarAllocation.bind_preserves _ _
    (lowerReadLoop_preserves (plan.reads.drop
      ((entry.circuit.inputs.filter (·.visibility == .«public»)).length)))
    (fun _ => lowerLedgerAfterReads_preserves plan)

private theorem lowerLedgerAfterPrelude_preserves (entry : Entrypoint)
    (plan : Impact.Plan) :
    ScalarAllocation.PreservesFrame (lowerLedgerAfterPrelude entry plan) := by
  dsimp only [lowerLedgerAfterPrelude]
  exact ScalarAllocation.bind_preserves _ _
    (lowerOutputLoop_preserves entry.circuit.outputs)
    (fun _ => lowerLedgerAfterOutput_preserves entry plan)

/-- Lower each actual Impact opcode as its own public group. The ordered
field vector, including each group boundary, matches the production fold. -/
theorem lowerOperationLoop_complete (ctx : EvalContext) (hash : Hash)
    (implementation : HashAgreement ctx hash)
    (complete : ∀ ty (expression : Expr ty), ExprComplete expression)
    (inputs initialWitness : NativeRelation.Assignment) (initialState : Zkir.LowerState)
    (aliases : Backend.Native.AliasEnvironment) (values : EvalEnv) (types : TypeEnv)
    (operations : List Impact.Op) (groups : List (List Scalar))
    (valid : ∀ operation ∈ operations, ∀ expression ∈ operation.fields,
      expression.validate {poseidon2 := true} types = .ok ())
    (fieldEvaluations : operations.mapM (fun operation =>
      GenericStateOps.evalFields ctx values operation.fields) = .ok groups)
    (sourceAliases : AliasAgreement hash inputs aliases values)
    (lowerAliases : LowerAliasAgreement hash inputs initialWitness aliases
      initialState.aliases values)
    (meaning : LowerStateMeaning hash initialWitness initialState)
    (inputFrame : ScalarCircuitLowering.InputFrame inputs initialWitness)
    (budget : (lowerOperationLoop operations).run initialState |>.2.next ≤ Native.maxInstructions * Native.maxVectorLength) :
    ∃ finalWitness finalState,
      (lowerOperationLoop operations).run initialState = ((), finalState) ∧
      LowerStateMeaning hash finalWitness finalState ∧
      ScalarCircuitLowering.InputFrame inputs finalWitness ∧
      LowerAliasAgreement hash inputs finalWitness aliases finalState.aliases values := by
  induction operations generalizing initialWitness initialState groups with
  | nil =>
    simp only [List.mapM_nil] at fieldEvaluations
    cases fieldEvaluations
    refine ⟨initialWitness, initialState, ?_, meaning, inputFrame, lowerAliases⟩
    rfl
  | cons operation operations ih =>
    simp only [List.mapM_cons, bind_ok] at fieldEvaluations
    obtain ⟨headGroup, headEval, tailGroups, tailEval, groupsShape⟩ := fieldEvaluations
    cases groupsShape
    have tailFrame : ScalarAllocation.PreservesFrame (lowerOperationLoop operations) :=
      lowerOperationLoop_preserves operations
    have wholeBudget : ((lowerOperationBody operation >>= fun _ =>
        lowerOperationLoop operations).run initialState).2.next ≤ Native.maxInstructions * Native.maxVectorLength := by
      simpa only [lowerOperationLoop_cons] using budget
    have bodyBudget := ScalarAllocation.bind_middle_budget
      (lowerOperationBody operation) (fun _ => lowerOperationLoop operations) initialState
      (fun _ => tailFrame) (Native.maxInstructions * Native.maxVectorLength) wholeBudget
    have expressionValid : ∀ expression ∈ operation.fields,
        expression.validate {poseidon2 := true} types = .ok () := by
      intro expression member
      exact valid operation (by simp) expression member
    have expressionSuccess := evalFields_values ctx values operation.fields headGroup headEval
    obtain ⟨middleWitness, middleState, bodyRun, middleMeaning, middleAliases,
      middleFrame⟩ := lowerFieldsImpact_complete ctx hash implementation complete inputs
      initialWitness initialState aliases values types operation.fields expressionValid
      expressionSuccess sourceAliases lowerAliases meaning inputFrame bodyBudget
    have operationRun : (lowerOperationBody operation).run initialState =
        ((), middleState) := by
      simpa only [lowerOperationBody] using bodyRun
    have tailBudget : (lowerOperationLoop operations).run middleState |>.2.next ≤
        (Native.maxInstructions * Native.maxVectorLength) := by
      change ((lowerOperationBody operation >>= fun _ =>
        lowerOperationLoop operations).run initialState).2.next ≤ _ at wholeBudget
      rw [StateT.run_bind, operationRun] at wholeBudget
      exact wholeBudget
    obtain ⟨finalWitness, finalState, tailRun, finalMeaning, finalFrame,
      finalAliases⟩ := ih middleWitness middleState
      tailGroups
      (fun item member => valid item (List.mem_cons_of_mem operation member))
      tailEval middleAliases middleMeaning middleFrame tailBudget
    have wholeRun : (lowerOperationLoop (operation :: operations)).run initialState =
        ((), finalState) := by
      rw [lowerOperationLoop_cons, StateT.run_bind, operationRun]
      exact tailRun
    exact ⟨finalWitness, finalState, wholeRun, finalMeaning, finalFrame, finalAliases⟩

/-- The production output loop prepends both native and SSA aliases. This
recursion tracks those exact pushes while constructing aliases for the reversed
source result stack used by later guards and operations. -/
theorem lowerOutputLoop_complete (ctx : EvalContext) (hash : Hash)
    (implementation : HashAgreement ctx hash)
    (complete : ∀ ty (expression : Expr ty), ExprComplete expression)
    (inputs initialWitness : NativeRelation.Assignment) (initialState : Zkir.LowerState)
    (types : TypeEnv) (values stackValues : EvalEnv)
    (outputs : List Output) (results : List (String × Value))
    (initial final : OutputFrame)
    (valid : ∀ output ∈ outputs,
      output.value.validate {poseidon2 := true} types = .ok ())
    (unused : ∀ output ∈ outputs, values.lookup output.name = none)
    (source : outputs.mapM (evalOutput ctx values) = .ok results)
    (accepted : outputFold initial outputs = .ok final)
    (sourceAliases : AliasAgreement hash inputs initial.1 values)
    (sourceLowerAliases : LowerAliasAgreement hash inputs initialWitness
      initial.1 initialState.aliases values)
    (expandedLowerAliases : LowerAliasAgreement hash inputs initialWitness
      initial.1 initialState.aliases stackValues)
    (meaning : LowerStateMeaning hash initialWitness initialState)
    (inputFrame : ScalarCircuitLowering.InputFrame inputs initialWitness)
    (budget : (lowerOutputLoop outputs).run initialState |>.2.next ≤ Native.maxInstructions * Native.maxVectorLength) :
    ∃ finalWitness finalState,
      (lowerOutputLoop outputs).run initialState = ((), finalState) ∧
      LowerStateMeaning hash finalWitness finalState ∧
      ScalarCircuitLowering.InputFrame inputs finalWitness ∧
      LowerAliasAgreement hash inputs finalWitness final.1 finalState.aliases
        (results.reverse ++ stackValues) ∧
      (∀ name text, (name, text) ∈ finalState.aliases →
        name ∈ outputs.map (·.name) ∨ (name, text) ∈ initialState.aliases) := by
  induction outputs generalizing initialWitness initialState results initial final stackValues with
  | nil =>
    simp only [List.mapM_nil] at source
    cases source
    simp [outputFold] at accepted
    cases accepted
    refine ⟨initialWitness, initialState, ?_, meaning, inputFrame, expandedLowerAliases, ?_⟩
    rfl
    intro name text member
    exact Or.inr member
  | cons output outputs ih =>
    rw [outputFold_cons] at accepted
    change (appendOutput output initial >>= fun frame => outputFold frame outputs) =
      .ok final at accepted
    simp only [bind_ok] at accepted
    obtain ⟨middle, firstAccepted, tailAccepted⟩ := accepted
    unfold appendOutput at firstAccepted
    simp only [bind_ok] at firstAccepted
    obtain ⟨normalized, normalizedAccepted, middleShape⟩ := firstAccepted
    cases middleShape
    have normalAccepted := normalizeOutput_ok initial.1 output normalized normalizedAccepted
    have sourceCons : ∃ pair tail,
        evalOutput ctx values output = .ok pair ∧
        outputs.mapM (evalOutput ctx values) = .ok tail ∧ results = pair :: tail := by
      rw [List.mapM_cons] at source
      change (evalOutput ctx values output >>= fun pair =>
        outputs.mapM (evalOutput ctx values) >>= fun tail => pure (pair :: tail)) =
          .ok results at source
      simp only [bind_ok] at source
      rcases source with ⟨pair, headAccepted, tail, tailAccepted, shape⟩
      cases shape
      exact ⟨pair, tail, headAccepted, tailAccepted, rfl⟩
    obtain ⟨pair, tailResults, headEval, tailEval, resultsShape⟩ := sourceCons
    obtain ⟨value, valueEval, pairShape⟩ := evalOutput_value ctx values output pair headEval
    subst pair
    have bodyFrame : ScalarAllocation.PreservesFrame (lowerOutputBody output) :=
      lowerOutputBody_preserves output
    have tailFrame : ScalarAllocation.PreservesFrame (lowerOutputLoop outputs) :=
      lowerOutputLoop_preserves outputs
    have wholeBudget : ((lowerOutputBody output >>= fun _ => lowerOutputLoop outputs).run
        initialState).2.next ≤ Native.maxInstructions * Native.maxVectorLength := by
      simpa only [lowerOutputLoop_cons] using budget
    have bodyBudget := ScalarAllocation.bind_middle_budget
      (lowerOutputBody output) (fun _ => lowerOutputLoop outputs) initialState
      (fun _ => tailFrame) (Native.maxInstructions * Native.maxVectorLength) wholeBudget
    have pushFrame : ∀ text, ScalarAllocation.PreservesFrame
        (modify fun state => {state with aliases := (output.name, text) :: state.aliases}) := by
      intro text
      exact ScalarAllocation.modify_preserves _ (by
        intro state
        change ScalarAllocation.Frame state
          {state with aliases := (output.name, text) :: state.aliases}
        exact ⟨by simp, by simp⟩)
    have outputBodyBudget := bodyBudget
    change (Zkir.lowerExpr output.value >>= fun text =>
      modify fun state => {state with aliases := (output.name, text) :: state.aliases}).run
        initialState |>.2.next ≤ Native.maxInstructions * Native.maxVectorLength at outputBodyBudget
    have expressionBudget := ScalarAllocation.bind_middle_budget
      (Zkir.lowerExpr output.value)
      (fun text => modify fun state => {state with aliases := (output.name, text) :: state.aliases})
      initialState pushFrame (Native.maxInstructions * Native.maxVectorLength) outputBodyBudget
    obtain ⟨step⟩ := complete output.ty output.value ctx hash implementation
      inputs initialWitness initialState initial.1 values types value
      (valid output (by simp)) valueEval sourceAliases sourceLowerAliases meaning
      expressionBudget
    have normalizedEqual : normalized = step.normalized :=
      Except.ok.inj (normalAccepted.symm.trans step.normalization)
    subst normalized
    let outputState : Zkir.LowerState :=
      {step.finalState with aliases := (output.name, step.text) :: step.finalState.aliases}
    have bodyRun : (lowerOutputBody output).run initialState = ((), outputState) := by
      dsimp only [lowerOutputBody]
      rw [StateT.run_bind, step.run]
      rfl
    have outputMeaning : LowerStateMeaning hash step.finalWitness outputState := by
      apply LowerStateMeaning.withAliases hash step.finalWitness step.finalState
        step.stateMeaning outputState.aliases
      intro name text member
      change (name, text) ∈ (output.name, step.text) :: step.finalState.aliases at member
      rcases List.mem_cons.mp member with equal | old
      · cases equal
        exact step.textScope
      · exact TextScope.mono (by simp [outputState])
          (step.stateMeaning.aliases name text old)
    have sourceAliasesNext : AliasAgreement hash inputs
        ((output.name, step.normalized.term) :: initial.1) values := by
      exact GenericStateAliases.aliasAgreement_cons_unused hash inputs initial.1 values
        output.name step.normalized.term sourceAliases (unused output (by simp))
    have sourceLowerAfterExpr : LowerAliasAgreement hash inputs step.finalWitness
        initial.1 step.finalState.aliases values := step.aliasAgreement
    have sourceLowerNext : LowerAliasAgreement hash inputs step.finalWitness
        ((output.name, step.normalized.term) :: initial.1)
        ((output.name, step.text) :: step.finalState.aliases) values :=
      lowerAliasAgreement_cons_unused hash inputs step.finalWitness initial.1
        step.finalState.aliases values output.name step.normalized.term step.text
        sourceLowerAfterExpr (unused output (by simp))
    have expandedAfterExpr := LowerAliasAgreement.of_frame_observed hash inputs initialWitness
      step.finalWitness initial.1 initialState.aliases stackValues initialState.next
      expandedLowerAliases meaning.aliases step.frame
    have expandedAfterExpr' : LowerAliasAgreement hash inputs step.finalWitness
        initial.1 step.finalState.aliases stackValues := by
      simpa only [step.aliasesPreserved] using expandedAfterExpr
    have expandedNext : LowerAliasAgreement hash inputs step.finalWitness
        ((output.name, step.normalized.term) :: initial.1)
        ((output.name, step.text) :: step.finalState.aliases)
        ((output.name, Value.pack output.ty value) :: stackValues) :=
      LowerAliasAgreement.cons hash inputs step.finalWitness initial.1
        step.finalState.aliases stackValues output.name output.ty value
        step.normalized.term step.text expandedAfterExpr' step.operandMeaning
    have nextFrame : ScalarCircuitLowering.InputFrame inputs step.finalWitness := by
      intro name
      exact (step.frame _ (Or.inl ⟨name, rfl⟩)).trans (inputFrame name)
    have tailBudget : (lowerOutputLoop outputs).run outputState |>.2.next ≤
        (Native.maxInstructions * Native.maxVectorLength) := by
      change ((lowerOutputBody output >>= fun _ => lowerOutputLoop outputs).run
        initialState).2.next ≤ _ at wholeBudget
      simp only [StateT.run_bind] at wholeBudget
      rw [bodyRun] at wholeBudget
      exact wholeBudget
    let nextOutputFrame : OutputFrame :=
      ((output.name, step.normalized.term) :: initial.1,
        initial.2.1 ++ step.normalized.bounds,
        initial.2.2 ++ step.normalized.assertions)
    obtain ⟨tailWitness, finalState, tailRun, finalMeaning, finalInputFrame,
      finalLowerAliases, tailAliasNames⟩ := ih step.finalWitness outputState
      ((output.name, Value.pack output.ty value) :: stackValues) tailResults
      nextOutputFrame final
      (fun item member => valid item (List.mem_cons_of_mem output member))
      (fun item member => unused item (List.mem_cons_of_mem output member))
      tailEval tailAccepted sourceAliasesNext sourceLowerNext expandedNext outputMeaning
      nextFrame tailBudget
    have wholeRun : (lowerOutputLoop (output :: outputs)).run initialState =
        ((), finalState) := by
      rw [lowerOutputLoop_cons, StateT.run_bind, bodyRun]
      exact tailRun
    refine ⟨tailWitness, finalState, wholeRun, finalMeaning, finalInputFrame, ?_, ?_⟩
    · simpa [resultsShape, List.reverse_cons, List.append_assoc] using finalLowerAliases
    · intro name text member
      obtain outputMember | beforeMember := tailAliasNames name text member
      · exact Or.inl (List.mem_cons_of_mem output.name outputMember)
      · have outputAliases : outputState.aliases =
          (output.name, step.text) :: initialState.aliases := by
          calc
            outputState.aliases =
                (output.name, step.text) :: step.finalState.aliases := rfl
            _ = (output.name, step.text) :: initialState.aliases := by
              rw [step.aliasesPreserved]
        have pushedMember : (name, text) ∈
            (output.name, step.text) :: initialState.aliases :=
          outputAliases ▸ beforeMember
        rcases List.mem_cons.mp pushedMember with same | old
        ·
          have nameEqual : name = output.name := congrArg Prod.fst same
          exact Or.inl (List.mem_map.mpr ⟨output, by simp, nameEqual.symm⟩)
        · exact Or.inr old

/-- The accepted decoded ledger call has an actual SSA witness for the exact
production body. The witness starts with the source-derived read assignment,
then extends only fresh SSA names. -/
theorem lowered_body_source_witness (state : List StateDecl)
    (entry : Entrypoint) (json : Lean.Json) (relation : NativeRelation.Program)
    (ctx : EvalContext) (hash : Hash) (implementation : HashAgreement ctx hash)
    (values outputs : EvalEnv) (inputs : NativeRelation.Assignment)
    (initial next : LedgerState) (slots : List NativeState.Slot)
    (admittedInputs : CanonicalInputs entry.circuit values inputs)
    (admittedState : GenericStateEncoding.AdmittedState state initial slots)
    (lowered : Zkir.lowerEntrypoint state entry = .ok json)
    (decoded : NativeRelationJson.decode json = .ok relation)
    (modulus : ctx.modulus = Field.modulus)
    (source : entry.run ctx values initial = .ok (outputs, next)) :
    ∃ plan expected finalEnv entries witness native finalSlots finalReads
      finalWitness finalState,
      Impact.lower state (Passes.pruneEntrypoint entry) = .ok plan ∧
      Native.expectedEntrypoint state (Passes.pruneEntrypoint entry) = .ok expected ∧
      Native.validate expected json = .ok () ∧
      GenericStateSourceReadInputs.sourceReadInputs ctx
        (Passes.pruneEntrypoint entry).effects
        (((Passes.pruneEntrypoint entry).circuit.inputs.filter
          (·.visibility == .«public»)).length)
        (outputs ++ values, initial) = .ok (entries, (finalEnv, next)) ∧
      witness = GenericStateReadAssignment.assign inputs entries ∧
      GenericStateCheckedSchedule.CheckedPlan ctx
        (Passes.pruneEntrypoint entry) plan values witness slots
        ⟨[.vector finalSlots], finalReads⟩ ∧
      GenericStateEncoding.encodeState state next = some finalSlots ∧
      CanonicalInputs (Passes.pruneEntrypoint entry).circuit values witness ∧
      (∀ requirement ∈ expected.bounds,
        (interpret hash witness requirement.1).val ≤ requirement.2) ∧
      (∀ assertion ∈ expected.assertions,
        interpret hash witness assertion = one) ∧
      expected.groups.map (fun group => group.map (interpret hash witness)) =
        NativeState.groups native ∧
      GenericStateOps.evalPlan ctx
        (GenericStateCheckedSchedule.outputCandidates ctx
          (Passes.pruneEntrypoint entry) values ++
          GenericStateInputValues.decodeReads
            (plan.reads.drop
              (((Passes.pruneEntrypoint entry).circuit.inputs.filter
                (·.visibility == .«public»)).length)) witness) plan =
        .ok native ∧
      (Zkir.lowerEntrypointBody (Passes.pruneEntrypoint entry) plan).run {} =
        ((), finalState) ∧
      LowerStateMeaning hash finalWitness finalState ∧
      ScalarCircuitLowering.InputFrame witness finalWitness := by
  obtain ⟨plan, expected, planAccepted, expectedAccepted, producerAccepted⟩ :=
    GenericStateLowering.lowerEntrypoint_validated state entry json lowered
  have admittedPruned : CanonicalInputs
      (Passes.pruneEntrypoint entry).circuit values inputs :=
    ⟨admittedInputs.unique, admittedInputs.declared,
      admittedInputs.complete, admittedInputs.binding⟩
  have sourcePruned : (Passes.pruneEntrypoint entry).run ctx values initial =
      .ok (outputs, next) := by
    simpa only [Passes.pruneEntrypoint_run] using source
  obtain ⟨finalEnv, entries, witness, native, finalSlots, finalReads,
    instrumented, witnessShape, checked, encoded, canonical,
    expectedBounds, expectedAssertions, expectedGroups, planEval⟩ :=
    GenericStateConverseResult.source_call_expected_checked state
      (Passes.pruneEntrypoint entry) plan expected ctx hash implementation
      values outputs inputs initial next slots admittedPruned admittedState
      planAccepted expectedAccepted modulus sourcePruned
  obtain ⟨tapeEnv, tapeEntries, circuitRun, tape⟩ :=
    GenericStateConverseSource.source_read_tape_of_entry_run ctx
      (Passes.pruneEntrypoint entry) values outputs initial next sourcePruned
  have entriesEqual : entries = tapeEntries := by
    rw [tape] at instrumented
    exact (congrArg Prod.fst (Except.ok.inj instrumented)).symm
  have sourceWitness : witness = GenericStateReadAssignment.assign inputs entries :=
    witnessShape
  have circuitValid := GenericStateAdmission.lower_circuit_validated state
    (Passes.pruneEntrypoint entry) plan planAccepted
  obtain ⟨constraintValidation, outputValidation⟩ :=
    ScalarNormalization.circuit_validation_parts
      (Passes.pruneEntrypoint entry).circuit circuitValid
  have circuitSteps := ScalarNormalization.circuit_run_steps ctx
    (Passes.pruneEntrypoint entry).circuit values outputs circuitRun
  have sourceOutputs : (Passes.pruneEntrypoint entry).circuit.outputs.mapM
      (evalOutput ctx values) = .ok outputs := circuitSteps.2
  obtain ⟨partsPlan, outputFrame, conditions, guards, operationFrame,
    partsLowered, outputsAccepted, conditionsAccepted, guardsAccepted,
    operationsAccepted, inputShape, groupsShape, returnsShape, modeShape,
    assertionsShape, boundsShape⟩ :=
    GenericStateCircuitParts.expectedEntrypoint_parts state
      (Passes.pruneEntrypoint entry) expected expectedAccepted
  have samePlan : partsPlan = plan := by
    rw [planAccepted] at partsLowered
    exact (Except.ok.inj partsLowered).symm
  subst partsPlan
  have outputValid : ∀ output ∈ (Passes.pruneEntrypoint entry).circuit.outputs,
      output.value.validate {poseidon2 := true}
        ((Passes.pruneEntrypoint entry).circuit.inputs.map
          (fun input => (input.name, input.ty))) = .ok () :=
    outputValidation
  have outputUnused := GenericStateAdmission.lower_output_names_unused state
    (Passes.pruneEntrypoint entry) plan values witness canonical planAccepted
  have initialTyped := GenericStateAliases.initialTypedEnvironment hash witness
    (Passes.pruneEntrypoint entry) plan values canonical
  obtain ⟨outputBounds, outputAssertions, sourceOutputAliases,
    expandedSourceOutputAliases⟩ :=
    GenericStateOutputCompleteness.normalizeOutputs_complete ctx hash
      implementation witness (GenericStateCircuitParts.initialAliases
        (Passes.pruneEntrypoint entry) plan) values
      (Passes.pruneEntrypoint entry).circuit.outputs outputFrame outputs
      initialTyped.aliases outputUnused sourceOutputs outputsAccepted
  have candidateTyped :=
    GenericStateConverseCandidateEnvironment.source_candidate_environment state
      (Passes.pruneEntrypoint entry) plan ctx hash implementation
      values outputs inputs initial next finalEnv entries outputFrame
      admittedPruned planAccepted instrumented circuitRun modulus outputsAccepted
  let reads := plan.reads.drop
    (((Passes.pruneEntrypoint entry).circuit.inputs.filter
      (·.visibility == .«public»)).length)
  let candidateValues := (outputs ++ values) ++
    GenericStateInputValues.decodeReads reads witness
  have candidateValuesShape :
      GenericStateCheckedSchedule.outputCandidates ctx
        (Passes.pruneEntrypoint entry) values = outputs ++ values := by
    simp only [GenericStateCheckedSchedule.outputCandidates, sourceOutputs,
      Except.toOption, Option.getD_some]
  have planEvalCandidate : GenericStateOps.evalPlan ctx candidateValues plan =
      .ok native := by
    simpa only [candidateValues, List.append_assoc, candidateValuesShape] using planEval
  obtain ⟨publicOps, publicCells, publicPrefixEval, publicPrefixGroups,
    publicPrefixRun⟩ :=
    GenericStateConversePublicPrefix.source_public_prefix state
      (Passes.pruneEntrypoint entry) plan ctx values outputs
      (GenericStateInputValues.decodeReads reads witness) witness
      [.vector slots] [] planAccepted canonical circuitRun modulus
  obtain ⟨traceEnv, traceEntries, traceWitness, segments, traceSlots,
    traceReads, sameCircuit, traceInstrumented, traceWitnessShape,
    unchangedInputs, traceNames, traceReadBounds, evaluatedChunks,
    nativeTrace, encodedTrace, guardTruth⟩ :=
    GenericStateConverseNativeTrace.source_call_native_trace state
      (Passes.pruneEntrypoint entry) plan ctx values outputs inputs initial next
      slots publicCells admittedPruned admittedState planAccepted modulus sourcePruned
  have traceEntriesEqual : traceEntries = entries := by
    have pairEqual := Except.ok.inj (instrumented.symm.trans traceInstrumented)
    exact (congrArg Prod.fst pairEqual).symm
  have traceWitnessEqual : traceWitness = witness := by
    calc
      traceWitness = GenericStateReadAssignment.assign inputs traceEntries :=
        traceWitnessShape
      _ = GenericStateReadAssignment.assign inputs entries := by rw [traceEntriesEqual]
      _ = witness := sourceWitness.symm
  have traceGuardTruth : ∀ guard ∈ plan.guards,
      guard.eval ctx candidateValues = .ok true := by
    intro guard member
    have actual := guardTruth guard member
    simpa only [candidateValues, traceWitnessEqual] using actual
  have inputIdentifiers :=
    GenericStateLedgerIdentifiers.accepted_input_identifiers state
      (Passes.pruneEntrypoint entry) plan expected json relation planAccepted
      expectedAccepted producerAccepted decoded
  obtain ⟨budgetPlan, budgetPlanAccepted, bodyBudget⟩ :=
    GenericStateLedgerAllocation.lowerEntrypoint_outputCapacity state entry json lowered
  have budgetPlanEqual : budgetPlan = plan := by
    rw [planAccepted] at budgetPlanAccepted
    exact (Except.ok.inj budgetPlanAccepted).symm
  subst budgetPlan
  let prelude := lowerLedgerPrelude (Passes.pruneEntrypoint entry).circuit
  let afterPrelude := lowerLedgerAfterPrelude (Passes.pruneEntrypoint entry) plan
  let preludeState := prelude.run {} |>.2
  have stagesBudget : (lowerLedgerBodyStages (Passes.pruneEntrypoint entry) plan).run
      {} |>.2.next ≤ Native.maxInstructions * Native.maxVectorLength := by
    rw [← lowerEntrypointBody_eq_stages]
    exact bodyBudget
  have wholePreludeBudget : (prelude >>= fun _ => afterPrelude).run {} |>.2.next ≤
      (Native.maxInstructions * Native.maxVectorLength) := by
    simpa only [lowerLedgerBodyStages, prelude, afterPrelude, bind_assoc, pure_bind]
      using stagesBudget
  have preludeBound := ScalarAllocation.bind_middle_budget prelude
    (fun _ => afterPrelude) {} (fun _ => lowerLedgerAfterPrelude_preserves
      (Passes.pruneEntrypoint entry) plan) (Native.maxInstructions * Native.maxVectorLength) wholePreludeBudget
  have preludeComplete := lowerLedgerPrelude_complete ctx hash implementation
    (fun ty expression => ScalarExpressionLowering.lowerExpr_complete expression)
    (Passes.pruneEntrypoint entry).circuit values witness canonical
    inputIdentifiers.1 circuitValid outputs circuitRun
  have emptyMeaning : LowerStateMeaning hash witness {} :=
    ScalarLowering.empty_state hash witness
  have initialInputFrame : ScalarCircuitLowering.InputFrame witness witness := by
    intro name
    rfl
  obtain ⟨preludeExtension⟩ := preludeComplete witness {} emptyMeaning
    initialInputFrame (by rfl) preludeBound
  have preludeRun : prelude.run {} = ((), preludeState) := rfl
  have afterPreludeBudget :
      (afterPrelude.run preludeState).2.next ≤ Native.maxInstructions * Native.maxVectorLength := by
    change (prelude >>= fun _ => afterPrelude).run {} |>.2.next ≤ _
      at wholePreludeBudget
    rw [StateT.run_bind, preludeRun] at wholePreludeBudget
    exact wholePreludeBudget
  have preludeMeaning : LowerStateMeaning hash preludeExtension.witness preludeState :=
    preludeExtension.meaning
  have preludeFrame : ScalarCircuitLowering.InputFrame witness
      preludeExtension.witness := by
    intro name
    exact preludeExtension.frame ("%input_" ++ name)
      (Or.inl ⟨name, rfl⟩)
  have preludeAliasesEmpty : preludeState.aliases = [] := by
    simpa only [preludeState] using preludeExtension.aliases
  have circuitLowerAliases := ScalarCircuitLowering.current_aliases hash witness
    preludeExtension.witness (Passes.pruneEntrypoint entry).circuit values
    preludeState canonical inputIdentifiers.1 preludeFrame preludeAliasesEmpty
  have sameInitialNormalAliases : ∀ name ty raw value,
      values.lookup name = some raw -> raw.as ty = some value ->
      (GenericStateCircuitParts.initialAliases
        (Passes.pruneEntrypoint entry) plan).lookup name =
        (ScalarNormalization.circuitAliases
          (Passes.pruneEntrypoint entry).circuit).lookup name := by
    intro name ty raw value lookup typed
    obtain ⟨input, inputMember, inputName⟩ := canonical.declared name raw
      (ScalarValidation.lookup_member lookup)
    subst name
    rw [initialAliases_lookup_input (Passes.pruneEntrypoint entry) plan
      input inputMember]
    exact (ScalarNormalization.aliases_lookup
      (Passes.pruneEntrypoint entry).circuit.inputs input.name
      ⟨input, inputMember, rfl⟩).symm
  have initialLowerAliases : LowerAliasAgreement hash witness
      preludeExtension.witness
      (GenericStateCircuitParts.initialAliases (Passes.pruneEntrypoint entry) plan)
      preludeState.aliases values :=
    LowerAliasAgreement.normalAliases_ext hash witness preludeExtension.witness
      (ScalarNormalization.circuitAliases
        (Passes.pruneEntrypoint entry).circuit)
      (GenericStateCircuitParts.initialAliases (Passes.pruneEntrypoint entry) plan)
      preludeState.aliases values circuitLowerAliases sameInitialNormalAliases
  let initialOutputFrame : GenericStateCircuitParts.OutputFrame :=
    (GenericStateCircuitParts.initialAliases (Passes.pruneEntrypoint entry) plan, [], [])
  have outputFoldAccepted :
      GenericStateCircuitParts.outputFold initialOutputFrame
        (Passes.pruneEntrypoint entry).circuit.outputs = .ok outputFrame := by
    simpa only [GenericStateCircuitParts.normalizeOutputs, initialOutputFrame]
      using outputsAccepted
  have outputTailBudget :
      ((lowerOutputLoop (Passes.pruneEntrypoint entry).circuit.outputs >>= fun _ =>
        lowerLedgerAfterOutput (Passes.pruneEntrypoint entry) plan).run preludeState).2.next ≤
        (Native.maxInstructions * Native.maxVectorLength) := by
    exact afterPreludeBudget
  have outputBound := ScalarAllocation.bind_middle_budget
    (lowerOutputLoop (Passes.pruneEntrypoint entry).circuit.outputs)
    (fun _ => lowerLedgerAfterOutput (Passes.pruneEntrypoint entry) plan)
    preludeState (fun _ => lowerLedgerAfterOutput_preserves
      (Passes.pruneEntrypoint entry) plan) (Native.maxInstructions * Native.maxVectorLength) outputTailBudget
  obtain ⟨outputWitness, outputState, outputRun, outputMeaning,
    outputInputFrame, outputLowerAliases, outputAliasNames⟩ :=
    lowerOutputLoop_complete ctx hash implementation
      (fun ty expression => ScalarExpressionLowering.lowerExpr_complete expression)
      witness preludeExtension.witness preludeState
      ((Passes.pruneEntrypoint entry).circuit.inputs.map
        (fun input => (input.name, input.ty))) values values
      (Passes.pruneEntrypoint entry).circuit.outputs outputs
      initialOutputFrame outputFrame outputValid outputUnused sourceOutputs
      outputFoldAccepted initialTyped.aliases initialLowerAliases initialLowerAliases preludeMeaning
      preludeFrame outputBound
  let reads := plan.reads.drop
    (((Passes.pruneEntrypoint entry).circuit.inputs.filter
      (·.visibility == .«public»)).length)
  have readBounds := GenericStateSourceReadInputs.sourceReadInputs_bounds ctx
    (Passes.pruneEntrypoint entry).effects
    (((Passes.pruneEntrypoint entry).circuit.inputs.filter
      (·.visibility == .«public»)).length)
    (outputs ++ values, initial) (finalEnv, next) entries modulus instrumented
  have entryNames := GenericStateSourceReadInputs.sourceReadInputs_names ctx
    (Passes.pruneEntrypoint entry).effects
    (((Passes.pruneEntrypoint entry).circuit.inputs.filter
      (·.visibility == .«public»)).length)
    (outputs ++ values, initial) (finalEnv, next) entries instrumented
  have readNames : entries.map Prod.fst = reads := by
    rw [← GenericStateReadTape.lower_read_chunks state
      (Passes.pruneEntrypoint entry) plan planAccepted] at entryNames
    simpa only [reads] using entryNames
  have readDistinct := GenericStateReadAssignment.sourceReadInputs_distinct
    state (Passes.pruneEntrypoint entry) plan ctx (outputs ++ values, initial)
    (finalEnv, next) entries planAccepted instrumented
  have readFacts : ∀ read ∈ reads, ∃ value,
      Canonical read.ty value ∧
      witness ("%input_" ++ read.name) = scalar (number read.ty value) := by
    intro read member
    have readMember : read ∈ entries.map Prod.fst := by
      rw [readNames]
      exact member
    obtain ⟨pair, pairMember, pairEqual⟩ := List.mem_map.mp readMember
    rcases pair with ⟨foundRead, rawScalar⟩
    have foundEqual : foundRead = read := by simpa using pairEqual
    subst foundRead
    let canonicalValue := GenericStateInputValues.sourceValue read.ty rawScalar
    obtain ⟨canonicalFacts, encodedValue⟩ :=
      GenericStateInputValues.sourceValue_canonical read.ty rawScalar
        (GenericStateReadTypes.lower_read_types state
          (Passes.pruneEntrypoint entry) plan planAccepted read member)
        (readBounds (read, rawScalar) pairMember)
    have assigned := GenericStateReadAssignment.assign_member inputs entries
      readDistinct read rawScalar pairMember
    have witnessBinding : witness ("%input_" ++ read.name) = rawScalar := by
      rw [sourceWitness]
      simpa only [GenericStateReadAssignment.identifier] using assigned
    refine ⟨canonicalValue, canonicalFacts, ?_⟩
    exact witnessBinding.trans encodedValue.symm
  have outputStateRun :
      (lowerOutputLoop (Passes.pruneEntrypoint entry).circuit.outputs).run
        preludeState = ((), outputState) := outputRun
  have readTailBudget :
      (lowerLedgerAfterOutput (Passes.pruneEntrypoint entry) plan).run outputState |>.2.next ≤
        (Native.maxInstructions * Native.maxVectorLength) := by
    change ((lowerOutputLoop (Passes.pruneEntrypoint entry).circuit.outputs >>= fun _ =>
      lowerLedgerAfterOutput (Passes.pruneEntrypoint entry) plan).run preludeState).2.next ≤ _
      at outputTailBudget
    rw [StateT.run_bind, outputStateRun] at outputTailBudget
    exact outputTailBudget
  have readBound := ScalarAllocation.bind_middle_budget
    (lowerReadLoop reads) (fun _ => lowerLedgerAfterReads plan) outputState
    (fun _ => lowerLedgerAfterReads_preserves plan) (Native.maxInstructions * Native.maxVectorLength)
    (by simpa only [lowerLedgerAfterOutput, reads, bind_assoc, pure_bind]
      using readTailBudget)
  have readNamesIdentifiers : ∀ read ∈ reads,
      validIdentifier ("%input_" ++ read.name) = true := inputIdentifiers.2
  obtain ⟨readWitness, readState, readRun, readMeaning,
    readInputFrame, readLowerAliases, readAliasesPreserved⟩ :=
    lowerReadLoop_complete hash witness outputWitness outputState outputFrame.1
      (outputs.reverse ++ values) reads readFacts readNamesIdentifiers
      outputLowerAliases outputMeaning outputInputFrame readBound
  have outputReadFresh : ∀ read ∈ reads,
      read.name ∉ (Passes.pruneEntrypoint entry).circuit.outputs.map (·.name) := by
    intro read member present
    obtain ⟨output, outputMember, outputName⟩ := List.mem_map.mp present
    have fresh := GenericStateReadFreshness.lower_read_base_fresh state
      (Passes.pruneEntrypoint entry) plan ctx values outputs witness canonical
      planAccepted circuitRun
    have typeAbsent := (fresh read member).2
    have outputTypeMember : (output.name, output.ty) ∈
        ((Passes.pruneEntrypoint entry).circuit.outputs.map
          (fun output => (output.name, output.ty)) ++
          (Passes.pruneEntrypoint entry).circuit.inputs.map
            (fun input => (input.name, input.ty))) :=
      List.mem_append_left _ (List.mem_map.mpr ⟨output, outputMember, rfl⟩)
    have nameDifferent := (List.lookup_eq_none_iff.mp typeAbsent)
      (output.name, output.ty) outputTypeMember
    simp [outputName] at nameDifferent
  have lowerReadAbsent : ∀ read ∈ reads,
      readState.aliases.lookup read.name = none := by
    intro read member
    apply List.lookup_eq_none_iff.mpr
    intro pair pairMember
    have outputPairMember : (pair.1, pair.2) ∈ outputState.aliases := by
      simpa only [readAliasesPreserved] using pairMember
    have outputMemberOrInitial := outputAliasNames pair.1 pair.2 outputPairMember
    rcases outputMemberOrInitial with outputMember | initialMember
    · have pairNameDifferent : pair.1 ≠ read.name := by
        intro same
        apply outputReadFresh read member
        simpa [same] using outputMember
      simp [pairNameDifferent.symm]
    · rw [preludeAliasesEmpty] at initialMember
      simp at initialMember
  have normalReadAliases := GenericStateReadAliasLookup.normalized_read_alias_lookup
    state (Passes.pruneEntrypoint entry) plan outputFrame planAccepted outputsAccepted
  have readExtendedLowerAliases := LowerAliasAgreement.append_reads hash witness
    readWitness outputFrame.1 readState.aliases (outputs.reverse ++ values) reads
    readLowerAliases normalReadAliases lowerReadAbsent inputIdentifiers.2
    readInputFrame
  let lowerValues := (outputs.reverse ++ values) ++
    GenericStateInputValues.decodeReads reads witness
  have outputsUnique : (outputs.map Prod.fst).Nodup := by
    rw [GenericStateReadFreshness.source_outputs_names ctx values
      (Passes.pruneEntrypoint entry).circuit.outputs outputs sourceOutputs]
    exact GenericStateOutputOrder.validated_output_names_unique
      (Passes.pruneEntrypoint entry).circuit circuitValid
  have sameCandidateLookups : ∀ name,
      lowerValues.lookup name = candidateValues.lookup name := by
    intro name
    exact lookup_reverse_append outputs values
      (GenericStateInputValues.decodeReads reads witness) outputsUnique name
  have guardLowerAliases := LowerAliasAgreement.environment_ext hash witness
    readWitness outputFrame.1 readState.aliases lowerValues candidateValues
    readExtendedLowerAliases sameCandidateLookups
  have candidateAliases : AliasAgreement hash witness outputFrame.1 candidateValues := by
    simpa only [candidateValues, reads, List.append_assoc, sourceWitness] using
      candidateTyped.aliases
  have planValidation := GenericStateAdmission.lower_validated state
    (Passes.pruneEntrypoint entry) plan planAccepted
  have guardsValid := GenericStateGuardSoundness.validated_guards plan
    (Passes.pruneEntrypoint entry) planValidation
  have guardsValidEach := validateConstraints_members guardsValid
  have guardWholeBudget :
      (lowerLedgerAfterReads plan).run readState |>.2.next ≤ Native.maxInstructions * Native.maxVectorLength := by
    change ((lowerReadLoop reads >>= fun _ => lowerLedgerAfterReads plan).run
      outputState).2.next ≤ _ at readTailBudget
    rw [StateT.run_bind, readRun] at readTailBudget
    exact readTailBudget
  have guardBound := ScalarAllocation.bind_middle_budget
    (lowerGuardLoop plan.guards) (fun _ => lowerLedgerAfterGuards plan) readState
    (fun _ => lowerLedgerAfterGuards_preserves plan) (Native.maxInstructions * Native.maxVectorLength)
    (by simpa only [lowerLedgerAfterReads, bind_assoc, pure_bind]
      using guardWholeBudget)
  obtain ⟨guardWitness, guardState, guardRun, guardMeaning,
    guardInputFrame, guardLowerAliasesFinal⟩ :=
    lowerGuardLoop_complete ctx hash implementation
      (fun ty expression => ScalarExpressionLowering.lowerExpr_complete expression)
      witness readWitness readState outputFrame.1 candidateValues
      (GenericStateAdmission.planTypes plan (Passes.pruneEntrypoint entry))
      plan.guards guardsValidEach
      traceGuardTruth candidateAliases guardLowerAliases
      readMeaning readInputFrame guardBound
  have operationTailBudget :
      (lowerLedgerAfterGuards plan).run guardState |>.2.next ≤ Native.maxInstructions * Native.maxVectorLength := by
    change ((lowerGuardLoop plan.guards >>= fun _ =>
      lowerLedgerAfterGuards plan).run readState).2.next ≤ _ at guardWholeBudget
    rw [StateT.run_bind, guardRun] at guardWholeBudget
    exact guardWholeBudget
  have operationBound := ScalarAllocation.bind_middle_budget
    (lowerOperationLoop plan.operations)
    (fun _ => Zkir.emit "output" [("vals", toJson ([] : List String))])
    guardState (fun _ => ScalarAllocation.emit_preserves _ _)
    (Native.maxInstructions * Native.maxVectorLength) operationTailBudget
  have planEvalCandidateExact : GenericStateOps.evalPlan ctx candidateValues plan =
      .ok native := by
    simpa only [candidateValues, reads, candidateValuesShape] using planEval
  have operationFields := GenericStateAdmission.lower_plan_groups state
    (Passes.pruneEntrypoint entry) plan ctx candidateValues native planAccepted
    modulus planEvalCandidateExact
  have fieldsValid := GenericStateAdmission.validated_fields plan
    (Passes.pruneEntrypoint entry) planValidation
  have operationFieldsValid : ∀ operation ∈ plan.operations,
      ∀ expression ∈ operation.fields,
        expression.validate {poseidon2 := true}
          (GenericStateAdmission.planTypes plan
            (Passes.pruneEntrypoint entry)) = .ok () := by
    intro operation operationMember expression expressionMember
    apply fieldsValid expression
    exact List.mem_flatMap.mpr ⟨operation, operationMember, expressionMember⟩
  obtain ⟨operationWitness, operationState, operationRun,
    operationMeaning, operationInputFrame, operationLowerAliases⟩ :=
    lowerOperationLoop_complete ctx hash implementation
      (fun ty expression => ScalarExpressionLowering.lowerExpr_complete expression)
      witness guardWitness guardState outputFrame.1 candidateValues
      (GenericStateAdmission.planTypes plan (Passes.pruneEntrypoint entry))
      plan.operations (NativeState.groups native) operationFieldsValid operationFields
      candidateAliases guardLowerAliasesFinal guardMeaning guardInputFrame
      operationBound
  let footer := Zkir.emit "output" [("vals", toJson ([] : List String))]
  let finalState := footer.run operationState |>.2
  have footerRun : footer.run operationState = ((), finalState) := rfl
  have footerMeaning : LowerStateMeaning hash operationWitness finalState := by
    simpa only [footer, finalState] using ScalarCircuitLowering.emit_output hash
      operationWitness operationState operationMeaning [] (by intro text member; simp at member)
  have bodyRun :
      (Zkir.lowerEntrypointBody (Passes.pruneEntrypoint entry) plan).run {} =
        ((), finalState) := by
    rw [lowerEntrypointBody_eq_stages]
    change (prelude >>= fun _ => afterPrelude).run {} = ((), finalState)
    rw [StateT.run_bind, preludeRun]
    change (lowerOutputLoop (Passes.pruneEntrypoint entry).circuit.outputs >>= fun _ =>
      lowerLedgerAfterOutput (Passes.pruneEntrypoint entry) plan).run preludeState =
        ((), finalState)
    rw [StateT.run_bind, outputRun]
    change (lowerReadLoop reads >>= fun _ => lowerLedgerAfterReads plan).run outputState =
      ((), finalState)
    rw [StateT.run_bind, readRun]
    change (lowerGuardLoop plan.guards >>= fun _ => lowerLedgerAfterGuards plan).run
      readState = ((), finalState)
    rw [StateT.run_bind, guardRun]
    change (lowerOperationLoop plan.operations >>= fun _ => footer).run guardState =
      ((), finalState)
    rw [StateT.run_bind, operationRun]
    exact footerRun
  have finalInputFrame : ScalarCircuitLowering.InputFrame witness operationWitness :=
    operationInputFrame
  refine ⟨plan, expected, finalEnv, entries, witness, native, finalSlots,
    finalReads,
    operationWitness, finalState, planAccepted, expectedAccepted, producerAccepted,
    instrumented, witnessShape, checked, encoded, canonical, expectedBounds,
    expectedAssertions, expectedGroups,
    ?_, bodyRun, footerMeaning, finalInputFrame⟩
  exact planEval

end Noctium.Verification.GenericStateLedgerWitness
