import Noctium.Verification.ScalarWitnessAssembly
import Noctium.Verification.ScalarAllocationOutputFrame

namespace Noctium.Verification.ScalarWitnessConstruction

open Lean Backend NativeRelation NativeRelationJson ScalarNormalization ScalarLowering
open ScalarInstructionEncoding ScalarWitness ScalarAllocationOutputFrame

private theorem bind_middle_output_budget (first : StateM Zkir.LowerState α)
    (next : α → StateM Zkir.LowerState β) (state : Zkir.LowerState)
    (remaining : ∀ value, Zkir.PreservesOutputCapacityFrame (next value))
    (limit : Nat) (bound : ((first >>= next).run state).2.next ≤ limit) :
    (first.run state).2.next ≤ limit := by
  have frame := remaining (first.run state).1 (first.run state).2
  rw [StateT.run_bind] at bound
  exact Nat.le_trans frame.next bound

private theorem lower_assertE (condition : Expr .bool) (body : Expr ty) :
    Zkir.lowerExpr (.assertE condition body) =
      (do
        let text ← Zkir.lowerExpr condition
        Zkir.emit "assert" [("cond", toJson text)]
        Zkir.lowerExpr body) := by
  simp only [Zkir.lowerExpr]

/-- A checked successful helper assertion emits the actual ZKIR assertion
before lowering its body. The asserted condition's Native meaning is one, so
the witness retains the assertion and the body's resulting state meaning. -/
theorem exprComplete_assertE (condition : Expr .bool) (body : Expr ty)
    (conditionAdmitted : ScalarExpression condition)
    (bodyAdmitted : ScalarExpression body)
    (conditionComplete : ExprComplete condition) (bodyComplete : ExprComplete body) :
    ExprComplete (.assertE condition body) := by
  intro ctx hash implementation inputs witness state normalAliases values types value
    valid success aliases lowerAliases stateMeaning budget
  have validation :
      (condition.validate Capabilities.crypto types >>= fun _ =>
        body.validate Capabilities.crypto types) = .ok () := by
    have validation := valid
    simp only [Expr.validate] at validation
    exact validation
  obtain ⟨_, conditionValid, bodyValid⟩ :=
    ScalarValidationMeaning.bind_ok.mp validation
  have sourceSuccess := success
  have conditionEval : condition.eval ctx values = .ok true := by
    cases evaluated : condition.eval ctx values with
    | error message =>
      simp [Expr.eval, evaluated, Bind.bind, Except.bind] at sourceSuccess
    | ok bit =>
      cases bit with
      | false =>
        simp [Expr.eval, evaluated, Bind.bind, Except.bind] at sourceSuccess
      | true => rfl
  have bodySuccess : body.eval ctx values = .ok value := by
    simpa only [Expr.eval, conditionEval, Bind.bind, Except.bind,
      Bool.true_eq_false, ↓reduceIte] using sourceSuccess

  have suffixFrame (text : String) :
      Zkir.PreservesOutputCapacityFrame (do
        Zkir.emit "assert" [("cond", toJson text)]
        Zkir.lowerExpr body) := by
    exact Zkir.bind_preservesOutputCapacityFrame _ _
      (Zkir.emit_preservesOutputCapacityFrame "assert" [("cond", toJson text)])
      (fun _ => lowerExpr_admitted_preservesOutputCapacityFrame body bodyAdmitted)
  have conditionBudget : ((Zkir.lowerExpr condition).run state).2.next ≤
      Native.maxInstructions * Native.maxVectorLength := by
    apply bind_middle_output_budget (Zkir.lowerExpr condition)
      (fun text => do
        Zkir.emit "assert" [("cond", toJson text)]
        Zkir.lowerExpr body) state suffixFrame _
    simpa only [lower_assertE] using budget
  obtain ⟨first⟩ := conditionComplete ctx hash implementation inputs witness state
    normalAliases values types true conditionValid conditionEval aliases lowerAliases
    stateMeaning conditionBudget

  obtain ⟨operand, parsed, interpreted⟩ := first.operandMeaning
  have interpretationIsOne : some (operand.read first.finalWitness) = some one := by
    have represented := first.represents.2.2
    rw [interpreted] at represented
    simpa [sourceScalar?, sourceNumber?, scalar_one] using represented
  have readOne : operand.read first.finalWitness = one :=
    Option.some.inj interpretationIsOne
  let assertedState : Zkir.LowerState := {first.finalState with
    instructions := first.finalState.instructions.push
      (Zkir.instruction "assert" [("cond", toJson first.text)])}
  have assertionMeaning : LowerStateMeaning hash first.finalWitness assertedState := by
    change LowerStateMeaning hash first.finalWitness
      ((Zkir.emit "assert" [("cond", toJson first.text)]).run first.finalState).2
    exact emit_assert hash first.finalWitness first.finalState
      first.stateMeaning first.text first.textScope ⟨operand, parsed, readOne⟩

  have bodyBudget : ((Zkir.lowerExpr body).run assertedState).2.next ≤
      Native.maxInstructions * Native.maxVectorLength := by
    have bound := budget
    rw [lower_assertE, StateT.run_bind, first.run] at bound
    dsimp [Zkir.emit, assertedState] at bound
    exact bound
  obtain ⟨second⟩ := bodyComplete ctx hash implementation inputs first.finalWitness
    assertedState normalAliases values types value bodyValid bodySuccess aliases
    first.aliasAgreement assertionMeaning bodyBudget

  obtain ⟨normalized, normalization, represents⟩ := normalize_success ctx hash
    implementation inputs normalAliases values aliases (.assertE condition body)
    (.assertE condition body conditionAdmitted bodyAdmitted) value sourceSuccess
  have termEq : normalized.term = second.normalized.term := by
    have actual := normalization
    simp only [Native.normalize] at actual
    rw [first.normalization, second.normalization] at actual
    change Except.ok _ = Except.ok normalized at actual
    cases actual
    rfl
  refine ⟨{
    text := second.text
    finalState := second.finalState
    finalWitness := second.finalWitness
    normalized
    run := ?_
    normalization
    represents
    operandMeaning := ?_
    textScope := second.textScope
    stateMeaning := second.stateMeaning
    budget := second.budget
    aliasAgreement := second.aliasAgreement
    aliasesPreserved := second.aliasesPreserved.trans first.aliasesPreserved
    frame := ?_
  }⟩
  · rw [lower_assertE, StateT.run_bind, first.run]
    dsimp [Zkir.emit, assertedState]
    exact second.run
  · rw [termEq]
    exact second.operandMeaning
  · intro name scope
    have conditionNext : state.next ≤ first.finalState.next := by
      have frame := lowerExpr_admitted_preservesOutputCapacityFrame condition conditionAdmitted state
      rw [first.run] at frame
      exact frame.next
    exact (second.frame name (InScope.mono conditionNext scope)).trans
      (first.frame name scope)

end Noctium.Verification.ScalarWitnessConstruction
