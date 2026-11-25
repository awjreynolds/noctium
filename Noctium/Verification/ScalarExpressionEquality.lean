import Noctium.Verification.ScalarAllocationOutputFrame
import Noctium.Verification.ScalarNativeWitnessSteps
import Noctium.Verification.ScalarLowering

namespace Noctium.Verification.ScalarWitnessConstruction

open Lean Backend NativeRelation NativeRelationJson ScalarNormalization ScalarLowering
open ScalarAllocationOutputFrame ScalarValidationMeaning

private theorem lower_eq_scalar {ty : Ty} (sourceType : ScalarType ty)
    (left right : Expr ty) :
    Zkir.lowerExpr (.eq left right) = (do
      let leftText ← Zkir.lowerExpr left
      let rightText ← Zkir.lowerExpr right
      Zkir.binary "test_eq" leftText rightText) := by
  cases sourceType <;> simp only [Zkir.lowerExpr]

/-- Equality lowers both operands through the live ZKIR lowerer, then emits
the native `test_eq` operation. The source scalar admission supplies the exact
normalization obligations and the output-bit bound. -/
theorem complete_scalar_eq {ty : Ty} (left right : Expr ty)
    (sourceType : ScalarType ty) (leftAdmitted : ScalarExpression left)
    (rightAdmitted : ScalarExpression right) (completeLeft : ExprComplete left)
    (completeRight : ExprComplete right) :
    ExprComplete (.eq left right) := by
  intro ctx hash implementation inputs witness state normalAliases values types result
    valid success aliasAgreement lowerAliasAgreement lowerStateMeaning budget
  have validChildren : (do
      left.validate Capabilities.crypto types
      right.validate Capabilities.crypto types) = .ok () := by
    cases sourceType <;>
      simpa [Expr.validate, Ty.isBytes, Capabilities.crypto] using valid
  obtain ⟨_, leftValid, rightValid⟩ := ScalarValidationMeaning.bind_ok.mp validChildren
  obtain ⟨leftValue, rightValue, leftEval, rightEval⟩ :
      ∃ a b, left.eval ctx values = .ok a ∧ right.eval ctx values = .ok b := by
    cases evaluatedLeft : left.eval ctx values with
    | error message =>
      simp [Expr.eval, evaluatedLeft, Bind.bind, Except.bind] at success
    | ok leftValue =>
      cases evaluatedRight : right.eval ctx values with
      | error message =>
        simp [Expr.eval, evaluatedLeft, evaluatedRight, Bind.bind, Except.bind] at success
      | ok rightValue => exact ⟨leftValue, rightValue, rfl, rfl⟩
  have leftFrame := lowerExpr_admitted_preservesOutputCapacityFrame left leftAdmitted
  have rightFrame := lowerExpr_admitted_preservesOutputCapacityFrame right rightAdmitted
  have testEqFrame (leftText rightText : String) :
      Zkir.PreservesOutputCapacityFrame (Zkir.binary "test_eq" leftText rightText) :=
    Zkir.ordinaryBinary_preservesOutputCapacityFrame "test_eq" leftText rightText
      ⟨by decide, by decide, by decide⟩
  rw [lower_eq_scalar sourceType left right] at budget
  have remainingFrame (leftText : String) :
      Zkir.PreservesOutputCapacityFrame (do
        let rightText ← Zkir.lowerExpr right
        Zkir.binary "test_eq" leftText rightText) :=
    Zkir.bind_preservesOutputCapacityFrame (Zkir.lowerExpr right)
      (fun rightText => Zkir.binary "test_eq" leftText rightText)
      rightFrame (testEqFrame leftText)
  have leftBudget : ((Zkir.lowerExpr left).run state).2.next ≤
      Native.maxInstructions * Native.maxVectorLength :=
    Nat.le_trans (remainingFrame ((Zkir.lowerExpr left).run state).1
      ((Zkir.lowerExpr left).run state).2).next budget
  obtain ⟨first⟩ := completeLeft ctx hash implementation inputs witness state normalAliases values
    types leftValue leftValid leftEval aliasAgreement lowerAliasAgreement lowerStateMeaning leftBudget
  have remainingBudget : ((do
      let rightText ← Zkir.lowerExpr right
      Zkir.binary "test_eq" first.text rightText).run first.finalState).2.next ≤
        Native.maxInstructions * Native.maxVectorLength := by
    rw [StateT.run_bind, first.run] at budget
    exact budget
  have rightBudget : ((Zkir.lowerExpr right).run first.finalState).2.next ≤
      Native.maxInstructions * Native.maxVectorLength := by
    have suffixBudget : ((Zkir.binary "test_eq" first.text
        ((Zkir.lowerExpr right).run first.finalState).1).run
        ((Zkir.lowerExpr right).run first.finalState).2).2.next ≤
        Native.maxInstructions * Native.maxVectorLength := by
      rw [StateT.run_bind] at remainingBudget
      exact remainingBudget
    exact Nat.le_trans (testEqFrame first.text
      ((Zkir.lowerExpr right).run first.finalState).1
      ((Zkir.lowerExpr right).run first.finalState).2).next suffixBudget
  obtain ⟨second⟩ := completeRight ctx hash implementation inputs first.finalWitness first.finalState
    normalAliases values types rightValue rightValid rightEval aliasAgreement first.aliasAgreement
    first.stateMeaning rightBudget
  have beforeSecond : state.next ≤ first.finalState.next := by
    simpa only [first.run] using (leftFrame state).next
  have beforeSuffix : first.finalState.next ≤ second.finalState.next := by
    simpa only [second.run] using (rightFrame first.finalState).next
  have leftMeaning := OperandMeaning.of_frame hash inputs first.finalWitness second.finalWitness
    first.finalState.next first.text first.normalized.term first.operandMeaning first.textScope second.frame
  have testEqBudget : ((Zkir.binary "test_eq" first.text second.text).run second.finalState).2.next ≤
      Native.maxInstructions * Native.maxVectorLength := by
    rw [StateT.run_bind, second.run] at remainingBudget
    exact remainingBudget
  obtain ⟨emitted⟩ := binary_testEq_step hash inputs second.finalWitness second.finalState
    first.text second.text first.normalized.term second.normalized.term second.stateMeaning
    leftMeaning second.operandMeaning (TextScope.mono beforeSuffix first.textScope)
    second.textScope testEqBudget
  let normalized : Native.Normalized := {
    term := .binary "test_eq" first.normalized.term second.normalized.term
    bounds := first.normalized.bounds ++ second.normalized.bounds ++
      [(.binary "test_eq" first.normalized.term second.normalized.term, 1)]
    assertions := first.normalized.assertions ++ second.normalized.assertions
  }
  have normalization : Native.normalize normalAliases (.eq left right) = .ok normalized := by
    simp only [Native.normalize, first.normalization, second.normalization, Bind.bind,
      Except.bind, Native.arithmetic_eq, Native.requireSourceType_eq]
    rfl
  have expressionAdmission : ScalarExpression (.eq left right) :=
    .eq left right sourceType leftAdmitted rightAdmitted
  obtain ⟨actual, actualNormalization, represents⟩ := normalize_success ctx hash
    implementation inputs normalAliases values aliasAgreement (.eq left right)
    expressionAdmission result success
  rw [normalization] at actualNormalization
  cases actualNormalization
  have rootFrame : ∀ name, InScope state.next name →
      emitted.finalWitness name = witness name := by
    intro name inScope
    have leftScope : InScope first.finalState.next name := InScope.mono beforeSecond inScope
    have rightScope : InScope second.finalState.next name := InScope.mono beforeSuffix leftScope
    exact (emitted.frame name rightScope).trans
      ((second.frame name leftScope).trans (first.frame name inScope))
  have aliasesPreserved : emitted.finalState.aliases = state.aliases := by
    rw [emitted.aliasesPreserved, second.aliasesPreserved, first.aliasesPreserved]
  have secondAliases : second.finalState.aliases = state.aliases := by
    rw [second.aliasesPreserved, first.aliasesPreserved]
  have finalAliasAgreement : LowerAliasAgreement hash inputs emitted.finalWitness
      normalAliases emitted.finalState.aliases values := by
    rw [aliasesPreserved]
    rw [← secondAliases]
    exact LowerAliasAgreement.of_frame hash inputs second.finalWitness emitted.finalWitness
      second.finalState.next
      normalAliases second.finalState.aliases values second.aliasAgreement
      second.stateMeaning.aliases emitted.frame
  refine ⟨{
    text := emitted.text
    finalState := emitted.finalState
    finalWitness := emitted.finalWitness
    normalized := normalized
    run := ?_
    normalization := normalization
    represents := represents
    operandMeaning := ?_
    textScope := emitted.textScope
    stateMeaning := emitted.stateMeaning
    budget := emitted.budget
    aliasAgreement := finalAliasAgreement
    aliasesPreserved := aliasesPreserved
    frame := rootFrame
  }⟩
  · rw [lower_eq_scalar sourceType left right]
    rw [StateT.run_bind, first.run]
    change ((do
      let rightText ← Zkir.lowerExpr right
      Zkir.binary "test_eq" first.text rightText).run first.finalState) = _
    rw [StateT.run_bind, second.run]
    exact emitted.run
  · simpa only [normalized] using emitted.operandMeaning

end Noctium.Verification.ScalarWitnessConstruction
