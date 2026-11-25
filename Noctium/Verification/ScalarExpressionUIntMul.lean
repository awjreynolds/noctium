import Noctium.Verification.ScalarExpressionUIntAdd
import Noctium.Verification.ScalarNativeWitnessSteps
import Noctium.Verification.ScalarAllocationOutputFrame
import Noctium.Verification.ScalarStateExtensions

namespace Noctium.Verification.ScalarWitnessConstruction

open Lean Backend NativeRelation NativeRelationJson ScalarLowering ScalarNormalization
open ScalarInstructionEncoding ScalarWitness

private theorem bind_middle_next (first : StateM Zkir.LowerState α)
    (next : α → StateM Zkir.LowerState β) (state : Zkir.LowerState)
    (preserves : ∀ value, Zkir.PreservesOutputCapacityFrame (next value)) :
    (first.run state).2.next ≤ ((first >>= next).run state).2.next := by
  change (first.run state).2.next ≤
    ((next (first.run state).1).run (first.run state).2).2.next
  exact (preserves (first.run state).1 (first.run state).2).next

private def asNativeStep {hash : Hash} {inputs witness : NativeRelation.Assignment}
    {state : Zkir.LowerState} {normalAliases : Backend.Native.AliasEnvironment}
    {values : EvalEnv} {expression : Expr ty} {value : ty.Denote}
    (step : ExprStepResult hash inputs witness state normalAliases values expression value) :
    NativeStepResult hash inputs witness state (Zkir.lowerExpr expression) step.normalized.term where
  text := step.text
  finalState := step.finalState
  finalWitness := step.finalWitness
  run := step.run
  operandMeaning := step.operandMeaning
  textScope := step.textScope
  stateMeaning := step.stateMeaning
  budget := step.budget
  aliasesPreserved := step.aliasesPreserved
  frame := step.frame

/-- Bounded UInt multiplication uses the emitted multiplication result, then
proves that the result satisfies the product type's declared range. -/
theorem complete_umul {m n : Nat} (left : Expr (.uint m)) (right : Expr (.uint n))
    (leftAdmission : ScalarExpression left) (rightAdmission : ScalarExpression right)
    (completeLeft : ExprComplete left) (completeRight : ExprComplete right) :
    ExprComplete (.umul left right) := by
  intro ctx hash implementation inputs witness state normalAliases values types value
    valid success aliases lowerAliases stateMeaning budget
  let admission : ScalarExpression (.umul left right) :=
    .umul left right leftAdmission rightAdmission
  let tail (a b : String) : StateM Zkir.LowerState String := do
    let output ← Zkir.binary "mul" a b
    Zkir.constrainUnsigned (m * n) output
    pure output
  have lowerRun : Zkir.lowerExpr (.umul left right) = (do
      let a ← Zkir.lowerExpr left
      let b ← Zkir.lowerExpr right
      tail a b) := by
    simp only [Zkir.lowerExpr, tail]
  have leftFrame := ScalarAllocationOutputFrame.lowerExpr_admitted_preservesOutputCapacityFrame
    left leftAdmission
  have rightFrame := ScalarAllocationOutputFrame.lowerExpr_admitted_preservesOutputCapacityFrame
    right rightAdmission
  have binaryFrame (a b : String) : Zkir.PreservesOutputCapacityFrame (Zkir.binary "mul" a b) :=
    Zkir.ordinaryBinary_preservesOutputCapacityFrame "mul" a b ⟨by decide, by decide, by decide⟩
  have rangeFrame (output : String) : Zkir.PreservesOutputCapacityFrame (do
      Zkir.constrainUnsigned (m * n) output
      pure output) :=
    Zkir.bind_preservesOutputCapacityFrame _ _
      (Zkir.constrainUnsigned_preservesOutputCapacityFrame (m * n) output)
      (fun _ => Zkir.pure_preservesOutputCapacityFrame output)
  have tailFrame (a b : String) : Zkir.PreservesOutputCapacityFrame (tail a b) := by
    exact Zkir.bind_preservesOutputCapacityFrame _ _ (binaryFrame a b) rangeFrame
  have rightSuffixFrame (a : String) : Zkir.PreservesOutputCapacityFrame (do
      let b ← Zkir.lowerExpr right
      tail a b) :=
    Zkir.bind_preservesOutputCapacityFrame _ _ rightFrame (tailFrame a)
  have loweredBudget := budget
  rw [lowerRun] at loweredBudget
  have leftBudget : ((Zkir.lowerExpr left).run state).2.next ≤
      Native.maxInstructions * Native.maxVectorLength :=
    Nat.le_trans (rightSuffixFrame _ _).next loweredBudget
  have nativeArithmetic : Capabilities.crypto.nativeArithmetic = true := rfl
  have validForm : (do
      (Ty.uint (m * n)).validate Capabilities.crypto
      left.validate Capabilities.crypto types
      right.validate Capabilities.crypto types) = .ok () := by
    simpa [Expr.validate, nativeArithmetic] using valid
  rcases ScalarValidationMeaning.bind_ok.mp validForm with
    ⟨_, typeValid, childrenValid⟩
  rcases ScalarValidationMeaning.bind_ok.mp childrenValid with
    ⟨_, leftValid, rightValid⟩
  have typeBound : m * n ≤ ScalarPolicy.maxUint := by
    by_cases bound : m * n ≤ ScalarPolicy.maxUint
    · exact bound
    · simp [Ty.validate, Ty.scalarKind, ScalarPolicy.validate, bound,
        Bind.bind, Except.bind] at typeValid
  cases leftEval : left.eval ctx values with
  | error message => simp [Expr.eval, leftEval, Bind.bind, Except.bind] at success
  | ok leftValue =>
    cases rightEval : right.eval ctx values with
    | error message => simp [Expr.eval, leftEval, rightEval, Bind.bind, Except.bind] at success
    | ok rightValue =>
      obtain ⟨first⟩ := completeLeft ctx hash implementation inputs witness state normalAliases
        values types leftValue leftValid leftEval aliases lowerAliases stateMeaning leftBudget
      have remainingBudget : ((do
          let b ← Zkir.lowerExpr right
          tail first.text b).run first.finalState).2.next ≤
          Native.maxInstructions * Native.maxVectorLength := by
        have bound := loweredBudget
        rw [StateT.run_bind, first.run] at bound
        exact bound
      have rightBudget : ((Zkir.lowerExpr right).run first.finalState).2.next ≤
          Native.maxInstructions * Native.maxVectorLength :=
        Nat.le_trans (tailFrame first.text _ _).next remainingBudget
      obtain ⟨second⟩ := completeRight ctx hash implementation inputs first.finalWitness
        first.finalState normalAliases values types rightValue rightValid rightEval aliases
        first.aliasAgreement first.stateMeaning rightBudget
      have firstNext : state.next ≤ first.finalState.next := by
        simpa only [first.run] using (leftFrame state).next
      have secondNext : first.finalState.next ≤ second.finalState.next := by
        simpa only [second.run] using (rightFrame first.finalState).next
      have leftMeaning := OperandMeaning.of_frame hash inputs first.finalWitness second.finalWitness
        first.finalState.next first.text first.normalized.term first.operandMeaning
        first.textScope second.frame
      have leftScope := TextScope.mono secondNext first.textScope
      have tailBudget : (tail first.text second.text).run second.finalState |>.2.next ≤
          Native.maxInstructions * Native.maxVectorLength := by
        rw [StateT.run_bind, second.run] at remainingBudget
        exact remainingBudget
      have binaryBudget : ((Zkir.binary "mul" first.text second.text).run second.finalState).2.next ≤
          Native.maxInstructions * Native.maxVectorLength :=
        Nat.le_trans
          (bind_middle_next (Zkir.binary "mul" first.text second.text)
            (fun output => do Zkir.constrainUnsigned (m * n) output; pure output)
            second.finalState rangeFrame)
          tailBudget
      obtain ⟨binary⟩ := ScalarWitnessConstruction.binary_mul_step hash inputs second.finalWitness
        second.finalState first.text second.text first.normalized.term second.normalized.term
        second.stateMeaning leftMeaning second.operandMeaning leftScope second.textScope binaryBudget
      have binaryNext : second.finalState.next ≤ binary.finalState.next := by
        simpa only [binary.run] using (binaryFrame first.text second.text second.finalState).next
      obtain ⟨normalized, normalization, represents⟩ :=
        normalize_success ctx hash implementation inputs normalAliases values aliases
          (.umul left right) admission value success
      have termEq : normalized.term = .binary "mul" first.normalized.term second.normalized.term := by
        have normal := normalization
        simp only [Native.normalize, first.normalization, second.normalization] at normal
        cases normal
        simp only [Native.arithmetic_eq, Native.requireSourceType_eq]
      have resultMeaning : interpret hash inputs
          (.binary "mul" first.normalized.term second.normalized.term) = some (scalar value) := by
        rw [← termEq]
        simpa [ScalarNormalization.number] using
          (represents.2.2.trans (sourceScalar_number (ScalarType.uint (m * n)) value))
      have valueBound : value ≤ m * n := represents.1.2.2
      have resultRange : ∃ found,
          interpret hash inputs (.binary "mul" first.normalized.term second.normalized.term) =
            some found ∧ found.val ≤ m * n := by
        refine ⟨scalar value, resultMeaning, ?_⟩
        exact Nat.le_trans (Nat.mod_le value Field.modulus) valueBound
      have rangeBudget : ((do
          Zkir.constrainUnsigned (m * n) binary.text
          pure binary.text).run binary.finalState).2.next ≤
          Native.maxInstructions * Native.maxVectorLength := by
        have bound := tailBudget
        change ((do
            let output ← Zkir.binary "mul" first.text second.text
            Zkir.constrainUnsigned (m * n) output
            pure output).run second.finalState).2.next ≤ _ at bound
        rw [StateT.run_bind, binary.run] at bound
        exact bound
      obtain ⟨bounded⟩ := constrainUnsigned_step hash inputs binary.finalWitness binary.finalState
        (m * n) binary.text (.binary "mul" first.normalized.term second.normalized.term)
        binary.stateMeaning binary.operandMeaning binary.textScope resultRange typeBound rangeBudget
      let native := binary.chain
        (fun output => do Zkir.constrainUnsigned (m * n) output; pure output) bounded binaryNext
      let firstNative := asNativeStep first
      let secondNative := asNativeStep second
      let pair := firstNative.chain (fun _ => Zkir.lowerExpr right) secondNative firstNext
      let full := pair.chain (fun rightText => tail first.text rightText) native
        (Nat.le_trans firstNext secondNext)
      refine ⟨{
        text := full.text
        finalState := full.finalState
        finalWitness := full.finalWitness
        normalized := normalized
        run := ?_
        normalization := normalization
        represents := represents
        operandMeaning := by rw [termEq]; exact full.operandMeaning
        textScope := full.textScope
        stateMeaning := full.stateMeaning
        budget := full.budget
        aliasAgreement := ?_
        aliasesPreserved := full.aliasesPreserved
        frame := ?_
      }⟩
      · rw [lowerRun, StateT.run_bind, first.run]
        change ((do
            let b ← Zkir.lowerExpr right
            tail first.text b).run first.finalState) = _
        rw [StateT.run_bind, second.run]
        exact native.run
      · rw [full.aliasesPreserved]
        have agreement := LowerAliasAgreement.of_frame hash inputs second.finalWitness full.finalWitness
          second.finalState.next normalAliases second.finalState.aliases values
          second.aliasAgreement second.stateMeaning.aliases native.frame
        simpa [second.aliasesPreserved, first.aliasesPreserved] using agreement
      · intro name inScope
        change native.finalWitness name = witness name
        rw [native.frame name (InScope.mono secondNext (InScope.mono firstNext inScope)),
          second.frame name (InScope.mono firstNext inScope), first.frame name inScope]

end Noctium.Verification.ScalarWitnessConstruction
