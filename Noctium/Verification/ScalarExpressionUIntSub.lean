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

private def uintSubAfterNeg (maximum : Nat) (left negated : String) :
    StateM Zkir.LowerState String := do
  let output ← Zkir.binary "add" left negated
  Zkir.constrainUnsigned maximum output
  pure output

private def uintSubOperation (maximum : Nat) (left right : String) :
    StateM Zkir.LowerState String := do
  let negated ← Zkir.unary "neg" right
  uintSubAfterNeg maximum left negated

private def uintSubTerm (left right : Native.Term) : Native.Term :=
  .binary "add" left (.unary "neg" right)

private theorem uint_sub_step (hash : Hash) (inputs witness : NativeRelation.Assignment)
    (state : Zkir.LowerState) (maximum : Nat) (left right : String)
    (leftTerm rightTerm : Native.Term)
    (stateMeaning : LowerStateMeaning hash witness state)
    (leftMeaning : OperandMeaning hash inputs witness left leftTerm)
    (rightMeaning : OperandMeaning hash inputs witness right rightTerm)
    (leftScope : TextScope state.next left) (rightScope : TextScope state.next right)
    (range : ∃ value, interpret hash inputs (uintSubTerm leftTerm rightTerm) =
      some value ∧ value.val ≤ maximum)
    (admitted : maximum ≤ ScalarPolicy.maxUint)
    (budget : (uintSubOperation maximum left right).run state |>.2.next ≤
      Native.maxInstructions * Native.maxVectorLength) :
    Nonempty (NativeStepResult hash inputs witness state
      (uintSubOperation maximum left right) (uintSubTerm leftTerm rightTerm)) := by
  have unaryFrame : ∀ value, Zkir.PreservesOutputCapacityFrame
      (Zkir.unary "neg" value) := by
    intro value
    exact Zkir.ordinaryUnary_preservesOutputCapacityFrame "neg" value
      ⟨by decide, by decide, by decide⟩
  have binaryFrame (negated : String) : Zkir.PreservesOutputCapacityFrame
      (Zkir.binary "add" left negated) :=
    Zkir.ordinaryBinary_preservesOutputCapacityFrame "add" left negated
      ⟨by decide, by decide, by decide⟩
  have rangeFrame (output : String) : Zkir.PreservesOutputCapacityFrame (do
      Zkir.constrainUnsigned maximum output
      pure output) :=
    Zkir.bind_preservesOutputCapacityFrame _ _
      (Zkir.constrainUnsigned_preservesOutputCapacityFrame maximum output)
      (fun _ => Zkir.pure_preservesOutputCapacityFrame output)
  have afterNegFrame (negated : String) : Zkir.PreservesOutputCapacityFrame
      (uintSubAfterNeg maximum left negated) := by
    exact Zkir.bind_preservesOutputCapacityFrame _ _ (binaryFrame negated) rangeFrame
  have unaryBudget : ((Zkir.unary "neg" right).run state).2.next ≤
      Native.maxInstructions * Native.maxVectorLength := by
    exact Nat.le_trans
      (bind_middle_next (Zkir.unary "neg" right)
        (fun negated => uintSubAfterNeg maximum left negated) state afterNegFrame)
      budget
  obtain ⟨negative⟩ := ScalarWitnessConstruction.unary_neg_step hash inputs witness state
    right rightTerm stateMeaning rightMeaning rightScope unaryBudget
  have unaryNext : state.next ≤ negative.finalState.next := by
    simpa only [negative.run] using (unaryFrame right state).next
  have leftMeaningAfterNeg := OperandMeaning.of_frame hash inputs witness negative.finalWitness
    state.next left leftTerm leftMeaning leftScope negative.frame
  have leftScopeAfterNeg := TextScope.mono unaryNext leftScope
  have afterNegBudget : (uintSubAfterNeg maximum left negative.text).run
      negative.finalState |>.2.next ≤ Native.maxInstructions * Native.maxVectorLength := by
    have bound := budget
    change ((do
        let negated ← Zkir.unary "neg" right
        uintSubAfterNeg maximum left negated).run state).2.next ≤ _ at bound
    rw [StateT.run_bind, negative.run] at bound
    exact bound
  have binaryBudget : ((Zkir.binary "add" left negative.text).run
      negative.finalState).2.next ≤ Native.maxInstructions * Native.maxVectorLength :=
    Nat.le_trans
      (bind_middle_next (Zkir.binary "add" left negative.text)
        (fun output => do
          Zkir.constrainUnsigned maximum output
          pure output) negative.finalState rangeFrame)
      afterNegBudget
  obtain ⟨binary⟩ := ScalarWitnessConstruction.binary_add_step hash inputs
    negative.finalWitness negative.finalState left negative.text leftTerm
    (.unary "neg" rightTerm) negative.stateMeaning leftMeaningAfterNeg
    negative.operandMeaning leftScopeAfterNeg negative.textScope binaryBudget
  have binaryNext : negative.finalState.next ≤ binary.finalState.next := by
    simpa only [binary.run] using (binaryFrame negative.text negative.finalState).next
  have rangeBudget : ((do
      Zkir.constrainUnsigned maximum binary.text
      pure binary.text).run binary.finalState).2.next ≤
        Native.maxInstructions * Native.maxVectorLength := by
    have bound := afterNegBudget
    change ((do
        let output ← Zkir.binary "add" left negative.text
        Zkir.constrainUnsigned maximum output
        pure output).run negative.finalState).2.next ≤ _ at bound
    rw [StateT.run_bind, binary.run] at bound
    exact bound
  obtain ⟨bounded⟩ := ScalarWitnessConstruction.constrainUnsigned_step hash inputs
    binary.finalWitness binary.finalState maximum binary.text
    (.binary "add" leftTerm (.unary "neg" rightTerm)) binary.stateMeaning
    binary.operandMeaning binary.textScope range admitted rangeBudget
  let afterBinary := binary.chain
    (fun output => do
      Zkir.constrainUnsigned maximum output
      pure output) bounded binaryNext
  let combined := negative.chain
    (fun negated => uintSubAfterNeg maximum left negated) afterBinary unaryNext
  have result : NativeStepResult hash inputs witness state
      (uintSubOperation maximum left right) (uintSubTerm leftTerm rightTerm) := {
    combined with
    run := by simpa [uintSubOperation] using combined.run
  }
  exact ⟨result⟩

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

/-- Unsigned subtraction lowers as field subtraction, then constrains the
result to the left operand's source bound. Source evaluation rejects
underflow, so every successful source result supplies that bound. -/
theorem complete_usub {m n : Nat} (left : Expr (.uint m)) (right : Expr (.uint n))
    (leftAdmission : ScalarExpression left) (rightAdmission : ScalarExpression right)
    (completeLeft : ExprComplete left) (completeRight : ExprComplete right) :
    ExprComplete (.usub left right) := by
  intro ctx hash implementation inputs witness state normalAliases values types value
    valid success aliases lowerAliases stateMeaning budget
  let admission : ScalarExpression (.usub left right) :=
    .usub left right leftAdmission rightAdmission
  let tail (a b : String) : StateM Zkir.LowerState String :=
    uintSubOperation m a b
  have lowerRun : Zkir.lowerExpr (.usub left right) = (do
      let a ← Zkir.lowerExpr left
      let b ← Zkir.lowerExpr right
      tail a b) := by
    simp only [Zkir.lowerExpr, tail, uintSubOperation, uintSubAfterNeg]
  have leftFrame := ScalarAllocationOutputFrame.lowerExpr_admitted_preservesOutputCapacityFrame
    left leftAdmission
  have rightFrame := ScalarAllocationOutputFrame.lowerExpr_admitted_preservesOutputCapacityFrame
    right rightAdmission
  have binaryFrame (a negated : String) : Zkir.PreservesOutputCapacityFrame
      (Zkir.binary "add" a negated) :=
    Zkir.ordinaryBinary_preservesOutputCapacityFrame "add" a negated
      ⟨by decide, by decide, by decide⟩
  have unaryFrame (b : String) : Zkir.PreservesOutputCapacityFrame
      (Zkir.unary "neg" b) :=
    Zkir.ordinaryUnary_preservesOutputCapacityFrame "neg" b
      ⟨by decide, by decide, by decide⟩
  have rangeFrame (output : String) : Zkir.PreservesOutputCapacityFrame (do
      Zkir.constrainUnsigned m output
      pure output) :=
    Zkir.bind_preservesOutputCapacityFrame _ _
      (Zkir.constrainUnsigned_preservesOutputCapacityFrame m output)
      (fun _ => Zkir.pure_preservesOutputCapacityFrame output)
  have tailAfterNegFrame (a negated : String) :
      Zkir.PreservesOutputCapacityFrame (uintSubAfterNeg m a negated) := by
    exact Zkir.bind_preservesOutputCapacityFrame _ _ (binaryFrame a negated) rangeFrame
  have tailFrame (a b : String) : Zkir.PreservesOutputCapacityFrame (tail a b) := by
    change Zkir.PreservesOutputCapacityFrame (uintSubOperation m a b)
    exact Zkir.bind_preservesOutputCapacityFrame _ _ (unaryFrame b) (tailAfterNegFrame a)
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
      (Ty.uint m).validate Capabilities.crypto
      left.validate Capabilities.crypto types
      right.validate Capabilities.crypto types) = .ok () := by
    simpa [Expr.validate, nativeArithmetic] using valid
  rcases ScalarValidationMeaning.bind_ok.mp validForm with
    ⟨_, typeValid, childrenValid⟩
  rcases ScalarValidationMeaning.bind_ok.mp childrenValid with
    ⟨_, leftValid, rightValid⟩
  have typeBound : m ≤ ScalarPolicy.maxUint := by
    by_cases bound : m ≤ ScalarPolicy.maxUint
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
      obtain ⟨normalized, normalization, represents⟩ :=
        normalize_success ctx hash implementation inputs normalAliases values aliases
          (.usub left right) admission value success
      have termEq : normalized.term = uintSubTerm first.normalized.term
          second.normalized.term := by
        have normal := normalization
        simp only [Native.normalize, first.normalization, second.normalization] at normal
        cases normal
        simp [uintSubTerm, Native.subtraction_eq, Native.requireSourceType_eq]
      have resultMeaning : interpret hash inputs
          (uintSubTerm first.normalized.term second.normalized.term) =
          some (scalar value) := by
        rw [← termEq]
        simpa [ScalarNormalization.number] using
          (represents.2.2.trans (sourceScalar_number (ScalarType.uint m) value))
      have valueBound : value ≤ m := represents.1.2.2
      have resultRange : ∃ found,
          interpret hash inputs (uintSubTerm first.normalized.term second.normalized.term) =
            some found ∧ found.val ≤ m := by
        refine ⟨scalar value, resultMeaning, ?_⟩
        exact Nat.le_trans (Nat.mod_le value Field.modulus) valueBound
      obtain ⟨native⟩ := uint_sub_step hash inputs second.finalWitness second.finalState m
        first.text second.text first.normalized.term second.normalized.term
        second.stateMeaning leftMeaning second.operandMeaning leftScope second.textScope
        resultRange typeBound tailBudget
      let firstNative : NativeStepResult hash inputs witness state
          (Zkir.lowerExpr left) first.normalized.term := {
        text := first.text
        finalState := first.finalState
        finalWitness := first.finalWitness
        run := first.run
        operandMeaning := first.operandMeaning
        textScope := first.textScope
        stateMeaning := first.stateMeaning
        budget := first.budget
        aliasesPreserved := first.aliasesPreserved
        frame := first.frame
      }
      let secondNative : NativeStepResult hash inputs first.finalWitness first.finalState
          (Zkir.lowerExpr right) second.normalized.term := {
        text := second.text
        finalState := second.finalState
        finalWitness := second.finalWitness
        run := second.run
        operandMeaning := second.operandMeaning
        textScope := second.textScope
        stateMeaning := second.stateMeaning
        budget := second.budget
        aliasesPreserved := second.aliasesPreserved
        frame := second.frame
      }
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
        have agreement := LowerAliasAgreement.of_frame hash inputs second.finalWitness
          full.finalWitness second.finalState.next normalAliases second.finalState.aliases values
          second.aliasAgreement second.stateMeaning.aliases native.frame
        simpa [second.aliasesPreserved, first.aliasesPreserved] using agreement
      · intro name inScope
        change native.finalWitness name = witness name
        rw [native.frame name (InScope.mono secondNext (InScope.mono firstNext inScope)),
          second.frame name (InScope.mono firstNext inScope), first.frame name inScope]

end Noctium.Verification.ScalarWitnessConstruction
