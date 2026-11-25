import Noctium.Verification.ScalarAllocationOutputFrame
import Noctium.Verification.ScalarNativeWitnessSteps
import Noctium.Verification.ScalarExpressionLeaves

namespace Noctium.Verification.ScalarWitnessConstruction

open Backend NativeRelation ScalarNormalization ScalarLowering
open ScalarAllocationOutputFrame

private inductive NativeOperator where
  | add | mul | sub

private def NativeOperator.expression (operator : NativeOperator)
    (left right : Expr .native) : Expr .native :=
  match operator with
  | .add => .add left right
  | .mul => .mul left right
  | .sub => .sub left right

private def NativeOperator.emit (operator : NativeOperator)
    (left right : Expr .native) (a b : String) : StateM Zkir.LowerState String :=
  match operator with
  | .add => Zkir.nativeAdd (Native.isLiteralNativeZero left) (Native.isLiteralNativeZero right) a b
  | .mul => Zkir.binary "mul" a b
  | .sub => do Zkir.binary "add" a (← Zkir.unary "neg" b)

private def NativeOperator.resultTerm (operator : NativeOperator)
    (left right : Expr .native) (a b : Native.Term) : Native.Term :=
  match operator with
  | .add => if Native.isLiteralNativeZero left then b
      else if Native.isLiteralNativeZero right then a else .binary "add" a b
  | .mul => .binary "mul" a b
  | .sub => .binary "add" a (.unary "neg" b)

private theorem NativeOperator.emit_capacity (operator : NativeOperator)
    (left right : Expr .native) (a b : String) :
    Zkir.PreservesOutputCapacityFrame (operator.emit left right a b) := by
  cases operator
  · exact Zkir.nativeAdd_preservesOutputCapacityFrame _ _ _ _
  · exact Zkir.ordinaryBinary_preservesOutputCapacityFrame "mul" a b ⟨by decide, by decide, by decide⟩
  · apply Zkir.bind_preservesOutputCapacityFrame _ _
      (Zkir.ordinaryUnary_preservesOutputCapacityFrame "neg" b ⟨by decide, by decide, by decide⟩)
    intro negated
    exact Zkir.ordinaryBinary_preservesOutputCapacityFrame "add" a negated
      ⟨by decide, by decide, by decide⟩

private theorem NativeOperator.lower (operator : NativeOperator) (left right : Expr .native) :
    Zkir.lowerExpr (operator.expression left right) =
      (do
        let a ← Zkir.lowerExpr left
        let b ← Zkir.lowerExpr right
        operator.emit left right a b) := by
  cases operator <;> simp only [NativeOperator.expression, NativeOperator.emit, Zkir.lowerExpr]

private theorem NativeOperator.normalized_term (operator : NativeOperator)
    {left right : Expr .native} {aliases : Native.AliasEnvironment}
    {a b output : Native.Normalized}
    (na : Native.normalize aliases left = .ok a)
    (nb : Native.normalize aliases right = .ok b)
    (normalization : Native.normalize aliases (operator.expression left right) = .ok output) :
    output.term = operator.resultTerm left right a.term b.term := by
  cases operator <;>
    simp only [NativeOperator.expression, Native.normalize, na, nb, bind_pure_comp,
      Native.arithmetic_eq, Native.subtraction_eq, Native.requireSourceType_eq] at normalization
  all_goals
    cases normalization
    rfl

private def pureStep {hash : Hash} {inputs witness : NativeRelation.Assignment} {state : Zkir.LowerState}
    {text : String} {term : Native.Term}
    (meaning : OperandMeaning hash inputs witness text term)
    (scope : TextScope state.next text)
    (stateMeaning : LowerStateMeaning hash witness state)
    (budget : state.next ≤ Native.maxInstructions * Native.maxVectorLength) :
    NativeStepResult hash inputs witness state (pure text) term where
  text := text
  finalState := state
  finalWitness := witness
  run := rfl
  operandMeaning := meaning
  textScope := scope
  stateMeaning := stateMeaning
  budget := budget
  aliasesPreserved := rfl
  frame := fun _ _ => rfl

private theorem NativeOperator.witness_step (operator : NativeOperator)
    (left right : Expr .native) {hash : Hash} {inputs witness : NativeRelation.Assignment}
    {state : Zkir.LowerState} {a b : String} {aTerm bTerm : Native.Term}
    (stateMeaning : LowerStateMeaning hash witness state)
    (leftMeaning : OperandMeaning hash inputs witness a aTerm)
    (rightMeaning : OperandMeaning hash inputs witness b bTerm)
    (leftScope : TextScope state.next a) (rightScope : TextScope state.next b)
    (budget : ((operator.emit left right a b).run state).2.next ≤
      Native.maxInstructions * Native.maxVectorLength) :
    Nonempty (NativeStepResult hash inputs witness state
      (operator.emit left right a b) (operator.resultTerm left right aTerm bTerm)) := by
  cases operator with
  | add =>
    cases leftZero : Native.isLiteralNativeZero left with
    | true =>
      simp only [NativeOperator.emit, Zkir.nativeAdd, NativeOperator.resultTerm, leftZero,
        ↓reduceIte] at budget ⊢
      exact ⟨pureStep rightMeaning rightScope stateMeaning budget⟩
    | false =>
      cases rightZero : Native.isLiteralNativeZero right with
      | true =>
        simp only [NativeOperator.emit, Zkir.nativeAdd, NativeOperator.resultTerm, leftZero,
          rightZero, Bool.false_eq_true, ↓reduceIte] at budget ⊢
        exact ⟨pureStep leftMeaning leftScope stateMeaning budget⟩
      | false =>
        simp only [NativeOperator.emit, Zkir.nativeAdd, NativeOperator.resultTerm, leftZero,
          rightZero, Bool.false_eq_true, ↓reduceIte] at budget ⊢
        exact binary_add_step hash inputs witness state a b aTerm bTerm stateMeaning
          leftMeaning rightMeaning leftScope rightScope budget
  | mul =>
    exact binary_mul_step hash inputs witness state a b aTerm bTerm stateMeaning
      leftMeaning rightMeaning leftScope rightScope budget
  | sub =>
    have addFrame := fun negated =>
      Zkir.ordinaryBinary_preservesOutputCapacityFrame "add" a negated ⟨by decide, by decide, by decide⟩
    let negated := (Zkir.unary "neg" b).run state
    have remainingNext := (addFrame negated.1 negated.2).next
    have negBudget : ((Zkir.unary "neg" b).run state).2.next ≤
        Native.maxInstructions * Native.maxVectorLength := Nat.le_trans remainingNext budget
    obtain ⟨negative⟩ := unary_neg_step hash inputs witness state b bTerm
      stateMeaning rightMeaning rightScope negBudget
    have negativeNext : state.next ≤ negative.finalState.next := by
      simpa only [negative.run] using
        (Zkir.ordinaryUnary_preservesOutputCapacityFrame "neg" b
          ⟨by decide, by decide, by decide⟩ state).next
    have addBudget : ((Zkir.binary "add" a negative.text).run negative.finalState).2.next ≤
        Native.maxInstructions * Native.maxVectorLength := by
      change ((Zkir.binary "add" a ((Zkir.unary "neg" b).run state).1).run
        ((Zkir.unary "neg" b).run state).2).2.next ≤ _ at budget
      simpa only [negative.run] using budget
    have preservedLeft := OperandMeaning.of_frame hash inputs witness negative.finalWitness
      state.next a aTerm leftMeaning leftScope negative.frame
    obtain ⟨added⟩ := binary_add_step hash inputs negative.finalWitness negative.finalState
      a negative.text aTerm (.unary "neg" bTerm) negative.stateMeaning preservedLeft negative.operandMeaning
      (TextScope.mono negativeNext leftScope) negative.textScope addBudget
    exact ⟨negative.chain (fun text => Zkir.binary "add" a text) added negativeNext⟩

private theorem NativeOperator.complete (operator : NativeOperator) (left right : Expr .native)
    (leftAdmitted : ScalarExpression left) (rightAdmitted : ScalarExpression right)
    (completeLeft : ExprComplete left) (completeRight : ExprComplete right) :
    ExprComplete (operator.expression left right) := by
  intro ctx hash implementation inputs witness state normalAliases values types value
    valid success aliases lowerAliases stateMeaning budget
  have nativeArithmetic : Capabilities.crypto.nativeArithmetic = true := rfl
  have validChildren : (do left.validate Capabilities.crypto types
                           right.validate Capabilities.crypto types) = .ok () := by
    cases operator <;> simpa [NativeOperator.expression, Expr.validate, nativeArithmetic] using valid
  obtain ⟨_, leftValid, rightValid⟩ := ScalarValidationMeaning.bind_ok.mp validChildren
  obtain ⟨leftValue, rightValue, leftEval, rightEval⟩ :
      ∃ a b, left.eval ctx values = .ok a ∧ right.eval ctx values = .ok b := by
    cases ea : left.eval ctx values with
    | error message =>
      cases operator <;> simp [NativeOperator.expression, Expr.eval, ea, implementation.modulus,
        Field.modulus, Bind.bind, Except.bind] at success
    | ok a =>
      cases eb : right.eval ctx values with
      | error message =>
        cases operator <;> simp [NativeOperator.expression, Expr.eval, ea, eb, implementation.modulus,
          Field.modulus, Bind.bind, Except.bind] at success
      | ok b => exact ⟨a, b, rfl, rfl⟩
  have leftFrame := lowerExpr_admitted_preservesOutputCapacityFrame left leftAdmitted
  have rightFrame := lowerExpr_admitted_preservesOutputCapacityFrame right rightAdmitted
  rw [operator.lower] at budget
  have remainingFrame := fun a =>
    Zkir.bind_preservesOutputCapacityFrame (Zkir.lowerExpr right)
      (operator.emit left right a) rightFrame (operator.emit_capacity left right a)
  have leftBudget : ((Zkir.lowerExpr left).run state).2.next ≤
      Native.maxInstructions * Native.maxVectorLength :=
    Nat.le_trans (remainingFrame _ _).next budget
  obtain ⟨first⟩ := completeLeft ctx hash implementation inputs witness state normalAliases values
    types leftValue leftValid leftEval aliases lowerAliases stateMeaning leftBudget
  have remainingBudget : ((do let b ← Zkir.lowerExpr right
                              operator.emit left right first.text b).run first.finalState).2.next ≤
      Native.maxInstructions * Native.maxVectorLength := by
    rw [StateT.run_bind, first.run] at budget
    exact budget
  have rightBudget : ((Zkir.lowerExpr right).run first.finalState).2.next ≤
      Native.maxInstructions * Native.maxVectorLength :=
    Nat.le_trans (operator.emit_capacity left right first.text _ _).next remainingBudget
  obtain ⟨second⟩ := completeRight ctx hash implementation inputs first.finalWitness first.finalState
    normalAliases values types rightValue rightValid rightEval aliases first.aliasAgreement
    first.stateMeaning rightBudget
  have beforeSecond : state.next ≤ first.finalState.next := by
    simpa only [first.run] using (leftFrame state).next
  have beforeSuffix : first.finalState.next ≤ second.finalState.next := by
    simpa only [second.run] using (rightFrame first.finalState).next
  have leftMeaning := OperandMeaning.of_frame hash inputs first.finalWitness second.finalWitness
    first.finalState.next first.text first.normalized.term first.operandMeaning first.textScope second.frame
  have emitBudget : ((operator.emit left right first.text second.text).run second.finalState).2.next ≤
      Native.maxInstructions * Native.maxVectorLength := by
    rw [StateT.run_bind, second.run] at remainingBudget
    exact remainingBudget
  obtain ⟨native⟩ := operator.witness_step left right second.stateMeaning leftMeaning
    second.operandMeaning (TextScope.mono beforeSuffix first.textScope) second.textScope emitBudget
  have admitted : ScalarExpression (operator.expression left right) := by
    cases operator
    · exact .add left right leftAdmitted rightAdmitted
    · exact .mul left right leftAdmitted rightAdmitted
    · exact .sub left right leftAdmitted rightAdmitted
  obtain ⟨normalized, normalization, represents⟩ := normalize_success ctx hash implementation inputs
    normalAliases values aliases (operator.expression left right) admitted value success
  refine ⟨{
    text := native.text
    finalState := native.finalState
    finalWitness := native.finalWitness
    normalized
    run := ?_
    normalization
    represents
    operandMeaning := ?_
    textScope := native.textScope
    stateMeaning := native.stateMeaning
    budget := native.budget
    aliasAgreement := ?_
    aliasesPreserved := native.aliasesPreserved.trans (second.aliasesPreserved.trans first.aliasesPreserved)
    frame := ?_
  }⟩
  · rw [operator.lower, StateT.run_bind, first.run]
    change ((do let b ← Zkir.lowerExpr right
                operator.emit left right first.text b).run first.finalState) = _
    rw [StateT.run_bind, second.run]
    exact native.run
  · rw [operator.normalized_term first.normalization second.normalization normalization]
    exact native.operandMeaning
  · rw [native.aliasesPreserved]
    exact LowerAliasAgreement.of_frame hash inputs second.finalWitness native.finalWitness second.finalState.next
      normalAliases second.finalState.aliases values second.aliasAgreement second.stateMeaning.aliases native.frame
  · intro name inScopeAt
    rw [native.frame name (InScope.mono beforeSuffix (InScope.mono beforeSecond inScopeAt)),
      second.frame name (InScope.mono beforeSecond inScopeAt), first.frame name inScopeAt]

/-- Native literal-zero addition still constructs both child witnesses. The
emitted suffix reuses one child's operand when the optimizer elides Add. -/
theorem complete_add (left right : Expr .native) (leftAdmitted : ScalarExpression left)
    (rightAdmitted : ScalarExpression right) (completeLeft : ExprComplete left)
    (completeRight : ExprComplete right) : ExprComplete (.add left right) :=
  NativeOperator.complete .add left right leftAdmitted rightAdmitted completeLeft completeRight

theorem complete_mul (left right : Expr .native) (leftAdmitted : ScalarExpression left)
    (rightAdmitted : ScalarExpression right) (completeLeft : ExprComplete left)
    (completeRight : ExprComplete right) : ExprComplete (.mul left right) :=
  NativeOperator.complete .mul left right leftAdmitted rightAdmitted completeLeft completeRight

theorem complete_sub (left right : Expr .native) (leftAdmitted : ScalarExpression left)
    (rightAdmitted : ScalarExpression right) (completeLeft : ExprComplete left)
    (completeRight : ExprComplete right) : ExprComplete (.sub left right) :=
  NativeOperator.complete .sub left right leftAdmitted rightAdmitted completeLeft completeRight

end Noctium.Verification.ScalarWitnessConstruction
