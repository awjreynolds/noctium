import Noctium.Verification.ScalarAllocation
import Noctium.Verification.ScalarExpressionUIntAdd

namespace Noctium.Verification.ScalarWitnessConstruction

open Lean Backend NativeRelation NativeRelationJson ScalarNormalization ScalarLowering
open ScalarWitness ScalarAllocationOutputFrame

private theorem lower_uint_cast (maximum : Nat) {sourceTy : Ty}
    (expression : Expr sourceTy) :
    Zkir.lowerExpr (.cast (.uint maximum) expression) =
      (do
        let text ← Zkir.lowerExpr expression
        Zkir.constrainUnsigned maximum text
        pure text) := by
  simp only [Zkir.lowerExpr]

private theorem uint_type_valid_admitted (maximum : Nat)
    (valid : (Ty.uint maximum).validate Capabilities.crypto = .ok ()) :
    maximum ≤ ScalarPolicy.maxUint := by
  by_cases bound : maximum ≤ ScalarPolicy.maxUint
  · exact bound
  · simp [Ty.validate, Ty.scalarKind, ScalarPolicy.validate, bound,
      Bind.bind, Except.bind] at valid

private theorem uint_cast_validation_parts {sourceTy : Ty} (maximum : Nat)
    (expression : Expr sourceTy) (sourceType : ScalarType sourceTy)
    (types : TypeEnv)
    (valid : (Expr.cast (.uint maximum) expression).validate Capabilities.crypto types = .ok ()) :
    (Ty.uint maximum).validate Capabilities.crypto = .ok () ∧
      expression.validate Capabilities.crypto types = .ok () := by
  have parts : ((Ty.uint maximum).validate Capabilities.crypto >>= fun _ =>
      expression.validate Capabilities.crypto types) = .ok () := by
    cases sourceType <;>
      simpa [Expr.validate, Ty.isBytes, Ty.isOpaqueBytes, Ty.isOpaqueString,
        Ty.isJubjub, Ty.isForeign] using valid
  obtain ⟨_, targetValid, expressionValid⟩ := ScalarValidationMeaning.bind_ok.mp parts
  exact ⟨targetValid, expressionValid⟩

/-- A scalar source cast to UInt lowers through the source operand, then applies
the actual ZKIR unsigned-range constraint. Checked source evaluation provides
the range witness consumed by the exact output-slot proof. -/
theorem exprComplete_uintCast {sourceTy : Ty} (maximum : Nat)
    (expression : Expr sourceTy) (sourceType : ScalarType sourceTy)
    (expressionAdmitted : ScalarExpression expression)
    (expressionComplete : ExprComplete expression) :
    ExprComplete (.cast (.uint maximum) expression) := by
  intro ctx hash implementation inputs witness state normalAliases values types value
    valid success aliases lowerAliases stateMeaning budget
  have sourceSuccess := success
  obtain ⟨targetValid, expressionValid⟩ := uint_cast_validation_parts maximum expression
    sourceType types valid
  have maximumAdmitted := uint_type_valid_admitted maximum targetValid
  have childEvaluation : ∃ childValue, expression.eval ctx values = .ok childValue := by
    cases evaluated : expression.eval ctx values with
    | ok childValue => exact ⟨childValue, rfl⟩
    | error message =>
      cases sourceType <;>
        simp [Expr.eval, evaluated, Ty.isBytes, Ty.isJubjub, Ty.isForeign,
          Bind.bind, Except.bind] at success
  obtain ⟨childValue, childSuccess⟩ := childEvaluation
  have castEvaluation := eval_cast_scalar ctx values expression sourceType
    (.uint maximum) childValue childSuccess
  rw [castEvaluation] at success
  simp only [scalarCast] at success
  change (if maximum ≤ ScalarPolicy.maxUint && number sourceType childValue ≤ maximum &&
      number sourceType childValue < ctx.modulus then
    Except.ok (number sourceType childValue)
    else Except.error "scalar conversion exceeds unsigned bound") = Except.ok value at success
  split at success
  next resultValid =>
    cases success
    simp only [Bool.and_eq_true, decide_eq_true_eq] at resultValid
    rcases resultValid with ⟨⟨_, valueBound⟩, _⟩
    have castFrame (text : String) :
        Zkir.PreservesOutputCapacityFrame (do
          Zkir.constrainUnsigned maximum text
          pure text) := by
      exact Zkir.bind_preservesOutputCapacityFrame _ _
        (Zkir.constrainUnsigned_preservesOutputCapacityFrame maximum text)
        (fun _ => Zkir.pure_preservesOutputCapacityFrame text)
    have castBudget : ((Zkir.lowerExpr (.cast (.uint maximum) expression)).run state).2.next ≤
        Native.maxInstructions * Native.maxVectorLength := budget
    rw [lower_uint_cast] at castBudget
    have childBudget : ((Zkir.lowerExpr expression).run state).2.next ≤
        Native.maxInstructions * Native.maxVectorLength := by
      exact ScalarAllocation.bind_middle_budget (Zkir.lowerExpr expression)
        (fun text => do Zkir.constrainUnsigned maximum text; pure text)
        state castFrame _ castBudget
    obtain ⟨child⟩ := expressionComplete ctx hash implementation inputs witness state
      normalAliases values types childValue expressionValid childSuccess aliases lowerAliases
      stateMeaning childBudget
    have childNext : state.next ≤ child.finalState.next := by
      have frame := lowerExpr_admitted_preservesOutputCapacityFrame expression expressionAdmitted state
      rw [child.run] at frame
      exact frame.next
    have castSuffixBudget :
        ((do Zkir.constrainUnsigned maximum child.text; pure child.text).run
          child.finalState).2.next ≤ Native.maxInstructions * Native.maxVectorLength := by
      rw [StateT.run_bind, child.run] at castBudget
      exact castBudget
    have childRange : ∃ scalarValue,
        interpret hash inputs child.normalized.term = some scalarValue ∧
          scalarValue.val ≤ maximum := by
      refine ⟨scalar (number sourceType childValue), ?_, ?_⟩
      · exact child.represents.2.2.trans (sourceScalar_number sourceType childValue)
      · change number sourceType childValue % Field.modulus ≤ maximum
        exact Nat.le_trans (Nat.mod_le _ _) valueBound
    obtain ⟨castStep⟩ := constrainUnsigned_step hash inputs child.finalWitness
      child.finalState maximum child.text child.normalized.term child.stateMeaning
      child.operandMeaning child.textScope childRange maximumAdmitted castSuffixBudget
    obtain ⟨normalized, normalization, represents⟩ := normalize_success ctx hash
      implementation inputs normalAliases values aliases (.cast (.uint maximum) expression)
      (.cast expression sourceType (.uint maximum) expressionAdmitted)
      (number sourceType childValue) sourceSuccess
    have termEq : normalized.term = child.normalized.term := by
      have actual := normalization
      simp only [Native.normalize, child.normalization] at actual
      cases actual
      simp only [Native.requireSourceType_eq]
    refine ⟨{
      text := castStep.text
      finalState := castStep.finalState
      finalWitness := castStep.finalWitness
      normalized
      run := ?_
      normalization
      represents
      operandMeaning := ?_
      textScope := castStep.textScope
      stateMeaning := castStep.stateMeaning
      budget := castStep.budget
      aliasAgreement := ?_
      aliasesPreserved := castStep.aliasesPreserved.trans child.aliasesPreserved
      frame := ?_
    }⟩
    · rw [lower_uint_cast, StateT.run_bind, child.run]
      exact castStep.run
    · rw [termEq]
      exact castStep.operandMeaning
    · rw [castStep.aliasesPreserved]
      exact LowerAliasAgreement.of_frame hash inputs child.finalWitness castStep.finalWitness
        child.finalState.next normalAliases child.finalState.aliases values child.aliasAgreement
        child.stateMeaning.aliases castStep.frame
    · intro name inScope
      exact (castStep.frame name (InScope.mono childNext inScope)).trans
        (child.frame name inScope)
  next => cases success

end Noctium.Verification.ScalarWitnessConstruction
