import Noctium.GuardedExpression
import Noctium.Verification.ScalarNormalization

namespace Noctium.Verification.GuardedScalarExpressionAdmission

open ScalarNormalization

private theorem zeroValue_admitted {ty : Ty} (scalarType : ScalarType ty) :
    ScalarExpression (GuardedExpression.zeroValue ty) := by
  cases scalarType with
  | native => exact ScalarExpression.native 0
  | bool => exact ScalarExpression.bool false
  | uint maximum => exact ScalarExpression.uint maximum 0

/-- Guard totalization preserves the exact scalar-expression admission
fragment. The inserted fallback expressions are limited to scalar types. -/
theorem totalize_scalarExpression (guard : Expr .bool)
    (guardAdmitted : ScalarExpression guard) (expression : Expr ty)
    (admitted : ScalarExpression expression) :
    ScalarExpression (GuardedExpression.totalize guard expression) := by
  induction admitted with
  | native value =>
      simpa [GuardedExpression.totalize] using (ScalarExpression.native value)
  | bool value =>
      simpa [GuardedExpression.totalize] using (ScalarExpression.bool value)
  | uint maximum value =>
      simpa [GuardedExpression.totalize] using (ScalarExpression.uint maximum value)
  | ref name scalarType =>
      simpa [GuardedExpression.totalize] using (ScalarExpression.ref name scalarType)
  | add left right leftAdmitted rightAdmitted ihLeft ihRight =>
      rw [GuardedExpression.totalize]
      exact ScalarExpression.add _ _ ihLeft ihRight
  | mul left right leftAdmitted rightAdmitted ihLeft ihRight =>
      rw [GuardedExpression.totalize]
      exact ScalarExpression.mul _ _ ihLeft ihRight
  | sub left right leftAdmitted rightAdmitted ihLeft ihRight =>
      rw [GuardedExpression.totalize]
      exact ScalarExpression.sub _ _ ihLeft ihRight
  | uadd left right leftAdmitted rightAdmitted ihLeft ihRight =>
      rw [GuardedExpression.totalize]
      exact ScalarExpression.uadd _ _ ihLeft ihRight
  | usub left right leftAdmitted rightAdmitted ihLeft ihRight =>
      rename_i m n
      rw [GuardedExpression.totalize]
      exact ScalarExpression.usub
        _ _
        (ScalarExpression.select guard (GuardedExpression.totalize guard left)
          (.uint m 0) (.uint m) guardAdmitted ihLeft (ScalarExpression.uint m 0))
        (ScalarExpression.select guard (GuardedExpression.totalize guard right)
          (.uint n 0) (.uint n) guardAdmitted ihRight (ScalarExpression.uint n 0))
  | umul left right leftAdmitted rightAdmitted ihLeft ihRight =>
      rw [GuardedExpression.totalize]
      exact ScalarExpression.umul _ _ ihLeft ihRight
  | cast value sourceType targetType valueAdmitted ihValue =>
      rename_i source target
      have fallbackAdmitted :
          ScalarExpression (GuardedExpression.zeroValue source) :=
        zeroValue_admitted sourceType
      simp only [GuardedExpression.totalize]
      split
      · exact ScalarExpression.cast _ sourceType targetType
          (ScalarExpression.select guard (GuardedExpression.totalize guard value)
            (GuardedExpression.zeroValue source) sourceType guardAdmitted ihValue
            fallbackAdmitted)
      · exact ScalarExpression.cast _ sourceType targetType ihValue
  | letE name value body sourceScalar valueAdmitted bodyAdmitted ihValue ihBody =>
      rw [GuardedExpression.totalize]
      exact ScalarExpression.letE name _ _ sourceScalar ihValue ihBody
  | assertE condition body conditionAdmitted bodyAdmitted ihCondition ihBody =>
      rw [GuardedExpression.totalize]
      exact ScalarExpression.assertE
        _ _
        (ScalarExpression.select guard (GuardedExpression.totalize guard condition)
          (.bool true) .bool guardAdmitted ihCondition (ScalarExpression.bool true))
        ihBody
  | copyValue value valueAdmitted ihValue =>
      rw [GuardedExpression.totalize]
      exact ScalarExpression.copyValue _ ihValue
  | disclose span value valueAdmitted ihValue =>
      rw [GuardedExpression.totalize]
      exact ScalarExpression.disclose span _ ihValue
  | eq left right scalarType leftAdmitted rightAdmitted ihLeft ihRight =>
      rw [GuardedExpression.totalize]
      exact ScalarExpression.eq _ _ scalarType ihLeft ihRight
  | select condition yes no scalarType conditionAdmitted yesAdmitted noAdmitted
      ihCondition ihYes ihNo =>
      rw [GuardedExpression.totalize]
      exact ScalarExpression.select _ _ _ scalarType ihCondition ihYes ihNo
  | poseidon2 domain left right leftAdmitted rightAdmitted ihLeft ihRight =>
      rw [GuardedExpression.totalize]
      exact ScalarExpression.poseidon2 domain _ _ ihLeft ihRight

end Noctium.Verification.GuardedScalarExpressionAdmission
