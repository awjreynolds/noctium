import Noctium.Verification.ScalarExpressionLowering

namespace ScalarExpressionAssertionTests

open Noctium Noctium.Verification ScalarLowering ScalarNormalization
open ScalarExpressionLowering

private def assertedNative : Expr .native := .assertE (.bool true) (.native 9)

private theorem assertedNativeAdmission : ScalarExpression assertedNative := by
  unfold assertedNative
  exact ScalarExpression.assertE _ _ (ScalarExpression.bool true) (ScalarExpression.native 9)

example : ExprComplete assertedNative :=
  lowerExpr_complete assertedNative assertedNativeAdmission

private def nestedAssertion : Expr (.uint 7) :=
  .assertE (.bool true) (.assertE (.bool true) (.uint 7 2))

private theorem nestedAssertionAdmission : ScalarExpression nestedAssertion := by
  unfold nestedAssertion
  exact ScalarExpression.assertE _ _ (ScalarExpression.bool true)
    (ScalarExpression.assertE _ _ (ScalarExpression.bool true) (ScalarExpression.uint 7 2))

example : ExprComplete nestedAssertion :=
  lowerExpr_complete nestedAssertion nestedAssertionAdmission

private def ctx : EvalContext := {modulus := Field.modulus, poseidon2 := fun _ _ _ => .ok 0}

example : (Expr.assertE (.bool false) (.usub (.uint 7 1) (.uint 7 2))).eval ctx [] =
    .error "helper assertion failed" := by cbv

example : (Expr.assertE (.bool true) (.usub (.uint 7 1) (.uint 7 2))).eval ctx [] =
    .error "unsigned subtraction underflow" := by cbv

#print axioms ScalarWitnessConstruction.exprComplete_assertE

end ScalarExpressionAssertionTests
