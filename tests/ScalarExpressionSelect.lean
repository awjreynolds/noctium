import Noctium.Verification.ScalarExpressionLowering

namespace ScalarExpressionSelectTests

open Noctium Noctium.Verification ScalarLowering ScalarNormalization
open ScalarExpressionLowering

private def nativeSelect : Expr .native := .select (.bool true) (.native 9) (.native 2)

private theorem nativeSelectAdmission : ScalarExpression nativeSelect := by
  unfold nativeSelect
  exact ScalarExpression.select _ _ _ .native (ScalarExpression.bool true)
    (ScalarExpression.native 9) (ScalarExpression.native 2)

example : ExprComplete nativeSelect :=
  lowerExpr_complete nativeSelect nativeSelectAdmission

private def uintSelect : Expr (.uint 3) :=
  .select (.bool false) (.uint 3 1) (.cast (.uint 3) (.native 2))

private theorem uintSelectAdmission : ScalarExpression uintSelect := by
  unfold uintSelect
  exact ScalarExpression.select _ _ _ (.uint 3) (ScalarExpression.bool false)
    (ScalarExpression.uint 3 1)
    (ScalarExpression.cast _ .native (.uint 3) (ScalarExpression.native 2))

example : ExprComplete uintSelect := lowerExpr_complete uintSelect uintSelectAdmission

private def ctx : EvalContext := {modulus := Field.modulus, poseidon2 := fun _ _ _ => .ok 0}

example : (Expr.select (.bool true) (.uint 3 1) (.cast (.uint 3) (.native 4))).eval ctx [] =
    .error "scalar conversion exceeds unsigned bound" := by cbv

example : (Expr.select (.bool false) (.native 9) (.native 2)).eval ctx [] = .ok 2 := by
  cbv

#print axioms ScalarWitnessConstruction.exprComplete_select

end ScalarExpressionSelectTests
