import Noctium.Verification.ScalarExpressionLowering

namespace ScalarExpressionHashTests

open Noctium Noctium.Verification ScalarLowering ScalarNormalization
open ScalarExpressionLowering

private def hashInput : Expr .native := .poseidon2 11 (.native 5) (.native 7)

private theorem hashInputAdmission : ScalarExpression hashInput := by
  unfold hashInput
  exact ScalarExpression.poseidon2 _ _ _ (ScalarExpression.native 5) (ScalarExpression.native 7)

example : ExprComplete hashInput := lowerExpr_complete hashInput hashInputAdmission

private def repeatedHashInput : Expr .native :=
  .poseidon2 11 (.add (.native 3) (.native 4)) (.add (.native 3) (.native 4))

private theorem repeatedHashInputAdmission : ScalarExpression repeatedHashInput := by
  unfold repeatedHashInput
  exact ScalarExpression.poseidon2 _ _ _
    (ScalarExpression.add _ _ (ScalarExpression.native 3) (ScalarExpression.native 4))
    (ScalarExpression.add _ _ (ScalarExpression.native 3) (ScalarExpression.native 4))

example : ExprComplete repeatedHashInput :=
  lowerExpr_complete repeatedHashInput repeatedHashInputAdmission

#print axioms ScalarWitnessConstruction.complete_poseidon2

end ScalarExpressionHashTests
