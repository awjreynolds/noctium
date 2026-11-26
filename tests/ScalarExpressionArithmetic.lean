import Noctium.Verification.ScalarExpressionLowering

namespace ScalarExpressionArithmeticTests

open Noctium Noctium.Backend Noctium.Verification
open ScalarLowering ScalarNormalization ScalarExpressionLowering

private def repeated : Expr .native :=
  .add (.mul (.native 3) (.native 4)) (.mul (.native 3) (.native 4))

private theorem repeatedAdmission : ScalarExpression repeated := by
  unfold repeated
  exact ScalarExpression.add _ _
    (ScalarExpression.mul _ _ (ScalarExpression.native 3) (ScalarExpression.native 4))
    (ScalarExpression.mul _ _ (ScalarExpression.native 3) (ScalarExpression.native 4))

example : ExprComplete repeated := lowerExpr_complete repeated repeatedAdmission

private def narrowed : Expr (.uint 15) :=
  .cast (.uint 15) (.usub (.uint 31 21) (.uint 7 6))

private theorem narrowedAdmission : ScalarExpression narrowed := by
  unfold narrowed
  exact ScalarExpression.cast _ (.uint 31) (.uint 15)
    (ScalarExpression.usub _ _ (ScalarExpression.uint 31 21) (ScalarExpression.uint 7 6))

example : ExprComplete narrowed := lowerExpr_complete narrowed narrowedAdmission

private def boolCast : Expr .bool := .cast .bool repeated

example : ExprComplete boolCast := by
  apply lowerExpr_complete boolCast
  exact ScalarExpression.cast _ .native .bool repeatedAdmission

private def uintArithmetic : Expr (.uint (7 + 3 * 4)) :=
  .uadd (.uint 7 2) (.umul (.uint 3 2) (.uint 4 3))

example : ExprComplete uintArithmetic := by
  apply lowerExpr_complete uintArithmetic
  exact ScalarExpression.uadd _ _ (ScalarExpression.uint 7 2)
    (ScalarExpression.umul _ _ (ScalarExpression.uint 3 2) (ScalarExpression.uint 4 3))

example (name : String) : ExprComplete (.ref (ty := .native) name) :=
  lowerExpr_complete _ (ScalarExpression.ref name .native)

example (name : String) : ExprComplete (.ref (ty := .bool) name) :=
  lowerExpr_complete _ (ScalarExpression.ref name .bool)

example (maximum : Nat) (name : String) :
    ExprComplete (.ref (ty := .uint maximum) name) :=
  lowerExpr_complete _ (ScalarExpression.ref name (.uint maximum))

private def context : EvalContext := {
  modulus := Field.modulus
  poseidon2 := fun _ _ _ => .error "unused"
}

example : repeated.eval context [] = .ok 24 := by cbv
example : narrowed.eval context [] = .ok 15 := by cbv
example : (Expr.usub (.uint 7 2) (.uint 7 3)).eval context [] =
    .error "unsigned subtraction underflow" := by cbv
example : (Expr.cast (.uint 14) narrowed).eval context [] =
    .error "scalar conversion exceeds unsigned bound" := by cbv

private def repeatedCircuit : Circuit := {
  name := "arithmetic_cache"
  inputs := []
  constraints := []
  outputs := [{name := "result", ty := .native, value := repeated}]
}

#guard match Zkir.lowerCircuit repeatedCircuit with
  | .error _ => false
  | .ok json => match NativeRelationJson.decode json with
    | .error _ => false
    | .ok program =>
      (program.instructions.filter fun instruction => match instruction with
        | .mul .. => true
        | _ => false).length == 1

#print axioms Noctium.Verification.ScalarExpressionLowering.lowerExpr_complete
#print axioms ScalarWitnessConstruction.complete_add
#print axioms ScalarWitnessConstruction.complete_mul
#print axioms ScalarWitnessConstruction.complete_sub

end ScalarExpressionArithmeticTests
