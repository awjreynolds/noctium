import Noctium.Verification.ScalarExpressionAssert
import Noctium.Verification.ScalarExpressionBoolCast
import Noctium.Verification.ScalarExpressionCopy
import Noctium.Verification.ScalarExpressionEquality
import Noctium.Verification.ScalarExpressionLet
import Noctium.Verification.ScalarExpressionNativeTree
import Noctium.Verification.ScalarExpressionPoseidon
import Noctium.Verification.ScalarExpressionSelect
import Noctium.Verification.ScalarExpressionUIntAdd
import Noctium.Verification.ScalarExpressionUIntCast
import Noctium.Verification.ScalarExpressionUIntMul
import Noctium.Verification.ScalarExpressionUIntSub
import Noctium.Verification.ScalarWitnessReturnProjection

namespace Noctium.Verification.ScalarExpressionLowering

open ScalarNormalization ScalarLowering ScalarWitnessConstruction

/-- Scalar admission supplies every expression witness constructor needed by
the current lowerer. Validation, successful evaluation, and output capacity
remain explicit in `ExprComplete`. -/
theorem lowerExpr_complete (expression : Expr ty) (admitted : ScalarExpression expression) :
    ExprComplete expression := by
  induction admitted with
  | native number => exact complete_native number
  | bool value => exact complete_bool value
  | uint maximum number => exact complete_uint maximum number
  | ref name scalarType => exact complete_ref _ scalarType name
  | add left right leftSupported rightSupported leftComplete rightComplete =>
    exact complete_add left right leftSupported rightSupported leftComplete rightComplete
  | mul left right leftSupported rightSupported leftComplete rightComplete =>
    exact complete_mul left right leftSupported rightSupported leftComplete rightComplete
  | sub left right leftSupported rightSupported leftComplete rightComplete =>
    exact complete_sub left right leftSupported rightSupported leftComplete rightComplete
  | uadd left right leftSupported rightSupported leftComplete rightComplete =>
    exact complete_uadd left right leftSupported rightSupported leftComplete rightComplete
  | usub left right leftSupported rightSupported leftComplete rightComplete =>
    exact complete_usub left right leftSupported rightSupported leftComplete rightComplete
  | umul left right leftSupported rightSupported leftComplete rightComplete =>
    exact complete_umul left right leftSupported rightSupported leftComplete rightComplete
  | cast value sourceType targetType valueSupported valueComplete =>
    cases targetType with
    | native => exact complete_native_cast value sourceType valueSupported valueComplete
    | bool => exact complete_cast_bool value sourceType valueSupported valueComplete
    | uint maximum =>
      exact exprComplete_uintCast maximum value sourceType valueSupported valueComplete
  | letE name value body sourceType valueSupported bodySupported valueComplete bodyComplete =>
    exact ScalarExpressionLet.exprComplete_letE name value body sourceType valueSupported
      bodySupported valueComplete bodyComplete
  | assertE condition body conditionSupported bodySupported conditionComplete bodyComplete =>
    exact exprComplete_assertE condition body conditionSupported bodySupported
      conditionComplete bodyComplete
  | copyValue value valueSupported valueComplete =>
    exact complete_copyValue value valueSupported valueComplete
  | disclose span value _ valueComplete =>
    exact complete_disclose span value valueComplete
  | eq left right scalarType leftSupported rightSupported leftComplete rightComplete =>
    exact complete_scalar_eq left right scalarType leftSupported rightSupported leftComplete rightComplete
  | select condition yes no scalarType conditionSupported yesSupported noSupported
      conditionComplete yesComplete noComplete =>
    exact exprComplete_select condition yes no scalarType
      conditionSupported yesSupported noSupported conditionComplete yesComplete noComplete
  | poseidon2 domain left right leftSupported rightSupported leftComplete rightComplete =>
    exact complete_poseidon2 domain left right leftSupported rightSupported leftComplete rightComplete

end Noctium.Verification.ScalarExpressionLowering
