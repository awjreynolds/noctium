import Noctium.Verification.ScalarNormalization

namespace Noctium.Verification.ScalarExpressionAdmission

open Noctium Noctium.Verification.ScalarNormalization

/-- Return a scalar type witness only for the three types with scalar meanings. -/
def type? : (ty : Ty) → Option (ScalarType ty)
  | .native => some .native
  | .bool => some .bool
  | .uint maximum => some (.uint maximum)
  | .bytes _ | .opaqueBytes | .opaqueString | .jubjubScalar | .jubjubPoint | .foreign _ => none

/-- Decide membership in the scalar-normalization fragment, returning the
constructor proof for every admitted expression. -/
def certify {ty : Ty} (expression : Expr ty) :
    Option (PLift (ScalarExpression expression)) :=
  match expression with
  | .native value => some ⟨ScalarExpression.native value⟩
  | .bool value => some ⟨ScalarExpression.bool value⟩
  | .uint maximum value => some ⟨ScalarExpression.uint maximum value⟩
  | .ref name => do
      let scalarType ← type? ty
      pure ⟨ScalarExpression.ref name scalarType⟩
  | .add left right => do
      let leftSupported ← certify left
      let rightSupported ← certify right
      pure ⟨ScalarExpression.add left right leftSupported.down rightSupported.down⟩
  | .mul left right => do
      let leftSupported ← certify left
      let rightSupported ← certify right
      pure ⟨ScalarExpression.mul left right leftSupported.down rightSupported.down⟩
  | .sub left right => do
      let leftSupported ← certify left
      let rightSupported ← certify right
      pure ⟨ScalarExpression.sub left right leftSupported.down rightSupported.down⟩
  | .uadd left right => do
      let leftSupported ← certify left
      let rightSupported ← certify right
      pure ⟨ScalarExpression.uadd left right leftSupported.down rightSupported.down⟩
  | .usub left right => do
      let leftSupported ← certify left
      let rightSupported ← certify right
      pure ⟨ScalarExpression.usub left right leftSupported.down rightSupported.down⟩
  | .umul left right => do
      let leftSupported ← certify left
      let rightSupported ← certify right
      pure ⟨ScalarExpression.umul left right leftSupported.down rightSupported.down⟩
  | @Expr.cast source target value => do
      let sourceScalar ← type? source
      let targetScalar ← type? target
      let valueSupported ← certify value
      pure ⟨ScalarExpression.cast value sourceScalar targetScalar valueSupported.down⟩
  | @Expr.letE source target name value body => do
      let sourceScalar ← type? source
      let valueSupported ← certify value
      let bodySupported ← certify body
      pure ⟨ScalarExpression.letE name value body sourceScalar
        valueSupported.down bodySupported.down⟩
  | .assertE condition body => do
      let conditionSupported ← certify condition
      let bodySupported ← certify body
      pure ⟨ScalarExpression.assertE condition body
        conditionSupported.down bodySupported.down⟩
  | .copyValue value => do
      let valueSupported ← certify value
      pure ⟨ScalarExpression.copyValue value valueSupported.down⟩
  | .disclose span value => do
      let valueSupported ← certify value
      pure ⟨ScalarExpression.disclose span value valueSupported.down⟩
  | @Expr.eq ty left right => do
      let scalarType ← type? ty
      let leftSupported ← certify left
      let rightSupported ← certify right
      pure ⟨ScalarExpression.eq left right scalarType
        leftSupported.down rightSupported.down⟩
  | @Expr.select ty condition yes no => do
      let scalarType ← type? ty
      let conditionSupported ← certify condition
      let yesSupported ← certify yes
      let noSupported ← certify no
      pure ⟨ScalarExpression.select condition yes no scalarType
        conditionSupported.down yesSupported.down noSupported.down⟩
  | .poseidon2 domain left right => do
      let leftSupported ← certify left
      let rightSupported ← certify right
      pure ⟨ScalarExpression.poseidon2 domain left right
        leftSupported.down rightSupported.down⟩
  | _ => none
termination_by sizeOf expression
decreasing_by all_goals simp_wf; all_goals omega

private theorem type_some (witness : ScalarType ty) : type? ty = some witness := by
  cases witness <;> rfl

/-- Every structurally admitted expression passes the executable certifier. -/
theorem certify_complete {expression : Expr ty} (supported : ScalarExpression expression) :
    (certify expression).isSome = true := by
  apply Option.isSome_iff_exists.mpr
  induction supported with
  | native value => exact ⟨_, by simp [certify] <;> rfl⟩
  | bool value => exact ⟨_, by simp [certify] <;> rfl⟩
  | uint maximum value => exact ⟨_, by simp [certify] <;> rfl⟩
  | ref name witness => exact ⟨_, by simp [certify, type_some witness] <;> rfl⟩
  | add _ _ _ _ left right
  | mul _ _ _ _ left right
  | sub _ _ _ _ left right
  | uadd _ _ _ _ left right
  | usub _ _ _ _ left right
  | umul _ _ _ _ left right
  | assertE _ _ _ _ left right
  | poseidon2 _ _ _ _ _ left right =>
    obtain ⟨_, left⟩ := left
    obtain ⟨_, right⟩ := right
    exact ⟨_, by simp [certify, left, right] <;> rfl⟩
  | cast _ sourceType targetType _ child =>
    obtain ⟨_, child⟩ := child
    exact ⟨_, by simp [certify, type_some sourceType, type_some targetType, child] <;> rfl⟩
  | letE _ _ _ sourceType _ _ val body =>
    obtain ⟨_, val⟩ := val
    obtain ⟨_, body⟩ := body
    exact ⟨_, by simp [certify, type_some sourceType, val, body] <;> rfl⟩
  | copyValue _ _ child
  | disclose _ _ _ child =>
    obtain ⟨_, child⟩ := child
    exact ⟨_, by simp [certify, child] <;> rfl⟩
  | eq _ _ witness _ _ left right =>
    obtain ⟨_, left⟩ := left
    obtain ⟨_, right⟩ := right
    exact ⟨_, by simp [certify, type_some witness, left, right] <;> rfl⟩
  | select _ _ _ witness _ _ _ condition yes no =>
    obtain ⟨_, condition⟩ := condition
    obtain ⟨_, yes⟩ := yes
    obtain ⟨_, no⟩ := no
    exact ⟨_, by simp [certify, type_some witness, condition, yes, no] <;> rfl⟩
