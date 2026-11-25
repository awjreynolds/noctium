import Noctium.Backend.Impact

namespace Noctium.Verification.ScalarWitnessConstruction

open Noctium Backend

private theorem validateConstraints_members {caps : Capabilities} {types : TypeEnv}
    {span : SourceSpan} {conditions : List (Expr .bool)}
    (valid : validateConstraints caps types span conditions = .ok ()) :
    ∀ condition ∈ conditions, condition.validate caps types = .ok () := by
  induction conditions with
  | nil => simp
  | cons condition rest ih =>
    cases checked : condition.validate caps types with
    | error message => simp [validateConstraints, checked] at valid
    | ok result =>
      cases result
      simp only [validateConstraints, checked] at valid
      intro found member
      rcases List.mem_cons.mp member with same | member
      · cases same
        exact checked
      · exact ih valid found member

private theorem Op.fieldGroups_flatten_eq_fields (operation : Impact.Op) :
    operation.fieldGroups.flatten = operation.fields := by
  cases operation <;>
    simp [Impact.Op.fieldGroups, Impact.Op.fields] <;>
    try rfl
  case listReset slot keys =>
    cases keys with
    | nil => rfl
    | cons key rest =>
      cases last : (key :: rest).getLast? with
      | none => simp [last]
      | some finalKey => simp [last]
  case mapRemove slot keys =>
    cases keys with
    | nil => rfl
    | cons key rest =>
      cases last : (key :: rest).getLast? with
      | none => simp
      | some finalKey => simp

/-- Every source guard in a plan returned by production lowering passed the
same crypto-capability validation used by Impact plan validation. -/
theorem lower_plan_guard_members_validated (state : List StateDecl) (entry : Entrypoint)
    (plan : Impact.Plan) (lowered : Impact.lower state entry = .ok plan) :
    ∀ guard ∈ plan.guards,
      guard.validate Capabilities.crypto (plan.typeEnvironment entry) = .ok () := by
  apply validateConstraints_members
  exact Impact.lower_guards_validate state entry plan lowered

/-- Each scalar in a real operation field group passed production plan
validation. Field groups flatten to the exact `Op.fields` list validated by
`Plan.validate_fields_success`. -/
theorem lower_operation_group_members_validated (state : List StateDecl)
    (entry : Entrypoint) (plan : Impact.Plan)
    (lowered : Impact.lower state entry = .ok plan) :
    ∀ operation ∈ plan.operations, ∀ group ∈ operation.fieldGroups,
      ∀ field ∈ group,
        field.validate Capabilities.crypto (plan.typeEnvironment entry) = .ok () := by
  have fieldsValidated := Impact.Plan.validate_fields_success plan entry
    (Impact.lower_validated state entry plan lowered)
  intro operation operationMember group groupMember field fieldMember
  have fieldInGroupFlattened : field ∈ operation.fieldGroups.flatten := by
    exact List.mem_flatten.mpr ⟨group, groupMember, fieldMember⟩
  have fieldInOperation : field ∈ operation.fields := by
    rw [← Op.fieldGroups_flatten_eq_fields operation]
    exact fieldInGroupFlattened
  have fieldInPlan : field ∈ plan.fields := by
    simp only [Impact.Plan.fields, List.mem_flatMap]
    exact ⟨operation, operationMember, fieldInOperation⟩
  exact fieldsValidated field fieldInPlan

end Noctium.Verification.ScalarWitnessConstruction
