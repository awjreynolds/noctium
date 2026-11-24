import Noctium.Verification.GenericStateAdmissionPrefix
import Noctium.Verification.GenericStateOps

namespace Noctium.Verification.GenericStateAdmissionBridge
open Backend

/-- An accepted production plan retains its fallible public-input plan and
guarded effect append, including the exact boundary list. -/
theorem lower_source (state : List StateDecl) (entry : Entrypoint)
    (plan : Impact.Plan)
    (lowered : Impact.lower state entry = .ok plan) :
    ∃ boundaries inputPlan,
      Impact.lowerWithEffectBoundaries state entry = .ok (plan, boundaries) ∧
      Impact.publicInputPlan entry.circuit.inputs {} = .ok inputPlan ∧
      Impact.appendEffectsGuardedWithBoundaries state entry.effects entry.effectGuards inputPlan =
        .ok (plan, boundaries) := by
  exact GenericStateAdmissionPrefix.lower_input_prefix state entry plan lowered

/-- A completed scalar interpretation admits only operations in the explicit
scalar VM fragment. This premise refers to the same plan as the interpretation. -/
theorem evaluated_operations_supported (ctx : EvalContext) (values : EvalEnv)
    (plan : Impact.Plan) (ops : List NativeState.Op)
    (evaluated : GenericStateOps.evalPlan ctx values plan = .ok ops) :
    ∀ operation ∈ plan.operations, GenericStateOps.ScalarOperation operation :=
  GenericStateOps.evalPlan_supported ctx values plan ops evaluated

private theorem public_input_operation_admitted (input : Input)
    (compatible : Impact.publicInputScalarCompatible input)
    (operation : Impact.Op)
    (member : operation ∈ Impact.publicInputScalarOperations input) :
    GenericStateOps.FieldAdmitted operation := by
  cases input with
  | mk name ty visibility span =>
    cases visibility with
    | «private» => simp [Impact.publicInputScalarOperations] at member
    | «public» =>
      cases ty with
      | native | bool | uint _ =>
        simp [Impact.publicInputScalarOperations] at member
        rcases member with member | member <;> subst operation <;>
          simp [GenericStateOps.FieldAdmitted]
      | bytes _ | opaqueBytes | opaqueString | jubjubScalar | jubjubPoint | foreign _ =>
        simp [Impact.publicInputScalarOperations] at member

/-- When production lowering contains only the checked scalar public-input
prefix, its accepted operations satisfy the field-literal admission needed by
the scalar group interpreter. This covers the Native, Bool, and UInt fixture. -/
theorem lower_public_input_only_admitted (state : List StateDecl)
    (entry : Entrypoint) (plan : Impact.Plan)
    (lowered : Impact.lower state entry = .ok plan)
    (noEffects : entry.effects = [])
    (compatible : ∀ input ∈ entry.circuit.inputs,
      Impact.publicInputScalarCompatible input) :
    ∀ operation ∈ plan.operations, GenericStateOps.FieldAdmitted operation := by
  obtain ⟨_, inputPlan, _, inputAccepted, effectsAccepted⟩ :=
    lower_source state entry plan lowered
  have guardsEmpty : entry.effectGuards = [] := by
    cases guards : entry.effectGuards with
    | nil => rfl
    | cons head tail =>
      have impossible : False := by
        rw [noEffects, guards, Impact.appendEffectsGuardedWithBoundaries] at effectsAccepted
        cases effectsAccepted
      exact impossible.elim
  have appended := effectsAccepted
  rw [noEffects, guardsEmpty, Impact.appendEffectsGuardedWithBoundaries] at appended
  have operationsEq : plan.operations = inputPlan.operations := by
    have pairEq := Except.ok.inj appended
    have planEq : inputPlan = plan := congrArg Prod.fst pairEq
    exact congrArg (fun candidate : Impact.Plan => candidate.operations) planEq.symm
  have scalarShape := Impact.publicInputPlan_scalar_operations
    entry.circuit.inputs {} inputPlan inputAccepted compatible
  rw [operationsEq, scalarShape]
  intro operation member
  obtain ⟨input, inputMember, operationMember⟩ := List.mem_flatMap.mp member
  exact public_input_operation_admitted input (compatible input inputMember)
    operation operationMember

/-- For an accepted production plan with only scalar public inputs, a successful
interpretation preserves each operation's exact native field group and proves
both scalar-fragment support and field admission for that same ordered plan. -/
theorem lower_plan_groups_supported (state : List StateDecl) (entry : Entrypoint)
    (plan : Impact.Plan) (ctx : EvalContext) (values : EvalEnv)
    (ops : List NativeState.Op)
    (lowered : Impact.lower state entry = .ok plan)
    (noEffects : entry.effects = [])
    (compatible : ∀ input ∈ entry.circuit.inputs,
      Impact.publicInputScalarCompatible input)
    (modulus : ctx.modulus = Field.modulus)
    (evaluated : GenericStateOps.evalPlan ctx values plan = .ok ops) :
    (∃ boundaries inputPlan,
      Impact.lowerWithEffectBoundaries state entry = .ok (plan, boundaries) ∧
      Impact.publicInputPlan entry.circuit.inputs {} = .ok inputPlan ∧
      Impact.appendEffectsGuardedWithBoundaries state entry.effects entry.effectGuards inputPlan =
        .ok (plan, boundaries)) ∧
    plan.operations.mapM (fun operation =>
      GenericStateOps.evalFields ctx values operation.fields) =
        .ok (NativeState.groups ops) ∧
      (∀ operation ∈ plan.operations, GenericStateOps.ScalarOperation operation) := by
  have source := lower_source state entry plan lowered
  have admitted := lower_public_input_only_admitted state entry plan lowered
    noEffects compatible
  refine ⟨source, ?_, evaluated_operations_supported ctx values plan ops evaluated⟩
  exact GenericStateOps.evalOperations_fields ctx values plan.operations ops
    modulus admitted (by simpa only [GenericStateOps.evalPlan] using evaluated)

end Noctium.Verification.GenericStateAdmissionBridge
