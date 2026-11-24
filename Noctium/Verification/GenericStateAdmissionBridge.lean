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

/-- Production validation bounds the operation literals. A successful
interpretation then preserves each operation's exact native field group and
proves scalar-fragment support for the same ordered plan. -/
theorem lower_plan_groups_supported (state : List StateDecl) (entry : Entrypoint)
    (plan : Impact.Plan) (ctx : EvalContext) (values : EvalEnv)
    (ops : List NativeState.Op)
    (lowered : Impact.lower state entry = .ok plan)
    (modulus : ctx.modulus = Field.modulus)
    (admitted : ∀ operation ∈ plan.operations,
      GenericStateOps.FieldAdmitted operation)
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
  refine ⟨source, ?_, evaluated_operations_supported ctx values plan ops evaluated⟩
  exact GenericStateOps.evalOperations_fields ctx values plan.operations ops
    modulus admitted (by simpa only [GenericStateOps.evalPlan] using evaluated)

end Noctium.Verification.GenericStateAdmissionBridge
