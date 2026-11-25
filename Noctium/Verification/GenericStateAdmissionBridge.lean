import Noctium.Verification.GenericStateAdmissionPrefix
import Noctium.Verification.GenericStateAliases
import Noctium.Verification.GenericStateOps

namespace Noctium.Verification.GenericStateAdmissionBridge
open Backend

private theorem bind_ok {α β : Type} {first : Except ε α}
    {next : α → Except ε β} {result : β} :
    (first >>= next) = .ok result ↔
      ∃ value, first = .ok value ∧ next value = .ok result := by
  cases first <;> simp [Bind.bind, Except.bind]

private theorem lower_plan_validated (state : List StateDecl) (entry : Entrypoint)
    (plan : Impact.Plan) (lowered : Impact.lower state entry = .ok plan) :
    plan.validate entry = .ok () := by
  obtain ⟨_, _, accepted, _, _⟩ :=
    GenericStateAdmissionPrefix.lower_input_prefix state entry plan lowered
  unfold Impact.lowerWithEffectBoundaries at accepted
  simp only [bind_ok] at accepted
  rcases accepted with ⟨_, _, _, _, ⟨⟨raw, _⟩, _, finished, finishAccepted, returned⟩⟩
  unfold Impact.finishPlan at finishAccepted
  cases checked : raw.validate entry with
  | error message => simp [checked, MonadExcept.throw] at finishAccepted
  | ok valid =>
    cases valid
    simp only [checked, Pure.pure, Except.pure, Except.ok.injEq] at finishAccepted
    subst finished
    simp only [Pure.pure, Except.pure, Except.ok.injEq, Prod.mk.injEq] at returned
    exact returned.1 ▸ checked

private theorem plan_native_literals_checked (plan : Impact.Plan) (entry : Entrypoint)
    (accepted : plan.validate entry = .ok ()) (n : Nat) (member : Expr.native n ∈ plan.fields) :
    n < Field.modulus := by
  unfold Impact.Plan.validate at accepted
  simp only [bind_ok] at accepted
  rcases accepted with ⟨_, _, value, fields, _⟩
  cases value
  let property := fun (field : Impact.Scalar) =>
    ∀ value, field = .native value → value < Field.modulus
  have actions := GenericStateAliases.forIn_extract _ property plan.fields (by
    intro field step checked
    simp only [bind_ok] at checked
    rcases checked with ⟨result, evaluated, equality⟩
    cases result
    refine ⟨(Except.ok.inj equality).symm, ?_⟩
    intro value same
    subst field
    simp only [Expr.validate] at evaluated
    change (if value < Field.modulus then Except.ok () else
      Except.error "noncanonical native constant") = (Except.ok () : Except String Unit) at evaluated
    by_cases fits : value < Field.modulus
    · exact fits
    · simp [fits] at evaluated) fields
  exact actions (.native n) member n rfl

/-- Accepted Impact lowering checks the native literals before the scalar VM
evaluates the plan. Index slots and insert encodings are field-admissible. -/
theorem lower_field_admission (state : List StateDecl) (entry : Entrypoint)
    (plan : Impact.Plan) (lowered : Impact.lower state entry = .ok plan) :
    ∀ operation ∈ plan.operations, GenericStateOps.FieldAdmitted operation := by
  have checked := lower_plan_validated state entry plan lowered
  intro operation present
  have bound (n : Nat) (member : Expr.native n ∈ operation.fields) : n < Field.modulus :=
    plan_native_literals_checked plan entry checked n
      (List.mem_flatMap.mpr ⟨operation, present, member⟩)
  cases operation <;> simp only [GenericStateOps.FieldAdmitted]
  · exact bound _ (by simp [Impact.Op.fields, Impact.Aligned.fields])
  · exact bound _ (by simp [Impact.Op.fields, Impact.Aligned.fields])
  · exact bound _ (by simp [Impact.Op.fields])
  all_goals trivial

/-- The accepted Impact plan orders the exact serialized scalar fields and
native operations. Under scalar operation admission, both evaluations return
the same groups on success or the same first evaluation error. -/
theorem lower_evaluated_plan_groups_exact (state : List StateDecl) (entry : Entrypoint)
    (plan : Impact.Plan) (ctx : EvalContext) (values : EvalEnv)
    (lowered : Impact.lower state entry = .ok plan)
    (modulus : ctx.modulus = Field.modulus)
    (supported : ∀ operation ∈ plan.operations, GenericStateOps.ScalarOperation operation) :
    plan.operations.mapM (fun operation =>
      GenericStateOps.evalFields ctx values operation.fields) =
        (GenericStateOps.evalPlan ctx values plan).map NativeState.groups := by
  exact GenericStateOps.evalOperations_fields_exact ctx values plan.operations supported modulus
    (lower_field_admission state entry plan lowered)

/-- The actual lowered plan and its successful scalar VM evaluation fix the
ordered native field groups and the supported operation fragment together. -/
theorem lower_evaluated_plan_groups (state : List StateDecl) (entry : Entrypoint)
    (plan : Impact.Plan) (ctx : EvalContext) (values : EvalEnv)
    (ops : List NativeState.Op)
    (lowered : Impact.lower state entry = .ok plan)
    (modulus : ctx.modulus = Field.modulus)
    (evaluated : GenericStateOps.evalPlan ctx values plan = .ok ops) :
    plan.operations.mapM (fun operation =>
      GenericStateOps.evalFields ctx values operation.fields) =
        .ok (NativeState.groups ops) ∧
      (∀ operation ∈ plan.operations, GenericStateOps.ScalarOperation operation) := by
  exact ⟨GenericStateOps.evalOperations_fields ctx values plan.operations ops
    modulus (lower_field_admission state entry plan lowered)
    (by simpa only [GenericStateOps.evalPlan] using evaluated),
    GenericStateOps.evalPlan_supported ctx values plan ops evaluated⟩

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
    GenericStateAdmissionPrefix.lower_input_prefix state entry plan lowered
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

/-- Exact production lowering and scalar execution preserve native groups for
any admitted plan, including guarded source effects. -/
theorem lower_plan_groups_supported_given_admission (state : List StateDecl)
    (entry : Entrypoint) (plan : Impact.Plan) (ctx : EvalContext)
    (values : EvalEnv) (ops : List NativeState.Op)
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
  have source := GenericStateAdmissionPrefix.lower_input_prefix state entry plan lowered
  refine ⟨source, ?_, GenericStateOps.evalPlan_supported ctx values plan ops evaluated⟩
  exact GenericStateOps.evalOperations_fields ctx values plan.operations ops
    modulus admitted (by simpa only [GenericStateOps.evalPlan] using evaluated)

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
  exact lower_plan_groups_supported_given_admission state entry plan ctx values ops
    lowered modulus (lower_public_input_only_admitted state entry plan lowered
      noEffects compatible) evaluated

end Noctium.Verification.GenericStateAdmissionBridge
