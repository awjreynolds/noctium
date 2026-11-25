import Noctium.Frontend
import Noctium.Verification.GenericStateAdmissionBridge
import Noctium.Verification.GenericStateAdmissionPrefix
import Noctium.Verification.GenericStateCellAdmission
import Noctium.Verification.GenericStateOps
import Noctium.Verification.GuardedEffectEvaluation
import Noctium.Verification.GuardedPlanActivity

open scoped Noctium
open Noctium
open Noctium.Verification
open Noctium.Verification.NativeRelation
open Noctium.Verification.NativeState

noctium_circuit guardedScalarCellInputs where
  public enabled : Bool
end

noctium_contract GuardedScalarCellAdmission where
  cell current : Native
  cell quantity : UInt 8
  entry update uses guardedScalarCellInputs where
    when enabled write current := 21
  end
  entry updateQuantity uses guardedScalarCellInputs where
    when enabled write quantity := 21
  end
end

namespace GuardedScalarCellAdmissionProof

private def updateEntry : Entrypoint :=
  (GuardedScalarCellAdmission.entrypoints.find? (·.name == "update")).getD
    {name := "missing", circuit := {name := "missing"}}

private def sourceState : List StateDecl := GuardedScalarCellAdmission.state

private def plan : Backend.Impact.Plan :=
  match Backend.Impact.lower sourceState updateEntry with
  | .ok plan => plan
  | .error _ => {}

private def lowerSucceeded : _root_.Bool :=
  match Backend.Impact.lower sourceState updateEntry with
  | .ok _ => _root_.Bool.true
  | .error _ => _root_.Bool.false

private theorem lower_succeeded : lowerSucceeded = _root_.Bool.true := by
  native_decide

private theorem lowered : Backend.Impact.lower sourceState updateEntry = .ok plan := by
  cases result : Backend.Impact.lower sourceState updateEntry with
  | error message =>
      have succeeded := lower_succeeded
      simp [lowerSucceeded, result] at succeeded
  | ok loweredPlan => simp [plan, result]

private def quantityEntry : Entrypoint :=
  (GuardedScalarCellAdmission.entrypoints.find? (·.name == "updateQuantity")).getD
    {name := "missing", circuit := {name := "missing"}}

private def quantityPlan : Backend.Impact.Plan :=
  match Backend.Impact.lower sourceState quantityEntry with
  | .ok plan => plan
  | .error _ => {}

private def quantityLowerSucceeded : _root_.Bool :=
  match Backend.Impact.lower sourceState quantityEntry with
  | .ok _ => _root_.Bool.true
  | .error _ => _root_.Bool.false

private theorem quantity_lower_succeeded : quantityLowerSucceeded = _root_.Bool.true := by
  decide +kernel

private theorem quantity_lowered :
    Backend.Impact.lower sourceState quantityEntry = .ok quantityPlan := by
  cases result : Backend.Impact.lower sourceState quantityEntry with
  | error message =>
      have succeeded := quantity_lower_succeeded
      simp [quantityLowerSucceeded, result] at succeeded
  | ok loweredPlan => simp [quantityPlan, result]

private theorem quantity_effects :
    quantityEntry.effects = [.writeCell "quantity" (.uint 255) (.uint 255 21)] := by
  rfl

theorem bounded_uint_cell_lowering_accepted :
    ∀ operation ∈ quantityPlan.operations, GenericStateOps.ScalarOperation operation := by
  apply GenericStateCellAdmission.lower_scalar_cell_operations_supported
    sourceState quantityEntry quantityPlan quantity_lowered
  · intro parameter parameterIn
    change parameter ∈ [guardedScalarCellInputs.inputs[0]'(by decide)] at parameterIn
    rw [List.mem_singleton.mp parameterIn]
    exact Or.inr (Or.inr (Or.inl rfl))
  · intro sourceEffect effectIn
    rw [quantity_effects] at effectIn
    rw [List.mem_singleton.mp effectIn]
    exact .writeCell _ _ _ (.uint 255 (by decide)) (by
      simp [GenericStateCellAdmission.ScalarCellDeclaration,
        Backend.Impact.UnalignedCellDeclaration, sourceState,
        GuardedScalarCellAdmission])

theorem guard_witness :
    ∃ condition : Expr .bool,
      updateEntry.effects = [.writeCell "current" .native (.native 21)] ∧
      updateEntry.effectGuards = [some condition] := by
  exact ⟨.ref "enabled", rfl, rfl⟩

private def context : EvalContext := {
  modulus := Field.modulus
  poseidon2 := fun _ _ _ => .error "unused by guarded scalar Cell admission fixture"
}

private def environment : EvalEnv := [("enabled", .bool Bool.true)]

private def operations : List NativeState.Op :=
  match GenericStateOps.evalPlan context environment plan with
  | .ok operations => operations
  | .error _ => []

private def evaluationSucceeded : _root_.Bool :=
  match GenericStateOps.evalPlan context environment plan with
  | .ok _ => _root_.Bool.true
  | .error _ => _root_.Bool.false

private theorem evaluation_succeeded : evaluationSucceeded = _root_.Bool.true := by
  native_decide

theorem exact_evalPlan_success :
    GenericStateOps.evalPlan context environment plan = .ok operations := by
  cases result : GenericStateOps.evalPlan context environment plan with
  | error message =>
      have succeeded := evaluation_succeeded
      simp [evaluationSucceeded, result] at succeeded
  | ok evaluated => simp [operations, result]

/-- The accepted guarded Cell plan preserves the ordered native field groups.
Scalar operation support follows separately from its typed inputs and effect. -/
theorem lower_guarded_cell_plan_groups :
    ∃ boundaries inputPlan,
      Backend.Impact.lowerWithEffectBoundaries sourceState updateEntry =
        .ok (plan, boundaries) ∧
      Backend.Impact.publicInputPlan updateEntry.circuit.inputs {} = .ok inputPlan ∧
      Backend.Impact.appendEffectsGuardedWithBoundaries sourceState updateEntry.effects
        updateEntry.effectGuards inputPlan = .ok (plan, boundaries) ∧
      Backend.Impact.GuardedEffectTrace sourceState updateEntry.effectGuards
        updateEntry.effects.zipIdx inputPlan plan boundaries ∧
      (∀ operation ∈ plan.operations, GenericStateOps.FieldAdmitted operation) ∧
      plan.operations.mapM (fun operation =>
        GenericStateOps.evalFields context environment operation.fields) =
          .ok (NativeState.groups operations) ∧
      (∀ operation ∈ plan.operations, GenericStateOps.ScalarOperation operation) := by
  obtain ⟨fields, _⟩ :=
    GenericStateAdmissionBridge.lower_evaluated_plan_groups sourceState updateEntry plan
      context environment operations lowered rfl exact_evalPlan_success
  have scalarSupport : ∀ operation ∈ plan.operations, GenericStateOps.ScalarOperation operation := by
    apply GenericStateCellAdmission.lower_scalar_cell_operations_supported
      sourceState updateEntry plan lowered
    · intro parameter parameterIn
      change parameter ∈ [guardedScalarCellInputs.inputs[0]'(by decide)] at parameterIn
      rw [List.mem_singleton.mp parameterIn]
      exact Or.inr (Or.inr (Or.inl rfl))
    · intro sourceEffect effectIn
      obtain ⟨_, exactEffects, _⟩ := guard_witness
      rw [exactEffects] at effectIn
      rw [List.mem_singleton.mp effectIn]
      exact .writeCell _ _ _ .native (by
        simp [GenericStateCellAdmission.ScalarCellDeclaration,
          Backend.Impact.UnalignedCellDeclaration, sourceState,
          GuardedScalarCellAdmission])
  obtain ⟨boundaries, inputPlan, loweredExact, inputAccepted, guardedAppend⟩ :=
    GenericStateAdmissionPrefix.lower_input_prefix sourceState updateEntry plan lowered
  have trace := Backend.Impact.appendEffectsGuardedWithBoundaries_trace sourceState
    updateEntry.effects updateEntry.effectGuards inputPlan plan boundaries guardedAppend
  exact ⟨boundaries, inputPlan, loweredExact, inputAccepted, guardedAppend, trace,
    GenericStateAdmissionBridge.lower_field_admission sourceState updateEntry plan lowered,
    fields, scalarSupport⟩

/-- The production guarded Cell write supplies the exact evaluation chunks and
source guard schedule, including the unconditional public-input prefix. -/
theorem lower_guarded_cell_evaluation_groups :
    ∃ boundaries inputPlan chunks publicNative groups,
      Backend.Impact.lowerWithEffectBoundaries sourceState updateEntry =
        .ok (plan, boundaries) ∧
      Backend.Impact.publicInputPlan updateEntry.circuit.inputs {} = .ok inputPlan ∧
      GuardedEffectEvaluation.GuardedEffectOperationChunks sourceState
        updateEntry.effectGuards updateEntry.effects.zipIdx inputPlan plan
        boundaries chunks ∧
      GenericStateCircuitParts.activityGuardSources plan =
        List.replicate inputPlan.fieldGroups.length none ++
          GuardedPlanActivity.effectFieldGuards updateEntry.effectGuards
            updateEntry.effects.zipIdx chunks ∧
      inputPlan.operations.mapM (GenericStateOps.evalOp context environment) =
        .ok publicNative ∧
      chunks.mapM (fun chunk => chunk.mapM
        (GenericStateOps.evalOp context environment)) = .ok groups ∧
      operations = publicNative ++ groups.flatten := by
  obtain ⟨condition, effectsExact, guardsExact⟩ := guard_witness
  have scope : GenericStateCheckedReadTrace.GuardedScalarReadEffects
      updateEntry.effectGuards updateEntry.effects.zipIdx := by
    intro item membership
    have itemShape : item = (.writeCell "current" .native (.native 21), 0) := by
      simpa [effectsExact] using membership
    subst item
    simpa [guardsExact] using
      GenericStateCheckedReadTrace.GuardedScalarReadEffect.writeCell
        condition "current" .native (.native 21)
  exact GuardedPlanActivity.lower_scoped_guarded_evaluation sourceState updateEntry plan
    context environment operations lowered scope exact_evalPlan_success

end GuardedScalarCellAdmissionProof
