import Noctium.Frontend
import Noctium.Verification.GenericStateAdmissionBridge
import Noctium.Verification.GenericStateAdmissionPrefix
import Noctium.Verification.GenericStateOps

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
  entry update uses guardedScalarCellInputs where
    when enabled write current := 21
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

private def operationFieldsAdmitted (operation : Backend.Impact.Op) : _root_.Bool :=
  match operation with
  | .index slot _ | .mapIndex slot _ => decide (slot < Field.modulus)
  | .insert levels => decide (0x90 + levels < Field.modulus)
  | _ => _root_.Bool.true

private theorem operationFieldsAdmitted_all :
    plan.operations.all operationFieldsAdmitted = _root_.Bool.true := by
  native_decide

private theorem field_admitted :
    ∀ operation ∈ plan.operations, GenericStateOps.FieldAdmitted operation := by
  intro operation membership
  have checked := (List.all_eq_true.mp operationFieldsAdmitted_all) operation membership
  cases operation with
  | index slot _ =>
      change decide (slot < Field.modulus) = _root_.Bool.true at checked
      change slot < Field.modulus
      exact of_decide_eq_true checked
  | mapIndex slot _ =>
      change decide (slot < Field.modulus) = _root_.Bool.true at checked
      change slot < Field.modulus
      exact of_decide_eq_true checked
  | «insert» levels =>
      change decide (0x90 + levels < Field.modulus) = _root_.Bool.true at checked
      change 0x90 + levels < Field.modulus
      exact of_decide_eq_true checked
  | _ => simp [GenericStateOps.FieldAdmitted]

/-- The exact accepted guarded Cell plan decomposes into the accepted public
input prefix and guarded append. Its separate evalPlan success preserves the
ordered native field groups and establishes scalar operation support. -/
theorem lower_guarded_cell_plan_groups :
    ∃ boundaries inputPlan,
      Backend.Impact.lowerWithEffectBoundaries sourceState updateEntry =
        .ok (plan, boundaries) ∧
      Backend.Impact.publicInputPlan updateEntry.circuit.inputs {} = .ok inputPlan ∧
      Backend.Impact.appendEffectsGuardedWithBoundaries sourceState updateEntry.effects
        updateEntry.effectGuards inputPlan = .ok (plan, boundaries) ∧
      (∀ operation ∈ plan.operations, GenericStateOps.FieldAdmitted operation) ∧
      plan.operations.mapM (fun operation =>
        GenericStateOps.evalFields context environment operation.fields) =
          .ok (NativeState.groups operations) ∧
      (∀ operation ∈ plan.operations, GenericStateOps.ScalarOperation operation) := by
  obtain ⟨production, fields, scalarSupport⟩ :=
    GenericStateAdmissionBridge.lower_plan_groups_supported_given_admission
    sourceState updateEntry plan context environment operations lowered (by rfl)
    field_admitted exact_evalPlan_success
  obtain ⟨boundaries, inputPlan, loweredExact, inputAccepted, guardedAppend⟩ := production
  exact ⟨boundaries, inputPlan, loweredExact, inputAccepted, guardedAppend,
    field_admitted, fields, scalarSupport⟩

end GuardedScalarCellAdmissionProof
