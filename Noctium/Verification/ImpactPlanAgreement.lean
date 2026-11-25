import Noctium.Verification.ArtifactBytes
import Noctium.Verification.ImpactScheduleTraversal
import Noctium.Verification.ImpactScheduledAgreement

namespace Noctium.Verification.ImpactPlanAgreement

open Lean Backend ImpactWireDecoder ImpactWireSoundness
open ImpactExpressionSchedule ImpactOperationAgreement ImpactReferenceEvaluation
open ImpactScheduledAgreement ScalarNormalization

/-- Evaluate the decoded scalar Impact schedule in artifact order. -/
def evaluatePlan (fuel : Nat) (ctx : EvalContext) (env : EvalEnv) (raw : Json) :
    Option (List NativeState.Op) :=
  (decodePlanOperations raw).toOption.bind fun schedule =>
    (schedule.mapM (evaluateScheduledOperation fuel ctx env)).map List.flatten

/-- Execute the independently parsed operation schedule on the scalar state model. -/
def runPlanBytes (fuel : Nat) (ctx : EvalContext) (env : EvalEnv)
    (bytes : ArtifactBytes.Bytes) (initial : NativeState.Machine) : Option NativeState.Machine := do
  let raw ← (ArtifactBytes.parse bytes).toOption
  let operations ← evaluatePlan fuel ctx env raw
  NativeState.run operations initial

/-- The recovered schedule evaluates to the same ordered active operations as
the typed plan. Both sides preserve rejection. The schedule alignment premise
is the guard-count check imposed by source plan evaluation. -/
theorem evaluate_nativePlanJson_agrees
    (profile : TargetProfile) (contractName : Name) (state : List StateDecl)
    (ctor : Option Constructor) (ep : Entrypoint) (plan : Impact.Plan)
    (standaloneFile : _root_.Bool) (projected : Nat → Operation)
    (ctx : EvalContext) (modulus : ctx.modulus = Field.modulus)
    {types : TypeEnv} {env : EvalEnv} (typed : TypedScalarEnv types env)
    (aligned : (GuardedPlanActivity.operationGuards plan).length = plan.operations.length)
    (projects : ∀ op index, (op, index) ∈ plan.operations.zipIdx →
      Projects op (projected index))
    (operandsAdmitted : ∀ op index, (op, index) ∈ plan.operations.zipIdx →
      ScalarOperandAdmission op)
    (operandsValid : ∀ op index, (op, index) ∈ plan.operations.zipIdx →
      SourceOperandsValid types op)
    (guardsAdmitted : ∀ op index, (op, index) ∈ plan.operations.zipIdx →
      ∀ guard, plan.activityGuards[index]?.getD none = some guard →
        ScalarExpression guard)
    (guardsValid : ∀ op index, (op, index) ∈ plan.operations.zipIdx →
      ∀ guard, plan.activityGuards[index]?.getD none = some guard →
        guard.validate Capabilities.scalarFragment types = .ok ()) :
    ∃ minimum, ∀ fuel, minimum ≤ fuel →
      evaluatePlan fuel ctx env
          (Compiler.nativePlanJson profile contractName state ctor ep plan standaloneFile) =
        (GuardedPlanExecution.evalPlan ctx env plan).toOption := by
  let wireItem (item : Impact.Op × Nat) : ScheduledOperation :=
    ⟨(plan.activityGuards[item.2]?.getD none).map NativeExpression.toJson, projected item.2⟩
  have guardNonNull (op : Impact.Op) (index : Nat)
      (inside : (op, index) ∈ plan.operations.zipIdx) :
      ∀ guard, plan.activityGuards[index]?.getD none = some guard →
        (NativeExpression.toJson guard).isNull = Bool.false := by
    intro guard selected
    exact ImpactExpressionSoundness.toJson_nonNull (guardsAdmitted op index inside guard selected)
  have decoded := decode_nativePlanJson_operations profile contractName state
    ctor ep plan standaloneFile projected projects guardNonNull
  have pointwise (item : Impact.Op × Nat) (inside : item ∈ plan.operations.zipIdx) :
      ∃ minimum, ∀ fuel, minimum ≤ fuel →
        evaluateScheduledOperation fuel ctx env (wireItem item) =
          GuardedPlanExecution.evalScheduledOperation ctx env plan item := by
    obtain ⟨op, index⟩ := item
    have itemDecoded := decode_operation (projects op index inside)
      (plan.activityGuards[index]?.getD none) (guardNonNull op index inside)
    obtain ⟨minimum, agrees⟩ := evaluate_nativeOperationJson_agrees ctx modulus
      (projects op index inside) (operandsAdmitted op index inside)
      (operandsValid op index inside) (guardsAdmitted op index inside)
      (guardsValid op index inside) typed
    refine ⟨minimum, ?_⟩
    intro fuel enough
    have result := agrees fuel enough
    rw [itemDecoded] at result
    exact result
  obtain ⟨minimum, scheduleAgrees⟩ :=
    ImpactScheduleTraversal.mapM_eventually_agrees plan.operations.zipIdx
      (fun fuel item => evaluateScheduledOperation fuel ctx env (wireItem item))
      (fun _ => GuardedPlanExecution.evalScheduledOperation ctx env plan) pointwise
  refine ⟨minimum, ?_⟩
  intro fuel enough
  rw [GuardedPlanExecution.evalPlan_toOption_eq_schedule ctx env plan aligned]
  unfold evaluatePlan
  rw [decoded]
  change ((plan.operations.zipIdx.map wireItem).mapM
      (evaluateScheduledOperation fuel ctx env)).map List.flatten = _
  simp only [List.mapM_map, Function.comp_def, scheduleAgrees fuel enough]

/-- Exact parsing of the production plan tree transfers schedule agreement to
the retained bytes and hence to the final modeled machine and read trace. -/
theorem runPlanBytes_agrees (fuel : Nat) (ctx : EvalContext) (env : EvalEnv)
    (bytes : ArtifactBytes.Bytes) (raw : Json) (plan : Impact.Plan)
    (parsed : ArtifactBytes.parse bytes = .ok raw)
    (agrees : evaluatePlan fuel ctx env raw = (GuardedPlanExecution.evalPlan ctx env plan).toOption)
    (initial : NativeState.Machine) :
    runPlanBytes fuel ctx env bytes initial =
      (GuardedPlanExecution.evalPlan ctx env plan).toOption.bind
        (fun operations => NativeState.run operations initial) := by
  unfold runPlanBytes
  rw [parsed]
  change (evaluatePlan fuel ctx env raw).bind _ = _
  rw [agrees]

end Noctium.Verification.ImpactPlanAgreement
