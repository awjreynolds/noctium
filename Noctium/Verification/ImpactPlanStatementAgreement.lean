import Noctium.Verification.ImpactPlanStatement

namespace Noctium.Verification.ImpactPlanStatementAgreement

open Lean Backend ImpactPlanStatement ImpactTranscriptSchedule
open ImpactExpressionSchedule ImpactOperationAgreement ImpactReferenceEvaluation
open ImpactTranscriptWidth ImpactWireDecoder ImpactWireSoundness ScalarNormalization

/-- The source statement evaluates the typed plan and traverses its guarded
field groups in source order. -/
def fromSource (ctx : EvalContext) (env : EvalEnv) (plan : Impact.Plan)
    (inputs : ImpactPlanStatement.Inputs) : Option (List NativeRelation.Scalar) := do
  let operations ← (GuardedPlanExecution.evalPlan ctx env plan).toOption
  let activity ← (plan.operations.zipIdx.mapM (sourceGroups ctx env plan)).map List.flatten
  publicInputs inputs operations activity

/-- Lower an entrypoint with the production Impact pass, then construct its
source statement. Callers supply the entrypoint used at the compiler seam. -/
def fromEntrypoint (ctx : EvalContext) (env : EvalEnv) (state : List StateDecl)
    (ep : Entrypoint) (inputs : ImpactPlanStatement.Inputs) :
    Option (List NativeRelation.Scalar) := do
  let plan ← (Backend.Impact.lower state ep).toOption
  fromSource ctx env plan inputs

/-- Successful production lowering connects the entrypoint statement to the
source-plan statement. -/
theorem fromEntrypoint_eq_fromSource
    (ctx : EvalContext) (env : EvalEnv) (state : List StateDecl)
    (ep : Entrypoint) (plan : Impact.Plan) (inputs : ImpactPlanStatement.Inputs)
    (lowered : Backend.Impact.lower state ep = .ok plan) :
    fromEntrypoint ctx env state ep inputs = fromSource ctx env plan inputs := by
  simp [fromEntrypoint, lowered, Except.toOption, Bind.bind]

/-- An exact byte artifact yields the same modeled statement as the lowered
entrypoint when its decoded operation schedule matches the compiler's plan.
The schedule retains every operation, operand, and activity guard. Equality
includes rejection by the operation and activity evaluators and statement
construction. Separate circuit assertions and native acceptance have their
own proof obligations. -/
theorem fromBytes_nativePlanJson_agrees
    (profile : TargetProfile) (contractName : Name) (state : List StateDecl)
    (ctor : Option Constructor) (ep : Entrypoint) (plan : Impact.Plan)
    (standaloneFile : _root_.Bool) (projected : Nat → ImpactWireDecoder.Operation)
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
        guard.validate Capabilities.scalarFragment types = .ok ())
    (keyWidth : Nat → Option Nat)
    (keys : ∀ op index, (op, index) ∈ plan.operations.zipIdx →
      ScalarKeyWidths keyWidth op)
    (bytes : ArtifactBytes.Bytes) (raw : Json) (inputs : ImpactPlanStatement.Inputs)
    (lowered : Impact.lower state ep = .ok plan)
    (parsed : ArtifactBytes.parse bytes = .ok raw)
    (scheduleMatches : decodePlanOperations raw = decodePlanOperations
      (Compiler.nativePlanJson profile contractName state ctor ep plan standaloneFile)) :
    ∃ minimum, ∀ fuel, minimum ≤ fuel →
      fromBytes fuel ctx env keyWidth bytes inputs = fromEntrypoint ctx env state ep inputs := by
  let emitted := Compiler.nativePlanJson profile contractName state ctor ep plan standaloneFile
  obtain ⟨operationMinimum, operationsAgree⟩ :=
    ImpactPlanAgreement.evaluate_nativePlanJson_agrees
      profile contractName state ctor ep plan standaloneFile projected ctx modulus
      typed aligned projects operandsAdmitted operandsValid guardsAdmitted guardsValid
  obtain ⟨activityMinimum, activityAgree⟩ :=
    ImpactTranscriptSchedule.evaluate_nativePlanJson_agrees
      profile contractName state ctor ep plan standaloneFile projected ctx modulus
      typed keyWidth projects keys guardsAdmitted guardsValid
  let minimum := max operationMinimum activityMinimum
  refine ⟨minimum, ?_⟩
  intro fuel enough
  have operationFuel : operationMinimum ≤ fuel :=
    Nat.le_trans (Nat.le_max_left _ _) enough
  have activityFuel : activityMinimum ≤ fuel :=
    Nat.le_trans (Nat.le_max_right _ _) enough
  have operationsMatch :
      ImpactPlanAgreement.evaluatePlan fuel ctx env raw =
        ImpactPlanAgreement.evaluatePlan fuel ctx env emitted := by
    unfold ImpactPlanAgreement.evaluatePlan
    rw [scheduleMatches]
  have activityMatches :
      evaluateSchedule fuel ctx env keyWidth raw =
        evaluateSchedule fuel ctx env keyWidth emitted := by
    unfold evaluateSchedule
    rw [scheduleMatches]
  unfold ImpactPlanStatement.fromBytes
  rw [parsed]
  simp only [Except.toOption, Bind.bind, Option.bind_some]
  rw [operationsMatch, activityMatches,
    fromEntrypoint_eq_fromSource ctx env state ep plan inputs lowered]
  dsimp only [emitted]
  unfold fromSource
  rw [operationsAgree fuel operationFuel, activityAgree fuel activityFuel]
  rfl

end Noctium.Verification.ImpactPlanStatementAgreement
