import Noctium.Verification.ImpactPlanStatement
import Noctium.Verification.ImpactScheduleComparison

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

/-- Check whether a supplied artifact has the compiler's scalar operation
schedule, including all operands and activity guards. -/
def matchesBytes (budget : Nat) (bytes : ArtifactBytes.Bytes) (expected : Json) : _root_.Bool :=
  match ArtifactBytes.parse bytes with
  | .ok raw => ImpactScheduleComparison.matches budget raw expected
  | .error _ => Bool.false

/-- Successful comparison of supplied bytes with the compiler's plan makes
their modeled public statements agree. This covers rejection by the scoped
evaluators and statement construction. Separate circuit assertions and
native acceptance have their own proof obligations. -/
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
    (budget : Nat) (bytes : ArtifactBytes.Bytes) (inputs : ImpactPlanStatement.Inputs)
    (lowered : Impact.lower state ep = .ok plan)
    (matched : matchesBytes budget bytes
      (Compiler.nativePlanJson profile contractName state ctor ep plan standaloneFile) = Bool.true) :
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
  have compared : ∃ raw, ArtifactBytes.parse bytes = .ok raw ∧
      ImpactScheduleComparison.matches budget raw emitted = Bool.true := by
    cases parsed : ArtifactBytes.parse bytes with
    | error reason => simp [matchesBytes, parsed] at matched
    | ok raw => exact ⟨raw, rfl, by simpa [matchesBytes, parsed, emitted] using matched⟩
  obtain ⟨raw, parsed, scheduleMatches⟩ := compared
  obtain ⟨operationsMatch, activityMatches⟩ :=
    ImpactScheduleComparison.evaluations_eq_of_matches scheduleMatches fuel ctx env keyWidth
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
