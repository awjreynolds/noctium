import Noctium.Verification.GuardedActiveObservation
import Noctium.Verification.GuardedSourceActivity
import Noctium.Verification.GuardedZkirArtifact
import Noctium.Verification.GuardedZkirRequirements
import Noctium.Verification.ScalarGuardedActivityAdmission

namespace Noctium.Verification.GuardedScalarSchedule

open Lean Backend NativeRelation ScalarNormalization
open GenericStateCircuitParts GuardedImpactObservation GuardedImpactTranscript
open ScalarGuardedPlanAdmission (ScalarEffect)

/-- The accepted scalar plan and its activity schedule determine exactly which
native field groups execute, in their original order. -/
theorem lower_active_scalar_schedule (state : List StateDecl) (sourceEntry : Entrypoint)
    (expected : Native.Expected) (plan : Impact.Plan) (frame : OutputFrame)
    (ctx : EvalContext) (hash : Hash) (implementation : HashAgreement ctx hash)
    (assignment : Assignment) (values : EvalEnv)
    (environment : TypedEnvironment hash assignment frame.1 values (plan.typeEnvironment sourceEntry))
    (accepted : Native.expectedEntrypoint state sourceEntry = .ok expected)
    (lowered : Impact.lower state sourceEntry = .ok plan)
    (normalized : normalizeOutputs (entrypointSeedAliases sourceEntry plan)
      sourceEntry.circuit.outputs = .ok frame)
    (readAliases : forIn ((plan.reads.drop
      (Impact.publicInputReadCount sourceEntry.circuit.inputs)).flatMap Impact.Read.scalarReads)
      frame.1 (readAliasStep sourceEntry) = .ok frame.1)
    (compatible : ∀ input ∈ sourceEntry.circuit.inputs, Impact.publicInputScalarCompatible input)
    (effects : ∀ effect ∈ sourceEntry.effects, ScalarEffect state effect)
    (guardsAdmitted : ∀ condition, some condition ∈ sourceEntry.effectGuards →
      ScalarExpression condition)
    (reads : ∀ readSpec ∈ (plan.reads.drop
      (Impact.publicInputReadCount sourceEntry.circuit.inputs)).flatMap Impact.Read.scalarReads,
      scalarAliasReadType readSpec.ty)
    (bounds : ∀ requirement ∈ expected.bounds,
      ∃ value, interpret hash assignment requirement.1 = some value ∧ value.val ≤ requirement.2)
    (assertions : ∀ term ∈ expected.assertions, interpret hash assignment term = some one)
    {observations : List Observation}
    (observed : expectedObservations hash assignment expected = some observations) :
    ∃ active, GuardedPlanExecution.evalPlan ctx values plan = .ok active ∧
      NativeState.groups active = (observations.filter (·.active)).map (·.payload) := by
  have admitted := ScalarGuardedPlanAdmission.lower_admitted_ops
    state sourceEntry plan lowered compatible effects guardsAdmitted
  obtain ⟨native, scalar, groupMeaning⟩ :=
    ScalarExpectedPlanSchedule.expected_schedule_of_admitted_operations state sourceEntry expected
      plan frame frame.1 ctx hash implementation assignment values environment accepted lowered
      normalized readAliases admitted bounds assertions
  have single : ∀ op ∈ plan.operations, op.fieldGroups = [op.fields] :=
    fun op present => ScalarImpactOperationMeaning.fieldGroups_eq_singleton (admitted op present).1
  have operationGuardsAdmitted : ∀ condition, some condition ∈ plan.activityGuards →
      ScalarExpression condition := by
    intro condition present
    exact guardsAdmitted condition
      (ScalarGuardedActivityAdmission.lower_activity_guard_mem state sourceEntry plan lowered
        effects condition present)
  obtain ⟨activities, aligned, guards, length, guardMeaning⟩ :=
    GuardedSourceActivity.lower_activity_schedule state sourceEntry ctx hash assignment values
      implementation plan expected frame lowered accepted normalized environment reads
      operationGuardsAdmitted single assertions bounds
  have nativeLength := GuardedPlanExecution.scalar_evalPlan_length ctx values plan native scalar
  exact ⟨GuardedPlanExecution.activeOperations native activities,
    GuardedPlanExecution.evalPlan_of_scalar_schedule
      ctx values plan native activities aligned scalar guards,
    GuardedActiveObservation.expected_active_groups hash assignment expected observations native
      activities guardMeaning groupMeaning (nativeLength.trans length.symm) observed⟩

/-- The same active schedule is fixed by the supplied checked ZKIR bytes.
Ordinary row satisfaction and the typed candidate environment remain explicit. -/
theorem lower_checked_guarded_artifact_schedule
    (state : List StateDecl) (sourceEntry : Entrypoint) (rewrites : Zkir.Rewrites)
    (expected : Native.Expected) (plan : Impact.Plan) (frame : OutputFrame)
    (ctx : EvalContext) (hash : Hash) (implementation : HashAgreement ctx hash)
    (assignment : Assignment) (values : EvalEnv)
    (bytes : ArtifactBytes.Bytes) (json : Json) (rows : List GuardedScalarRows.Row)
    (environment : TypedEnvironment hash assignment frame.1 values
      (plan.typeEnvironment (Passes.pruneEntrypoint sourceEntry)))
    (emitted : Zkir.lowerEntrypoint state sourceEntry rewrites = .ok json)
    (artifact : GuardedZkirArtifact.check bytes json = .ok rows)
    (ordinary : ∀ row ∈ rows, ordinaryHolds hash assignment row)
    (accepted : Native.expectedEntrypoint state (Passes.pruneEntrypoint sourceEntry) = .ok expected)
    (lowered : Impact.lower state (Passes.pruneEntrypoint sourceEntry) = .ok plan)
    (normalized : normalizeOutputs (entrypointSeedAliases (Passes.pruneEntrypoint sourceEntry) plan)
      (Passes.pruneEntrypoint sourceEntry).circuit.outputs = .ok frame)
    (readAliases : forIn ((plan.reads.drop
      (Impact.publicInputReadCount (Passes.pruneEntrypoint sourceEntry).circuit.inputs)).flatMap
      Impact.Read.scalarReads) frame.1
      (readAliasStep (Passes.pruneEntrypoint sourceEntry)) = .ok frame.1)
    (compatible : ∀ input ∈ (Passes.pruneEntrypoint sourceEntry).circuit.inputs,
      Impact.publicInputScalarCompatible input)
    (effects : ∀ effect ∈ (Passes.pruneEntrypoint sourceEntry).effects, ScalarEffect state effect)
    (guardsAdmitted : ∀ condition, some condition ∈ (Passes.pruneEntrypoint sourceEntry).effectGuards →
      ScalarExpression condition)
    (reads : ∀ readSpec ∈ (plan.reads.drop
      (Impact.publicInputReadCount (Passes.pruneEntrypoint sourceEntry).circuit.inputs)).flatMap
      Impact.Read.scalarReads, scalarAliasReadType readSpec.ty)
    (schema : ∀ requirement ∈ expected.rawInputs ++ expected.inputs,
      requirement.ty.isForeign = Bool.false) :
    (GuardedZkirArtifact.decodeBytes bytes).map GuardedZkirArtifact.View.rows = .ok rows ∧
    ∃ observations active,
      emittedObservations assignment rows = some observations ∧
      GuardedPlanExecution.evalPlan ctx values plan = .ok active ∧
      NativeState.groups active = (observations.filter (·.active)).map (·.payload) := by
  obtain ⟨exactRows, instructions, parsed, decoded⟩ := GuardedZkirArtifact.check_sound artifact
  have schemaFromExpected (other : Native.Expected)
      (otherAccepted : Native.expectedEntrypoint state (Passes.pruneEntrypoint sourceEntry) =
        .ok other) : ∀ requirement ∈ other.rawInputs ++ other.inputs,
        requirement.ty.isForeign = Bool.false := by
    have same := Except.ok.inj (otherAccepted.symm.trans accepted)
    subst other
    exact schema
  obtain ⟨requirementExpected, requirementAccepted, requirements⟩ :=
    GuardedZkirRequirements.lowerEntrypoint_guardedRows_sourceRequirements
      rewrites emitted parsed decoded schemaFromExpected
  have same := Except.ok.inj (requirementAccepted.symm.trans accepted)
  subst requirementExpected
  obtain ⟨assertions, bounds, _⟩ := requirements ordinary
  obtain ⟨_, observedExpected, _, _, observedAccepted, _, observed⟩ :=
    lowerEntrypoint_guardedImpactTranscript rewrites emitted parsed decoded schemaFromExpected
  have same := Except.ok.inj (observedAccepted.symm.trans accepted)
  subst observedExpected
  obtain ⟨observations, emittedGroups, expectedGroups, _⟩ := observed ordinary
  obtain ⟨active, evaluation, payloads⟩ := lower_active_scalar_schedule state
    (Passes.pruneEntrypoint sourceEntry) expected plan frame ctx hash implementation assignment values
    environment accepted lowered normalized readAliases compatible effects guardsAdmitted reads
    bounds assertions expectedGroups
  exact ⟨exactRows, observations, active, emittedGroups, evaluation, payloads⟩

end Noctium.Verification.GuardedScalarSchedule
