import Noctium.Verification.GenericStateNativeSchedule
import Noctium.Verification.GuardedScalarCandidateState
import Noctium.Verification.ScalarCellPublicFields

namespace Noctium.Verification.GenericStateCheckedSchedule

open Backend NativeRelation ScalarNormalization Backend.Native
open GenericStateCircuitParts GenericStateInputValues
open GuardedEffectEvaluation
open ScalarGuardedPlanAdmission (ScalarEffect)

/-- Candidate output frame used by the converse proof. -/
def outputCandidates (ctx : EvalContext) (sourceEntry : Entrypoint)
    (values : EvalEnv) : EvalEnv :=
  (sourceEntry.circuit.outputs.mapM (evalOutput ctx values)).toOption.getD [] ++ values

/-- Check the accepted plan with the current guard-aware scalar VM. -/
def CheckedPlan (ctx : EvalContext) (sourceEntry : Entrypoint)
    (plan : Impact.Plan) (values : EvalEnv) (assignment : Assignment)
    (slots : List NativeState.Slot) (final : NativeState.Machine) : Prop :=
  GuardedScalarCandidateState.runCheckedCandidates ctx sourceEntry plan values assignment slots = some final

/-- A satisfying strictly decoded relation and a checked VM run share one
accepted plan and candidate frame. The relation supplies the complete ordered
schedule, and the VM trace records the active operations of each source
effect after the public-input prefix. -/
theorem accepted_checked_trace (state : List StateDecl)
    (sourceEntry : Entrypoint) (json : Lean.Json) (relation : Program)
    (ctx : EvalContext) (hash : Hash) (implementation : HashAgreement ctx hash)
    (values : EvalEnv) (assignment : Assignment)
    (streams : InputStreams) (publicGroups : List (List Scalar))
    (slots : List NativeState.Slot) (final : NativeState.Machine)
    (admittedInputs : CanonicalInputs sourceEntry.circuit values assignment)
    (circuitAdmission : ScalarCircuitAdmission sourceEntry.circuit)
    (effects : ∀ effect ∈ sourceEntry.effects, ScalarEffect state effect)
    (guardsAdmitted : ∀ condition, some condition ∈ sourceEntry.effectGuards →
      ScalarExpression condition)
    (lowered : Zkir.lowerEntrypoint state sourceEntry = .ok json)
    (decoded : NativeRelationJson.decode json = .ok relation)
    (satisfies : CircuitSatisfies hash relation streams assignment publicGroups)
    (plan : Impact.Plan)
    (planAccepted : Impact.lower state (Passes.pruneEntrypoint sourceEntry) = .ok plan)
    (planGuardsAdmitted : ∀ guard ∈ plan.guards, ScalarExpression guard)
    (checked : CheckedPlan ctx sourceEntry plan values assignment slots final) :
    ∃ (result candidates : EvalEnv) (scheduled active : List NativeState.Op)
        (offsets : List Nat) (inputPlan : Impact.Plan) (chunks : List (List Impact.Op))
        (publicNative : List NativeState.Op)
        (groups : List (Option _root_.Bool × List NativeState.Op)) (publicReads : List NativeState.Cell),
      let ep := Passes.pruneEntrypoint sourceEntry
      let env := (result ++ values) ++ candidates
      sourceEntry.circuit.run ctx values = .ok result ∧
      decodeReads (plan.reads.drop (Impact.publicInputReadCount sourceEntry.circuit.inputs))
        assignment = .ok candidates ∧
      GenericStateOps.evalPlan ctx env plan = .ok scheduled ∧
      publicGroups = NativeState.groups scheduled ∧
      GuardedPlanExecution.evalPlan ctx env plan = .ok active ∧
      Impact.lowerWithEffectBoundaries state ep = .ok (plan, offsets) ∧
      Impact.publicInputPlan ep.circuit.inputs {} = .ok inputPlan ∧
      GuardedEffectOperationChunks state ep.effectGuards ep.effects.zipIdx
        inputPlan plan offsets chunks ∧
      inputPlan.operations.mapM (GenericStateOps.evalOp ctx env) = .ok publicNative ∧
      (ep.effects.zipIdx.zip chunks).mapM (fun (item, chunk) =>
        GuardedPlanExecution.evalChunk ctx env (ep.effectGuardAt item.2) chunk) = .ok groups ∧
      active = publicNative ++ (groups.map Prod.snd).flatten ∧
      NativeState.run publicNative ⟨[.vector slots], []⟩ = some ⟨[.vector slots], publicReads⟩ ∧
      GenericStateVM.RunsChunks (groups.map Prod.snd) ⟨[.vector slots], publicReads⟩ final := by
  let ep := Passes.pruneEntrypoint sourceEntry
  obtain ⟨actualPlan, expected, frame, result, candidates, scheduled, actualPlanAccepted,
    expectedAccepted, sound, normalized, sourceRun, candidatesDecoded, environment, _,
    scheduledEval, scheduledGroups⟩ :=
    GenericStateNativeSchedule.accepted_native_schedule state sourceEntry json relation
      ctx hash implementation values assignment streams publicGroups admittedInputs
      circuitAdmission effects guardsAdmitted lowered decoded satisfies
  have planEq := Except.ok.inj (actualPlanAccepted.symm.trans planAccepted)
  subst actualPlan
  let env := (result ++ values) ++ candidates
  obtain ⟨active, evaluated, vmRun⟩ :=
    GuardedScalarCandidateState.run_of_checked_candidates ctx sourceEntry plan values assignment
      slots result candidates final sourceRun candidatesDecoded checked
  have prunedEffects : ∀ effect ∈ ep.effects, ScalarEffect state effect := by
    simpa only [ep, Passes.pruneEntrypoint] using effects
  have admittedReads :=
    (ScalarGuardedReadAdmission.lower_read_admission state ep plan planAccepted prunedEffects).1
  let reads := plan.reads.drop (Impact.publicInputReadCount ep.circuit.inputs)
  have scalarReads : ∀ descriptor ∈ reads.flatMap Impact.Read.scalarReads, scalarAliasReadType descriptor.ty := by
    rw [ScalarPlanGuardSoundness.plain_reads_scalarReads reads
      (fun descriptor present => (admittedReads descriptor present).1)]
    exact fun descriptor present =>
      ScalarPlanGuardSoundness.scalarType_shape descriptor.ty (admittedReads descriptor present).2.1
  obtain ⟨guardFrame, guards, guardNormalized, normalizeGuards, guardAssertions, guardBounds⟩ :=
    expectedEntrypoint_guards state ep expected plan planAccepted expectedAccepted scalarReads
  have frameEq := Except.ok.inj (guardNormalized.symm.trans normalized)
  subst guardFrame
  have assertions := ScalarPlanGuardSoundness.checked_plan_guard_truth ctx hash
    implementation assignment (plan.typeEnvironment ep) frame.1 env plan ep.span expected guards
    environment (Impact.lower_guards_validate state ep plan planAccepted) planGuardsAdmitted
    normalizeGuards guardBounds guardAssertions sound.bounds sound.assertions
  have scope := ScalarGuardedActivityAdmission.lower_guarded_scalar_read_scope
    state ep plan planAccepted prunedEffects
  have compatible := ScalarCellPublicFields.canonical_inputs_scalar_compatible
    sourceEntry.circuit values assignment admittedInputs
  obtain ⟨offsets, inputPlan, chunks, publicNative, groups, publicReads,
    boundaries, publicAccepted, compiled, publicEvaluated, effectsEvaluated, sequence,
    publicRun, trace⟩ :=
    GuardedPlanTrace.lower_checked_effect_chunks state ep plan ctx env active slots final
      planAccepted scope compatible evaluated assertions vmRun
  exact ⟨result, candidates, scheduled, active, offsets, inputPlan, chunks, publicNative, groups,
    publicReads, sourceRun, candidatesDecoded, scheduledEval, scheduledGroups,
    evaluated, boundaries, publicAccepted, compiled, publicEvaluated, effectsEvaluated,
    sequence, publicRun, trace⟩

end Noctium.Verification.GenericStateCheckedSchedule
