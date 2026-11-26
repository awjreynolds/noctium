import Noctium.Verification.GuardedVmReadTranscript
import Noctium.Verification.GuardedZkirStateSoundness

namespace Noctium.Verification.GuardedCallArtifacts

open Lean Backend NativeRelation ScalarNormalization
open GenericStateCircuitParts
open GenericStateInputValues (decodeReads)
open GenericStatePrefixEnvironment (AgreesOnTypes)
open GuardedImpactObservation GuardedImpactTranscript
open GuardedScalarCandidateState (runCheckedCandidates)
open GuardedStatementConsumption
open ScalarGuardedPlanAdmission (ScalarEffect)

/-- The checked artifacts and encoded initial state describe one guarded
scalar call. Its VM acceptance determines the ZKIR transcript and source
post-state. Successful Impact statement construction supplies the metadata
header used to project the same public instance from ZKIR. -/
theorem lower_checked_guarded_call_artifacts
    (state : List StateDecl) (sourceEntry : Entrypoint) (rewrites : Zkir.Rewrites)
    (expected : Native.Expected) (plan : Impact.Plan)
    (ctx : EvalContext) (hash : Hash) (implementation : HashAgreement ctx hash)
    (values : EvalEnv) (assignment : Assignment)
    (zkirBytes : ArtifactBytes.Bytes) (json : Json) (rows : List GuardedScalarRows.Row)
    (initial : LedgerState) (slots : List NativeState.Slot) (final : NativeState.Machine)
    (emitted : Zkir.lowerEntrypoint state sourceEntry rewrites = .ok json)
    (artifact : GuardedZkirArtifact.check zkirBytes json = .ok rows)
    (ordinary : ∀ row ∈ rows, ordinaryHolds hash assignment row)
    (planAccepted : Impact.lower state (Passes.pruneEntrypoint sourceEntry) = .ok plan)
    (expectedAccepted :
      Native.expectedEntrypoint state (Passes.pruneEntrypoint sourceEntry) = .ok expected)
    (inputs : CanonicalInputs sourceEntry.circuit values assignment)
    (admitted : ScalarCircuitAdmission sourceEntry.circuit)
    (effects : ∀ effect ∈ sourceEntry.effects, ScalarEffect state effect)
    (guardsAdmitted : ∀ condition, some condition ∈ sourceEntry.effectGuards →
      ScalarExpression condition)
    (guardAdmission : plan.guards.all
      (fun guard => (ScalarExpressionAdmission.certify guard).isSome) = _root_.Bool.true)
    (encoded : GenericStateEncoding.encodeState state initial = some slots)
    (distinct : state.Pairwise (fun left right => left.name ≠ right.name))
    (stateBound : state.length < Field.modulus)
    (checked : runCheckedCandidates ctx sourceEntry plan values assignment slots = some final)
    (profile : TargetProfile) (contractName : Name) (ctor : Option Constructor)
    (standaloneFile : _root_.Bool) (impactBytes : ArtifactBytes.Bytes) (budget : Nat)
    (keyWidth : Nat → Option Nat)
    (statementAdmitted :
      ImpactPlanStatementAgreement.admitsScalarPlan keyWidth plan = _root_.Bool.true)
    (statementMatched : ImpactPlanStatementAgreement.matchesBytes budget impactBytes
      (Compiler.nativePlanJson profile contractName state ctor (Passes.pruneEntrypoint sourceEntry)
        plan standaloneFile) = _root_.Bool.true) :
    let ep := Passes.pruneEntrypoint sourceEntry
    (GuardedZkirArtifact.decodeBytes zkirBytes).map GuardedZkirArtifact.View.rows = .ok rows ∧
    ∃ (result candidates : EvalEnv) (operations : List NativeState.Op)
        (observations : List Observation),
      let complete := (result ++ values) ++ candidates
      let streams : Inputs :=
        ⟨operations.flatMap ImpactStatementScalar.opFields, final.reads.map NativeState.Cell.value⟩
      sourceEntry.circuit.run ctx values = .ok result ∧
      decodeReads (plan.reads.drop (Impact.publicInputReadCount sourceEntry.circuit.inputs))
        assignment = .ok candidates ∧
      GuardedPlanExecution.evalPlan ctx complete plan = .ok operations ∧
      NativeState.run operations ⟨[.vector slots], []⟩ = some final ∧
      consumeArtifact zkirBytes assignment streams = some observations ∧
      (∃ minimum, ∀ fuel, minimum ≤ fuel → ∃ raw,
        ArtifactBytes.parse impactBytes = .ok raw ∧
        ImpactPlanAgreement.evaluatePlan fuel ctx complete raw = some operations ∧
        ImpactTranscriptSchedule.evaluateSchedule fuel ctx complete keyWidth raw =
          some (observationActivity observations) ∧
        ∀ metadata fields,
          ImpactPlanStatement.fromBytes fuel ctx complete keyWidth impactBytes metadata =
            some fields →
          ∃ header : ImpactCallStatement.Header,
            ImpactPlanStatement.headerFor metadata operations (observationActivity observations) =
              some header ∧
            fromArtifact zkirBytes assignment header streams =
              some ⟨fields, observationActivity observations⟩ ∧
            ImpactPlanStatementAgreement.fromEntrypoint ctx complete state ep metadata =
              some fields) ∧
      ∃ finalTypes finalEnv finalState finalSlots,
        runEffectsWithGuardsAndEnv ctx ep.effects ep.effectGuards (result ++ values) initial =
          .ok (finalEnv, finalState) ∧
        GenericStateEncoding.encodeState state finalState = some finalSlots ∧
        final.stack = [.vector finalSlots] ∧
        AgreesOnTypes finalTypes finalEnv complete ∧
        ∀ returnValue ∈ ep.returns,
          returnValue.value.validate GenericStateEffectValidation.stateEffectCaps finalTypes = .ok () := by
  let ep := Passes.pruneEntrypoint sourceEntry
  obtain ⟨exactRows, result, candidates, operations, observations, executed, decoded,
    evaluated, vmRun, _, _, consumed⟩ :=
    GuardedVmReadTranscript.lower_checked_guarded_statement_consumes
      state sourceEntry rewrites expected plan ctx hash implementation values assignment
      zkirBytes json rows slots final emitted artifact ordinary planAccepted expectedAccepted
      inputs admitted effects guardsAdmitted guardAdmission checked
  obtain ⟨_, schema, compatible, plainReads, distinctReads, _, frame, framedResult, framedCandidates,
    normalized, framedExecuted, framedDecoded, baseTyped, _, fresh, aliases, _⟩ :=
    GuardedScalarCandidateSchedule.lower_checked_guarded_source_frame
      state sourceEntry rewrites expected plan ctx hash implementation values assignment
      zkirBytes json rows emitted artifact ordinary planAccepted expectedAccepted inputs admitted effects
  have sameResult : framedResult = result := Except.ok.inj
    ((show sourceEntry.circuit.run ctx values = .ok framedResult by
      simpa only [Passes.pruneEntrypoint, Passes.pruneCircuit_run] using framedExecuted).symm.trans executed)
  subst framedResult
  have sameCandidates := Except.ok.inj (framedDecoded.symm.trans decoded)
  subst framedCandidates
  have scope := ScalarGuardedActivityAdmission.lower_guarded_scalar_read_scope
    state ep plan planAccepted effects
  have readGuards (readSpec : Impact.Read)
      (present : readSpec ∈ plan.reads.drop (Impact.publicInputReadCount ep.circuit.inputs))
      (condition : Expr .bool) (selected : readSpec.guard = some condition) :
      ScalarExpression condition :=
    guardsAdmitted condition (GuardedReadDescriptorTrace.lower_post_public_read_guard_mem
      state ep plan planAccepted scope readSpec present condition selected)
  have scalarEffects := ScalarGuardedActivityAdmission.scalar_state_effects_of_admitted
    state sourceEntry.effects effects
  have operands (effect : Effect) (present : effect ∈ sourceEntry.effects) :=
    GuardedScalarOperands.of_admitted (effects effect present)
  obtain ⟨_, _, artifactAgreement, finalTypes, finalEnv, finalState, finalSlots, finalReads,
    sourceRun, finalEncoded, layout, agree, _, returns⟩ :=
    GuardedZkirStateSoundness.lowerEntrypoint_checked_guarded_state
      state sourceEntry rewrites ctx hash implementation assignment zkirBytes json rows plan expected
      frame (result ++ values) candidates initial slots operations final emitted artifact ordinary
      planAccepted expectedAccepted schema normalized baseTyped scope plainReads fresh distinctReads
      aliases readGuards guardAdmission decoded scalarEffects operands compatible encoded distinct
      stateBound evaluated vmRun observations consumed profile contractName ctor standaloneFile
      impactBytes budget keyWidth statementAdmitted statementMatched
  refine ⟨exactRows, result, candidates, operations, observations, executed, decoded, evaluated,
    vmRun, consumed, ?_, finalTypes, finalEnv, finalState, finalSlots, sourceRun, finalEncoded,
    congrArg NativeState.Machine.stack layout, agree, returns⟩
  obtain ⟨minimum, agreement⟩ := artifactAgreement
  refine ⟨minimum, ?_⟩
  intro fuel enough
  obtain ⟨raw, parsed, native, activity, _, fields⟩ := agreement fuel enough
  exact ⟨raw, parsed, native, activity, fields⟩

end Noctium.Verification.GuardedCallArtifacts
