import Noctium.Verification.GuardedOutputRows
import Noctium.Verification.GuardedReturnTypeFrame
import Noctium.Verification.GuardedVmReadTranscript
import Noctium.Verification.GuardedZkirStateSoundness
import Noctium.Verification.ScalarReturnSoundness

namespace Noctium.Verification.GuardedCallArtifacts

open Lean Backend NativeRelation ScalarNormalization
open GenericStateCircuitParts
open GenericStateInputValues (decodeReads)
open GenericStatePrefixEnvironment (AgreesOnTypes)
open GuardedImpactObservation GuardedImpactTranscript
open GuardedScalarCandidateState (runCheckedCandidates)
open GuardedStatementConsumption
open ScalarGuardedPlanAdmission (ScalarEffect)

/-- The checked return requirements evaluate in the actual final source
environment. The typed complete frame supplies the interpretation used by
the expected artifact, while the effect proof transports it to source. -/
private theorem expected_returns_after_checked_call
    (state : List StateDecl) (sourceEntry : Entrypoint)
    (expected : Native.Expected) (plan : Impact.Plan)
    (ctx : EvalContext) (hash : Hash) (implementation : HashAgreement ctx hash)
    (assignment : Assignment) (frame : OutputFrame)
    (finalEnv complete : EvalEnv) (finalTypes : TypeEnv)
    (planAccepted : Impact.lower state (Passes.pruneEntrypoint sourceEntry) = .ok plan)
    (expectedAccepted : Native.expectedEntrypoint state (Passes.pruneEntrypoint sourceEntry) = .ok expected)
    (normalizedFrame : normalizeOutputs
      (entrypointSeedAliases (Passes.pruneEntrypoint sourceEntry) plan)
      (Passes.pruneEntrypoint sourceEntry).circuit.outputs = .ok frame)
    (scalarReads : ∀ readSpec ∈
      (plan.reads.drop (Impact.publicInputReadCount sourceEntry.circuit.inputs)).flatMap
        Impact.Read.scalarReads, scalarAliasReadType readSpec.ty)
    (typed : TypedEnvironment hash assignment frame.1 complete finalTypes)
    (agreement : AgreesOnTypes finalTypes finalEnv complete)
    (returns : ∀ returnValue ∈ sourceEntry.returns,
      returnValue.value.validate GenericStateEffectValidation.stateEffectCaps finalTypes = .ok ())
    (admittedReturns : ∀ returnValue ∈ sourceEntry.returns,
      Nonempty (ScalarType returnValue.ty) ∧ ScalarExpression returnValue.value)
    (assertions : ∀ term ∈ expected.assertions, interpret hash assignment term = some one)
    (bounds : ∀ bound ∈ expected.bounds,
      ∃ value, interpret hash assignment bound.1 = some value ∧ value.val ≤ bound.2) :
    ∃ returned,
      sourceEntry.evalReturns ctx finalEnv = .ok returned ∧
      expected.returns.map (interpret hash assignment) =
        returned.map (fun binding => some (scalar (valueNumber binding.2))) := by
  let ep := Passes.pruneEntrypoint sourceEntry
  obtain ⟨returnFrame, normalTerms, frameAccepted, normalized, expectedTerms,
    boundMembers, assertionMembers⟩ :=
    expectedEntrypoint_scalar_returns state ep expected plan planAccepted expectedAccepted
      scalarReads (fun item present => (admittedReturns item present).1)
  have sameFrame := Except.ok.inj (frameAccepted.symm.trans normalizedFrame)
  subst returnFrame
  have returnScope : ∀ returnValue ∈ sourceEntry.returns,
      returnValue.value.validate Capabilities.scalarFragment finalTypes = .ok () := by
    intro returnValue present
    rw [Capabilities.scalarFragment, ← GenericStateCaps.expr_validate_source_crypto]
    simpa [GenericStateEffectValidation.stateEffectCaps, Capabilities.source] using returns returnValue present
  obtain ⟨returned, evaluated, interpreted⟩ :=
    ScalarReturnSoundness.normalized_scalar_return_values ctx sourceEntry hash implementation
      assignment frame.1 finalEnv complete finalTypes typed agreement sourceEntry.returns
      normalTerms (fun item present => (admittedReturns item present).1)
      (fun item present => (admittedReturns item present).2) returnScope normalized
      (fun bound present => bounds bound (boundMembers bound present))
      (fun term present => assertions term (assertionMembers term present))
  refine ⟨returned, evaluated, ?_⟩
  simpa only [expectedTerms, List.map_map, Function.comp_def] using interpreted

/-- The checked artifacts and encoded initial state describe one guarded
scalar call. Its VM acceptance determines the ZKIR transcript and source
post-state. Successful Impact statement construction supplies the metadata
header used to project the same public instance from ZKIR. Admitted scalar
returns use the same final source environment and checked output row. -/
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
        (∀ returnValue ∈ ep.returns,
          returnValue.value.validate GenericStateEffectValidation.stateEffectCaps finalTypes = .ok ()) ∧
        ((∀ returnValue ∈ ep.returns,
            Nonempty (ScalarType returnValue.ty) ∧ ScalarExpression returnValue.value) →
          ∃ returned,
            sourceEntry.evalReturns ctx finalEnv = .ok returned ∧
            GuardedOutputRows.emittedReturnValues assignment rows =
              returned.map (fun binding => scalar (valueNumber binding.2))) := by
  let ep := Passes.pruneEntrypoint sourceEntry
  obtain ⟨exactRows, result, candidates, operations, observations, executed, decoded,
    evaluated, vmRun, _, _, consumed⟩ :=
    GuardedVmReadTranscript.lower_checked_guarded_statement_consumes
      state sourceEntry rewrites expected plan ctx hash implementation values assignment
      zkirBytes json rows slots final emitted artifact ordinary planAccepted expectedAccepted
      inputs admitted effects guardsAdmitted guardAdmission checked
  obtain ⟨_, schema, compatible, plainReads, distinctReads, scalarReads, frame, framedResult, framedCandidates,
    normalized, framedExecuted, framedDecoded, baseTyped, typedPlan, fresh, aliases, _⟩ :=
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
    sourceRun, finalEncoded, layout, agree, validated, returns⟩ :=
    GuardedZkirStateSoundness.lowerEntrypoint_checked_guarded_state
      state sourceEntry rewrites ctx hash implementation assignment zkirBytes json rows plan expected
      frame (result ++ values) candidates initial slots operations final emitted artifact ordinary
      planAccepted expectedAccepted schema normalized baseTyped scope plainReads fresh distinctReads
      aliases readGuards guardAdmission decoded scalarEffects operands compatible encoded distinct
      stateBound evaluated vmRun observations consumed profile contractName ctor standaloneFile
      impactBytes budget keyWidth statementAdmitted statementMatched
  refine ⟨exactRows, result, candidates, operations, observations, executed, decoded, evaluated,
    vmRun, consumed, ?_, finalTypes, finalEnv, finalState, finalSlots, sourceRun, finalEncoded,
    congrArg NativeState.Machine.stack layout, agree, returns, ?_⟩
  · obtain ⟨minimum, agreement⟩ := artifactAgreement
    refine ⟨minimum, ?_⟩
    intro fuel enough
    obtain ⟨raw, parsed, native, activity, _, fields⟩ := agreement fuel enough
    exact ⟨raw, parsed, native, activity, fields⟩
  · intro admittedReturns
    have typedFinal := GuardedReturnTypeFrame.lower_guarded_return_type_frame
      state ep plan hash assignment frame.1 ((result ++ values) ++ candidates) finalTypes
      planAccepted effects scope validated typedPlan
    have schemaFor (other : Native.Expected)
        (accepted : Native.expectedEntrypoint state ep = .ok other) :
        ∀ requirement ∈ other.rawInputs ++ other.inputs,
          requirement.ty.isForeign = _root_.Bool.false := by
      have same := Except.ok.inj (accepted.symm.trans expectedAccepted)
      subst other
      exact schema
    obtain ⟨rowExpected, rowAccepted, assertions, bounds, _, outputMeaning⟩ :=
      GuardedOutputRows.lowerEntrypoint_guardedOutputValues rewrites emitted artifact schemaFor ordinary
    have sameExpected := Except.ok.inj (rowAccepted.symm.trans expectedAccepted)
    subst rowExpected
    obtain ⟨returned, evaluatedReturns, returnMeaning⟩ := expected_returns_after_checked_call
      state sourceEntry expected plan ctx hash implementation assignment frame
      finalEnv ((result ++ values) ++ candidates) finalTypes planAccepted expectedAccepted
      normalized scalarReads typedFinal agree returns admittedReturns assertions bounds
    refine ⟨returned, evaluatedReturns, ?_⟩
    apply (List.map_inj_right (f := some) (fun _ _ => Option.some.inj)).mp
    simpa only [List.map_map, Function.comp_def] using outputMeaning.symm.trans returnMeaning

end Noctium.Verification.GuardedCallArtifacts
