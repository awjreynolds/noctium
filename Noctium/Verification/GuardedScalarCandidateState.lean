import Noctium.Verification.GuardedScalarCandidateSchedule
import Noctium.Verification.GuardedScalarOperands
import Noctium.Verification.GuardedStateEffectFold
import Noctium.Verification.GuardedZkirPlanSoundness

namespace Noctium.Verification.GuardedScalarCandidateState

open Lean Backend NativeRelation ScalarNormalization
open GenericStateCircuitParts GenericStateInputValues GenericStatePrefixEnvironment
open ScalarGuardedPlanAdmission (ScalarEffect)

/-- Run the active scalar operations on the initial encoded state using only
values from source circuit execution and the artifact's decoded candidates. -/
def runCheckedCandidates (ctx : EvalContext) (sourceEntry : Entrypoint)
    (plan : Impact.Plan) (values : EvalEnv) (assignment : Assignment)
    (slots : List NativeState.Slot) : Option NativeState.Machine := do
  let result ← (sourceEntry.circuit.run ctx values).toOption
  let candidates ← (decodeReads
    (plan.reads.drop (Impact.publicInputReadCount sourceEntry.circuit.inputs)) assignment).toOption
  let operations ← (GuardedPlanExecution.evalPlan ctx ((result ++ values) ++ candidates) plan).toOption
  NativeState.run operations ⟨[.vector slots], []⟩

/-- Recover the exact operation sequence and modeled run from the candidate check. -/
theorem run_of_checked_candidates
    (ctx : EvalContext) (sourceEntry : Entrypoint) (plan : Impact.Plan)
    (values : EvalEnv) (assignment : Assignment) (slots : List NativeState.Slot)
    (result candidates : EvalEnv) (final : NativeState.Machine)
    (source : sourceEntry.circuit.run ctx values = .ok result)
    (decoded : decodeReads
      (plan.reads.drop (Impact.publicInputReadCount sourceEntry.circuit.inputs)) assignment =
        .ok candidates)
    (checked : runCheckedCandidates ctx sourceEntry plan values assignment slots = some final) :
    ∃ operations,
      GuardedPlanExecution.evalPlan ctx ((result ++ values) ++ candidates) plan = .ok operations ∧
      NativeState.run operations ⟨[.vector slots], []⟩ = some final := by
  cases evaluated : GuardedPlanExecution.evalPlan ctx ((result ++ values) ++ candidates) plan with
  | error reason =>
    simp [runCheckedCandidates, source, decoded, evaluated, Except.toOption, -List.append_assoc] at checked
  | ok operations =>
    exact ⟨operations, rfl, by
      simpa [runCheckedCandidates, source, decoded, evaluated, Except.toOption, -List.append_assoc] using checked⟩

/-- When the modeled ledger accepts the exact candidates from checked guarded
ZKIR, its final root encodes the state produced by the corresponding source
execution. Row satisfaction and VM acceptance are independent premises. -/
theorem lower_checked_guarded_candidate_state
    (state : List StateDecl) (sourceEntry : Entrypoint) (rewrites : Zkir.Rewrites)
    (expected : Native.Expected) (plan : Impact.Plan)
    (ctx : EvalContext) (hash : Hash) (implementation : HashAgreement ctx hash)
    (values : EvalEnv) (assignment : Assignment)
    (bytes : ArtifactBytes.Bytes) (json : Json) (rows : List GuardedScalarRows.Row)
    (initial : LedgerState) (slots : List NativeState.Slot) (final : NativeState.Machine)
    (emitted : Zkir.lowerEntrypoint state sourceEntry rewrites = .ok json)
    (artifact : GuardedZkirArtifact.check bytes json = .ok rows)
    (ordinary : ∀ row ∈ rows, GuardedImpactTranscript.ordinaryHolds hash assignment row)
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
    (checked : runCheckedCandidates ctx sourceEntry plan values assignment slots = some final) :
    (GuardedZkirArtifact.decodeBytes bytes).map GuardedZkirArtifact.View.rows = .ok rows ∧
    ∃ (result candidates : EvalEnv) (operations : List NativeState.Op)
        (finalTypes : TypeEnv) (finalEnv : EvalEnv) (finalState : LedgerState)
        (finalSlots : List NativeState.Slot) (finalReads : List NativeState.Cell),
      sourceEntry.circuit.run ctx values = .ok result ∧
      decodeReads (plan.reads.drop (Impact.publicInputReadCount sourceEntry.circuit.inputs))
        assignment = .ok candidates ∧
      GuardedPlanExecution.evalPlan ctx ((result ++ values) ++ candidates) plan = .ok operations ∧
      NativeState.run operations ⟨[.vector slots], []⟩ = some final ∧
      runEffectsWithGuardsAndEnv ctx sourceEntry.effects sourceEntry.effectGuards
        (result ++ values) initial = .ok (finalEnv, finalState) ∧
      GenericStateEncoding.encodeState state finalState = some finalSlots ∧
      final = ⟨[.vector finalSlots], finalReads⟩ ∧
      AgreesOnTypes finalTypes finalEnv ((result ++ values) ++ candidates) ∧
      GenericStateEffectValidation.GuardValidatedEffects state (Passes.pruneEntrypoint sourceEntry)
        (GenericStateEffectValidation.initialEffectTypeEnv (Passes.pruneEntrypoint sourceEntry))
        sourceEntry.effects.zipIdx finalTypes ∧
      ∀ result ∈ sourceEntry.returns,
        result.value.validate GenericStateEffectValidation.stateEffectCaps finalTypes = .ok () := by
  let ep := Passes.pruneEntrypoint sourceEntry
  have scope := ScalarGuardedActivityAdmission.lower_guarded_scalar_read_scope
    state ep plan planAccepted effects
  have scalarEffects := ScalarGuardedActivityAdmission.scalar_state_effects_of_admitted
    state sourceEntry.effects effects
  have operands (effect : Effect) (present : effect ∈ sourceEntry.effects) :=
    GuardedScalarOperands.of_admitted (effects effect present)
  have readGuards (readSpec : Impact.Read)
      (present : readSpec ∈ plan.reads.drop (Impact.publicInputReadCount ep.circuit.inputs))
      (condition : Expr .bool) (selected : readSpec.guard = some condition) :
      ScalarExpression condition :=
    guardsAdmitted condition (GuardedReadDescriptorTrace.lower_post_public_read_guard_mem
      state ep plan planAccepted scope readSpec present condition selected)
  obtain ⟨exactRows, schema, compatible, plainReads, distinctReads,
      _, frame, result, candidates, normalized, executed, decoded,
      base, _, fresh, aliases, _⟩ :=
    GuardedScalarCandidateSchedule.lower_checked_guarded_source_frame state sourceEntry rewrites
      expected plan ctx hash implementation values assignment bytes json rows emitted artifact
      ordinary planAccepted expectedAccepted inputs admitted effects
  have sourceRun : sourceEntry.circuit.run ctx values = .ok result := by
    simpa only [ep, Passes.pruneEntrypoint, Passes.pruneCircuit_run] using executed
  obtain ⟨_, actualCandidates, actualDecoded, _, readFacts, assertions, inactiveZero, _⟩ :=
    GuardedZkirPlanSoundness.lowerEntrypoint_guardedArtifactRequirements
      state sourceEntry rewrites ctx hash implementation assignment bytes json rows plan expected
      frame (result ++ values) initial emitted artifact ordinary planAccepted expectedAccepted
      schema normalized base scope plainReads fresh distinctReads aliases readGuards guardAdmission
  have sameCandidates := Except.ok.inj (actualDecoded.symm.trans decoded)
  subst actualCandidates
  obtain ⟨operations, evaluated, checkedRun⟩ :=
    run_of_checked_candidates ctx sourceEntry plan values assignment slots result candidates final
      sourceRun decoded checked
  have initialAgreement := GenericStatePrefixEnvironment.initial_from_typed hash assignment
    frame.1 (GenericStateEffectValidation.initialEffectTypeEnv ep) (result ++ values)
    candidates base
  obtain ⟨finalTypes, finalEnv, finalState, finalSlots, finalReads, effectsRan, finalEncoded,
      finalShape, agree, validated, returns⟩ :=
    GuardedStateEffectFold.lower_checked_guarded_effects ctx state ep plan (result ++ values)
      candidates assignment initial slots operations final planAccepted scalarEffects scope operands
      compatible decoded distinctReads readFacts inactiveZero assertions initialAgreement
      encoded distinct stateBound implementation.modulus evaluated checkedRun
  exact ⟨exactRows, result, candidates, operations, finalTypes, finalEnv, finalState, finalSlots,
    finalReads, sourceRun, decoded, evaluated, checkedRun, effectsRan, finalEncoded, finalShape,
    agree, validated, returns⟩

end Noctium.Verification.GuardedScalarCandidateState
