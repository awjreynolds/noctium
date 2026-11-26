import Noctium.Verification.GuardedScalarCandidateState
import Noctium.Verification.GuardedNativeInsertDepth
import Noctium.Verification.GuardedStatementConsumption
import Noctium.Verification.NativeStateReadTape
import Noctium.Verification.ScalarCellPublicFields
import Noctium.Verification.ScalarPlanInsertDepth

namespace Noctium.Verification.GuardedScalarCandidateTranscript

open Lean Backend NativeRelation ScalarNormalization
open GenericStateCircuitParts
open GenericStateInputValues (decodeReads)
open GuardedImpactObservation GuardedImpactTranscript GuardedInputTranscript
open GuardedScalarInput GuardedStatementConsumption
open GuardedScalarCandidateState (runCheckedCandidates)
open ScalarGuardedPlanAdmission (ScalarEffect)

/-- The exact active operations of a checked guarded call determine the Impact
input fields and the aligned read tape of the same modeled VM result. The
artifact then consumes both streams exactly when its public read rows match
that tape and all inactive read rows have canonical zero values. -/
theorem lower_checked_guarded_vm_transcript
    (state : List StateDecl) (sourceEntry : Entrypoint) (rewrites : Zkir.Rewrites)
    (expected : Native.Expected) (plan : Impact.Plan)
    (ctx : EvalContext) (hash : Hash) (implementation : HashAgreement ctx hash)
    (values : EvalEnv) (assignment : Assignment)
    (bytes : ArtifactBytes.Bytes) (json : Json) (rows : List GuardedScalarRows.Row)
    (slots : List NativeState.Slot) (final : NativeState.Machine)
    (emitted : Zkir.lowerEntrypoint state sourceEntry rewrites = .ok json)
    (artifact : GuardedZkirArtifact.check bytes json = .ok rows)
    (ordinary : ∀ row ∈ rows, ordinaryHolds hash assignment row)
    (planAccepted : Impact.lower state (Passes.pruneEntrypoint sourceEntry) = .ok plan)
    (expectedAccepted :
      Native.expectedEntrypoint state (Passes.pruneEntrypoint sourceEntry) = .ok expected)
    (inputs : CanonicalInputs sourceEntry.circuit values assignment)
    (admitted : ScalarCircuitAdmission sourceEntry.circuit)
    (effects : ∀ effect ∈ sourceEntry.effects, ScalarEffect state effect)
    (guardsAdmitted : ∀ condition, some condition ∈ sourceEntry.effectGuards →
      ScalarExpression condition)
    (checked : runCheckedCandidates ctx sourceEntry plan values assignment slots = some final) :
    (GuardedZkirArtifact.decodeBytes bytes).map GuardedZkirArtifact.View.rows = .ok rows ∧
    ∃ (result candidates : EvalEnv) (operations : List NativeState.Op)
        (observations : List Observation),
      sourceEntry.circuit.run ctx values = .ok result ∧
      decodeReads (plan.reads.drop (Impact.publicInputReadCount sourceEntry.circuit.inputs))
        assignment = .ok candidates ∧
      GuardedPlanExecution.evalPlan ctx ((result ++ values) ++ candidates) plan = .ok operations ∧
      NativeState.run operations ⟨[.vector slots], []⟩ = some final ∧
      final.reads = NativeStateReadTape.expectedCells operations ∧
      emittedObservations assignment rows = some observations ∧
      operations.map ImpactStatementScalar.opFields =
        (observations.filter (·.active)).map (·.payload) ∧
      (consumeArtifact bytes assignment
          ⟨operations.flatMap ImpactStatementScalar.opFields, final.reads.map NativeState.Cell.value⟩ =
            some observations ↔
        final.reads.map NativeState.Cell.value = activeReadValues (emittedPublicReads assignment rows) ∧
        ∀ publicRead ∈ emittedPublicReads assignment rows,
          publicRead.guard = one ∨ (publicRead.guard = zero ∧ publicRead.value = zero)) := by
  obtain ⟨exactRows, _, result, candidates, observations, operations,
      _, executed, readDecoded, _, observed, evaluated, groups⟩ :=
    GuardedScalarCandidateSchedule.lower_checked_guarded_candidate_schedule
      state sourceEntry rewrites expected plan ctx hash implementation values assignment
      bytes json rows emitted artifact ordinary planAccepted expectedAccepted inputs admitted
      effects guardsAdmitted
  have run : NativeState.run operations ⟨[.vector slots], []⟩ = some final := by
    simpa [runCheckedCandidates, executed, readDecoded, evaluated, Except.toOption,
      -List.append_assoc] using checked
  have ledgerReads : final.reads = NativeStateReadTape.expectedCells operations := by
    simpa only [List.nil_append] using NativeStateReadTape.run_reads run
  have compatible := ScalarCellPublicFields.canonical_inputs_scalar_compatible
    sourceEntry.circuit values assignment inputs
  have planInserts := ScalarPlanInsertDepth.lower_inserts_fit state
    (Passes.pruneEntrypoint sourceEntry) plan planAccepted compatible effects
  have activeInserts := GuardedNativeInsertDepth.evalPlan_inserts_fit
    ctx ((result ++ values) ++ candidates) plan operations evaluated planInserts
  have fieldGroups : operations.map ImpactStatementScalar.opFields =
      (observations.filter (·.active)).map (·.payload) := by
    rw [← groups, NativeState.groups]
    apply List.map_congr_left
    intro operation present
    apply ImpactStatementScalar.opFields_eq_nativeFields
    cases operation <;> try trivial
    case «insert» depth => exact activeInserts depth present
  have fields : operations.flatMap ImpactStatementScalar.opFields =
      activePayloads observations := by
    rw [List.flatMap_def, fieldGroups, activePayloads_filter]
  obtain ⟨view, bytesDecoded, exactViewRows, committed⟩ :=
    GuardedZkirArtifact.check_lowerEntrypoint_header emitted artifact
  refine ⟨exactRows, result, candidates, operations, observations, executed, readDecoded,
    evaluated, run, ledgerReads, observed, fieldGroups, ?_⟩
  let streams : GuardedStatementConsumption.Inputs :=
    ⟨operations.flatMap ImpactStatementScalar.opFields, final.reads.map NativeState.Cell.value⟩
  change consumeArtifact bytes assignment streams = some observations ↔ _
  have consumption : consumeArtifact bytes assignment streams =
      consumeRows assignment rows streams := by
    simp [consumeArtifact, bytesDecoded, committed, exactViewRows, Except.toOption]
  rw [consumption, consumeRows_iff]
  exact ⟨fun accepted => accepted.2.2, fun reads => ⟨observed, fields, reads⟩⟩

end Noctium.Verification.GuardedScalarCandidateTranscript
