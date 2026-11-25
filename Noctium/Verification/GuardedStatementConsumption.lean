import Noctium.Verification.GuardedInputTranscript
import Noctium.Verification.GuardedZkirArtifact
import Noctium.Verification.ImpactCallStatement
import Noctium.Verification.ImpactStatementPayload
import Noctium.Verification.ImpactStatementScalar

namespace Noctium.Verification.GuardedStatementConsumption

open NativeRelation
open Noctium.Verification.GuardedImpactObservation
open Noctium.Verification.GuardedImpactTranscript
open Noctium.Verification.GuardedInputTranscript
open Noctium.Verification.GuardedScalarInput
open Noctium.Verification.GuardedScalarRows
open Noctium.Verification.ImpactCallStatement

/-- The public Impact input stream and guarded public read output stream
consumed by the pinned ZKIR preprocessor. -/
structure Inputs where
  transcriptInputs : List Scalar
  transcriptOutputs : List Scalar

/-- The public instance produced by the call header and ordered Impact rows.
Activity records whether each Impact row consumes transcript inputs. -/
structure Projection where
  fields : List Scalar
  activity : List (Option Nat)
  deriving Repr, DecidableEq

/-- Activity schedule for ordered Impact observations. Active observations
consume their payload. Inactive observations retain a zero-padded width. -/
def observationActivity (observations : List Observation) : List (Option Nat) :=
  observations.map fun observation =>
    if observation.active then none else some observation.payload.length

/-- Public fields after the two call header fields, preserving the fixed width
of each active or inactive Impact row. -/
def observationFields (observations : List Observation) : List Scalar :=
  observations.flatMap Observation.payload

/-- Project checked guarded rows through the pinned scalar preprocessing
contract. Impact inputs and public read outputs are independently consumed.
This models statement projection, not the cryptographic authentication of the
commitment or the circuit relation. -/
def fromRows (assignment : Assignment) (rows : List GuardedScalarRows.Row)
    (header : ImpactCallStatement.Header) (inputs : Inputs) : Option Projection := do
  let observations ← emittedObservations assignment rows
  let reads := emittedPublicReads assignment rows
  let consumedReads := consumeReads (reads.map ReadObservation.guard) inputs.transcriptOutputs
  if consumedReads != some (reads.map ReadObservation.value, []) then none
  else if inputs.transcriptInputs != activePayloads observations then none
  else
    pure {
      fields := [header.bindingInput, header.communicationsCommitment] ++
        observationFields observations
      activity := observationActivity observations
    }

/-- Decode exact ZKIR bytes and project their guarded rows only when the
artifact declares the communications commitment used by the call header. -/
def fromArtifact (bytes : ArtifactBytes.Bytes) (assignment : Assignment)
    (header : ImpactCallStatement.Header) (inputs : Inputs) : Option Projection := do
  let view ← (GuardedZkirArtifact.decodeBytes bytes).toOption
  if view.header.communicationsCommitment then
    fromRows assignment view.rows header inputs
  else
    none

/-- The projection accepts exactly the ordered streams and public fields of
the observations, including zero-valued inactive reads and their activity. -/
theorem fromRows_iff (assignment : Assignment) (rows : List GuardedScalarRows.Row)
    (header : ImpactCallStatement.Header) (inputs : Inputs) (projection : Projection) :
    fromRows assignment rows header inputs = some projection ↔ ∃ observations,
      emittedObservations assignment rows = some observations ∧
      inputs.transcriptInputs = activePayloads observations ∧
      inputs.transcriptOutputs = activeReadValues (emittedPublicReads assignment rows) ∧
      (∀ read ∈ emittedPublicReads assignment rows,
        read.guard = one ∨ (read.guard = zero ∧ read.value = zero)) ∧
      projection.fields =
        [header.bindingInput, header.communicationsCommitment] ++ observationFields observations ∧
      projection.activity = observationActivity observations := by
  let reads := emittedPublicReads assignment rows
  let consumedReads := consumeReads (reads.map ReadObservation.guard) inputs.transcriptOutputs
  have readContract := consumeReads_iff reads inputs.transcriptOutputs []
  constructor
  · intro accepted
    unfold fromRows at accepted
    cases observationsResult : emittedObservations assignment rows with
    | none => simp [observationsResult] at accepted
    | some observations =>
      by_cases readsAccepted : consumedReads = some (reads.map ReadObservation.value, [])
      · by_cases impactAccepted : inputs.transcriptInputs = activePayloads observations
        · simp [observationsResult, reads, consumedReads, readsAccepted, impactAccepted] at accepted
          cases accepted
          have readsMeaning := readContract.mp readsAccepted
          exact ⟨observations, rfl, impactAccepted,
            by simpa [reads] using readsMeaning.1,
            by simpa [reads] using readsMeaning.2, rfl, rfl⟩
        · simp [observationsResult, reads, consumedReads, readsAccepted, impactAccepted] at accepted
      · simp [observationsResult, reads, consumedReads, readsAccepted] at accepted
  · rintro ⟨observations, observed, impactStream, readStream, readDefaults, fields, activity⟩
    have readsAccepted := readContract.mpr ⟨by simpa [reads] using readStream, readDefaults⟩
    cases projection with
    | mk projectedFields projectedActivity =>
      cases fields
      cases activity
      simp [fromRows, observed, reads, readsAccepted, impactStream, observationActivity]

/-- Successful byte projection identifies the exact parsed artifact view,
requires its communications commitment field, and projects its ordered rows. -/
theorem fromArtifact_sound (bytes : ArtifactBytes.Bytes) (assignment : Assignment)
    (header : ImpactCallStatement.Header) (inputs : Inputs) (projection : Projection)
    (accepted : fromArtifact bytes assignment header inputs = some projection) :
    ∃ view,
      GuardedZkirArtifact.decodeBytes bytes = .ok view ∧
      view.header.communicationsCommitment = Bool.true ∧
      fromRows assignment view.rows header inputs = some projection := by
  unfold fromArtifact at accepted
  cases decoded : GuardedZkirArtifact.decodeBytes bytes with
  | error message =>
    simp [decoded, Except.toOption] at accepted
  | ok view =>
    simp only [decoded, Except.toOption] at accepted
    by_cases committed : view.header.communicationsCommitment
    · simp [committed] at accepted
      exact ⟨view, rfl, committed, accepted⟩
    · simp [committed] at accepted

private theorem observeImpact_inactive_zero (guard : Scalar) (values : List Scalar)
    (observation : Observation)
    (observed : observeImpact guard values = some observation)
    (inactive : observation.active = false) :
    observation.payload = List.replicate observation.payload.length zero := by
  by_cases isOne : guard = one
  · simp [observeImpact, isOne] at observed
    cases observed
    simp at inactive
  · by_cases isZero : guard = zero
    · simp [observeImpact, isZero] at observed
      cases observed
      simp
    · simp [observeImpact, isOne, isZero] at observed

/-- Emitted inactive rows retain their width and contain only zero fields. -/
theorem emittedObservations_inactive_zero (witness : Assignment) (rows : List Row)
    {observations : List Observation}
    (observed : emittedObservations witness rows = some observations) :
    ∀ obs ∈ observations, obs.active = false →
      obs.payload = List.replicate obs.payload.length zero := by
  induction rows generalizing observations with
  | nil =>
    simp [emittedObservations] at observed
    subst observations
    intro obs member
    simp at member
  | cons row rest ih =>
    cases row with
    | strict instruction =>
      simpa [emittedObservations] using
        (ih (observations := observations) observed)
    | publicInput output guard =>
      simpa [emittedObservations] using
        (ih (observations := observations) observed)
    | impact guard values =>
      simp only [emittedObservations] at observed
      cases head : observeImpact (guard.read witness) (values.map (·.read witness)) with
      | none => simp [head] at observed
      | some observation =>
        cases tail : emittedObservations witness rest with
        | none => simp [head, tail] at observed
        | some tailObservations =>
          simp [head, tail] at observed
          cases observed
          intro obs member inactive
          simp only [List.mem_cons] at member
          rcases member with same | member
          · subst obs
            exact observeImpact_inactive_zero _ _ _ head inactive
          · exact ih (observations := tailObservations) tail obs member inactive

private theorem flatMap_eq_of_equal_widths {α β : Type}
    (encode : α → List β) (operations : List α) (payloads : List (List β))
    (flat : operations.flatMap encode = payloads.flatten)
    (widths : operations.map (fun operation => (encode operation).length) =
      payloads.map List.length) :
    operations.map encode = payloads := by
  induction operations generalizing payloads with
  | nil =>
    cases payloads with
    | nil => rfl
    | cons payload rest => simp at widths
  | cons operation rest ih =>
    cases payloads with
    | nil => simp at widths
    | cons payload payloadRest =>
      simp only [List.map_cons, List.cons.injEq] at widths
      obtain ⟨headWidth, tailWidths⟩ := widths
      have flatParts : encode operation ++ rest.flatMap encode =
          payload ++ payloadRest.flatten := by
        simpa only [List.flatMap_cons, List.flatten_cons] using flat
      have sameHead : encode operation = payload := by
        calc
          encode operation = List.take (encode operation).length
              (encode operation ++ rest.flatMap encode) := by rw [List.take_left]
          _ = List.take (encode operation).length
              (payload ++ payloadRest.flatten) := by rw [flatParts]
          _ = List.take (encode operation).length payload :=
            List.take_append_of_le_length (by omega)
          _ = payload := by rw [headWidth, List.take_length]
      have sameTail : rest.flatMap encode = payloadRest.flatten := by
        have cancel : encode operation ++ rest.flatMap encode =
            encode operation ++ payloadRest.flatten := by
          simpa [sameHead] using flatParts
        exact List.append_cancel_left cancel
      have tailMap := ih payloadRest sameTail tailWidths
      simp [sameHead, tailMap]

private theorem scheduledPayload_aligned (encode : α → List Scalar)
    (operations : List α) (observations : List Observation)
    (aligned : operations.map encode =
      (observations.filter (·.active)).map Observation.payload)
    (inactiveZero : ∀ obs ∈ observations, obs.active = false →
      obs.payload = List.replicate obs.payload.length zero) :
    ImpactStatementPayload.scheduledPayload encode operations
        (observationActivity observations) = some (observationFields observations) := by
  induction observations generalizing operations with
  | nil =>
    cases operations with
    | nil => rfl
    | cons operation rest => simp at aligned
  | cons observation rest ih =>
    cases observation with
    | mk active payload =>
      cases active with
      | true =>
        cases operations with
        | nil => simp at aligned
        | cons operation restOperations =>
          simp at aligned
          obtain ⟨head, tail⟩ := aligned
          have restResult := ih restOperations tail
            (by
              intro obs member inactive
              exact inactiveZero obs (by simp [member]) inactive)
          simpa [ImpactStatementPayload.scheduledPayload, observationActivity,
            observationFields, head] using restResult
      | false =>
        have restAligned : operations.map encode =
            (rest.filter (·.active)).map Observation.payload := by
          simpa [List.filter_cons] using aligned
        have restResult := ih operations restAligned
          (by
            intro obs member inactive
            exact inactiveZero obs (by simp [member]) inactive)
        have zeroPayload := inactiveZero ⟨false, payload⟩ (by simp) rfl
        change ImpactStatementPayload.scheduledPayload encode operations
            (some payload.length :: observationActivity rest) =
          some (payload ++ observationFields rest)
        cases operations with
        | nil =>
          rw [ImpactStatementPayload.scheduledPayload.eq_def]
          dsimp
          rw [restResult]
          simp [observationFields]
          exact zeroPayload.symm
        | cons operation restOperations =>
          rw [ImpactStatementPayload.scheduledPayload.eq_def]
          dsimp
          rw [restResult]
          simp [observationFields]
          exact zeroPayload.symm

private theorem activePayloads_filter (observations : List Observation) :
    activePayloads observations =
      ((observations.filter (·.active)).map Observation.payload).flatten := by
  induction observations with
  | nil => rfl
  | cons observation rest ih =>
    cases observation with
    | mk active payload =>
      change List.flatMap activePayload (⟨active, payload⟩ :: rest) =
        ((List.filter (·.active) (⟨active, payload⟩ :: rest)).map
          Observation.payload).flatten
      cases active with
      | false =>
        simp [List.flatMap_cons, activePayload]
        change activePayloads rest =
          ((List.filter (·.active) rest).map Observation.payload).flatten
        exact ih
      | true =>
        simp [List.flatMap_cons, activePayload]
        change activePayloads rest =
          ((List.filter (·.active) rest).map Observation.payload).flatten
        exact ih

/-- Matching operation field widths recover each active observation payload
from the ordered flattened stream, then schedule inactive rows as zero padding. -/
theorem scheduledPayload_of_observations (operations : List NativeState.Op)
    (observations : List Observation)
    (fields : operations.flatMap ImpactStatementScalar.opFields =
      activePayloads observations)
    (widths : operations.map
      (fun operation => (ImpactStatementScalar.opFields operation).length) =
      (observations.filter (·.active)).map (fun row => row.payload.length))
    (inactiveZero : ∀ obs ∈ observations, obs.active = false →
      obs.payload = List.replicate obs.payload.length zero) :
    ImpactStatementPayload.scheduledPayload ImpactStatementScalar.opFields operations
        (observationActivity observations) = some (observationFields observations) := by
  apply scheduledPayload_aligned
  · apply flatMap_eq_of_equal_widths ImpactStatementScalar.opFields operations
        ((observations.filter (·.active)).map Observation.payload)
    · rw [activePayloads_filter] at fields
      exact fields
    · simpa [List.map_map, Function.comp_def] using widths
  · exact inactiveZero

end Noctium.Verification.GuardedStatementConsumption
