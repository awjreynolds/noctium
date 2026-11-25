import Noctium.Verification.GuardedInputTranscript
import Noctium.Verification.GuardedZkirArtifact
import Noctium.Verification.ImpactCallStatement

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

end Noctium.Verification.GuardedStatementConsumption
