import Noctium.Verification.ImpactBindingInput
import Noctium.Verification.ImpactCallPreview
import Noctium.Verification.ImpactStatementPayload

namespace Noctium.Verification.ImpactCallStatement

open ImpactCallPreview ImpactNoopPreview ImpactStatementPayload NativeRelation

/-- Pinned ledger cap, including the two fixed header fields. -/
def maxPublicInputs : Nat := 2 ^ 16

/-- The binding digest field and communication commitment supplied by the
ledger. Their cryptographic derivations are outside the field layout model. -/
structure Header where
  bindingInput : Scalar
  communicationsCommitment : Scalar

/-- Construct the header from ledger-serialized binding inputs and the
communication commitment already checked by the caller. -/
def Header.ofBindingInput (inputs : ImpactBindingInput.SerializedInputs)
    (commitment : Scalar) : Header :=
  ⟨ImpactBindingInput.bindingInput inputs, commitment⟩

def partitionEntries (part : Option (Transcript (PreviewEntry α))) :
    List (PreviewEntry α) :=
  (part.map Transcript.program).getD []

/-- Count the statement fields before materializing any Noop padding. -/
def publicInputsLength (encode : α → List Scalar)
    (call : CallTranscripts (PreviewEntry α)) : Nat :=
  let guaranteed := partitionEntries call.guaranteed
  let fallible := partitionEntries call.fallible
  2 + max (payloadWidth encode guaranteed) guaranteed.length +
    max (payloadWidth encode fallible) fallible.length

/-- Pinned contract-call field layout, with the ledger's bound checked before
the guaranteed and fallible payloads are materialized. -/
def publicInputs (encode : α → List Scalar) (header : Header)
    (call : CallTranscripts (PreviewEntry α)) : Option (List Scalar) :=
  if publicInputsLength encode call ≤ maxPublicInputs then
    some ([header.bindingInput, header.communicationsCommitment] ++
      payload encode (partitionEntries call.guaranteed) ++
      payload encode (partitionEntries call.fallible))
  else none

theorem publicInputs_success_iff (encode : α → List Scalar) (header : Header)
    (call : CallTranscripts (PreviewEntry α)) (fields : List Scalar) :
    publicInputs encode header call = some fields ↔
      fields = [header.bindingInput, header.communicationsCommitment] ++
        payload encode (partitionEntries call.guaranteed) ++
        payload encode (partitionEntries call.fallible) ∧
      publicInputsLength encode call ≤ maxPublicInputs := by
  by_cases bounded : publicInputsLength encode call ≤ maxPublicInputs
  · simp [publicInputs, bounded, eq_comm]
  · simp [publicInputs, bounded]

/-- The admission count also bounds the materialized field list, including
malformed empty-field operations for which program length is the larger bound. -/
theorem accepted_length (encode : α → List Scalar) (header : Header)
    (call : CallTranscripts (PreviewEntry α)) {fields : List Scalar}
    (accepted : publicInputs encode header call = some fields) :
    fields.length ≤ maxPublicInputs := by
  obtain ⟨layout, bounded⟩ := (publicInputs_success_iff encode header call fields).mp accepted
  apply Nat.le_trans _ bounded
  rw [layout]
  simp only [List.length_append, List.length_cons, List.length_nil,
    payload_length_eq_payloadWidth, publicInputsLength]
  exact Nat.add_le_add
    (Nat.add_le_add_left (Nat.le_max_left _ _) _)
    (Nat.le_max_left _ _)

theorem rejects_over_limit (encode : α → List Scalar) (header : Header)
    (call : CallTranscripts (PreviewEntry α))
    (over : maxPublicInputs < publicInputsLength encode call) :
    publicInputs encode header call = none := by
  simp [publicInputs, Nat.not_le_of_lt over]

def scheduledPartitionPayload (encode : α → List Scalar)
    (before : Option (Transcript α)) (used : List (Option Nat)) :
    Option (List Scalar) :=
  match before with
  | none => if used.isEmpty then some [] else none
  | some part => scheduledPayload encode part.program used

private theorem partitionPayload_matches (encode : α → List Scalar) (cost : ImpactPreviewGas.CostModel)
    {before : Option (Transcript α)} {after : Option (Transcript (PreviewEntry α))}
    {used : List (Option Nat)} (partAgrees : PartMatches cost before after used) :
    scheduledPartitionPayload encode before used = some (payload encode (partitionEntries after)) := by
  cases before with
  | none =>
      cases after with
      | none =>
          have unused : used = [] := partAgrees
          subst used
          rfl
      | some preview => contradiction
  | some part =>
      cases after with
      | none => contradiction
      | some preview => exact payload_of_previewProgram encode partAgrees.1

/-- Accepted call fields equal the header followed by the guaranteed and
fallible streams selected from the original programs and the exact activity
splits. Skipped fields appear at their scheduled positions. -/
theorem previewCall_publicInputs
    (encode : α → List Scalar) (header : Header) (cost : ImpactPreviewGas.CostModel)
    {before : CallTranscripts α} {after : CallTranscripts (PreviewEntry α)}
    {activity : List (Option Nat)} {fields : List Scalar}
    (previewed : previewCall cost before activity = some after)
    (accepted : publicInputs encode header after = some fields) :
    ∃ guaranteedActivity fallibleActivity,
      guaranteedActivity ++ fallibleActivity = activity ∧
      (do
        let guaranteed ← scheduledPartitionPayload encode before.guaranteed guaranteedActivity
        let fallible ← scheduledPartitionPayload encode before.fallible fallibleActivity
        pure ([header.bindingInput, header.communicationsCommitment] ++ guaranteed ++ fallible)) =
        some fields ∧ fields.length ≤ maxPublicInputs := by
  obtain ⟨guaranteed, fallible, split, first, last, _⟩ :=
    previewCall_sound cost before activity previewed
  have layout := ((publicInputs_success_iff encode header after fields).mp accepted).1
  refine ⟨guaranteed, fallible, split, ?_, accepted_length encode header after accepted⟩
  rw [partitionPayload_matches encode cost first, partitionPayload_matches encode cost last]
  exact congrArg some layout.symm

end Noctium.Verification.ImpactCallStatement
