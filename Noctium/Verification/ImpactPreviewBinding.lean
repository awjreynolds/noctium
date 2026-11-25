import Noctium.Verification.ImpactBindingIdentity
import Noctium.Verification.ImpactBindingNumber
import Noctium.Verification.ImpactCallStatement

namespace Noctium.Verification.ImpactPreviewBinding

open ImpactBindingIdentity ImpactBindingNumber ImpactNoopPreview ImpactCallPreview

/-- Public runtime metadata retained by preview. Preview supplies the new
compute time. The other costs and effects come from the ledger transcript. -/
structure PartitionMetadata where
  readTime : Nat
  bytesWritten : Nat
  bytesDeleted : Nat
  effects : ByteArray

/-- Raw call identity and ledger metadata. Effects and parent commitment
bytes come from the pinned ledger serializers. -/
structure Metadata where
  address : ByteArray
  entryPoint : ByteArray
  guaranteed : Option PartitionMetadata
  fallible : Option PartitionMetadata
  parentPedersen : ByteArray

private def serializePart (part : Option (Transcript (PreviewEntry α)))
    (metadata : Option PartitionMetadata) : Option (Option (ByteArray × ByteArray)) :=
  match part, metadata with
  | none, none => some none
  | some part, some metadata => do
      let gas ← encodeRunningCost ⟨metadata.readTime, part.computeTime,
        metadata.bytesWritten, metadata.bytesDeleted⟩
      pure (some (gas, metadata.effects))
  | _, _ => none

/-- The guaranteed count covers the previewed program, including coalesced
Noops. An absent guaranteed transcript uses zero. -/
def guaranteedLength (call : CallTranscripts (PreviewEntry α)) : Nat :=
  ((call.guaranteed.map Transcript.program).getD []).length

/-- Build the binding preimage inputs from a preview, checking numeric and
identity encodings and exact metadata presence for both partitions. -/
def serialize (metadata : Metadata) (call : CallTranscripts (PreviewEntry α)) :
    Option ImpactBindingInput.SerializedInputs := do
  let address ← encodeAddress metadata.address
  let entryPoint ← encodeEntryPoint metadata.entryPoint
  let guaranteed ← serializePart call.guaranteed metadata.guaranteed
  let fallible ← serializePart call.fallible metadata.fallible
  let defaultGas ← encodeRunningCost ⟨0, 0, 0, 0⟩
  let parent ← encodeParentPedersen metadata.parentPedersen
  let length ← encodeU64 (guaranteedLength call)
  pure {
    address
    entryPoint
    guaranteedGasOrDefault := (guaranteed.map Prod.fst).getD defaultGas
    guaranteedEffects := guaranteed.map Prod.snd
    fallibleTranscript := fallible.map fun (gas, effects) => (ByteArray.mk #[1] ++ gas, effects)
    guaranteedProgramLength := length
    parentPedersen := parent
  }

/-- The serialized length comes from the exact preview, including its Noops. -/
theorem serialize_guaranteedLength (metadata : Metadata)
    (call : CallTranscripts (PreviewEntry α)) {serialized : ImpactBindingInput.SerializedInputs}
    (accepted : serialize metadata call = some serialized) :
    encodeU64 (guaranteedLength call) = some serialized.guaranteedProgramLength := by
  unfold serialize at accepted
  simp only [Bind.bind, Option.bind_eq_some_iff, Pure.pure] at accepted
  obtain ⟨_, _, _, _, _, _, _, _, _, _, _, _, length, encoded, assembled⟩ := accepted
  cases assembled
  exact encoded

/-- A present guaranteed transcript uses the previewed compute time and the
three preserved resource counters in its serialized cost. -/
theorem serialize_guaranteedCost (metadata : Metadata)
    (call : CallTranscripts (PreviewEntry α))
    {part : Transcript (PreviewEntry α)} {supplement : PartitionMetadata}
    {serialized : ImpactBindingInput.SerializedInputs}
    (hasPart : call.guaranteed = some part)
    (hasMetadata : metadata.guaranteed = some supplement)
    (accepted : serialize metadata call = some serialized) :
    encodeRunningCost ⟨supplement.readTime, part.computeTime,
      supplement.bytesWritten, supplement.bytesDeleted⟩ =
      some serialized.guaranteedGasOrDefault ∧
    serialized.guaranteedEffects = some supplement.effects := by
  unfold serialize at accepted
  simp only [Bind.bind, Option.bind_eq_some_iff, Pure.pure] at accepted
  obtain ⟨_, _, _, _, guaranteed, encoded, _, _, _, _, _, _, _, _, assembled⟩ := accepted
  cases assembled
  simp only [serializePart, hasPart, hasMetadata, Bind.bind, Option.bind_eq_some_iff,
    Pure.pure, Option.some.injEq] at encoded
  obtain ⟨gas, costEncoded, rfl⟩ := encoded
  exact ⟨costEncoded, rfl⟩

/-- A present fallible transcript serializes its gas as `Some(cost)` and
leaves the supplied serialized effects separate for the binding preimage. -/
theorem serialize_fallibleCost (metadata : Metadata)
    (call : CallTranscripts (PreviewEntry α))
    {part : Transcript (PreviewEntry α)} {supplement : PartitionMetadata}
    {serialized : ImpactBindingInput.SerializedInputs}
    (hasPart : call.fallible = some part)
    (hasMetadata : metadata.fallible = some supplement)
    (accepted : serialize metadata call = some serialized) :
    ∃ gas, encodeRunningCost ⟨supplement.readTime, part.computeTime,
      supplement.bytesWritten, supplement.bytesDeleted⟩ = some gas ∧
      serialized.fallibleTranscript = some (ByteArray.mk #[1] ++ gas, supplement.effects) := by
  unfold serialize at accepted
  simp only [Bind.bind, Option.bind_eq_some_iff, Pure.pure] at accepted
  obtain ⟨_, _, _, _, _, _, fallible, encoded, _, _, _, _, _, _, assembled⟩ := accepted
  cases assembled
  simp only [serializePart, hasPart, hasMetadata, Bind.bind, Option.bind_eq_some_iff,
    Pure.pure, Option.some.injEq] at encoded
  obtain ⟨gas, costEncoded, rfl⟩ := encoded
  exact ⟨gas, costEncoded, rfl⟩

/-- Construct a statement header from the preview and ledger metadata. -/
def header (metadata : Metadata) (call : CallTranscripts (PreviewEntry α))
    (communication : NativeRelation.Scalar) : Option ImpactCallStatement.Header :=
  (serialize metadata call).map fun bytes =>
    ImpactCallStatement.Header.ofBindingInput bytes communication

end Noctium.Verification.ImpactPreviewBinding
