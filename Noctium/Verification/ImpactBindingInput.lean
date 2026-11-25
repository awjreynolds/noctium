import Noctium.EntryPointHash
import Noctium.Field
import Noctium.ScalarPolicy
import Noctium.Verification.NativeRelation
import Noctium.Verification.ScalarTermMeaning

namespace Noctium.Verification.ImpactBindingInput

open Noctium.Verification.NativeRelation

/-- Components at the serializer boundary used by Midnight's
`ContractCall::binding_input`. Every byte array is the exact output of the named
Rust serialization call, except for the explicit optional transcript cases
below. -/
structure SerializedInputs where
  /-- `Serializable::serialize(&self.address, ...)`. -/
  address : ByteArray
  /-- `Serializable::serialize(&self.entry_point, ...)`. -/
  entryPoint : ByteArray
  /-- Upstream serialization of the guaranteed transcript gas, or of
  `Default::default()` when the guaranteed transcript is absent. -/
  guaranteedGasOrDefault : ByteArray
  /-- `some` contains serialized `t.effects`. `none` uses the native fallback of
  exactly twenty literal zero bytes. -/
  guaranteedEffects : Option ByteArray
  /-- Some contains the serialization of `Some(t.gas)` followed by the
  serialization of `t.effects`. None is encoded as the two literal absence
  discriminants `[0, 0]` from the pinned native implementation. -/
  fallibleTranscript : Option (ByteArray × ByteArray)
  /-- Upstream serialization of the guaranteed program's previewed `u64`
  length, including Noops, or the serialized default length when absent. -/
  guaranteedProgramLength : ByteArray
  /-- `Serializable::serialize(&Into::<Pedersen>::into(binding_com), ...)`. -/
  parentPedersen : ByteArray

/-- The domain bytes prepended by the pinned native implementation. -/
def domain : ByteArray := "midnight:binding-input[v1]".toUTF8

private def twentyZeroBytes : ByteArray :=
  ByteArray.mk ((List.replicate 20 (0 : UInt8)).toArray)

private def oneByte : ByteArray := ByteArray.mk #[1]

private def absentFallibleBytes : ByteArray := ByteArray.mk #[0, 0]

/-- Exact native concatenation after the component serializers have run.
Guaranteed transcript absence preserves the native twenty-zero fallback.
Fallible transcript absence preserves the pinned `(None, None)` bytes `[0, 0]`.
When present, the serialized `Some(gas)` bytes are followed by the explicit
`Some` discriminant and serialized effects. -/
def preimage (inputs : SerializedInputs) : ByteArray :=
  domain ++
    inputs.address ++
    inputs.entryPoint ++
    inputs.guaranteedGasOrDefault ++
    (inputs.guaranteedEffects.getD twentyZeroBytes) ++
    (match inputs.fallibleTranscript with
      | none => absentFallibleBytes
      | some (someGas, effects) => someGas ++ oneByte ++ effects) ++
    inputs.guaranteedProgramLength ++
    inputs.parentPedersen

/-- SHA-256 output bytes in FIPS output order. -/
def digest (inputs : SerializedInputs) : List UInt8 :=
  EntryPointHash.sha256Bytes (preimage inputs)

/-- The first 31 digest bytes are interpreted in little-endian order, exactly
as in `Fr::from_le_bytes(&digest[..31])`. -/
def fieldValueNat (inputs : SerializedInputs) : Nat :=
  Backend.Native.littleEndian ((digest inputs).take 31 |>.map UInt8.toNat)

theorem fieldValueNat_lt_modulus (inputs : SerializedInputs) :
    fieldValueNat inputs < Field.modulus := by
  let bytes := (digest inputs).take 31 |>.map UInt8.toNat
  have byteBound : ∀ value ∈ bytes, value < 256 := by
    intro value member
    obtain ⟨byte, _, rfl⟩ := List.mem_map.mp member
    exact byte.toFin.isLt
  have inRange := ScalarTermMeaning.littleEndian_lt_pow_of_bytes bytes byteBound
  have lengthBound : bytes.length ≤ 31 := by
    simp [bytes]
    omega
  have radixBound : 256 ^ bytes.length ≤ 256 ^ 31 :=
    Nat.pow_le_pow_right (by decide) lengthBound
  have radix : 256 ^ 31 = ScalarPolicy.maxUint + 1 := by decide
  have belowMax : Backend.Native.littleEndian bytes < ScalarPolicy.maxUint + 1 := by
    rw [← radix]
    exact Nat.lt_of_lt_of_le inRange radixBound
  have atMostMax : Backend.Native.littleEndian bytes ≤ ScalarPolicy.maxUint := by
    omega
  exact Nat.lt_of_le_of_lt atMostMax ScalarPolicy.maxUint_lt_native

/-- The exact scalar binding input produced by the pinned Rust function. The
31-byte truncation always yields a canonical little-endian BLS12-381 scalar. -/
def bindingInput (inputs : SerializedInputs) : Scalar :=
  ⟨fieldValueNat inputs, fieldValueNat_lt_modulus inputs⟩

end Noctium.Verification.ImpactBindingInput
