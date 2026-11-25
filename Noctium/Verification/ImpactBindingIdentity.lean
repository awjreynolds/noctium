import Noctium.Verification.ImpactBindingNumber

namespace Noctium.Verification.ImpactBindingIdentity

/-- `ContractAddress` wraps a fixed 32-byte `HashOutput`. -/
def contractAddressWidth : Nat := 32

/-- A `Vec<u8>` length is serialized as `u32`, so modeled entrypoint lengths
must fit in that type. -/
def entryPointLengthLimit : Nat := 2 ^ 32

/-- Check a serialized 32-byte value without interpreting its contents. -/
def encodeFixed32 (bytes : ByteArray) : Option ByteArray :=
  if bytes.size = contractAddressWidth then some bytes else none

/-- Keep the fixed-width address bytes exactly as supplied. -/
def encodeAddress (address : ByteArray) : Option ByteArray :=
  encodeFixed32 address

/-- Keep the parent's Pedersen encoding when it has the pinned 32-byte shape.
This does not check that the bytes encode a valid group point. -/
def encodeParentPedersen (pedersen : ByteArray) : Option ByteArray :=
  encodeFixed32 pedersen

/-- Serialize `EntryPointBuf(Vec<u8>)` as its SCALE-compact `u32` length,
followed by the exact entrypoint bytes. The `u64` helper has the same SCALE
encoding over this checked `u32` range. -/
def encodeEntryPoint (entryPoint : ByteArray) : Option ByteArray :=
  if entryPoint.size < entryPointLengthLimit then
    (ImpactBindingNumber.encodeU64 entryPoint.size).map (· ++ entryPoint)
  else none

theorem encodeAddress_success_iff (address encoded : ByteArray) :
    encodeAddress address = some encoded ↔
      address.size = contractAddressWidth ∧ address = encoded := by
  simp [encodeAddress, encodeFixed32]

theorem encodeAddress_success_size {address encoded : ByteArray}
    (success : encodeAddress address = some encoded) :
    encoded.size = contractAddressWidth := by
  obtain ⟨width, same⟩ := (encodeAddress_success_iff address encoded).mp success
  rw [← same]
  exact width

theorem encodeParentPedersen_success_iff (pedersen encoded : ByteArray) :
    encodeParentPedersen pedersen = some encoded ↔
      pedersen.size = contractAddressWidth ∧ pedersen = encoded := by
  simp [encodeParentPedersen, encodeFixed32]

theorem encodeParentPedersen_success_size {pedersen encoded : ByteArray}
    (success : encodeParentPedersen pedersen = some encoded) :
    encoded.size = contractAddressWidth := by
  obtain ⟨width, same⟩ :=
    (encodeParentPedersen_success_iff pedersen encoded).mp success
  rw [← same]
  exact width

theorem encodeEntryPoint_success_iff (entryPoint encoded : ByteArray) :
    encodeEntryPoint entryPoint = some encoded ↔
      entryPoint.size < entryPointLengthLimit ∧
      ∃ lengthPrefix,
        ImpactBindingNumber.encodeU64 entryPoint.size = some lengthPrefix ∧
        encoded = lengthPrefix ++ entryPoint := by
  constructor
  · intro success
    by_cases bounded : entryPoint.size < entryPointLengthLimit
    · simp [encodeEntryPoint, bounded] at success
      cases encodedLengthEq : ImpactBindingNumber.encodeU64 entryPoint.size with
      | none => simp [encodedLengthEq] at success
      | some lengthPrefix =>
        have outputEq : lengthPrefix ++ entryPoint = encoded := by
          simpa [encodedLengthEq] using success
        exact ⟨bounded, lengthPrefix, rfl, outputEq.symm⟩
    · simp [encodeEntryPoint, bounded] at success
  · rintro ⟨bounded, lengthPrefix, lengthPrefixEq, outputEq⟩
    simp [encodeEntryPoint, bounded, lengthPrefixEq, outputEq]

/-- Every modeled `EntryPointBuf` length below the `u32` bound has an encoding. -/
theorem encodeEntryPoint_succeeds (entryPoint : ByteArray)
    (bounded : entryPoint.size < entryPointLengthLimit) :
    ∃ encoded, encodeEntryPoint entryPoint = some encoded := by
  have bound64 : entryPoint.size < ImpactBindingNumber.u64Limit := by
    exact Nat.lt_trans bounded (by decide)
  have prefixExists :=
    ImpactBindingNumber.encodeU64_isSome_of_lt entryPoint.size bound64
  cases encodedLengthEq : ImpactBindingNumber.encodeU64 entryPoint.size with
  | none => simp [encodedLengthEq] at prefixExists
  | some lengthPrefix =>
    refine ⟨lengthPrefix ++ entryPoint, ?_⟩
    simp [encodeEntryPoint, bounded, encodedLengthEq]

/-- Successful entrypoint serialization consists of the length prefix and all
raw entrypoint bytes, with no truncation or padding. -/
theorem encodeEntryPoint_success_size {entryPoint encoded : ByteArray}
    (success : encodeEntryPoint entryPoint = some encoded) :
    encoded.size =
      ImpactBindingNumber.u64CompactSize entryPoint.size + entryPoint.size := by
  obtain ⟨bounded, lengthPrefix, lengthPrefixEq, outputEq⟩ :=
    (encodeEntryPoint_success_iff entryPoint encoded).mp success
  have bound64 : entryPoint.size < ImpactBindingNumber.u64Limit := by
    exact Nat.lt_trans bounded (by decide)
  have prefixSize :
      lengthPrefix.size = ImpactBindingNumber.u64CompactSize entryPoint.size := by
    have sizeEquation := ImpactBindingNumber.encodeU64_size entryPoint.size bound64
    rw [lengthPrefixEq] at sizeEquation
    simpa using sizeEquation
  rw [outputEq, ByteArray.size_append, prefixSize]

end Noctium.Verification.ImpactBindingIdentity
