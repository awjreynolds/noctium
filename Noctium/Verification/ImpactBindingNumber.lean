/- Numeric encodings used by Midnight's impact binding preimage.

At midnight-ledger commit `a2b30128ca4b660b73a068e29b56b48ede8c9a74`,
`Serializable for u64` uses `via_scale!`, which encodes a `ScaleBigInt` in
SCALE compact form. `CostDuration` serializes transparently through its inner
`u64`, and `RunningCost` serializes its fields in declaration order. -/
namespace Noctium.Verification.ImpactBindingNumber

/-- Exclusive upper bound for values representable by Rust `u64`. -/
def u64Limit : Nat := 2 ^ 64

private def littleEndianBytes (number : Nat) : Nat → List Nat
  | 0 => []
  | width + 1 => number % 256 :: littleEndianBytes (number / 256) width

private def scaleNBytes (number width : Nat) : List UInt8 :=
  UInt8.ofNat ((width - 4) * 4 + 3) ::
    (littleEndianBytes number width).map UInt8.ofNat

/-- The exact compact SCALE byte sequence used by the pinned `u64` serializer.
For inputs below `2^64`, the branches correspond to 1, 2, 4, or 5–9 encoded
bytes, including the SCALE mode marker. -/
def u64CompactBytes (number : Nat) : List UInt8 :=
  if number < 2 ^ 6 then
    [UInt8.ofNat (number * 4)]
  else if number < 2 ^ 14 then
    [UInt8.ofNat ((number % 64) * 4 + 1), UInt8.ofNat (number / 64)]
  else if number < 2 ^ 30 then
    (littleEndianBytes (number * 4 + 2) 4).map UInt8.ofNat
  else if number < 2 ^ 32 then
    scaleNBytes number 4
  else if number < 2 ^ 40 then
    scaleNBytes number 5
  else if number < 2 ^ 48 then
    scaleNBytes number 6
  else if number < 2 ^ 56 then
    scaleNBytes number 7
  else
    scaleNBytes number 8

/-- Encoded size of a compact SCALE integer, in bytes. -/
def u64CompactSize (number : Nat) : Nat :=
  if number < 2 ^ 6 then 1
  else if number < 2 ^ 14 then 2
  else if number < 2 ^ 30 then 4
  else if number < 2 ^ 32 then 5
  else if number < 2 ^ 40 then 6
  else if number < 2 ^ 48 then 7
  else if number < 2 ^ 56 then 8
  else 9

private theorem littleEndianBytes_length (number width : Nat) :
    (littleEndianBytes number width).length = width := by
  induction width generalizing number with
  | zero => rfl
  | succ width ih => simp [littleEndianBytes, ih]

private theorem listToArray_size {α : Type} (values : List α) :
    values.toArray.size = values.length := by
  induction values with
  | nil => rfl
  | cons head tail ih => simp

/-- The encoder's exact serialized-width law, including all SCALE thresholds. -/
theorem u64CompactBytes_size (number : Nat) :
    (u64CompactBytes number).length = u64CompactSize number := by
  unfold u64CompactBytes u64CompactSize
  by_cases h1 : number < 2 ^ 6
  · simp [h1]
  · by_cases h2 : number < 2 ^ 14
    · simp [h1, h2]
    · by_cases h3 : number < 2 ^ 30
      · simp [h1, h2, h3, littleEndianBytes_length]
      · by_cases h4 : number < 2 ^ 32
        · simp [h1, h2, h3, h4, scaleNBytes, littleEndianBytes_length]
        · by_cases h5 : number < 2 ^ 40
          · simp [h1, h2, h3, h4, h5, scaleNBytes, littleEndianBytes_length]
          · by_cases h6 : number < 2 ^ 48
            · simp [h1, h2, h3, h4, h5, h6, scaleNBytes, littleEndianBytes_length]
            · by_cases h7 : number < 2 ^ 56
              · simp [h1, h2, h3, h4, h5, h6, h7, scaleNBytes, littleEndianBytes_length]
              · simp [h1, h2, h3, h4, h5, h6, h7, scaleNBytes, littleEndianBytes_length]

/-- Checked Rust `u64` serialization. Values outside the Rust type range reject. -/
def encodeU64 (number : Nat) : Option ByteArray :=
  if number < u64Limit then
    some (ByteArray.mk (u64CompactBytes number).toArray)
  else
    none

/-- Every Rust `u64` value has a serialized byte array. -/
theorem encodeU64_isSome_of_lt (number : Nat) (bound : number < u64Limit) :
    (encodeU64 number).isSome = true := by
  simp [encodeU64, bound]

/-- The checked encoder rejects every value outside the Rust `u64` range. -/
theorem encodeU64_isSome_iff (number : Nat) :
    (encodeU64 number).isSome = true ↔ number < u64Limit := by
  simp [encodeU64]

/-- Encoded `ByteArray.size` follows the exact compact SCALE width. -/
theorem encodeU64_size (number : Nat) (bound : number < u64Limit) :
    (encodeU64 number).map (fun bytes => bytes.data.size) =
      some (u64CompactSize number) := by
  simp only [encodeU64, ite_eq_left bound, Option.map_some]
  change some ((u64CompactBytes number).toArray.size) = some (u64CompactSize number)
  congr 1
  rw [listToArray_size, u64CompactBytes_size]

/-- A cost duration is a picosecond count serialized as its underlying `u64`. -/
structure RunningCost where
  readTime : Nat
  computeTime : Nat
  bytesWritten : Nat
  bytesDeleted : Nat
  deriving Repr, DecidableEq

/-- Exact `RunningCost` serialization: four compact `u64`s in Rust field order.
Both duration fields use the same compact encoding as their transparent
`CostDuration(u64)` representation. -/
def encodeRunningCost (cost : RunningCost) : Option ByteArray := do
  let readTime ← encodeU64 cost.readTime
  let computeTime ← encodeU64 cost.computeTime
  let bytesWritten ← encodeU64 cost.bytesWritten
  let bytesDeleted ← encodeU64 cost.bytesDeleted
  pure (readTime ++ computeTime ++ bytesWritten ++ bytesDeleted)

/-- A running cost serializes when all four components fit in `u64`. -/
theorem encodeRunningCost_isSome_of_bounds (cost : RunningCost)
    (readBound : cost.readTime < u64Limit)
    (computeBound : cost.computeTime < u64Limit)
    (writtenBound : cost.bytesWritten < u64Limit)
    (deletedBound : cost.bytesDeleted < u64Limit) :
    (encodeRunningCost cost).isSome = true := by
  simp [encodeRunningCost, encodeU64, readBound, computeBound, writtenBound, deletedBound]

end Noctium.Verification.ImpactBindingNumber
