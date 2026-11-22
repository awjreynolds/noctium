import Noctium.IR

namespace Noctium.Wire

structure ScalarCodec (type : Ty) where
  width : Nat
  encode : Expr type → Expr (.bytes width)
  deserialize : {length : Nat} → Expr (.bytes length) → Expr type

private def decodeNative (frame : Expr (.bytes 32)) : Expr .native :=
  let input : Expr (.bytes 32) := .ref "$deserializeBytes"
  let result : Expr .native := .ref "$deserializeResult"
  let encoded : Expr (.bytes 32) := .ref "$deserializeEncoded"
  -- The primitive reduces modulo the field. Check both chunks of the round trip.
  .letE "$deserializeBytes" frame
    (.letE "$deserializeResult" (.fromBytes32 (target := .native) input)
      (.letE "$deserializeEncoded" (.toBytes32 result)
        (.assertE (.eq (.bytesField encoded 0) (.bytesField input 0))
          (.assertE (.eq (.bytesField encoded 1) (.bytesField input 1)) result))))

private def leading (width : Nat) (value : Expr (.bytes length)) : Expr (.bytes width) :=
  if equal : length = width then equal ▸ value
  else .sliceBytes value 0 width

def scalarCodec : (type : Ty) → Option (ScalarCodec type)
  | .native => some ⟨32, Expr.toBytes32, fun value => decodeNative (leading 32 value)⟩
  | .bool => some ⟨1,
      fun value => .select value (.bytesLiteral 1 [1]) (.bytesLiteral 1 [0]),
      fun value => .eq (.cast (.uint 1) (.bytesAt value 0)) (.uint 1 1)⟩
  | .uint maximum =>
    let width := if maximum == 0 then 0 else maximum.log2 / 8 + 1
    some ⟨width,
      fun value => .sliceBytes (.toBytes32 (.cast .native value)) 0 width,
      fun value => .cast (.uint maximum) (.fromBytes (target := .native) (leading width value))⟩
  | .bytes length => some ⟨length, id, leading length⟩
  | .jubjubScalar => some ⟨32, Expr.toBytes32, fun value => .fromBytes32 (leading 32 value)⟩
  | .foreign (.base curve) =>
    some ⟨32, Expr.foreignToBytes, fun value => .foreignFromBytes (.base curve) (leading 32 value)⟩
  | .foreign (.scalar curve) =>
    some ⟨32, Expr.foreignToBytes, fun value => .foreignFromBytes (.scalar curve) (leading 32 value)⟩
  | _ => none

def scalarWidth (type : Ty) : Option Nat := (scalarCodec type).map (·.width)

/-- Choose the scalar type used by `toBytes`. Narrow outputs use a checked
UInt cast so their little-endian encoding rejects values that do not fit.
Widths of 32 bytes or more keep the source type and serialize with zero
padding, matching the canonical scalar codec. -/
def numericBytesTarget (source : Ty) (length : Nat) : Except String Ty := do
  unless 0 < length && length ≤ maxBytesLength do
    throw s!"toBytes requires a byte width from 1 through {maxBytesLength}"
  match source with
  | .native =>
    if length ≤ 31 then pure (.uint (2 ^ (length * 8) - 1)) else pure .native
  | .uint maximum => do
    ScalarPolicy.validate (.uint maximum)
    if length ≤ 31 then
      let byteMaximum := 2 ^ (length * 8) - 1
      if maximum ≤ byteMaximum then pure source else pure (.uint byteMaximum)
    else pure source
  | _ => throw "toBytes requires Native or UInt"

def ScalarCodec.serialize (codec : ScalarCodec type) (value : Expr type)
    (length : Nat) (fits : codec.width ≤ length) : Expr (.bytes length) :=
  if equal : codec.width = length then
    equal ▸ codec.encode value
  else
    have sum : codec.width + (length - codec.width) = length := by omega
    sum ▸ Expr.concatBytes (codec.encode value)
      (.bytesLiteral (length - codec.width) (List.replicate (length - codec.width) 0))

private def shieldedNonceDomainTag (change : Bool) : String :=
  if change then "midnight:kernel:nonce_evolve/2" else "midnight:kernel:nonce_evolve"

private def shieldedNonceDomain (change : Bool) : Expr .native :=
  let domain := shieldedNonceDomainTag change
  .fromBytes (.bytesLiteral domain.utf8ByteSize (domain.toUTF8.data.toList.map UInt8.toNat))

/-- Keep a transient digest's low 31 bytes and zero the high byte for persistent hashing. -/
def upgradeFromNative (value : Expr .native) : Expr (.bytes 32) :=
  .concatBytes (.sliceBytes (.toBytes32 value) 0 31) (.bytesLiteral 1 [0])

private def degradeShieldedNonce (value : Expr (.bytes 32)) : Expr .native :=
  .bytesField value 1

private def evolveShieldedNonce (change : Bool) (nonce : Expr (.bytes 32)) :
    Expr (.bytes 32) :=
  upgradeFromNative
    (.transientHash [shieldedNonceDomain change, degradeShieldedNonce nonce])

/-- Derive the recipient nonce for a shielded send. -/
def shieldedOutputNonce (nonce : Expr (.bytes 32)) : Expr (.bytes 32) :=
  evolveShieldedNonce false nonce

/-- Derive a shielded nonce for an indexed output under the shared nonce domain. -/
def shieldedIndexedNonce (index : Expr (.uint (2 ^ 128 - 1)))
    (nonce : Expr (.bytes 32)) : Expr (.bytes 32) :=
  upgradeFromNative (.transientHash [
    shieldedNonceDomain false,
    .cast .native index,
    degradeShieldedNonce nonce])

/-- Derive the contract-owned change nonce for a partial shielded send. -/
def shieldedChangeNonce (nonce : Expr (.bytes 32)) : Expr (.bytes 32) :=
  evolveShieldedNonce true nonce

end Noctium.Wire
