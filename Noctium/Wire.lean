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

private def curveEncodingMatches (value : Expr ty) (fields : List (Expr .native)) : Expr .bool :=
  let comparisons := (value.nativeCallFields.zip fields).map fun (encoded, input) =>
    Expr.eq encoded input
  match comparisons with
  | [] => .bool false
  | first :: rest => rest.foldl Expr.boolAnd first

private def decodeForeignField (kind : Foreign.FieldKind)
    (literal : Nat → Expr (.foreign kind.kind))
    (low high : Expr .native) : Expr (.foreign kind.kind) :=
  let lowBytes := Expr.toBytes32 low
  let highBytes := Expr.toBytes32 high
  let shifted :=
    if kind.kind.lowRadix == Foreign.lowRadix then
      .foreignFromBytes kind.kind
        (.concatBytes (.sliceBytes lowBytes 0 24) (.sliceBytes highBytes 0 8))
    else
      let lo := Expr.foreignFromBytes kind.kind lowBytes
      let hi := Expr.foreignFromBytes kind.kind highBytes
      let scaled := Expr.foreignBinary (.mul kind) hi (literal kind.kind.lowRadix)
      Expr.foreignBinary (.add kind.kind) lo scaled
  .foreignBinary (.add kind.kind) shifted (literal 1)

private def decodeForeignPoint (curve : Foreign.Curve) (x y : Expr (.foreign (.base curve)))
    (identity : Option (Expr .native)) : Expr (.foreign (.point curve)) :=
  match identity with
  | none => .foreignBinary (.fromCoordinates curve) x y
  | some flag =>
    let isIdentity := Expr.eq flag (.native 1)
    let generator : Expr (.foreign (.point curve)) := .ref "$curveGenerator"
    let point := Expr.foreignBinary (.fromCoordinates curve)
      (.select isIdentity (.foreignUnary (.x curve) generator) x)
      (.select isIdentity (.foreignUnary (.y curve) generator) y)
    .letE "$curveGenerator" (.foreignUnary (.mulGenerator curve) (.foreignScalar curve 1))
      (.select isIdentity (.foreignPoint curve .identity) point)

private def decodeCurveValue : (type : Ty) → List (Expr .native) → Except String (Expr type)
  | .jubjubScalar, [value] => pure (.jubjubScalarFromNative value)
  | .jubjubPoint, [x, y] => pure (.jubjubFromCoordinates x y)
  | .foreign (.base curve), [low, high] =>
    pure (decodeForeignField (.base curve) (.foreignBase curve) low high)
  | .foreign (.scalar curve), [low, high] =>
    pure (decodeForeignField (.scalar curve) (.foreignScalar curve) low high)
  | .foreign (.point curve), fields => do
    let (xLow, xHigh, yLow, yHigh, identity) ← match curve, fields with
      | .curve25519, [xl, xh, yl, yh] => pure (xl, xh, yl, yh, none)
      | .secp256k1, [xl, xh, yl, yh, flag]
      | .secp256r1, [xl, xh, yl, yh, flag] => pure (xl, xh, yl, yh, some flag)
      | _, _ => throw "wrong number of native fields for a foreign point"
    let x := decodeForeignField (.base curve) (.foreignBase curve) xLow xHigh
    let y := decodeForeignField (.base curve) (.foreignBase curve) yLow yHigh
    pure (decodeForeignPoint curve x y identity)
  | type, _ => throw s!"invalid native field shape for curve type {repr type}"

/-- Check the exact canonical Native-field encoding, decoding the curve value once. -/
def curveFieldsCanonical (type : Ty) (fields : List (Expr .native)) : Except String (Expr .bool) := do
  let value ← decodeCurveValue type fields
  let result : Expr type := .ref "$curveDecoded"
  pure (.letE "$curveDecoded" value (curveEncodingMatches result fields))

/-- Recover a logical curve value and check its exact canonical Native-field encoding. -/
def decodeCurveFields (type : Ty) (fields : List (Expr .native)) : Except String (Expr type) := do
  let value ← decodeCurveValue type fields
  let result : Expr type := .ref "$curveDecoded"
  pure (.letE "$curveDecoded" value (.assertE (curveEncodingMatches result fields) result))

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
  | .jubjubPoint => some ⟨32, Expr.toBytes32, fun value => .fromBytes32 (leading 32 value)⟩
  | .foreign kind =>
    some ⟨kind.byteLength, Expr.foreignToBytes,
      fun value => .foreignFromBytes kind (leading kind.byteLength value)⟩
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
