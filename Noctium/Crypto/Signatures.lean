import Noctium.Helpers.Wire

namespace Noctium.Crypto

/-! Compact-compatible typed records used to pass signature components as one value.
The fields retain their curve-specific Lean expression types. -/

structure JubjubSchnorrSignature where
  announcement : Expr .jubjubPoint
  response : Expr .native
  deriving Repr

structure Secp256k1EcdsaSignature where
  r : Expr (.foreign (.scalar .secp256k1))
  s : Expr (.foreign (.scalar .secp256k1))
  deriving Repr

structure Secp256r1EcdsaSignature where
  r : Expr (.foreign (.scalar .secp256r1))
  s : Expr (.foreign (.scalar .secp256r1))
  deriving Repr

structure Ed25519Signature where
  r : Expr (.foreign (.point .curve25519))
  s : Expr (.foreign (.scalar .curve25519))
  deriving Repr

private def signatureCodec (id : Types.DeclId) (fields : List (String × Ty)) : Helpers.Wire.Codec := {
  payload := .structure id
  frameBytes := 64
  composites := {structures := [{id, fields := fields.map fun (name, ty) =>
    {name, type := .scalar ty}}]}
}

private def ecdsaChecks (curve : Foreign.Curve) (msgHash : Expr (.bytes 32))
    (r s : Expr (.foreign (.scalar curve)))
    (pk : Expr (.foreign (.point curve))) : List (Expr .bool) × Expr .bool := Id.run do
  let z : Expr (.foreign (.scalar curve)) :=
    .foreignFromBytes (.scalar curve) (.reverseBytes32 msgHash)
  let w : Expr (.foreign (.scalar curve)) := .foreignUnary (.inv (.scalar curve)) s
  let u1 : Expr (.foreign (.scalar curve)) := .foreignBinary (.mul (.scalar curve)) z w
  let u2 : Expr (.foreign (.scalar curve)) := .foreignBinary (.mul (.scalar curve)) r w
  let generatorTerm : Expr (.foreign (.point curve)) :=
    .foreignUnary (.mulGenerator curve) u1
  let publicKeyTerm : Expr (.foreign (.point curve)) := .foreignBinary (.ecMul curve) pk u2
  let point : Expr (.foreign (.point curve)) :=
    .foreignBinary (.add (.point curve)) generatorTerm publicKeyTerm
  let x : Expr (.foreign (.base curve)) := .foreignUnary (.x curve) point
  let xModN : Expr (.foreign (.scalar curve)) := .foreignFromBytes (.scalar curve) (.foreignToBytes x)
  let nonIdentity := .eq (.eq pk (.foreignIdentity curve)) (.bool false)
  let nonzeroR := .eq (.eq r (.foreignScalar curve 0)) (.bool false)
  let nonzeroS := .eq (.eq s (.foreignScalar curve 0)) (.bool false)
  return ([nonIdentity, nonzeroR, nonzeroS], .eq xModN r)

private def ecdsaVerify (curve : Foreign.Curve) (msgHash : Expr (.bytes 32))
    (r s : Expr (.foreign (.scalar curve)))
    (pk : Expr (.foreign (.point curve))) : Expr .bool :=
  let (checks, equation) := ecdsaChecks curve msgHash r s pk
  checks.foldr (fun check result => .assertE check result) equation

-- Readable circuits schedule these same checks before the equation in the witness plan.
private partial def readableEcdsaTerm : Expr ty → Except String Helpers.Term
  | .ref name => pure (.ref name)
  | .bool value => pure (.bool value)
  | .eq left right => return .eq (← readableEcdsaTerm left) (← readableEcdsaTerm right)
  | .foreignPoint curve point =>
    return .foreignConstant (.point curve) (← Foreign.encodePoint curve point)
  | .foreignScalar curve value =>
    return .foreignConstant (.scalar curve) (← Foreign.encodeField (.scalar curve) value)
  | .foreignUnary operation operand =>
    return .curve (.foreignUnary operation) [← readableEcdsaTerm operand]
  | .foreignBinary operation left right =>
    return .curve (.foreignBinary operation) [← readableEcdsaTerm left, ← readableEcdsaTerm right]
  | .reverseBytes32 bytes => return .bytes .reverseBytes32 [← readableEcdsaTerm bytes]
  | .foreignFromBytes (length := length) kind bytes =>
    return .bytes (.foreignFromBytes kind length) [← readableEcdsaTerm bytes]
  | .foreignToBytes (kind := kind) operand =>
    return .bytes (.foreignToBytes kind) [← readableEcdsaTerm operand]
  | _ => throw "operation in the ECDSA recipe lacks a readable witness representation"

def readableEcdsaChecks (curve : Foreign.Curve) (digest r s key : String) :
    Except String (List Helpers.Term × Helpers.Term) := do
  let (checks, equation) := ecdsaChecks curve (.ref digest) (.ref r) (.ref s) (.ref key)
  return (← checks.mapM readableEcdsaTerm, ← readableEcdsaTerm equation)

def secp256k1EcdsaVerify (msgHash : Expr (.bytes 32))
    (r s : Expr (.foreign (.scalar .secp256k1)))
    (pk : Expr (.foreign (.point .secp256k1))) : Expr .bool :=
  ecdsaVerify .secp256k1 msgHash r s pk

namespace Secp256k1EcdsaSignature

def codec : Helpers.Wire.Codec := signatureCodec "Noctium.Crypto.Secp256k1EcdsaSignature"
  [("r", .foreign (.scalar .secp256k1)), ("s", .foreign (.scalar .secp256k1))]

def verify (msgHash : Expr (.bytes 32)) (signature : Secp256k1EcdsaSignature)
    (pk : Expr (.foreign (.point .secp256k1))) : Expr .bool :=
  secp256k1EcdsaVerify msgHash signature.r signature.s pk

end Secp256k1EcdsaSignature

def secp256r1EcdsaVerify (msgHash : Expr (.bytes 32))
    (r s : Expr (.foreign (.scalar .secp256r1)))
    (pk : Expr (.foreign (.point .secp256r1))) : Expr .bool :=
  ecdsaVerify .secp256r1 msgHash r s pk

namespace Secp256r1EcdsaSignature

def codec : Helpers.Wire.Codec := signatureCodec "Noctium.Crypto.Secp256r1EcdsaSignature"
  [("r", .foreign (.scalar .secp256r1)), ("s", .foreign (.scalar .secp256r1))]

def verify (msgHash : Expr (.bytes 32)) (signature : Secp256r1EcdsaSignature)
    (pk : Expr (.foreign (.point .secp256r1))) : Expr .bool :=
  secp256r1EcdsaVerify msgHash signature.r signature.s pk

end Secp256r1EcdsaSignature

def jubjubSchnorrVerify (msg : List (Expr .native))
    (announcement : Expr .jubjubPoint) (response : Expr .native)
    (pk : Expr .jubjubPoint) : Expr .bool := Id.run do
  let challengeInputs : List (Expr .native) :=
    [Expr.jubjubCoordinate announcement 0, Expr.jubjubCoordinate announcement 1,
      Expr.jubjubCoordinate pk 0, Expr.jubjubCoordinate pk 1] ++ msg
  let challenge := Expr.jubjubScalarFromNative (.transientHash challengeInputs)
  let lhs := Expr.jubjubMulGenerator (Expr.jubjubScalarFromNative response)
  let rhs := Expr.jubjubAdd announcement (Expr.jubjubMul pk challenge)
  let identity := Expr.jubjubFromCoordinates (.native 0) (.native 1)
  let nonIdentity := Expr.eq (.eq pk identity) (.bool false)
  return .assertE nonIdentity (.eq lhs rhs)

namespace JubjubSchnorrSignature

def codec : Helpers.Wire.Codec := signatureCodec "Noctium.Crypto.JubjubSchnorrSignature"
  [("announcement", .jubjubPoint), ("response", .native)]

def verify (msg : List (Expr .native)) (signature : JubjubSchnorrSignature)
    (pk : Expr .jubjubPoint) : Expr .bool :=
  jubjubSchnorrVerify msg signature.announcement signature.response pk

end JubjubSchnorrSignature

def ed25519Verify {length : Nat} (msg : Expr (.bytes length))
    (r : Expr (.foreign (.point .curve25519)))
    (s : Expr (.foreign (.scalar .curve25519)))
    (pk : Expr (.foreign (.point .curve25519))) : Expr .bool := Id.run do
  let encodedR : Expr (.bytes 32) := .foreignToBytes r
  let encodedPk : Expr (.bytes 32) := .foreignToBytes pk
  let preimage := Expr.concatBytes (Expr.concatBytes encodedR encodedPk) msg
  let challengeBytes := Expr.sha512 preimage
  let challenge : Expr (.foreign (.scalar .curve25519)) :=
    .foreignFromBytes (.scalar .curve25519) challengeBytes
  let lhs : Expr (.foreign (.point .curve25519)) :=
    .foreignUnary (.mulGenerator .curve25519) s
  let publicKeyTerm : Expr (.foreign (.point .curve25519)) :=
    .foreignBinary (.ecMul .curve25519) pk challenge
  let rhs : Expr (.foreign (.point .curve25519)) :=
    .foreignBinary (.add (.point .curve25519)) r publicKeyTerm
  let x : Expr (.foreign (.base .curve25519)) := .foreignUnary (.x .curve25519) pk
  let nonIdentity := .eq (.eq x (.foreignBase .curve25519 0)) (.bool false)
  return .assertE nonIdentity (.eq lhs rhs)

namespace Ed25519Signature

def codec : Helpers.Wire.Codec := signatureCodec "Noctium.Crypto.Ed25519Signature"
  [("r", .foreign (.point .curve25519)), ("s", .foreign (.scalar .curve25519))]

def verify {length : Nat} (msg : Expr (.bytes length)) (signature : Ed25519Signature)
    (pk : Expr (.foreign (.point .curve25519))) : Expr .bool :=
  ed25519Verify msg signature.r signature.s pk

end Ed25519Signature

def secp256k1EthereumAddress (pk : Expr (.foreign (.point .secp256k1))) : Expr (.bytes 20) :=
  let x : Expr (.foreign (.base .secp256k1)) := .foreignUnary (.x .secp256k1) pk
  let y : Expr (.foreign (.base .secp256k1)) := .foreignUnary (.y .secp256k1) pk
  let coordinates := Expr.concatBytes (Expr.reverseBytes (.foreignToBytes x))
    (Expr.reverseBytes (.foreignToBytes y))
  let address := Expr.sliceBytes (.keccak256 coordinates) 12 32
  let nonIdentity := Expr.eq (Expr.eq pk (.foreignIdentity .secp256k1)) (.bool false)
  Expr.assertE nonIdentity address

end Noctium.Crypto
