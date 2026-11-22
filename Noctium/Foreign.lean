import Noctium.Field

namespace Noctium.Foreign

inductive Curve where
  | secp256k1 | secp256r1 | curve25519
  deriving Repr, BEq, DecidableEq, Inhabited

inductive Kind where
  | base (curve : Curve)
  | scalar (curve : Curve)
  | point (curve : Curve)
  deriving Repr, BEq, DecidableEq, Inhabited

/-- The two field roles supported by each foreign curve. -/
inductive FieldKind where
  | base (curve : Curve)
  | scalar (curve : Curve)
  deriving Repr, BEq, DecidableEq, Inhabited

/-- Logical points do not expose their five native wire fields. -/
inductive Point where
  | identity
  | affine (x y : Nat)
  deriving Repr, BEq, DecidableEq, Inhabited

abbrev Kind.Denote : Kind → Type
  | .base _ | .scalar _ => Nat
  | .point _ => Point

instance (kind : Kind) : BEq kind.Denote := by
  cases kind <;> simp only [Kind.Denote] <;> infer_instance

instance (kind : Kind) : DecidableEq kind.Denote := by
  cases kind <;> simp only [Kind.Denote] <;> infer_instance

abbrev FieldKind.curve : FieldKind → Curve
  | .base curve | .scalar curve => curve

abbrev FieldKind.kind : FieldKind → Kind
  | .base curve => .base curve
  | .scalar curve => .scalar curve

def Kind.fieldKind? : Kind → Option FieldKind
  | .base curve => some (.base curve)
  | .scalar curve => some (.scalar curve)
  | .point _ => none

/-- One-input curve operation, indexed by its exact input and output kinds. -/
inductive UnaryOp where
  | neg (kind : Kind)
  | inv (kind : FieldKind)
  | mulGenerator (curve : Curve)
  | x (curve : Curve)
  | y (curve : Curve)
  deriving Repr, BEq, DecidableEq, Inhabited

abbrev UnaryOp.inputKind : UnaryOp → Kind
  | .neg kind => kind
  | .inv kind => kind.kind
  | .mulGenerator curve => .scalar curve
  | .x curve | .y curve => .point curve

abbrev UnaryOp.outputKind : UnaryOp → Kind
  | .neg kind => kind
  | .inv kind => kind.kind
  | .mulGenerator curve => .point curve
  | .x curve | .y curve => .base curve

def UnaryOp.name : UnaryOp → String
  | .neg _ => "neg"
  | .inv _ => "inv"
  | .mulGenerator _ => "mulGenerator"
  | .x _ => "x"
  | .y _ => "y"

/-- Two-input curve operation, indexed by exact operand and result kinds. -/
inductive BinaryOp where
  | add (kind : Kind)
  | sub (kind : Kind)
  | mul (kind : FieldKind)
  | ecMul (curve : Curve)
  | fromCoordinates (curve : Curve)
  deriving Repr, BEq, DecidableEq, Inhabited

abbrev BinaryOp.leftKind : BinaryOp → Kind
  | .add kind | .sub kind => kind
  | .mul kind => kind.kind
  | .ecMul curve => .point curve
  | .fromCoordinates curve => .base curve

abbrev BinaryOp.rightKind : BinaryOp → Kind
  | .add kind | .sub kind => kind
  | .mul kind => kind.kind
  | .ecMul curve => .scalar curve
  | .fromCoordinates curve => .base curve

abbrev BinaryOp.outputKind : BinaryOp → Kind
  | .add kind | .sub kind => kind
  | .mul kind => kind.kind
  | .ecMul curve | .fromCoordinates curve => .point curve

def BinaryOp.name : BinaryOp → String
  | .add _ => "add"
  | .sub _ => "sub"
  | .mul _ => "mul"
  | .ecMul _ => "ecMul"
  | .fromCoordinates _ => "fromCoordinates"

def Curve.name : Curve → String
  | .secp256k1 => "Secp256k1"
  | .secp256r1 => "Secp256r1"
  | .curve25519 => "Curve25519"

private def curve25519P : Nat := 2 ^ 255 - 19
private def curve25519L : Nat := 2 ^ 252 + 27742317777372353535851937790883648493

/-- Moduli matching the pinned midnight-curves 0.3.1 foreign field types. -/
def Curve.baseModulus : Curve → Nat
  | .secp256k1 => 0xfffffffffffffffffffffffffffffffffffffffffffffffffffffffefffffc2f
  | .secp256r1 => 0xffffffff00000001000000000000000000000000ffffffffffffffffffffffff
  | .curve25519 => curve25519P

def Curve.scalarModulus : Curve → Nat
  | .secp256k1 => 0xfffffffffffffffffffffffffffffffebaaedce6af48a03bbfd25e8cd0364141
  | .secp256r1 => 0xffffffff00000000ffffffffffffffffbce6faada7179e84f3b9cac2fc632551
  | .curve25519 => curve25519L

def FieldKind.modulus : FieldKind → Nat
  | .base curve => curve.baseModulus
  | .scalar curve => curve.scalarModulus

def Kind.curve : Kind → Curve
  | .base curve | .scalar curve | .point curve => curve

def Kind.nativeName : Kind → String
  | .base curve => s!"Base<{curve.name}>"
  | .scalar curve => s!"Scalar<{curve.name}>"
  | .point curve => s!"Point<{curve.name}>"

def Kind.sourceName : Kind → String
  | .base curve => curve.name ++ "Base"
  | .scalar curve => curve.name ++ "Scalar"
  | .point curve => curve.name ++ "Point"

def Kind.encodedFieldCount : Kind → Nat
  | .base _ | .scalar _ => 2
  | .point .curve25519 => 4
  | .point _ => 5

def Kind.byteLength : Kind → Nat
  | .base _ | .scalar _ => 32
  | .point .curve25519 => 32
  | .point _ => 33

def Kind.modulus? : Kind → Option Nat
  | .base curve => some curve.baseModulus
  | .scalar curve => some curve.scalarModulus
  | .point _ => none

def kinds : List Kind := [
  .point .secp256k1, .base .secp256k1, .scalar .secp256k1,
  .point .secp256r1, .base .secp256r1, .scalar .secp256r1,
  .point .curve25519, .base .curve25519, .scalar .curve25519]

def lowRadix : Nat := 2 ^ 192
def highRadix : Nat := 2 ^ 64

/-- The scalar AssignedField packs four 51-bit limbs into its low native field. -/
def Kind.lowRadix : Kind → Nat
  | .scalar .curve25519 => 2 ^ 204
  | _ => Noctium.Foreign.lowRadix

/-- Canonical native Encode uses x-1 modulo the selected foreign field. -/
def encodeField (kind : Kind) (value : Nat) : Except String (List Nat) := do
  let some modulus := kind.modulus? | throw "foreign point requires a point encoding"
  unless value < modulus do throw "foreign field value is not canonical"
  let radix := kind.lowRadix
  let shifted := (value + modulus - 1) % modulus
  pure [shifted % radix, shifted / radix]

/-- Exact inverse of canonical field encoding, with both limb and range checks. -/
def decodeField (kind : Kind) (encoding : List Nat) : Except String Nat := do
  let some modulus := kind.modulus? | throw "foreign point requires a point decoding"
  let [low, high] := encoding | throw "foreign field encoding requires two limbs"
  let radix := kind.lowRadix
  unless low < radix && high < highRadix do throw "foreign field limb is out of range"
  let shifted := low + radix * high
  unless shifted < modulus do throw "foreign field encoding is not canonical"
  pure ((shifted + 1) % modulus)

/-- Encode the universal identity as Secp's flagged zero or Edwards `(0,1)`. -/
def identityEncoding (curve : Curve) : List Nat :=
  let zeroShifted := curve.baseModulus - 1
  let zero := [zeroShifted % lowRadix, zeroShifted / lowRadix]
  if curve == .curve25519 then zero ++ [0, 0]
  else zero ++ zero ++ [1]

/-- Normalize the Edwards coordinate identity to the universal logical point. -/
def normalizePoint (curve : Curve) (x y : Nat) : Point :=
  if curve == .curve25519 && x == 0 && y == 1 then .identity else .affine x y

private def curve25519D : Nat :=
  37095705934669439343138083508754565189542113879843219016388785533085940283555

private structure EdwardsPoint where
  x : Nat
  y : Nat
  z : Nat
  t : Nat

private def edwardsIdentity : EdwardsPoint := ⟨0, 1, 1, 0⟩

private def edwardsAdd (p coefficient : Nat) (p₁ p₂ : EdwardsPoint) : EdwardsPoint := Id.run do
  let a := (((p₁.y + p - p₁.x) % p) * ((p₂.y + p - p₂.x) % p)) % p
  let b := (((p₁.y + p₁.x) % p) * ((p₂.y + p₂.x) % p)) % p
  let c := (((2 * coefficient % p) * p₁.t % p) * p₂.t) % p
  let d := ((2 * p₁.z % p) * p₂.z) % p
  let e := (b + p - a) % p
  let f := (d + p - c) % p
  let g := (d + c) % p
  let h := (b + a) % p
  return ⟨e * f % p, g * h % p, f * g % p, e * h % p⟩

private def secpPointValid (curve : Curve) (x y : Nat) : Bool :=
  let p := curve.baseModulus
  let lhs := y * y % p
  match curve with
  | .secp256k1 => lhs == (x * x % p * x + 7) % p
  | .secp256r1 => lhs == (x * x % p * x + (p - 3) * x +
      0x5ac635d8aa3a93e7b3ebbd55769886bc651d06b0cc53b0f63bce3c3e27d2604b) % p
  | .curve25519 => false

/-- Check a canonical affine point on a twisted Edwards curve with a = -1.
Used with the pinned Curve25519 and Jubjub parameters. -/
def edwardsPrimePoint (p coefficient order x y : Nat) : Bool := Id.run do
  if x >= p || y >= p then return false
  let xSq := x * x % p
  let ySq := y * y % p
  let lhs := (ySq + p - xSq) % p
  let rhs := (1 + coefficient * xSq % p * ySq) % p
  if lhs != rhs then return false
  let point : EdwardsPoint := ⟨x, y, 1, x * y % p⟩
  let mut multiple := point
  let mut result := edwardsIdentity
  let mut scalar := order
  for _ in [0:order.log2 + 1] do
    if scalar % 2 == 1 then result := edwardsAdd p coefficient result multiple
    multiple := edwardsAdd p coefficient multiple multiple
    scalar := scalar / 2
  return result.z != 0 && result.x == 0 && result.y == result.z

/-- Canonical curve membership for the supported Secp and Edwards curves. -/
def pointValid (curve : Curve) : Point → Bool
  | .identity => true
  | .affine x y =>
    if curve == .curve25519 then
      !(x == 0 && y == 1) && edwardsPrimePoint curve25519P curve25519D curve25519L x y
    else
      x < curve.baseModulus && y < curve.baseModulus && secpPointValid curve x y

def Kind.canonical : (kind : Kind) → kind.Denote → Bool
  | .base curve, value => value < curve.baseModulus
  | .scalar curve, value => value < curve.scalarModulus
  | .point curve, value => pointValid curve value

/-- Encode a canonical point in the selected curve's native field layout. -/
def encodePoint (curve : Curve) (point : Point) : Except String (List Nat) := do
  unless pointValid curve point do throw "foreign point is not canonical or on curve"
  match point with
  | .identity => pure (identityEncoding curve)
  | .affine x y => do
    let xFields ← encodeField (.base curve) x
    let yFields ← encodeField (.base curve) y
    if curve == .curve25519 then pure (xFields ++ yFields)
    else pure (xFields ++ yFields ++ [0])

private def littleEndianBytes (length value : Nat) : List Nat :=
  (List.range length).map fun index => value / (256 ^ index) % 256

/-- Scalar transport bytes used by the typed host ABI. -/
def canonicalBytes : (kind : Kind) → kind.Denote → Except String (List Nat)
  | .base curve, value => do
    unless value < curve.baseModulus do throw "foreign field value is not canonical"
    pure (littleEndianBytes 32 value)
  | .scalar curve, value => do
    unless value < curve.scalarModulus do throw "foreign field value is not canonical"
    pure (littleEndianBytes 32 value)
  | .point curve, value => do
    unless pointValid curve value do throw "foreign point is not canonical or on curve"
    match value with
    | .identity =>
      if curve == .curve25519 then pure (littleEndianBytes 32 1)
      else pure (List.replicate 33 0)
    | .affine x y =>
      if curve == .curve25519 then pure (littleEndianBytes 32 (y + x % 2 * 2 ^ 255))
      else pure ((2 + y % 2) :: (littleEndianBytes 32 x).reverse)

/-- Compact's `keccak256<Secp256k1Point>` hashes the canonical FAB encoding:
two 24-byte/8-byte coordinate pairs and a 32-byte identity field. -/
def secp256k1PointFabBytes (point : Point) : Except String (List Nat) := do
  let [xLow, xHigh, yLow, yHigh, identity] ← encodePoint .secp256k1 point
    | throw "Secp256k1 point Encode must produce five fields"
  let preimage := littleEndianBytes 24 xLow ++ littleEndianBytes 8 xHigh ++
    littleEndianBytes 24 yLow ++ littleEndianBytes 8 yHigh ++
    littleEndianBytes 32 identity
  unless preimage.length == 96 && preimage.all (· ≤ 255) do
    throw "Secp256k1 point FAB encoding is not a canonical 96-byte value"
  pure preimage

/-- Decode canonical Secp flags or Curve25519 coordinates, then validate. -/
def decodePoint (curve : Curve) (encoding : List Nat) : Except String Point := do
  if curve == .curve25519 then
    let [xLow, xHigh, yLow, yHigh] := encoding
      | throw "foreign Curve25519 point encoding requires four fields"
    let x ← decodeField (.base curve) [xLow, xHigh]
    let y ← decodeField (.base curve) [yLow, yHigh]
    let point := normalizePoint curve x y
    unless pointValid curve point do throw "Curve25519 point is not in the prime subgroup"
    return point
  let [xLow, xHigh, yLow, yHigh, flag] := encoding
    | throw "foreign point encoding requires five fields"
  unless flag ≤ 1 do throw "foreign point identity flag must be zero or one"
  let x ← decodeField (.base curve) [xLow, xHigh]
  let y ← decodeField (.base curve) [yLow, yHigh]
  if flag == 1 then
    unless x == 0 && y == 0 do throw "foreign identity encoding has nonzero coordinates"
    pure .identity
  else do
    let point := .affine x y
    unless pointValid curve point do throw "foreign point is not on curve"
    pure point

def encodeValue : (kind : Kind) → kind.Denote → Except String (List Nat)
  | .base curve, value => do
    unless value < curve.baseModulus do throw "foreign value is not canonical"
    encodeField (.base curve) value
  | .scalar curve, value => do
    unless value < curve.scalarModulus do throw "foreign value is not canonical"
    encodeField (.scalar curve) value
  | .point curve, value => encodePoint curve value

def decodeValue : (kind : Kind) → List Nat → Except String kind.Denote
  | .base curve, encoding => decodeField (.base curve) encoding
  | .scalar curve, encoding => decodeField (.scalar curve) encoding
  | .point curve, encoding => decodePoint curve encoding

end Noctium.Foreign
