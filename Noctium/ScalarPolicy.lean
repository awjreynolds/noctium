import Noctium.Field
import Noctium.Foreign
import Lean

namespace Noctium

/-- A source-level bounded unsigned type with the ordinary UInt wire representation. -/
structure NominalUIntType where
  name : String
  maximum : Nat
  deriving Repr, BEq, DecidableEq

/-- Source-only nominal labels for the scalar key and value of a root Map.
The state wire types remain ordinary bounded UInt values. -/
structure NominalUIntMap where
  key : Option NominalUIntType := none
  value : Option NominalUIntType := none
  deriving Repr, BEq, DecidableEq, Inhabited

end Noctium

namespace Noctium.ScalarPolicy

/-- Source-derived scalar policy for the pinned feature reference. Bounds are
inclusive maxima internally. This module does not yet extend the source DSL. -/
inductive Kind where
  | bool
  | native
  | uint (maximum : Nat)
  | bytes (length : Nat)
  | opaqueBytes
  | jubjubScalar | jubjubPoint
  | foreign (kind : Foreign.Kind)
  deriving Repr, BEq, DecidableEq

inductive Binary where
  | add | sub | mul
  deriving Repr, BEq, DecidableEq

def maxBits : Nat := 248
def maxUint : Nat := 2 ^ maxBits - 1

def validate : Kind → Except String Unit
  | .bool | .native => pure ()
  | .uint maximum =>
    if maximum ≤ maxUint then pure () else .error "unsigned type exceeds target maximum"
  | .bytes _ => .error "byte strings are not scalar values"
  | .opaqueBytes => .error "opaque byte strings are not scalar values"
  | .jubjubScalar => .error "Jubjub scalars require a qualified curve operation"
  | .jubjubPoint => .error "Jubjub points require a qualified curve operation"
  | .foreign _ => .error "foreign values require a qualified curve operation"

def sized (bits : Nat) : Except String Kind :=
  if bits ≤ maxBits then .ok (.uint (2 ^ bits - 1))
  else .error "unsigned width exceeds target maximum"

def bounded (exclusive : Nat) : Except String Kind := do
  if exclusive == 0 then throw "unsigned exclusive bound must be positive"
  let result := Kind.uint (exclusive - 1)
  validate result
  return result

def accepts : Kind → Nat → Bool
  | .bool, value => value ≤ 1
  | .native, value => value < Field.modulus
  | .uint maximum, value => maximum ≤ maxUint && value ≤ maximum
  | .bytes _, _ => false
  | .opaqueBytes, _ => false
  | .jubjubScalar, _ | .jubjubPoint, _ | .foreign _, _ => false

def infer (op : Binary) (left right : Kind) : Except String Kind := do
  validate left
  validate right
  match left, right with
  | .bool, _ | _, .bool => throw "boolean arithmetic requires an explicit cast"
  | .native, _ | _, .native => return .native
  | .uint m, .uint n =>
    let maximum := match op with
      | .add => m + n
      | .sub => m
      | .mul => m * n
    let result := Kind.uint maximum
    validate result
    return result
  | .bytes _, _ | _, .bytes _ | .opaqueBytes, _ | _, .opaqueBytes =>
    throw "byte strings do not support scalar arithmetic"
  | .jubjubScalar, _ | _, .jubjubScalar | .jubjubPoint, _ | _, .jubjubPoint =>
    throw "Jubjub values do not support scalar arithmetic"
  | .foreign _, _ | _, .foreign _ =>
    throw "foreign values require a qualified curve operation"

structure Value where
  kind : Kind
  /-- Logical values only: Boolean is 0/1. This is not an external ABI encoding. -/
  number : Nat
  deriving Repr, BEq, DecidableEq

def Value.validate (value : Value) : Except String Unit := do
  ScalarPolicy.validate value.kind
  unless accepts value.kind value.number do throw "scalar value is outside its declared type"

def evaluate (op : Binary) (left right : Value) : Except String Value := do
  left.validate
  right.validate
  let result ← infer op left.kind right.kind
  let a := left.number
  let b := right.number
  let number ← match result with
    | .bool => throw "invalid arithmetic result type"
    | .native => pure <| match op with
      | .add => (a + b) % Field.modulus
      | .sub => (Field.modulus + a - b) % Field.modulus
      | .mul => (a * b) % Field.modulus
    | .uint _ => match op with
      | .add => pure (a + b)
      | .mul => pure (a * b)
      | .sub =>
        if b ≤ a then pure (a - b) else throw "unsigned subtraction underflow"
    | .bytes _ | .opaqueBytes => throw "byte strings do not support scalar arithmetic"
    | .jubjubScalar => throw "Jubjub scalars require a qualified curve operation"
    | .jubjubPoint => throw "Jubjub points require a qualified curve operation"
    | .foreign _ => throw "foreign values require a qualified curve operation"
  let value := { kind := result, number : Value }
  value.validate
  return value

/-- Casts between the three scalar families are allowed; narrowing is checked.
Nominal aliases and composites require separate rules and are not modeled here. -/
def cast (value : Value) (target : Kind) : Except String Value := do
  value.validate
  validate target
  if value.kind == .jubjubScalar || value.kind == .jubjubPoint ||
      (match value.kind with | .foreign _ | .opaqueBytes => true | _ => false) then
    throw "Jubjub values do not support scalar casts"
  if target == .jubjubScalar || target == .jubjubPoint ||
      (match target with | .foreign _ | .opaqueBytes => true | _ => false) then
    throw "Jubjub values do not support scalar casts"
  let number := if target == .bool then (if value.number == 0 then 0 else 1) else value.number
  let result := {kind := target, number : Value}
  result.validate
  return result

def literal (number : Nat) : Except String Value := do
  let kind := if number ≤ maxUint then Kind.uint number else .native
  let value := {kind, number : Value}
  value.validate
  return value

theorem maxUint_lt_native : maxUint < Field.modulus := by decide

theorem addition_range (a b m n : Nat) (ha : a ≤ m) (hb : b ≤ n) :
    a + b ≤ m + n := Nat.add_le_add ha hb

theorem multiplication_range (a b m n : Nat) (ha : a ≤ m) (hb : b ≤ n) :
    a * b ≤ m * n := Nat.mul_le_mul ha hb

theorem subtraction_range (a b m : Nat) (ha : a ≤ m) : a - b ≤ m :=
  Nat.le_trans (Nat.sub_le a b) ha

theorem widening_range (value source target : Nat)
    (hv : value ≤ source) (hst : source ≤ target) : value ≤ target :=
  Nat.le_trans hv hst

theorem exclusive_addition_maximum (m n : Nat) (hm : 0 < m) (hn : 0 < n) :
    (m - 1) + (n - 1) + 1 = m + n - 1 := by omega

end Noctium.ScalarPolicy
