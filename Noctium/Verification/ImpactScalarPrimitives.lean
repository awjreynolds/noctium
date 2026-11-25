import Noctium.Verification.ScalarNormalization
import Noctium.Verification.ImpactExpressionNode

namespace Noctium.Verification.ImpactScalarPrimitives

open Noctium

abbrev Binary := ImpactExpressionNode.Binary
abbrev Unsigned := ImpactExpressionNode.Unsigned

/-- Scalar tags carried by the Rust `Value` representation. -/
def scalarType? : Value → Option Ty
  | .native _ => some .native
  | .bool _ => some .bool
  | .uint maximum _ => some (.uint maximum)
  | _ => none

/-- Numeric projection for the three scalar families accepted by Rust casts. -/
def scalarNumber? : Value → Option Nat
  | .native value => some value
  | .bool value => some (if value then 1 else 0)
  | .uint _ value => some value
  | _ => none

/-- Rust-compatible scalar validity, parameterized by the active field modulus. -/
def canonical (modulus : Nat) : Value → Bool
  | .native value => value < modulus
  | .bool _ => true
  | .uint maximum value =>
      maximum ≤ ScalarPolicy.maxUint && value ≤ maximum && value < modulus
  | _ => false

/-- Check a Native literal before constructing its dynamic value. -/
def nativeLiteral (modulus value : Nat) : Option Value :=
  if value < modulus then some (.native value) else none

/-- Check a UInt literal against its inclusive declared maximum. -/
def uintLiteral (modulus maximum value : Nat) : Option Value :=
  if maximum ≤ ScalarPolicy.maxUint && value ≤ maximum && value < modulus then
    some (.uint maximum value)
  else none

/-- Evaluate a Rust-like Native field operator. Inputs must already be
canonical Native values. -/
def nativeBinary (modulus : Nat) (op : Binary) (left right : Value) : Option Value := do
  guard (0 < modulus)
  guard (canonical modulus left)
  guard (canonical modulus right)
  let .native a := left | none
  let .native b := right | none
  match op with
  | .add => some (.native ((a + b) % modulus))
  | .mul => some (.native ((a * b) % modulus))
  | .sub => some (.native ((modulus + a - b) % modulus))
  | .eq => none

/-- Evaluate a Rust-like checked UInt operator. `encodedBound` is the
inclusive maximum supplied by the serialized operation. -/
def unsignedBinary (modulus encodedBound : Nat) (op : Unsigned)
    (left right : Value) : Option Value := do
  guard (0 < modulus)
  guard (canonical modulus left)
  guard (canonical modulus right)
  let .uint leftMaximum a := left | none
  let .uint rightMaximum b := right | none
  let inferredMaximum := match op with
    | .add => leftMaximum + rightMaximum
    | .sub => leftMaximum
    | .mul => leftMaximum * rightMaximum
  guard (inferredMaximum ≤ ScalarPolicy.maxUint)
  guard (encodedBound == inferredMaximum)
  let result ← match op with
    | .add => some (a + b)
    | .sub => if a < b then none else some (a - b)
    | .mul => some (a * b)
  guard (result ≤ inferredMaximum)
  guard (result < modulus)
  some (.uint inferredMaximum result)

/-- Scalar equality checks both dynamic tags before comparing payloads. -/
def equal (modulus : Nat) (left right : Value) : Option Value := do
  guard (canonical modulus left)
  guard (canonical modulus right)
  let leftType ← scalarType? left
  let rightType ← scalarType? right
  guard (leftType == rightType)
  match left, right with
  | .native a, .native b => some (.bool (a == b))
  | .bool a, .bool b => some (.bool (a == b))
  | .uint _ a, .uint _ b => some (.bool (a == b))
  | _, _ => none

/-- Select between already evaluated scalar values, preserving Rust's eager
child evaluation and checking the two result tags before choosing. -/
def select (modulus : Nat) (condition yes no : Value) : Option Value := do
  guard (canonical modulus condition)
  guard (canonical modulus yes)
  guard (canonical modulus no)
  let .bool choice := condition | none
  let yesType ← scalarType? yes
  let noType ← scalarType? no
  guard (yesType == noType)
  if choice then some yes else some no

/-- Cast a canonical scalar `Value` to a scalar target type. Non-scalar source
or target values fail, matching Rust's explicit-conversion boundary. -/
def cast (modulus : Nat) (target : Ty) (value : Value) : Option Value := do
  guard (canonical modulus value)
  let number ← scalarNumber? value
  match target with
  | .native => nativeLiteral modulus number
  | .bool => some (.bool (number != 0))
  | .uint maximum => uintLiteral modulus maximum number
  | _ => none

/-- The Rust `assertThen` guard accepts only a true Bool value. -/
def assert (condition : Value) : Option Unit :=
  match condition with
  | .bool true => some ()
  | _ => none

/-- Evaluate Poseidon2 with the supplied pinned oracle, only under the
canonical field modulus and for canonical Native operands and result. -/
def poseidon (ctx : EvalContext) (domain : Nat) (left right : Value) : Option Value := do
  guard (ctx.modulus == Field.modulus)
  guard (domain < ctx.modulus)
  guard (canonical ctx.modulus left)
  guard (canonical ctx.modulus right)
  let .native left := left | none
  let .native right := right | none
  let .ok result := ctx.poseidon2 domain left right | none
  guard (result < ctx.modulus)
  some (.native result)

theorem scalarType_pack (scalarType : ScalarNormalization.ScalarType ty)
    (value : ty.Denote) : scalarType? (Value.pack ty value) = some ty := by
  cases scalarType <;> rfl

theorem canonical_pack_iff (ctx : EvalContext)
    (fieldModulus : ctx.modulus = Field.modulus)
    {ty : Ty} (scalarType : ScalarNormalization.ScalarType ty)
    (value : ty.Denote) :
    canonical ctx.modulus (Value.pack ty value) = true ↔
      ScalarNormalization.Canonical ty value := by
  rw [fieldModulus]
  cases scalarType with
  | native =>
      simp [canonical, ScalarNormalization.Canonical,
        ScalarNormalization.sourceNumber?, Value.pack]
  | bool => cases value <;>
      simp [canonical, ScalarNormalization.Canonical,
        ScalarNormalization.sourceNumber?, Value.pack, Field.modulus] <;> decide
  | uint maximum =>
      change (decide (maximum ≤ ScalarPolicy.maxUint) && decide (value ≤ maximum) &&
        decide (value < Field.modulus)) = true ↔
        ScalarNormalization.Canonical (.uint maximum) value
      simp only [Bool.and_eq_true, decide_eq_true_eq,
        ScalarNormalization.Canonical, ScalarNormalization.sourceNumber?]
      constructor
      · rintro ⟨⟨maximumBound, valueBound⟩, fieldBound⟩
        exact ⟨fieldBound, maximumBound, valueBound⟩
      · rintro ⟨fieldBound, maximumBound, valueBound⟩
        exact ⟨⟨maximumBound, valueBound⟩, fieldBound⟩

/-- Dynamic scalar casting agrees with the typed normalization cast after the
source has passed the same canonical check. -/
theorem cast_eq_scalarCast (ctx : EvalContext)
    (fieldModulus : ctx.modulus = Field.modulus)
    {source target : Ty} (sourceType : ScalarNormalization.ScalarType source)
    (targetType : ScalarNormalization.ScalarType target) (value : source.Denote)
    (canonicalSource : ScalarNormalization.Canonical source value) :
    cast ctx.modulus target (Value.pack source value) =
      (ScalarNormalization.scalarCast ctx target targetType
        (ScalarNormalization.number sourceType value)).toOption.map (Value.pack target) := by
  rw [fieldModulus]
  cases sourceType <;> cases targetType <;>
    simp_all [guard, Except.toOption, Option.map,
      cast, canonical,
      scalarNumber?, nativeLiteral,
      uintLiteral, ScalarNormalization.scalarCast,
      ScalarNormalization.number, ScalarNormalization.Canonical,
      ScalarNormalization.sourceNumber?, Value.pack] <;> split <;>
      split <;> simp_all

/-- Under the pinned-oracle agreement used by scalar verification, dynamic
Poseidon2 returns the same canonical hash value as the relation. -/
theorem poseidon_agrees (ctx : EvalContext) (hash : NativeRelation.Hash)
    (agreement : NativeRelation.HashAgreement ctx hash)
    (domain left right : Nat) (domainBound : domain < Field.modulus)
    (leftBound : left < Field.modulus) (rightBound : right < Field.modulus) :
    poseidon ctx domain (.native left) (.native right) =
      some (.native (hash [NativeRelation.scalar domain, NativeRelation.scalar left,
        NativeRelation.scalar right]).val) := by
  have domainScalar : NativeRelation.scalar domain = ⟨domain, domainBound⟩ := by
    apply Fin.ext
    simp [NativeRelation.scalar, Nat.mod_eq_of_lt domainBound]
  have leftScalar : NativeRelation.scalar left = ⟨left, leftBound⟩ := by
    apply Fin.ext
    simp [NativeRelation.scalar, Nat.mod_eq_of_lt leftBound]
  have rightScalar : NativeRelation.scalar right = ⟨right, rightBound⟩ := by
    apply Fin.ext
    simp [NativeRelation.scalar, Nat.mod_eq_of_lt rightBound]
  have oracle := agreement.calls (NativeRelation.scalar domain) (NativeRelation.scalar left)
    (NativeRelation.scalar right)
  rw [domainScalar, leftScalar, rightScalar] at oracle
  have resultBound' :
      (hash [⟨domain, domainBound⟩, ⟨left, leftBound⟩,
        ⟨right, rightBound⟩]).val < Field.modulus :=
    (hash [⟨domain, domainBound⟩, ⟨left, leftBound⟩,
      ⟨right, rightBound⟩]).isLt
  rw [domainScalar, leftScalar, rightScalar]
  simp [poseidon, agreement.modulus, canonical, domainBound, leftBound,
    rightBound, oracle, resultBound'] <;> rfl

end Noctium.Verification.ImpactScalarPrimitives
