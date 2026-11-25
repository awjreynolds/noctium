import Noctium.Verification.NativeState

namespace Noctium.Verification.ImpactStatementScalar

open NativeRelation NativeState

/-- Conditions under which a modeled operation has the runtime conversion
used by the scalar Noctium state backend. Root slots come from its `u32`
schema, map keys are field-aligned scalar values, and insert depths match the
scoped runtime conversion. The ledger declaration must supply the corresponding
field-aligned map key schema. -/
def RuntimeConversionCompatible : NativeState.Op → Prop
  | .push _ _ | .popeq _ | .dup | .member => True
  | .index slot _ => slot < 2 ^ 32
  | .mapIndex slot key => slot < 2 ^ 32 ∧ key.alignment = .field
  | .insert levels => 0 < levels ∧ levels < 16

/-- The `FieldRepr` opcode for an uncached native insert. The upstream opcode
uses bitwise OR. For supported insertion depths this equals `0x90 + levels`.
-/
def insertOpcode (levels : Nat) : Nat := 0x90 ||| levels

/-- Scalar field encoding of the modeled onchain VM operations. `Cell.fields`
is the aligned-value representation. A pushed state cell carries its
`StateValue::Cell` tag after the opcode. `mapIndex` encodes `Idx` with the
two-entry path `[root slot, field key]`. -/
def opFields : NativeState.Op → List NativeRelation.Scalar
  | .push value storage =>
      [scalar (if storage then 0x11 else 0x10), one] ++ value.fields
  | .popeq value => scalar 0x0c :: value.fields
  | .dup => [scalar 0x30]
  | .index slot pushPath =>
      scalar (if pushPath then 0x70 else 0x50) :: (field (scalar slot)).fields
  | .mapIndex slot key =>
      scalar 0x51 :: ((field (scalar slot)).fields ++ key.fields)
  | .member => [scalar 0x18]
  | .insert levels => [scalar (insertOpcode levels)]

@[simp] theorem fieldCell_fields (value : NativeRelation.Scalar) :
    (NativeState.field value).fields =
      [one, scalar (Field.modulus - 2), value] := by
  simp [NativeState.field, NativeState.Cell.fields]

@[simp] theorem booleanCell_fields (value : _root_.Bool) :
    (NativeState.boolean value).fields = [one, one, bit value] := by
  simp [NativeState.boolean, NativeState.Cell.fields]

/-- The pinned VM's field-size equations reduce to these widths for the
modeled scalar operations. -/
def opFieldWidth : NativeState.Op → Nat
  | .push _ _ => 5
  | .popeq _ => 4
  | .dup => 1
  | .index _ _ => 4
  | .mapIndex _ _ => 7
  | .member => 1
  | .insert _ => 1

@[simp] theorem cellFields_length (value : NativeState.Cell) :
    value.fields.length = 3 := by
  simp [NativeState.Cell.fields]

/-- Every encoded operation has the width reported by the pinned
`FieldRepr::field_size` cases for this modeled subset. -/
theorem opFields_length (operation : NativeState.Op) :
    (opFields operation).length = opFieldWidth operation := by
  cases operation <;> simp [opFields, opFieldWidth, NativeState.Cell.fields]

theorem insertOpcode_eq_add_of_lt16 (levels : Nat) (fits : levels < 16) :
    insertOpcode levels = 0x90 + levels := by
  have bounded : levels = 0 ∨ levels = 1 ∨ levels = 2 ∨ levels = 3 ∨
      levels = 4 ∨ levels = 5 ∨ levels = 6 ∨ levels = 7 ∨
      levels = 8 ∨ levels = 9 ∨ levels = 10 ∨ levels = 11 ∨
      levels = 12 ∨ levels = 13 ∨ levels = 14 ∨ levels = 15 := by omega
  rcases bounded with h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h
  all_goals subst levels <;> decide

/-- The new encoder agrees field-for-field with the existing Lean native
relation encoder for operations whose insert depth fits the VM's low opcode
bits. -/
theorem opFields_eq_nativeFields (operation : NativeState.Op)
    (insertFits : match operation with
      | .insert levels => levels < 16
      | _ => True) :
    opFields operation = operation.fields := by
  cases operation with
  | push value storage => rfl
  | popeq value => rfl
  | dup => rfl
  | index slot pushPath => rfl
  | mapIndex slot key => rfl
  | member => rfl
  | insert levels =>
      simp only [opFields, NativeState.Op.fields]
      rw [insertOpcode_eq_add_of_lt16 levels insertFits]

theorem opFields_eq_nativeFields_of_runtimeCompatible (operation : NativeState.Op)
    (compatible : RuntimeConversionCompatible operation) :
    opFields operation = operation.fields := by
  cases operation with
  | push value storage => rfl
  | popeq value => rfl
  | dup => rfl
  | index slot pushPath => rfl
  | mapIndex slot key => rfl
  | member => rfl
  | insert levels =>
      simp only [RuntimeConversionCompatible] at compatible
      exact opFields_eq_nativeFields (.insert levels) compatible.2

end Noctium.Verification.ImpactStatementScalar
