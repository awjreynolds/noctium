import Noctium.Verification.NativeState
import Noctium.Verification.ScalarNormalization
import Noctium.Verification.SourceEffects
import Noctium.Verification.GenericStateKeys

namespace Noctium.Verification.GenericStateEncoding
open NativeRelation NativeState ScalarNormalization

/-- The native flat state root stores only Native, Bool, and bounded UInt
scalars. Carry the source scalar witness into every accepted field projection. -/
@[simp] def scalarType? : (ty : Ty) → Option (ScalarType ty)
  | .native => some .native
  | .bool => some .bool
  | .uint maximum => if maximum ≤ ScalarPolicy.maxUint then some (.uint maximum) else none
  | .bytes _ | .opaqueBytes | .opaqueString | .jubjubScalar | .jubjubPoint | .foreign _ => none

/-- Numeric projection on the historical scalar storage subset. Unsupported
types only appear in impossible canonical theorem branches, and the encoder
rejects them before constructing a field. -/
@[simp] def number : (ty : Ty) → ty.Denote → Nat
  | .native, value | .uint _, value => value
  | .bool, value => if value then 1 else 0
  | .bytes _, _ | .opaqueBytes, _ | .opaqueString, _ | .jubjubScalar, _ |
    .jubjubPoint, _ | .foreign _, _ => 0

theorem sourceScalar_eq_field {ty : Ty} (support : ScalarType ty)
    (value : ty.Denote) :
    sourceScalar? ty value = some (scalar (number ty value)) := by
  cases support <;> rfl

/-- A native field cell retains the source type in the declaration schema.
Boolean cells use field alignment; membership results use bit alignment. -/
@[simp] private def encodeScalarValue : (ty : Ty) → ty.Denote → Option Cell
  | .native, value =>
    if value < Field.modulus then some (field (scalar value)) else none
  | .bool, value => some (field (scalar (if value then 1 else 0)))
  | .uint maximum, value =>
    if maximum ≤ ScalarPolicy.maxUint && value ≤ maximum && value < Field.modulus then
      some (field (scalar value))
    else none
  | .bytes _, _ | .opaqueBytes, _ | .opaqueString, _ | .jubjubScalar, _ |
    .jubjubPoint, _ | .foreign _, _ => none

def encodeValue (ty : Ty) (raw : Value) : Option Cell := do
  let some value := raw.as ty | none
  encodeScalarValue ty value

def decodeValue : Ty → Cell → Option Value
  | .native, ⟨.field, value⟩ => some (.native value.val)
  | .bool, ⟨.field, value⟩ =>
    if value = zero then some (.bool false)
    else if value = one then some (.bool true) else none
  | .uint maximum, ⟨.field, value⟩ =>
    if maximum ≤ ScalarPolicy.maxUint && value.val ≤ maximum then
      some (.uint maximum value.val)
    else none
  | _, _ => none

def encodeMapEntry (keyTy valueTy : Ty) (entry : Value × Value) : Option (Scalar × Scalar) := do
  let some key := encodeValue keyTy entry.1 | none
  let some value := encodeValue valueTy entry.2 | none
  some (key.value, value.value)

def encodeDeclaration (state : LedgerState) (declaration : StateDecl) : Option Slot :=
  match declaration.kind with
  | .cell ty => do
    unless declaration.cellAlignment?.isNone do none
    let raw ← state.cells.lookup declaration.name
    let value ← encodeValue ty raw
    some (Slot.cell value)
  | .map keyTy valueTy => do
    let entries ← state.maps.lookup declaration.name
    let encoded ← entries.mapM (encodeMapEntry keyTy valueTy)
    if (encoded.map Prod.fst).eraseDups.length != encoded.length then none else
    some (Slot.map encoded)
  | .tree _ | .merkleTree _ | .historicMerkleTree _ | .opaqueString => none

/-- Raw declaration fold used by transition and frame proofs. It preserves
declaration order and encodes each declared cell or map, but it does not
validate the complete initial ledger shape or reject unsupported empty maps.
Initial-state admission must go through `encodeInitialState`. -/
def encodeState (declarations : List StateDecl) (state : LedgerState) :
    Option (List Slot) := declarations.mapM (encodeDeclaration state)

def initial (slots : List Slot) : Machine :=
  ⟨[.vector slots], []⟩

def cellCount (declarations : List StateDecl) : Nat :=
  (declarations.filter fun declaration => match declaration.kind with
    | .cell _ => true
    | .map _ _ | .tree _ | .merkleTree _ | .historicMerkleTree _ | .opaqueString => false).length

def mapCount (declarations : List StateDecl) : Nat :=
  (declarations.filter fun declaration => match declaration.kind with
    | .map _ _ => true
    | .cell _ | .tree _ | .merkleTree _ | .historicMerkleTree _ | .opaqueString => false).length

/-- Checked entry point for a native initial state. It admits only unique,
declaration-ordered Native, Bool, bounded UInt cells and maps, requires exact
cell/map association-list counts, and rejects trees and unencoded effect
collections. `encodeState` remains the raw declaration fold used after this
boundary by transition proofs. -/
def declarationSupported : StateDecl → Bool
  | {kind := .cell ty, cellAlignment? := none, ..} => (scalarType? ty).isSome
  | {kind := .map keyTy valueTy, ..} =>
    (scalarType? keyTy).isSome && (scalarType? valueTy).isSome
  | _ => false

def initialShapeValid (declarations : List StateDecl) (state : LedgerState) : Bool :=
  decide (declarations.length < Field.modulus) &&
    state.cells.length == cellCount declarations &&
    state.maps.length == mapCount declarations && state.trees.isEmpty &&
    state.events.isEmpty && state.shieldedMints.isEmpty && state.unshieldedMints.isEmpty &&
    state.unshieldedInputs.isEmpty && state.unshieldedOutputs.isEmpty &&
    state.unshieldedSpendClaims.isEmpty &&
    uniqueNames (declarations.map (·.name)) &&
    uniqueNames (state.cells.map Prod.fst) && uniqueNames (state.maps.map Prod.fst) &&
    declarations.all declarationSupported

def encodeInitialState (declarations : List StateDecl) (state : LedgerState) :
    Option (List Slot) :=
  if initialShapeValid declarations state then encodeState declarations state else none

/-- Proof boundary for a checked initial ledger: declarations and source
associations have unique names, cell/map counts match exactly, no recursive
roots exist, and `encodeInitialState` produced the supplied ordered slots.
This does not assert a source transition result or native trace outcome. -/
structure AdmittedState (declarations : List StateDecl)
    (source : LedgerState) (slots : List Slot) : Prop where
  uniqueDeclarations : uniqueNames (declarations.map (·.name)) = true
  uniqueCells : uniqueNames (source.cells.map Prod.fst) = true
  uniqueMaps : uniqueNames (source.maps.map Prod.fst) = true
  exactCellCount : source.cells.length = cellCount declarations
  exactMapCount : source.maps.length = mapCount declarations
  noRecursiveRoots : source.trees = []
  slotBound : declarations.length < Field.modulus
  initialEncoded : encodeInitialState declarations source = some slots

theorem AdmittedState.encoded (admitted : AdmittedState declarations source slots) :
    encodeState declarations source = some slots := by
  have encoded := admitted.initialEncoded
  unfold encodeInitialState at encoded
  split at encoded
  · exact encoded
  · simp at encoded

/-- The checked initial encoder admits every declaration, including empty maps
whose element types cannot be inferred from stored values. -/
theorem AdmittedState.declarationsSupported
    (admitted : AdmittedState declarations source slots) :
    ∀ declaration ∈ declarations, declarationSupported declaration = true := by
  have encoded := admitted.initialEncoded
  unfold encodeInitialState at encoded
  split at encoded
  · rename_i valid
    simp only [initialShapeValid, Bool.and_eq_true] at valid
    exact List.all_eq_true.mp valid.2
  · cases encoded

/-- The cell located by the actual source name has an unaligned scalar type
in the checked ledger schema. -/
theorem AdmittedState.cellType
    (admitted : AdmittedState declarations source slots)
    (name : String) (declaration : StateDecl) (ty : Ty)
    (found : declarations.find? (·.name == name) = some declaration)
    (kind : declaration.kind = .cell ty) :
    declaration.cellAlignment? = none ∧ (scalarType? ty).isSome = true := by
  have supported := admitted.declarationsSupported declaration (List.mem_of_find?_eq_some found)
  cases declaration with
  | mk name declaredKind sealed span alignment =>
    change declaredKind = .cell ty at kind
    subst declaredKind
    cases alignment <;> simp_all [declarationSupported]

/-- An empty map still supplies checked key and value type witnesses from the
initial schema. A successful raw state fold alone does not establish this. -/
theorem AdmittedState.mapTypes
    (admitted : AdmittedState declarations source slots)
    (name : String) (declaration : StateDecl) (keyTy valueTy : Ty)
    (found : declarations.find? (·.name == name) = some declaration)
    (kind : declaration.kind = .map keyTy valueTy) :
    (scalarType? keyTy).isSome = true ∧ (scalarType? valueTy).isSome = true := by
  have supported := admitted.declarationsSupported declaration (List.mem_of_find?_eq_some found)
  cases declaration with
  | mk name declaredKind sealed span alignment =>
    change declaredKind = .map keyTy valueTy at kind
    subst declaredKind
    exact Bool.and_eq_true_iff.mp supported

theorem AdmittedState.distinctDeclarations
    (admitted : AdmittedState declarations source slots) :
    declarations.Pairwise (fun left right => left.name ≠ right.name) := by
  have unique : (declarations.map (·.name)).eraseDups.length =
      (declarations.map (·.name)).length := by
    apply beq_iff_eq.mp
    simpa [uniqueNames] using admitted.uniqueDeclarations
  have namesDistinct := GenericStateKeys.nodup_of_eraseDups_length_eq
    (declarations.map (·.name)) unique
  exact List.Pairwise.of_map (fun declaration : StateDecl => declaration.name)
    (by intro left right different; exact different)
    (List.nodup_iff_pairwise_ne.mp namesDistinct)

theorem encodeState_nil (state : LedgerState) : encodeState [] state = some [] := rfl

theorem encodeState_length (declarations : List StateDecl) (state : LedgerState)
    (slots : List Slot) (encoded : encodeState declarations state = some slots) :
    slots.length = declarations.length := by
  induction declarations generalizing slots with
  | nil => simp [encodeState] at encoded; cases encoded; rfl
  | cons head tail ih =>
    simp only [encodeState, List.mapM_cons] at encoded
    cases first : encodeDeclaration state head with
    | none => simp [first] at encoded
    | some value =>
      cases rest : tail.mapM (encodeDeclaration state) with
      | none => simp [first, rest] at encoded
      | some result =>
        simp [first, rest] at encoded
        cases encoded
        simp [ih result rest]

/-- Each native root slot comes from the corresponding declared state item.
The option equality also covers out-of-range indexes without inventing a slot. -/
theorem encodeState_slot (declarations : List StateDecl) (state : LedgerState)
    (slots : List Slot) (slot : Nat)
    (accepted : encodeState declarations state = some slots) :
    slots[slot]? = (declarations[slot]?).bind (encodeDeclaration state) := by
  induction declarations generalizing slots slot with
  | nil =>
    simp [encodeState] at accepted
    cases accepted
    simp
  | cons declaration rest ih =>
    simp only [encodeState, List.mapM_cons] at accepted
    cases first : encodeDeclaration state declaration with
    | none => simp [first] at accepted
    | some value =>
      cases later : rest.mapM (encodeDeclaration state) with
      | none => simp [first, later] at accepted
      | some remainder =>
        simp [first, later] at accepted
        cases accepted
        cases slot with
        | zero => simp [first]
        | succ index => simpa using ih remainder index later

theorem encodeValue_pack (ty : Ty) (value : ty.Denote)
    (canonical : Canonical ty value) :
    encodeValue ty (Value.pack ty value) = some (field (scalar (number ty value))) := by
  cases ty <;> simp_all [Canonical, ScalarNormalization.sourceNumber?, encodeValue,
    Value.pack, Value.as, scalarType?, encodeScalarValue, number]

theorem encodeMapEntry_pack (keyTy valueTy : Ty)
    (key : keyTy.Denote) (value : valueTy.Denote)
    (keyCanonical : Canonical keyTy key)
    (valueCanonical : Canonical valueTy value) :
    encodeMapEntry keyTy valueTy
      (Value.pack keyTy key, Value.pack valueTy value) =
      some (scalar (number keyTy key), scalar (number valueTy value)) := by
  simp [encodeMapEntry, encodeValue_pack, keyCanonical, valueCanonical, field]

theorem decode_encode_pack (ty : Ty) (value : ty.Denote)
    (canonical : Canonical ty value) :
    decodeValue ty (field (scalar (number ty value))) = some (Value.pack ty value) := by
  cases ty with
  | native =>
    simp only [Canonical, ScalarNormalization.sourceNumber?] at canonical
    simp [decodeValue, field, Value.pack, scalar_no_wrap _ canonical.1]
  | bool =>
    cases value <;> decide
  | uint maximum =>
    simp only [Canonical, ScalarNormalization.sourceNumber?] at canonical
    simp [decodeValue, field, Value.pack, scalar_no_wrap _ canonical.1,
      canonical.2.1, canonical.2.2]
  | bytes _ | opaqueBytes | opaqueString | jubjubScalar | jubjubPoint | foreign _ =>
    simp [Canonical, ScalarNormalization.sourceNumber?] at canonical

/-- Accepted typed encodings round-trip. This rules out a native read being
attributed to a different source value of the same declared type. -/
theorem decode_encodeValue (ty : Ty) (raw : Value) (cell : Cell)
    (accepted : encodeValue ty raw = some cell) :
    decodeValue ty cell = some raw := by
  cases ty with
  | native =>
    cases raw with
    | native value =>
      by_cases canonical : value < Field.modulus
      · simp [encodeValue, Value.as, encodeScalarValue, canonical] at accepted
        cases accepted
        exact decode_encode_pack .native value ⟨canonical, trivial⟩
      · simp [encodeValue, Value.as, encodeScalarValue, canonical] at accepted
    | _ => simp [encodeValue, Value.as] at accepted
  | bool =>
    cases raw with
    | bool value =>
      simp [encodeValue, Value.as, encodeScalarValue] at accepted
      cases accepted
      exact decode_encode_pack .bool value ⟨by cases value <;> decide, trivial⟩
    | _ => simp [encodeValue, Value.as] at accepted
  | uint maximum =>
    cases raw with
    | uint found value =>
      by_cases same : maximum = found
      · subst found
        by_cases within : maximum ≤ ScalarPolicy.maxUint ∧
            value ≤ maximum ∧ value < Field.modulus
        · simp [encodeValue, Value.as, encodeScalarValue, within.1, within.2.1,
            within.2.2] at accepted
          cases accepted
          exact decode_encode_pack (.uint maximum) value
            ⟨within.2.2, within.1, within.2.1⟩
        · simp [encodeValue, Value.as, encodeScalarValue] at accepted
          have allowed : maximum ≤ ScalarPolicy.maxUint ∧
              value ≤ maximum ∧ value < Field.modulus :=
            ⟨accepted.1.1.1, accepted.1.1.2, accepted.1.2⟩
          exact False.elim (within allowed)
      · simp [encodeValue, Value.as, same] at accepted
    | _ => simp [encodeValue, Value.as] at accepted
  | bytes length =>
    cases h : raw.as (.bytes length) <;> simp [encodeValue, encodeScalarValue, h] at accepted
  | opaqueBytes =>
    cases h : raw.as .opaqueBytes <;> simp [encodeValue, encodeScalarValue, h] at accepted
  | opaqueString =>
    cases h : raw.as .opaqueString <;> simp [encodeValue, encodeScalarValue, h] at accepted
  | jubjubScalar =>
    cases h : raw.as .jubjubScalar <;> simp [encodeValue, encodeScalarValue, h] at accepted
  | jubjubPoint =>
    cases h : raw.as .jubjubPoint <;> simp [encodeValue, encodeScalarValue, h] at accepted
  | foreign kind =>
    cases h : raw.as (.foreign kind) <;> simp [encodeValue, encodeScalarValue, h] at accepted

theorem encodeValue_source (ty : Ty) (raw : Value) (cell : Cell)
    (accepted : encodeValue ty raw = some cell) :
    ∃ value, raw.as ty = some value ∧ Canonical ty value ∧
      cell = field (scalar (number ty value)) := by
  cases ty with
  | native =>
    cases raw with
    | native value =>
      by_cases bound : value < Field.modulus
      · simp [encodeValue, Value.as, encodeScalarValue, bound] at accepted
        exact ⟨value, rfl, ⟨bound, trivial⟩, accepted.symm⟩
      · simp [encodeValue, Value.as, encodeScalarValue, bound] at accepted
    | _ => simp [encodeValue, Value.as] at accepted
  | bool =>
    cases raw with
    | bool value =>
      simp [encodeValue, Value.as, encodeScalarValue] at accepted
      exact ⟨value, rfl, ⟨by cases value <;> decide, trivial⟩, accepted.symm⟩
    | _ => simp [encodeValue, Value.as] at accepted
  | uint maximum =>
    cases raw with
    | uint found value =>
      by_cases same : maximum = found
      · subst found
        simp [encodeValue, Value.as, encodeScalarValue] at accepted
        have hmax := accepted.1.1.1
        have hvalue := accepted.1.1.2
        have hfield := accepted.1.2
        have equal := accepted.2
        exact ⟨value, by simp [Value.as], ⟨hfield, hmax, hvalue⟩, equal.symm⟩
      · simp [encodeValue, Value.as, same] at accepted
    | _ => simp [encodeValue, Value.as] at accepted
  | bytes length =>
    cases h : raw.as (.bytes length) <;> simp [encodeValue, encodeScalarValue, h] at accepted
  | opaqueBytes =>
    cases h : raw.as .opaqueBytes <;> simp [encodeValue, encodeScalarValue, h] at accepted
  | opaqueString =>
    cases h : raw.as .opaqueString <;> simp [encodeValue, encodeScalarValue, h] at accepted
  | jubjubScalar =>
    cases h : raw.as .jubjubScalar <;> simp [encodeValue, encodeScalarValue, h] at accepted
  | jubjubPoint =>
    cases h : raw.as .jubjubPoint <;> simp [encodeValue, encodeScalarValue, h] at accepted
  | foreign kind =>
    cases h : raw.as (.foreign kind) <;> simp [encodeValue, encodeScalarValue, h] at accepted

theorem encoded_cell_source (state : LedgerState) (name : String)
    (ty : Ty) (cell : Cell)
    (encoded : encodeDeclaration state {name, kind := .cell ty} =
      some (.cell cell)) :
    ∃ raw, state.cells.lookup name = some raw ∧ decodeValue ty cell = some raw := by
  unfold encodeDeclaration at encoded
  cases found : state.cells.lookup name with
  | none => simp [found] at encoded
  | some raw =>
    cases packed : encodeValue ty raw with
    | none => simp [found, packed] at encoded
    | some actual =>
      simp [found, packed] at encoded
      cases encoded
      exact ⟨raw, rfl, decode_encodeValue ty raw cell packed⟩

theorem encoded_cell_typed (state : LedgerState) (name : String)
    (ty : Ty) (cell : Cell)
    (encoded : encodeDeclaration state {name, kind := .cell ty} =
      some (.cell cell)) :
    ∃ value,
      state.cells.lookup name = some (Value.pack ty value) ∧
      Canonical ty value ∧
      cell = field (scalar (number ty value)) := by
  unfold encodeDeclaration at encoded
  cases found : state.cells.lookup name with
  | none => simp [found] at encoded
  | some raw =>
    cases packed : encodeValue ty raw with
    | none => simp [found, packed] at encoded
    | some actual =>
      simp [found, packed] at encoded
      cases encoded
      obtain ⟨value, typed, canonical, same⟩ := encodeValue_source ty raw cell packed
      cases ty with
      | native =>
        cases raw <;> simp [Value.as] at typed
        cases typed
        exact ⟨value, rfl, canonical, same⟩
      | bool =>
        cases raw <;> simp [Value.as] at typed
        cases typed
        exact ⟨value, rfl, canonical, same⟩
      | uint maximum =>
        cases raw <;> simp [Value.as] at typed
        rcases typed with ⟨sameMax, sameValue⟩
        subst sameMax
        cases sameValue
        exact ⟨value, rfl, canonical, same⟩
      | bytes _ | opaqueBytes | opaqueString | jubjubScalar | jubjubPoint | foreign _ =>
        simp [Canonical, ScalarNormalization.sourceNumber?] at canonical

private theorem option_mapM_member {α β : Type} (f : α → Option β)
    (items : List α) (results : List β) (item : α)
    (accepted : items.mapM f = some results) (member : item ∈ items) :
    ∃ result, f item = some result ∧ result ∈ results := by
  induction items generalizing results with
  | nil => simp at member
  | cons head tail ih =>
    simp only [List.mapM_cons] at accepted
    cases first : f head with
    | none => simp [first] at accepted
    | some value =>
      cases later : tail.mapM f with
      | none => simp [first, later] at accepted
      | some rest =>
        simp [first, later] at accepted
        cases accepted
        rcases List.mem_cons.mp member with equal | inTail
        · subst item
          exact ⟨value, first, by simp⟩
        · obtain ⟨result, encoded, inResults⟩ := ih rest later inTail
          exact ⟨result, encoded, List.mem_cons_of_mem _ inResults⟩

private theorem foreignCurve_beq_eq (left right : Foreign.Curve)
    (same : (left == right) = true) : left = right := by
  cases left <;> cases right
  all_goals change Foreign.instBEqCurve.beq _ _ = true at same
  all_goals simp [Foreign.instBEqCurve.beq, Foreign.Curve.ctorIdx] at same ⊢

private theorem foreignPoint_beq_eq (left right : Foreign.Point)
    (same : (left == right) = true) : left = right := by
  cases left with
  | identity => cases right with
    | identity => rfl
    | affine _ _ => simp [Foreign.instBEqPoint.beq, BEq.beq] at same
  | affine leftX leftY => cases right with
    | identity => simp [Foreign.instBEqPoint.beq, BEq.beq] at same
    | affine rightX rightY =>
      change Foreign.instBEqPoint.beq (.affine leftX leftY) (.affine rightX rightY) = true at same
      simp [Foreign.instBEqPoint.beq, BEq.beq] at same
      rcases same with ⟨sameX, sameY⟩
      cases sameX
      cases sameY
      rfl

private theorem foreignCurve_beq_refl (curve : Foreign.Curve) :
    Foreign.instBEqCurve.beq curve curve = true := by
  cases curve <;> rfl

private theorem foreignPoint_beq_refl (point : Foreign.Point) :
    Foreign.instBEqPoint.beq point point = true := by
  cases point <;> simp [Foreign.instBEqPoint.beq, BEq.beq]

private theorem foreignKind_beq_eq (left right : Foreign.Kind)
    (same : (left == right) = true) : left = right := by
  cases left with
  | base leftCurve =>
    cases right with
    | base rightCurve =>
      change (leftCurve == rightCurve) = true at same
      exact congrArg Foreign.Kind.base (foreignCurve_beq_eq leftCurve rightCurve same)
    | _ => simp [BEq.beq, Foreign.instBEqKind.beq, Foreign.Kind.ctorIdx] at same
  | scalar leftCurve =>
    cases right with
    | scalar rightCurve =>
      change (leftCurve == rightCurve) = true at same
      exact congrArg Foreign.Kind.scalar (foreignCurve_beq_eq leftCurve rightCurve same)
    | _ => simp [BEq.beq, Foreign.instBEqKind.beq, Foreign.Kind.ctorIdx] at same
  | point leftCurve =>
    cases right with
    | point rightCurve =>
      change (leftCurve == rightCurve) = true at same
      exact congrArg Foreign.Kind.point (foreignCurve_beq_eq leftCurve rightCurve same)
    | _ => simp [BEq.beq, Foreign.instBEqKind.beq, Foreign.Kind.ctorIdx] at same

private theorem ty_beq_refl (ty : Ty) : (ty == ty) = true := by
  cases ty with
  | native | bool | opaqueBytes | opaqueString | jubjubScalar | jubjubPoint => rfl
  | uint maximum => simp [BEq.beq, Noctium.instBEqTy.beq, Noctium.Ty.ctorIdx]
  | bytes length => simp [BEq.beq, Noctium.instBEqTy.beq, Noctium.Ty.ctorIdx]
  | foreign kind =>
    cases kind with
    | base curve => cases curve <;> rfl
    | scalar curve => cases curve <;> rfl
    | point curve => cases curve <;> rfl

private theorem ty_beq_eq (left right : Ty) (same : (left == right) = true) : left = right := by
  cases left with
  | native => cases right <;> simp [BEq.beq, Noctium.instBEqTy.beq, Noctium.Ty.ctorIdx] at same <;> rfl
  | bool => cases right <;> simp [BEq.beq, Noctium.instBEqTy.beq, Noctium.Ty.ctorIdx] at same <;> rfl
  | uint leftMaximum =>
    cases right with
    | uint rightMaximum =>
      simp only [BEq.beq, Noctium.instBEqTy.beq, Noctium.Ty.ctorIdx] at same
      exact congrArg Ty.uint (beq_iff_eq.mp same)
    | _ => simp [BEq.beq, Noctium.instBEqTy.beq, Noctium.Ty.ctorIdx] at same
  | bytes leftLength =>
    cases right with
    | bytes rightLength =>
      simp only [BEq.beq, Noctium.instBEqTy.beq, Noctium.Ty.ctorIdx] at same
      exact congrArg Ty.bytes (beq_iff_eq.mp same)
    | _ => simp [BEq.beq, Noctium.instBEqTy.beq, Noctium.Ty.ctorIdx] at same
  | opaqueBytes => cases right <;> simp [BEq.beq, Noctium.instBEqTy.beq, Noctium.Ty.ctorIdx] at same <;> rfl
  | opaqueString => cases right <;> simp [BEq.beq, Noctium.instBEqTy.beq, Noctium.Ty.ctorIdx] at same <;> rfl
  | jubjubScalar => cases right <;> simp [BEq.beq, Noctium.instBEqTy.beq, Noctium.Ty.ctorIdx] at same <;> rfl
  | jubjubPoint => cases right <;> simp [BEq.beq, Noctium.instBEqTy.beq, Noctium.Ty.ctorIdx] at same <;> rfl
  | foreign leftKind =>
    cases right with
    | foreign rightKind =>
      simp only [BEq.beq, Noctium.instBEqTy.beq, Noctium.Ty.ctorIdx] at same
      exact congrArg Ty.foreign (foreignKind_beq_eq leftKind rightKind same)
    | _ => simp [BEq.beq, Noctium.instBEqTy.beq, Noctium.Ty.ctorIdx] at same

local instance : LawfulBEq Ty where
  rfl {a} := ty_beq_refl a
  eq_of_beq {a b} h := ty_beq_eq a b h

private theorem recordFields_beq_refl (fields : List (Ty × List Nat)) :
    (fields == fields) = true := beq_self_eq_true fields

private theorem recordFields_beq_eq (left right : List (Ty × List Nat))
    (same : (left == right) = true) : left = right := beq_iff_eq.mp same

private theorem value_beq_refl (value : Value) : (value == value) = true := by
  cases value with
  | native value => simp [BEq.beq, Noctium.instBEqValue.beq, Noctium.Value.ctorIdx]
  | bool value => simp [BEq.beq, Noctium.instBEqValue.beq, Noctium.Value.ctorIdx]
  | uint maximum value => simp [BEq.beq, Noctium.instBEqValue.beq, Noctium.Value.ctorIdx]
  | bytes length values =>
    change Noctium.instBEqValue.beq (.bytes length values) (.bytes length values) = true
    simp [Noctium.instBEqValue.beq, Noctium.Value.ctorIdx,
      show (values == values) = true from beq_self_eq_true values]
  | opaqueBytes values =>
    change Noctium.instBEqValue.beq (.opaqueBytes values) (.opaqueBytes values) = true
    simp [Noctium.instBEqValue.beq, Noctium.Value.ctorIdx,
      show (values == values) = true from beq_self_eq_true values]
  | opaqueString value => simp [BEq.beq, Noctium.instBEqValue.beq, Noctium.Value.ctorIdx]
  | jubjubScalar value => simp [BEq.beq, Noctium.instBEqValue.beq, Noctium.Value.ctorIdx]
  | jubjubPoint x y => simp [BEq.beq, Noctium.instBEqValue.beq, Noctium.Value.ctorIdx]
  | foreignBase curve value =>
    change Foreign.instBEqCurve.beq curve curve && (value == value) = true
    simp [foreignCurve_beq_refl, beq_self_eq_true]
  | foreignScalar curve value =>
    change Foreign.instBEqCurve.beq curve curve && (value == value) = true
    simp [foreignCurve_beq_refl, beq_self_eq_true]
  | foreignPoint curve value =>
    change Foreign.instBEqCurve.beq curve curve && Foreign.instBEqPoint.beq value value = true
    simp [foreignCurve_beq_refl, foreignPoint_beq_refl]
  | record fields =>
    change Noctium.instBEqValue.beq (.record fields) (.record fields) = true
    simp [Noctium.instBEqValue.beq, Noctium.Value.ctorIdx, recordFields_beq_refl]

private theorem value_beq_eq (left right : Value) (same : (left == right) = true) :
    left = right := by
  cases left with
  | native leftValue =>
    cases right with
    | native rightValue =>
      simp only [BEq.beq, Noctium.instBEqValue.beq, Noctium.Value.ctorIdx] at same
      exact congrArg Value.native (beq_iff_eq.mp same)
    | _ => simp [BEq.beq, Noctium.instBEqValue.beq, Noctium.Value.ctorIdx] at same
  | bool leftValue =>
    cases right with
    | bool rightValue =>
      simp only [BEq.beq, Noctium.instBEqValue.beq, Noctium.Value.ctorIdx] at same
      exact congrArg Value.bool (beq_iff_eq.mp same)
    | _ => simp [BEq.beq, Noctium.instBEqValue.beq, Noctium.Value.ctorIdx] at same
  | uint leftMaximum leftValue =>
    cases right with
    | uint rightMaximum rightValue =>
      simp only [BEq.beq, Noctium.instBEqValue.beq, Noctium.Value.ctorIdx,
        Bool.and_eq_true] at same
      cases of_decide_eq_true same.1
      cases of_decide_eq_true same.2
      rfl
    | _ => simp [BEq.beq, Noctium.instBEqValue.beq, Noctium.Value.ctorIdx] at same
  | bytes leftLength leftValue =>
    cases right with
    | bytes rightLength rightValue =>
      simp only [BEq.beq, Noctium.instBEqValue.beq, Noctium.Value.ctorIdx,
        Bool.and_eq_true] at same
      cases of_decide_eq_true same.1
      have valuesEqual := same.2
      change (leftValue == rightValue) = true at valuesEqual
      cases beq_iff_eq.mp valuesEqual
      rfl
    | _ => simp [BEq.beq, Noctium.instBEqValue.beq, Noctium.Value.ctorIdx] at same
  | opaqueBytes leftValue =>
    cases right with
    | opaqueBytes rightValue =>
      simp only [BEq.beq, Noctium.instBEqValue.beq, Noctium.Value.ctorIdx] at same
      exact congrArg Value.opaqueBytes (beq_iff_eq.mp same)
    | _ => simp [BEq.beq, Noctium.instBEqValue.beq, Noctium.Value.ctorIdx] at same
  | opaqueString leftValue =>
    cases right with
    | opaqueString rightValue =>
      simp only [BEq.beq, Noctium.instBEqValue.beq, Noctium.Value.ctorIdx] at same
      exact congrArg Value.opaqueString (beq_iff_eq.mp same)
    | _ => simp [BEq.beq, Noctium.instBEqValue.beq, Noctium.Value.ctorIdx] at same
  | jubjubScalar leftValue =>
    cases right with
    | jubjubScalar rightValue =>
      simp only [BEq.beq, Noctium.instBEqValue.beq, Noctium.Value.ctorIdx] at same
      exact congrArg Value.jubjubScalar (beq_iff_eq.mp same)
    | _ => simp [BEq.beq, Noctium.instBEqValue.beq, Noctium.Value.ctorIdx] at same
  | jubjubPoint leftX leftY =>
    cases right with
    | jubjubPoint rightX rightY =>
      simp only [BEq.beq, Noctium.instBEqValue.beq, Noctium.Value.ctorIdx,
        Bool.and_eq_true] at same
      cases of_decide_eq_true same.1
      cases of_decide_eq_true same.2
      rfl
    | _ => simp [BEq.beq, Noctium.instBEqValue.beq, Noctium.Value.ctorIdx] at same
  | foreignBase leftCurve leftValue =>
    cases right with
    | foreignBase rightCurve rightValue =>
      simp only [BEq.beq, Noctium.instBEqValue.beq, Noctium.Value.ctorIdx,
        Bool.and_eq_true] at same
      cases foreignCurve_beq_eq leftCurve rightCurve same.1
      cases of_decide_eq_true same.2
      rfl
    | _ => simp [BEq.beq, Noctium.instBEqValue.beq, Noctium.Value.ctorIdx] at same
  | foreignScalar leftCurve leftValue =>
    cases right with
    | foreignScalar rightCurve rightValue =>
      simp only [BEq.beq, Noctium.instBEqValue.beq, Noctium.Value.ctorIdx,
        Bool.and_eq_true] at same
      cases foreignCurve_beq_eq leftCurve rightCurve same.1
      cases of_decide_eq_true same.2
      rfl
    | _ => simp [BEq.beq, Noctium.instBEqValue.beq, Noctium.Value.ctorIdx] at same
  | foreignPoint leftCurve leftValue =>
    cases right with
    | foreignPoint rightCurve rightValue =>
      simp only [BEq.beq, Noctium.instBEqValue.beq, Noctium.Value.ctorIdx,
        Bool.and_eq_true] at same
      cases foreignCurve_beq_eq leftCurve rightCurve same.1
      cases foreignPoint_beq_eq leftValue rightValue same.2
      rfl
    | _ => simp [BEq.beq, Noctium.instBEqValue.beq, Noctium.Value.ctorIdx] at same
  | record leftFields =>
    cases right with
    | record rightFields =>
      simp only [BEq.beq, Noctium.instBEqValue.beq, Noctium.Value.ctorIdx] at same
      exact congrArg Value.record (recordFields_beq_eq leftFields rightFields same)
    | _ => simp [BEq.beq, Noctium.instBEqValue.beq, Noctium.Value.ctorIdx] at same

private theorem lookup_member_value (entries : List (Value × Value))
    (key raw : Value) (found : entries.lookup key = some raw) :
    (key, raw) ∈ entries := by
  induction entries with
  | nil => simp at found
  | cons head tail ih =>
    rcases head with ⟨oldKey, oldValue⟩
    simp only [List.lookup_cons] at found
    split at found
    next same =>
      have keyEqual := value_beq_eq key oldKey same
      cases found
      simp [keyEqual]
    next => exact List.mem_cons_of_mem _ (ih found)

private theorem encodedMapEntry_key (keyTy valueTy : Ty)
    (key : keyTy.Denote) (raw : Value) (result : Scalar × Scalar)
    (canonical : Canonical keyTy key)
    (accepted : encodeMapEntry keyTy valueTy (Value.pack keyTy key, raw) =
      some result) :
    result.1 = scalar (number keyTy key) := by
  unfold encodeMapEntry at accepted
  rw [encodeValue_pack keyTy key canonical] at accepted
  cases valueEncoded : encodeValue valueTy raw with
  | none => simp [valueEncoded] at accepted
  | some cell =>
    simp [valueEncoded] at accepted
    cases accepted
    rfl

/-- A missing key in an encoded native map was also absent from the original
typed source map. A source association shadow cannot fabricate absence. -/
theorem encodedMap_absent (keyTy valueTy : Ty)
    (entries : List (Value × Value)) (encoded : List (Scalar × Scalar))
    (key : keyTy.Denote)
    (canonical : Canonical keyTy key)
    (accepted : entries.mapM (encodeMapEntry keyTy valueTy) = some encoded)
    (absent : encoded.any (fun pair => pair.1 == scalar (number keyTy key)) = false) :
    entries.lookup (Value.pack keyTy key) = none := by
  cases found : entries.lookup (Value.pack keyTy key) with
  | none => rfl
  | some raw =>
    have sourceMember : (Value.pack keyTy key, raw) ∈ entries :=
      lookup_member_value entries (Value.pack keyTy key) raw found
    obtain ⟨pair, encodedPair, pairMember⟩ :=
      option_mapM_member (encodeMapEntry keyTy valueTy) entries encoded
        (Value.pack keyTy key, raw) accepted sourceMember
    have keyEqual := encodedMapEntry_key keyTy valueTy key raw pair canonical encodedPair
    have present : encoded.any (fun item => item.1 == scalar (number keyTy key)) = true := by
      apply List.any_eq_true.mpr
      exact ⟨pair, pairMember, by simp [keyEqual]⟩
    rw [present] at absent
    contradiction

theorem encoded_map_source (state : LedgerState) (name : String)
    (keyTy valueTy : Ty) (encoded : List (Scalar × Scalar))
    (accepted : encodeDeclaration state {name, kind := .map keyTy valueTy} =
      some (.map encoded)) :
    ∃ entries,
      state.maps.lookup name = some entries ∧
      entries.mapM (encodeMapEntry keyTy valueTy) = some encoded := by
  unfold encodeDeclaration at accepted
  cases found : state.maps.lookup name with
  | none => simp [found] at accepted
  | some entries =>
    cases mapped : entries.mapM (encodeMapEntry keyTy valueTy) with
    | none => simp [found, mapped] at accepted
    | some result =>
      by_cases unique : (result.map Prod.fst).eraseDups.length != result.length
      · simp [found, mapped] at accepted
        have sameLength := accepted.1
        simp [sameLength] at unique
      · simp [found, mapped] at accepted
        cases accepted.2
        exact ⟨entries, rfl, mapped⟩

theorem encoded_map_nodup (state : LedgerState) (name : String)
    (keyTy valueTy : Ty) (encoded : List (Scalar × Scalar))
    (accepted : encodeDeclaration state {name, kind := .map keyTy valueTy} =
      some (.map encoded)) : (encoded.map Prod.fst).Nodup := by
  unfold encodeDeclaration at accepted
  cases found : state.maps.lookup name with
  | none => simp [found] at accepted
  | some entries =>
    cases mapped : entries.mapM (encodeMapEntry keyTy valueTy) with
    | none => simp [found, mapped] at accepted
    | some result =>
      simp [found, mapped] at accepted
      have lengthEq := accepted.1
      cases accepted.2
      apply GenericStateKeys.nodup_of_eraseDups_length_eq
      simpa only [List.length_map] using lengthEq

theorem updateEntry_lookup_same (key : String) (value : β)
    (entries : List (String × β)) :
    (SourceEffects.updateEntry key value entries).lookup key = some value := by
  simp [SourceEffects.updateEntry]

theorem updateEntry_lookup_other (key other : String) (value : β)
    (entries : List (String × β)) (different : other ≠ key) :
    (SourceEffects.updateEntry key value entries).lookup other =
      entries.lookup other := by
  unfold SourceEffects.updateEntry
  simp only [List.lookup_cons, show (other == key) = false by simp [different]]
  induction entries with
  | nil => rfl
  | cons head tail ih =>
    rcases head with ⟨oldKey, oldValue⟩
    by_cases removed : oldKey = key
    · have notOther : other ≠ oldKey := by simpa [removed] using different
      have notEqual : (other == oldKey) = false := by simp [notOther]
      have notKey : (other == key) = false := by simp [different]
      simp [removed, List.lookup_cons, notKey, ih]
    · by_cases found : other = oldKey
      · simp [removed, found]
      · have notEqual : (other == oldKey) = false := by simp [found]
        simp [removed, List.lookup_cons, notEqual, ih]

theorem encodeDeclaration_updateCell_other (state : LedgerState)
    (name : String) (raw : Value) (declaration : StateDecl)
    (different : declaration.name ≠ name) :
    encodeDeclaration {state with cells :=
      (SourceEffects.updateEntry name raw state.cells)} declaration =
      encodeDeclaration state declaration := by
  cases kind : declaration.kind with
  | cell ty =>
    simp [encodeDeclaration, kind,
      updateEntry_lookup_other name declaration.name raw state.cells different]
  | map keyTy valueTy => simp [encodeDeclaration, kind]
  | tree _ | merkleTree _ | historicMerkleTree _ | opaqueString =>
    simp [encodeDeclaration, kind]

theorem encodeDeclaration_updateCell_same (state : LedgerState)
    (name : String) (ty : Ty) (value : ty.Denote)
    (canonical : Canonical ty value) :
    encodeDeclaration {state with cells :=
      (SourceEffects.updateEntry name (Value.pack ty value) state.cells)}
      {name, kind := .cell ty} =
      some (.cell (field (scalar (number ty value)))) := by
  simp [encodeDeclaration, updateEntry_lookup_same,
    encodeValue_pack, canonical]

theorem encodeState_updateCell_framed (declarations : List StateDecl)
    (state : LedgerState) (name : String) (raw : Value)
    (different : ∀ declaration ∈ declarations, declaration.name ≠ name) :
    encodeState declarations {state with cells :=
      (SourceEffects.updateEntry name raw state.cells)} =
      encodeState declarations state := by
  induction declarations with
  | nil => rfl
  | cons declaration rest ih =>
    have headDifferent := different declaration (by simp)
    have restDifferent : ∀ item ∈ rest, item.name ≠ name := by
      intro item member
      exact different item (by simp [member])
    have tailEq := ih restDifferent
    change rest.mapM (encodeDeclaration {state with cells :=
      (SourceEffects.updateEntry name raw state.cells)}) =
        rest.mapM (encodeDeclaration state) at tailEq
    simp only [encodeState, List.mapM_cons,
      encodeDeclaration_updateCell_other state name raw declaration headDifferent]
    rw [tailEq]

theorem encodeState_updateCell_at (declarations : List StateDecl)
    (state : LedgerState) (slots : List Slot) (slot : Nat)
    (name : String) (ty : Ty) (value : ty.Denote)
    (encoded : encodeState declarations state = some slots)
    (declaration : declarations[slot]? = some {name, kind := .cell ty})
    (distinct : declarations.Pairwise (fun left right => left.name ≠ right.name))
    (canonical : Canonical ty value) :
    encodeState declarations {state with cells :=
      (SourceEffects.updateEntry name (Value.pack ty value) state.cells)} =
      some (slots.set slot (.cell (field (scalar (number ty value))))) := by
  induction declarations generalizing slots slot with
  | nil => simp at declaration
  | cons head tail ih =>
    cases distinct with
    | cons headDifferent tailDistinct =>
      simp only [encodeState, List.mapM_cons] at encoded
      cases first : encodeDeclaration state head with
      | none => simp [first] at encoded
      | some old =>
        cases restEncoded : tail.mapM (encodeDeclaration state) with
        | none => simp [first, restEncoded] at encoded
        | some oldTail =>
          simp [first, restEncoded] at encoded
          cases encoded
          cases slot with
          | zero =>
            simp at declaration
            subst head
            have framed : encodeState tail {state with cells :=
                (SourceEffects.updateEntry name (Value.pack ty value) state.cells)} =
                encodeState tail state := by
              apply encodeState_updateCell_framed
              intro item member
              exact (headDifferent item member).symm
            have tailEq : tail.mapM (encodeDeclaration {state with cells :=
                (SourceEffects.updateEntry name (Value.pack ty value) state.cells)}) =
                tail.mapM (encodeDeclaration state) := framed
            simp only [encodeState, List.mapM_cons,
              encodeDeclaration_updateCell_same state name ty value canonical]
            rw [tailEq, restEncoded]
            rfl
          | succ index =>
            simp only [List.getElem?_cons_succ] at declaration
            have headNotTarget : head.name ≠ name :=
              headDifferent {name, kind := .cell ty} (List.mem_of_getElem? declaration)
            have tailUpdated := ih oldTail index restEncoded declaration tailDistinct
            have tailEq : tail.mapM (encodeDeclaration {state with cells :=
                (SourceEffects.updateEntry name (Value.pack ty value) state.cells)}) =
                some (oldTail.set index (.cell (field (scalar (number ty value))))) :=
              tailUpdated
            simp only [encodeState, List.mapM_cons,
              encodeDeclaration_updateCell_other state name (Value.pack ty value)
                head headNotTarget]
            rw [first, tailEq]
            rfl

/-- Each fixed source type has a left inverse through its canonical field
cell. Thus distinct typed keys cannot collapse in the native map encoding. -/
theorem encodeValue_pack_injective (ty : Ty) (left right : ty.Denote)
    (leftCanonical : Canonical ty left) (rightCanonical : Canonical ty right)
    (same : encodeValue ty (Value.pack ty left) = encodeValue ty (Value.pack ty right)) :
    left = right := by
  rw [encodeValue_pack ty left leftCanonical,
    encodeValue_pack ty right rightCanonical] at same
  have sameCell := Option.some.inj same
  have decoded := congrArg (decodeValue ty) sameCell
  rw [decode_encode_pack ty left leftCanonical,
    decode_encode_pack ty right rightCanonical] at decoded
  have packed := Option.some.inj decoded
  cases ty with
  | native => exact Value.native.inj packed
  | bool => exact Value.bool.inj packed
  | uint _ => exact Value.uint.inj packed |>.2
  | bytes _ | opaqueBytes | opaqueString | jubjubScalar | jubjubPoint | foreign _ =>
    simp [Canonical, ScalarNormalization.sourceNumber?] at leftCanonical

private theorem encodeMapEntry_key_cell (keyTy valueTy : Ty)
    (entry : Value × Value) (pair : Scalar × Scalar)
    (accepted : encodeMapEntry keyTy valueTy entry = some pair) :
    encodeValue keyTy entry.1 = some (field pair.1) := by
  unfold encodeMapEntry at accepted
  cases keyCell : encodeValue keyTy entry.1 with
  | none => simp [keyCell] at accepted
  | some cell =>
    cases valueCell : encodeValue valueTy entry.2 with
    | none => simp [keyCell, valueCell] at accepted
    | some result =>
      simp [keyCell, valueCell] at accepted
      cases accepted
      obtain ⟨typed, _, _, same⟩ := encodeValue_source keyTy entry.1 cell keyCell
      simp [same, field]

/-- The typed source key comparison and encoded scalar comparison agree for
each successful map entry. This prevents an encoded update from removing a
different source key. -/
theorem encodeMapEntry_key_match (keyTy valueTy : Ty)
    (entry : Value × Value) (pair : Scalar × Scalar)
    (key : keyTy.Denote) (canonical : Canonical keyTy key)
    (accepted : encodeMapEntry keyTy valueTy entry = some pair) :
    (entry.1 == Value.pack keyTy key) =
      (pair.1 == scalar (number keyTy key)) := by
  have cell := encodeMapEntry_key_cell keyTy valueTy entry pair accepted
  by_cases same : entry.1 = Value.pack keyTy key
  · rw [same] at cell ⊢
    rw [encodeValue_pack keyTy key canonical] at cell
    have pairEqual : pair.1 = scalar (number keyTy key) := by
      simpa [field] using congrArg Cell.value (Option.some.inj cell).symm
    cases keyTy with
    | native => simp [pairEqual, Value.pack, value_beq_refl]
    | bool => simp [pairEqual, Value.pack, value_beq_refl]
    | uint _ => simp [pairEqual, Value.pack, value_beq_refl]
    | bytes _ | opaqueBytes | opaqueString | jubjubScalar | jubjubPoint | foreign _ =>
      simp [Canonical, ScalarNormalization.sourceNumber?] at canonical
  · have sourceFalse : (entry.1 == Value.pack keyTy key) = false := by
      cases sourceEq : (entry.1 == Value.pack keyTy key) with
      | false => rfl
      | true => exact False.elim (same (value_beq_eq _ _ sourceEq))
    have scalarFalse : (pair.1 == scalar (number keyTy key)) = false := by
      cases scalarEq : (pair.1 == scalar (number keyTy key)) with
      | false => rfl
      | true =>
        have pairEqual : pair.1 = scalar (number keyTy key) := by
          simpa using scalarEq
        rw [pairEqual] at cell
        have decoded := decode_encodeValue keyTy entry.1 _ cell
        rw [decode_encode_pack keyTy key canonical] at decoded
        exact False.elim (same (Option.some.inj decoded).symm)
    rw [sourceFalse, scalarFalse]

/-- Exact scalar map encoding preserves a missing source key. Together with
`encodedMap_absent`, this rules out both invented and lost key matches. -/
theorem sourceMap_absent (keyTy valueTy : Ty)
    (entries : List (Value × Value)) (encoded : List (Scalar × Scalar))
    (key : keyTy.Denote) (canonical : Canonical keyTy key)
    (mapped : entries.mapM (encodeMapEntry keyTy valueTy) = some encoded)
    (missing : entries.lookup (Value.pack keyTy key) = none) :
    encoded.any (fun pair => pair.1 == scalar (number keyTy key)) = false := by
  induction entries generalizing encoded with
  | nil =>
    simp only [List.mapM_nil] at mapped
    cases mapped
    rfl
  | cons entry rest ih =>
    simp only [List.mapM_cons] at mapped
    cases first : encodeMapEntry keyTy valueTy entry with
    | none => simp [first] at mapped
    | some pair =>
      cases later : rest.mapM (encodeMapEntry keyTy valueTy) with
      | none => simp [first, later] at mapped
      | some remaining =>
        simp [first, later] at mapped
        cases mapped
        have noSource := List.lookup_eq_none_iff.mp missing
        have headMissing : (entry.1 == Value.pack keyTy key) = false := by
          cases equal : (entry.1 == Value.pack keyTy key) with
          | false => rfl
          | true =>
            have rawEqual := value_beq_eq _ _ equal
            have different := noSource entry (by simp)
            rw [rawEqual] at different
            simp [bne, value_beq_refl] at different
        have tailMissing : rest.lookup (Value.pack keyTy key) = none := by
          apply List.lookup_eq_none_iff.mpr
          intro item member
          exact noSource item (List.mem_cons_of_mem _ member)
        have nativeMissing :=
          (encodeMapEntry_key_match keyTy valueTy entry pair key canonical first).symm.trans
            headMissing
        simpa only [List.any_cons, nativeMissing, Bool.false_or] using ih remaining later tailMissing

/-- Every successful lookup in a checked scalar map yields an encodable value. -/
theorem encodedMap_lookup_value (keyTy valueTy : Ty)
    (entries : List (Value × Value)) (encoded : List (Scalar × Scalar))
    (key raw : Value)
    (mapped : entries.mapM (encodeMapEntry keyTy valueTy) = some encoded)
    (found : entries.lookup key = some raw) :
    ∃ cell, encodeValue valueTy raw = some cell := by
  obtain ⟨entry, entryEncoded, _⟩ := option_mapM_member (encodeMapEntry keyTy valueTy)
    entries encoded (key, raw) mapped (lookup_member_value entries key raw found)
  unfold encodeMapEntry at entryEncoded
  cases keyEncoding : encodeValue keyTy key with
  | none => simp [keyEncoding] at entryEncoded
  | some keyCell =>
    cases valueEncoding : encodeValue valueTy raw with
    | none => simp [keyEncoding, valueEncoding] at entryEncoded
    | some cell => exact ⟨cell, rfl⟩

/-- The ordered encoding preserves the first exact lookup result, including
missing keys. This connects a successful native index to a source map value. -/
theorem sourceMap_lookup (keyTy valueTy : Ty)
    (entries : List (Value × Value)) (encoded : List (Scalar × Scalar))
    (key : keyTy.Denote) (canonical : Canonical keyTy key)
    (mapped : entries.mapM (encodeMapEntry keyTy valueTy) = some encoded) :
    (entries.lookup (Value.pack keyTy key)).bind
        (fun raw => (encodeValue valueTy raw).map Cell.value) =
      encoded.lookup (scalar (number keyTy key)) := by
  induction entries generalizing encoded with
  | nil =>
    simp only [List.mapM_nil] at mapped
    cases mapped
    rfl
  | cons entry rest ih =>
    simp only [List.mapM_cons] at mapped
    cases first : encodeMapEntry keyTy valueTy entry with
    | none => simp [first] at mapped
    | some pair =>
      cases later : rest.mapM (encodeMapEntry keyTy valueTy) with
      | none => simp [first, later] at mapped
      | some remaining =>
        simp [first, later] at mapped
        cases mapped
        have keyMatch := encodeMapEntry_key_match keyTy valueTy entry pair key canonical first
        have sourceForward : (Value.pack keyTy key == entry.1) =
            (entry.1 == Value.pack keyTy key) := by
          by_cases equal : Value.pack keyTy key = entry.1
          · rw [equal]
          · cases left : (Value.pack keyTy key == entry.1) with
            | true => exact False.elim (equal (value_beq_eq _ _ left))
            | false =>
              cases right : (entry.1 == Value.pack keyTy key) with
              | true => exact False.elim (equal (value_beq_eq _ _ right).symm)
              | false => rfl
        have nativeForward : (pair.1 == scalar (number keyTy key)) =
            (scalar (number keyTy key) == pair.1) :=
          Bool.eq_iff_iff.mpr (beq_iff_eq.trans (eq_comm.trans beq_iff_eq.symm))
        rcases entry with ⟨entryKey, entryValue⟩
        rcases pair with ⟨encodedKey, encodedValue⟩
        simp only [List.lookup_cons]
        rw [sourceForward.trans (keyMatch.trans nativeForward)]
        cases checked : (scalar (number keyTy key) == encodedKey) with
        | false => exact ih remaining later
        | true =>
          unfold encodeMapEntry at first
          cases keyEncoded : encodeValue keyTy entryKey with
          | none => simp [keyEncoded] at first
          | some keyCell =>
            cases valueEncoded : encodeValue valueTy entryValue with
            | none => simp [keyEncoded, valueEncoded] at first
            | some valueCell =>
              simp [keyEncoded, valueEncoded] at first
              simpa only [Option.bind_some, valueEncoded, Option.map_some] using
                congrArg some first.2

theorem encodeMapEntries_filter_key (keyTy valueTy : Ty)
    (entries : List (Value × Value)) (encoded : List (Scalar × Scalar))
    (key : keyTy.Denote) (canonical : Canonical keyTy key)
    (accepted : entries.mapM (encodeMapEntry keyTy valueTy) = some encoded) :
    (entries.filter (fun entry => !(entry.1 == Value.pack keyTy key))).mapM
      (encodeMapEntry keyTy valueTy) =
      some (encoded.filter (fun pair => pair.1 != scalar (number keyTy key))) := by
  induction entries generalizing encoded with
  | nil =>
    simp only [List.filter_nil, List.mapM_nil] at accepted ⊢
    simp at accepted
    cases accepted
    rfl
  | cons entry rest ih =>
    simp only [List.mapM_cons] at accepted
    cases first : encodeMapEntry keyTy valueTy entry with
    | none => simp [first] at accepted
    | some pair =>
      cases later : rest.mapM (encodeMapEntry keyTy valueTy) with
      | none => simp [first, later] at accepted
      | some remaining =>
        simp [first, later] at accepted
        cases accepted
        have restFiltered := ih remaining later
        have matched := encodeMapEntry_key_match keyTy valueTy entry pair key canonical first
        cases equal : (entry.1 == Value.pack keyTy key) with
        | false =>
          have encodedEqual : (pair.1 == scalar (number keyTy key)) = false := by
            simpa [equal] using matched.symm
          have encodedKeep : (pair.1 != scalar (number keyTy key)) = true := by
            apply bne_iff_ne.mpr
            intro pairEquality
            rw [pairEquality, beq_self_eq_true] at encodedEqual
            cases encodedEqual
          have sourceKept : (entry :: rest).filter
              (fun entry => !(entry.1 == Value.pack keyTy key)) =
              entry :: rest.filter (fun entry => !(entry.1 == Value.pack keyTy key)) := by
            simp [equal]
          have encodedKept : (pair :: remaining).filter
              (fun pair => pair.1 != scalar (number keyTy key)) =
              pair :: remaining.filter (fun pair => pair.1 != scalar (number keyTy key)) := by
            rw [List.filter_cons, encodedKeep]
            rfl
          rw [sourceKept, encodedKept]
          simp [first, restFiltered]
        | true =>
          have encodedEqual : (pair.1 == scalar (number keyTy key)) = true := by
            simpa [equal] using matched.symm
          have encodedDrop : (pair.1 != scalar (number keyTy key)) = false := by
            have pairEquality : pair.1 = scalar (number keyTy key) :=
              beq_iff_eq.mp encodedEqual
            simp [pairEquality]
          have sourceDropped : (entry :: rest).filter
              (fun entry => !(entry.1 == Value.pack keyTy key)) =
              rest.filter (fun entry => !(entry.1 == Value.pack keyTy key)) := by
            simp [equal]
          have encodedDropped : (pair :: remaining).filter
              (fun pair => pair.1 != scalar (number keyTy key)) =
              remaining.filter (fun pair => pair.1 != scalar (number keyTy key)) := by
            rw [List.filter_cons, encodedDrop]
            rfl
          rw [sourceDropped, encodedDropped]
          exact restFiltered

theorem encodeMapEntries_update_key (keyTy valueTy : Ty)
    (entries : List (Value × Value)) (encoded : List (Scalar × Scalar))
    (key : keyTy.Denote) (value : valueTy.Denote)
    (keyCanonical : Canonical keyTy key)
    (valueCanonical : Canonical valueTy value)
    (accepted : entries.mapM (encodeMapEntry keyTy valueTy) = some encoded) :
    (SourceEffects.updateEntry (Value.pack keyTy key) (Value.pack valueTy value)
      entries).mapM (encodeMapEntry keyTy valueTy) =
      some ((scalar (number keyTy key), scalar (number valueTy value)) ::
        encoded.filter (fun pair => pair.1 != scalar (number keyTy key))) := by
  unfold SourceEffects.updateEntry
  simp [List.mapM_cons,
    encodeMapEntry_pack keyTy valueTy key value keyCanonical valueCanonical,
    encodeMapEntries_filter_key keyTy valueTy entries encoded key keyCanonical accepted]

theorem eraseDups_eq_self_of_nodup {α : Type} [BEq α] [LawfulBEq α]
    (items : List α) (distinct : items.Nodup) : items.eraseDups = items := by
  induction items with
  | nil => rfl
  | cons head tail ih =>
    obtain ⟨headAbsent, tailDistinct⟩ := List.nodup_cons.mp distinct
    rw [List.eraseDups_cons]
    have retained : (tail.filter fun item => !(item == head)) = tail := by
      apply List.filter_eq_self.mpr
      intro item member
      apply bne_iff_ne.mpr
      intro same
      exact headAbsent (same ▸ member)
    rw [retained, ih tailDistinct]

theorem encodedMap_update_distinct (encoded : List (Scalar × Scalar))
    (key value : Scalar) (distinct : (encoded.map Prod.fst).Nodup) :
    (((key, value) :: encoded.filter (fun pair => pair.1 != key)).map Prod.fst).Nodup := by
  have pairwise : encoded.Pairwise (fun left right => left.1 ≠ right.1) :=
    List.pairwise_map.mp (List.nodup_iff_pairwise_ne.mp distinct)
  have filtered : ((encoded.filter (fun pair => pair.1 != key)).map Prod.fst).Nodup :=
    List.nodup_iff_pairwise_ne.mpr
      (List.pairwise_map.mpr (pairwise.filter fun pair => pair.1 != key))
  apply List.nodup_cons.mpr
  constructor
  · intro member
    obtain ⟨pair, pairMember, equal⟩ := List.mem_map.mp member
    obtain ⟨_, different⟩ := List.mem_filter.mp pairMember
    have differentKey : pair.1 ≠ key := bne_iff_ne.mp different
    exact differentKey equal
  · exact filtered

theorem encodeDeclaration_updateMap_other (state : LedgerState)
    (name : String) (entries : List (Value × Value)) (declaration : StateDecl)
    (different : declaration.name ≠ name) :
    encodeDeclaration {state with maps := (SourceEffects.updateEntry name entries state.maps)} declaration =
      encodeDeclaration state declaration := by
  cases kind : declaration.kind with
  | cell ty => simp [encodeDeclaration, kind]
  | map keyTy valueTy =>
    simp [encodeDeclaration, kind,
      updateEntry_lookup_other name declaration.name entries state.maps different]
  | tree _ | merkleTree _ | historicMerkleTree _ | opaqueString =>
    simp [encodeDeclaration, kind]

theorem encodeDeclaration_updateMap_same (state : LedgerState)
    (name : String) (keyTy valueTy : Ty)
    (entries : List (Value × Value)) (encoded : List (Scalar × Scalar))
    (key : keyTy.Denote) (value : valueTy.Denote)
    (oldEncoded : entries.mapM (encodeMapEntry keyTy valueTy) = some encoded)
    (distinct : (encoded.map Prod.fst).Nodup)
    (keyCanonical : Canonical keyTy key)
    (valueCanonical : Canonical valueTy value) :
    encodeDeclaration {state with maps := (SourceEffects.updateEntry name
        (SourceEffects.updateEntry (Value.pack keyTy key) (Value.pack valueTy value) entries)
        state.maps)} {name, kind := .map keyTy valueTy} =
      some (.map ((scalar (number keyTy key), scalar (number valueTy value)) ::
        encoded.filter (fun pair => pair.1 != scalar (number keyTy key)))) := by
  have updated := encodeMapEntries_update_key keyTy valueTy entries encoded key value
    keyCanonical valueCanonical oldEncoded
  have noDuplicates := encodedMap_update_distinct encoded
    (scalar (number keyTy key)) (scalar (number valueTy value)) distinct
  have sameLength := eraseDups_eq_self_of_nodup _ noDuplicates
  simp only [encodeDeclaration, updateEntry_lookup_same]
  change Option.bind
      (some (SourceEffects.updateEntry (Value.pack keyTy key)
        (Value.pack valueTy value) entries))
      (fun entries => do
        let encoded ← entries.mapM (encodeMapEntry keyTy valueTy)
        if (encoded.map Prod.fst).eraseDups.length != encoded.length then none
        else some (Slot.map encoded)) = _
  rw [Option.bind_some]
  rw [updated]
  change Option.bind
      (some ((scalar (number keyTy key), scalar (number valueTy value)) ::
        List.filter (fun pair => pair.1 != scalar (number keyTy key)) encoded))
      (fun encoded => if
        ((encoded.map Prod.fst).eraseDups.length != encoded.length) = true then none
        else some (Slot.map encoded)) = _
  rw [Option.bind_some]
  have lengths :
      (List.map Prod.fst
        ((scalar (number keyTy key), scalar (number valueTy value)) ::
          List.filter (fun pair => pair.1 != scalar (number keyTy key)) encoded)).eraseDups.length =
        ((scalar (number keyTy key), scalar (number valueTy value)) ::
          List.filter (fun pair => pair.1 != scalar (number keyTy key)) encoded).length := by
    simpa only [List.length_map] using congrArg List.length sameLength
  have noLengthMismatch :
      ((List.map Prod.fst
        ((scalar (number keyTy key), scalar (number valueTy value)) ::
          List.filter (fun pair => pair.1 != scalar (number keyTy key)) encoded)).eraseDups.length !=
        ((scalar (number keyTy key), scalar (number valueTy value)) ::
          List.filter (fun pair => pair.1 != scalar (number keyTy key)) encoded).length) = false := by
    rw [lengths]
    simp
  rw [noLengthMismatch]
  rfl

theorem encodeState_updateMap_framed (declarations : List StateDecl)
    (state : LedgerState) (name : String) (entries : List (Value × Value))
    (different : ∀ declaration ∈ declarations, declaration.name ≠ name) :
    encodeState declarations {state with maps := (SourceEffects.updateEntry name entries state.maps)} =
      encodeState declarations state := by
  induction declarations with
  | nil => rfl
  | cons declaration rest ih =>
    have headDifferent := different declaration (by simp)
    have restDifferent : ∀ item ∈ rest, item.name ≠ name := by
      intro item member
      exact different item (by simp [member])
    have tailEq := ih restDifferent
    change rest.mapM (encodeDeclaration {state with maps :=
      (SourceEffects.updateEntry name entries state.maps)}) =
        rest.mapM (encodeDeclaration state) at tailEq
    simp only [encodeState, List.mapM_cons,
      encodeDeclaration_updateMap_other state name entries declaration headDifferent]
    rw [tailEq]

theorem encodeState_updateMap_at (declarations : List StateDecl)
    (state : LedgerState) (slots : List Slot) (slot : Nat)
    (name : String) (keyTy valueTy : Ty)
    (entries : List (Value × Value)) (encodedEntries : List (Scalar × Scalar))
    (key : keyTy.Denote) (value : valueTy.Denote)
    (encoded : encodeState declarations state = some slots)
    (declaration : declarations[slot]? = some {name, kind := .map keyTy valueTy})
    (distinct : declarations.Pairwise (fun left right => left.name ≠ right.name))
    (mapEncoded : entries.mapM (encodeMapEntry keyTy valueTy) = some encodedEntries)
    (distinctKeys : (encodedEntries.map Prod.fst).Nodup)
    (keyCanonical : Canonical keyTy key)
    (valueCanonical : Canonical valueTy value) :
    encodeState declarations {state with maps := (SourceEffects.updateEntry name
      (SourceEffects.updateEntry (Value.pack keyTy key) (Value.pack valueTy value) entries)
      state.maps)} =
      some (slots.set slot (.map ((scalar (number keyTy key), scalar (number valueTy value)) ::
        encodedEntries.filter (fun pair => pair.1 != scalar (number keyTy key))))) := by
  induction declarations generalizing slots slot with
  | nil => simp at declaration
  | cons head tail ih =>
    cases distinct with
    | cons headDifferent tailDistinct =>
      simp only [encodeState, List.mapM_cons] at encoded
      cases first : encodeDeclaration state head with
      | none => simp [first] at encoded
      | some old =>
        cases restEncoded : tail.mapM (encodeDeclaration state) with
        | none => simp [first, restEncoded] at encoded
        | some oldTail =>
          simp [first, restEncoded] at encoded
          cases encoded
          cases slot with
          | zero =>
            simp at declaration
            subst head
            have framed : encodeState tail {state with maps := (SourceEffects.updateEntry name
                (SourceEffects.updateEntry (Value.pack keyTy key) (Value.pack valueTy value) entries)
                state.maps)} = encodeState tail state := by
              apply encodeState_updateMap_framed
              intro item member
              exact (headDifferent item member).symm
            have tailEq : tail.mapM (encodeDeclaration {state with maps := (SourceEffects.updateEntry name
                (SourceEffects.updateEntry (Value.pack keyTy key) (Value.pack valueTy value) entries)
                state.maps)}) = tail.mapM (encodeDeclaration state) := framed
            simp only [encodeState, List.mapM_cons,
              encodeDeclaration_updateMap_same state name keyTy valueTy entries encodedEntries key value
                mapEncoded distinctKeys keyCanonical valueCanonical]
            rw [tailEq, restEncoded]
            rfl
          | succ index =>
            simp only [List.getElem?_cons_succ] at declaration
            have headNotTarget : head.name ≠ name :=
              headDifferent {name, kind := .map keyTy valueTy} (List.mem_of_getElem? declaration)
            have tailUpdated := ih oldTail index restEncoded declaration tailDistinct
            have tailEq : tail.mapM (encodeDeclaration {state with maps := (SourceEffects.updateEntry name
                (SourceEffects.updateEntry (Value.pack keyTy key) (Value.pack valueTy value) entries)
                state.maps)}) =
                some (oldTail.set index (.map ((scalar (number keyTy key), scalar (number valueTy value)) ::
                  encodedEntries.filter (fun pair => pair.1 != scalar (number keyTy key))))) :=
              tailUpdated
            simp only [encodeState, List.mapM_cons,
              encodeDeclaration_updateMap_other state name
                (SourceEffects.updateEntry (Value.pack keyTy key) (Value.pack valueTy value) entries)
                head headNotTarget]
            rw [first, tailEq]
            rfl

theorem encodedMapEntry_typed (keyTy valueTy : Ty)
    (entry : Value × Value) (pair : Scalar × Scalar)
    (accepted : encodeMapEntry keyTy valueTy entry = some pair) :
    ∃ key value,
      entry.1.as keyTy = some key ∧ entry.2.as valueTy = some value ∧
      Canonical keyTy key ∧ Canonical valueTy value := by
  unfold encodeMapEntry at accepted
  cases keyCell : encodeValue keyTy entry.1 with
  | none => simp [keyCell] at accepted
  | some first =>
    cases valueCell : encodeValue valueTy entry.2 with
    | none => simp [keyCell, valueCell] at accepted
    | some second =>
      obtain ⟨key, keyTyped, keyCanonical, _⟩ :=
        encodeValue_source keyTy entry.1 first keyCell
      obtain ⟨value, valueTyped, valueCanonical, _⟩ :=
        encodeValue_source valueTy entry.2 second valueCell
      exact ⟨key, value, keyTyped, valueTyped, keyCanonical, valueCanonical⟩

theorem encodedMapEntries_typed (keyTy valueTy : Ty)
    (entries : List (Value × Value)) (encoded : List (Scalar × Scalar))
    (accepted : entries.mapM (encodeMapEntry keyTy valueTy) = some encoded) :
    ∀ entry ∈ entries,
      ∃ key value, entry.1.as keyTy = some key ∧ entry.2.as valueTy = some value := by
  intro entry member
  obtain ⟨pair, encodedPair, _⟩ := option_mapM_member
    (encodeMapEntry keyTy valueTy) entries encoded entry accepted member
  obtain ⟨key, value, keyTyped, valueTyped, _, _⟩ :=
    encodedMapEntry_typed keyTy valueTy entry pair encodedPair
  exact ⟨key, value, keyTyped, valueTyped⟩

/-- The declared map retains its ordered encoded entries at the same slot. -/
theorem encoded_map_slot (declarations : List StateDecl)
    (current : LedgerState) (slots : List Slot) (slot : Nat)
    (declaration : StateDecl) (name : String) (keyTy valueTy : Ty)
    (entries : List (Value × Value))
    (declared : declarations[slot]? = some declaration)
    (named : declaration.name = name)
    (kind : declaration.kind = .map keyTy valueTy)
    (encoded : encodeState declarations current = some slots)
    (lookup : current.maps.lookup name = some entries) :
    ∃ nativeEntries, entries.mapM (encodeMapEntry keyTy valueTy) = some nativeEntries ∧
      slots[slot]? = some (.map nativeEntries) := by
  have inRange : slot < declarations.length := List.getElem?_eq_some_iff.mp declared |>.1
  have slotsRange : slot < slots.length := by
    rw [encodeState_length declarations current slots encoded]
    exact inRange
  have slotEncoding := encodeState_slot declarations current slots slot encoded
  rw [declared] at slotEncoding
  simp only [Option.bind_some] at slotEncoding
  cases mapped : entries.mapM (encodeMapEntry keyTy valueTy) with
  | none =>
    have absent : slots[slot]? = none := by
      simpa [encodeDeclaration, named, kind, lookup, mapped] using slotEncoding
    exact False.elim (Nat.not_le_of_gt slotsRange (List.getElem?_eq_none_iff.mp absent))
  | some nativeEntries =>
    by_cases unique : (nativeEntries.map Prod.fst).eraseDups.length = nativeEntries.length
    · refine ⟨nativeEntries, rfl, ?_⟩
      simpa [encodeDeclaration, named, kind, lookup, mapped, unique] using slotEncoding
    · have absent : slots[slot]? = none := by
        simpa [encodeDeclaration, named, kind, lookup, mapped, unique] using slotEncoding
      exact False.elim (Nat.not_le_of_gt slotsRange (List.getElem?_eq_none_iff.mp absent))

end Noctium.Verification.GenericStateEncoding
