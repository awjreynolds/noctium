import Noctium.Verification.NativeRelation

namespace Noctium.Verification.NativeState
open NativeRelation

inductive Alignment where
  | field | bit
  deriving Repr, DecidableEq

structure Cell where
  alignment : Alignment
  value : Scalar
  deriving Repr, DecidableEq

def field (value : Scalar) : Cell := ⟨.field, value⟩
def boolean (value : _root_.Bool) : Cell := ⟨.bit, bit value⟩

/-- The current native state backend stores a flat array of scalar cells and
field-keyed maps. -/
inductive Slot where
  | cell (value : Cell)
  | map (entries : List (Scalar × Scalar))
  deriving Repr, DecidableEq

/-- The legacy array constructor retains the fixed claim certificate. The
vector constructor represents arbitrary current scalar cell/map schemas. Map
entries store scalar representatives, with the declaration fixing each map's
key and value types. The scalar map-index proof therefore covers schema-fixed
field keys and field-valued entries. -/
inductive Node where
  | cell (value : Cell)
  | map (entries : List (Scalar × Scalar))
  | array (cells : List Cell) (entries : List (Scalar × Scalar))
  | vector (items : List Slot)
  deriving Repr, DecidableEq

def Slot.toNode : Slot → Node
  | .cell value => .cell value
  | .map entries => .map entries

inductive Op where
  | push (value : Cell) (storage : _root_.Bool)
  | popeq (value : Cell)
  | dup
  | index (slot : Nat) (pushPath : _root_.Bool)
  | mapIndex (slot : Nat) (key : Cell)
  | member
  | insert (levels : Nat)
  deriving Repr, DecidableEq

structure Machine where
  stack : List Node
  reads : List Cell := []
  deriving Repr, DecidableEq

/-- Native stack insertion walks saved (container,key) pairs from the top.
Map replacement and root-array insertion are separate VM steps. -/
def insert : Nat → Node → List Node → Option (List Node)
  | 0, value, rest => some (value :: rest)
  | n + 1, .cell value, .cell ⟨.field, key⟩ :: .vector items :: rest =>
    match items[key.val]? with
    | some (.cell _) => insert n (.vector (items.set key.val (Slot.cell value))) rest
    | _ => none
  | n + 1, .map entries, .cell ⟨.field, key⟩ :: .vector items :: rest =>
    match items[key.val]? with
    | some (.map _) => insert n (.vector (items.set key.val (Slot.map entries))) rest
    | _ => none
  | n + 1, .cell ⟨.field, value⟩, .cell ⟨.field, key⟩ :: .map entries :: rest =>
    insert n (.map ((key, value) :: entries.filter (fun p => p.1 != key))) rest
  | n + 1, .map entries, .cell ⟨.field, key⟩ :: .array cells _ :: rest =>
    if key.val = cells.length then insert n (.array cells entries) rest else none
  | _, _, _ => none

/-- Executable semantics independent of source.run and compiler lowering.
Popeq consumes actual stack cells and compares complete aligned values. -/
def step (op : Op) (machine : Machine) : Option Machine := do
  match op, machine.stack with
  | .push value _, rest => pure {machine with stack := .cell value :: rest}
  | .popeq expected, .cell actual :: rest =>
    if actual = expected then pure {stack := rest, reads := machine.reads ++ [actual]} else none
  | .dup, top :: rest => pure {machine with stack := top :: top :: rest}
  | .index slot path, .array cells entries :: rest =>
    let child ← if slot < cells.length then cells[slot]?.map Node.cell
      else if slot = cells.length then some (.map entries) else none
    let rest := if path then .cell (field (scalar slot)) :: .array cells entries :: rest else rest
    pure {machine with stack := child :: rest}
  | .index slot path, .vector items :: rest =>
    let child ← (items[slot]?).map Slot.toNode
    let rest := if path then .cell (field (scalar slot)) :: .vector items :: rest else rest
    pure {machine with stack := child :: rest}
  | .mapIndex slot ⟨.field, key⟩, .vector items :: rest => do
    let some (.map entries) := items[slot]? | none
    let some value := entries.lookup key | none
    pure {machine with stack := .cell (field value) :: rest}
  | .mapIndex slot ⟨.field, key⟩, .array cells entries :: rest => do
    if slot != cells.length then none
    let some value := entries.lookup key | none
    pure {machine with stack := .cell (field value) :: rest}
  | .mapIndex _ _, _ => none
  | .member, .cell ⟨.field, key⟩ :: .map entries :: rest =>
    pure {machine with stack := .cell (boolean (entries.any (fun p => p.1 == key))) :: rest}
  | .insert levels, value :: rest =>
    let stack ← insert levels value rest
    pure {machine with stack}
  | _, _ => none

def run : List Op → Machine → Option Machine
  | [], machine => some machine
  | op :: rest, machine => (step op machine).bind (run rest)

theorem run_append (first second : List Op) (before : Machine) :
    run (first ++ second) before = (run first before).bind (run second) := by
  induction first generalizing before with
  | nil => rfl
  | cons op rest ih =>
    simp only [List.cons_append, run]
    cases stepped : step op before with
    | none => simp
    | some middle => simpa [stepped] using ih middle

@[simp] theorem field_inj (a b : Scalar) : field a = field b ↔ a = b := by simp [field, Cell.mk.injEq]
@[simp] theorem boolean_ne : boolean true ≠ boolean false := by decide

theorem run_nil (machine : Machine) : run [] machine = some machine := by rfl

theorem run_push (value : Cell) (storage : _root_.Bool) (ops : List Op) (stack : List Node) (reads : List Cell) :
    run (.push value storage :: ops) ⟨stack, reads⟩ = run ops ⟨.cell value :: stack, reads⟩ := by rfl

theorem run_popeq (actual expected : Cell) (ops : List Op) (stack : List Node) (reads : List Cell) :
    run (.popeq expected :: ops) ⟨.cell actual :: stack, reads⟩ =
      if actual = expected then run ops ⟨stack, reads ++ [actual]⟩ else none := by
  by_cases eq : actual = expected <;> simp [run, step, eq]

theorem run_dup (top : Node) (ops : List Op) (stack : List Node) (reads : List Cell) :
    run (.dup :: ops) ⟨top :: stack, reads⟩ = run ops ⟨top :: top :: stack, reads⟩ := by rfl

theorem run_index_zero (a b : Cell) (entries : List (Scalar × Scalar)) (ops : List Op)
    (stack : List Node) (reads : List Cell) :
    run (.index 0 false :: ops) ⟨.array [a,b] entries :: stack, reads⟩ =
      run ops ⟨.cell a :: stack, reads⟩ := by rfl

theorem run_index_one (a b : Cell) (entries : List (Scalar × Scalar)) (ops : List Op)
    (stack : List Node) (reads : List Cell) :
    run (.index 1 false :: ops) ⟨.array [a,b] entries :: stack, reads⟩ =
      run ops ⟨.cell b :: stack, reads⟩ := by rfl

theorem run_index_two (a b : Cell) (entries : List (Scalar × Scalar)) (path : _root_.Bool) (ops : List Op)
    (stack : List Node) (reads : List Cell) :
    run (.index 2 path :: ops) ⟨.array [a,b] entries :: stack, reads⟩ =
      run ops ⟨.map entries :: (if path then .cell (field (scalar 2)) :: .array [a,b] entries :: stack else stack), reads⟩ := by rfl

theorem run_member (key : Scalar) (entries : List (Scalar × Scalar)) (ops : List Op)
    (stack : List Node) (reads : List Cell) :
    run (.member :: ops) ⟨.cell (field key) :: .map entries :: stack, reads⟩ =
      run ops ⟨.cell (boolean (entries.any (fun p => p.1 == key))) :: stack, reads⟩ := by rfl

theorem run_insert_two (a b : Cell) (entries : List (Scalar × Scalar)) (key value : Scalar)
    (ops : List Op) (stack : List Node) (reads : List Cell) :
    run (.insert 2 :: ops) ⟨.cell (field value) :: .cell (field key) :: .map entries ::
      .cell (field (scalar 2)) :: .array [a,b] entries :: stack, reads⟩ =
      run ops ⟨.array [a,b] ((key,value) :: entries.filter (fun p => p.1 != key)) :: stack, reads⟩ := by
  simp [run, step, insert, field, show (scalar 2).val = 2 by decide]

/-- Generic root slots use the same native index and insert opcodes as the
fixed claim. A slot's former constructor must match the inserted constructor. -/
theorem run_index_vector (items : List Slot) (slot : Nat) (path : _root_.Bool)
    (child : Slot) (ops : List Op) (stack : List Node) (reads : List Cell)
    (found : items[slot]? = some child) :
    run (.index slot path :: ops) ⟨.vector items :: stack, reads⟩ =
      run ops ⟨child.toNode ::
        (if path then .cell (field (scalar slot)) :: .vector items :: stack else stack), reads⟩ := by
  simp [run, step, found]

/-- A direct map index traverses the root slot and the typed scalar key in one
native VM operation. It returns the field-aligned stored value and leaves the
caller-owned stack below the root untouched. -/
theorem run_mapIndex_vector (items : List Slot) (slot : Nat)
    (entries : List (Scalar × Scalar)) (key value : Scalar)
    (ops : List Op) (stack : List Node) (reads : List Cell)
    (foundMap : items[slot]? = some (.map entries))
    (foundKey : entries.lookup key = some value) :
    run (.mapIndex slot (field key) :: ops) ⟨.vector items :: stack, reads⟩ =
      run ops ⟨.cell (field value) :: stack, reads⟩ := by
  simp [run, step, field, foundMap, foundKey]

/-- The legacy fixed-claim array representation places its embedded map after
the fixed cell prefix, matching its root-array index. -/
theorem run_mapIndex_array (cells : List Cell)
    (entries : List (Scalar × Scalar)) (key value : Scalar)
    (ops : List Op) (stack : List Node) (reads : List Cell)
    (slotIsMap : cells.length = slot)
    (foundKey : entries.lookup key = some value) :
    run (.mapIndex slot (field key) :: ops) ⟨.array cells entries :: stack, reads⟩ =
      run ops ⟨.cell (field value) :: stack, reads⟩ := by
  simp [run, step, field, slotIsMap, foundKey]

/-- Missing map keys reject instead of yielding a default scalar. -/
theorem run_mapIndex_vector_missing (items : List Slot) (slot : Nat)
    (entries : List (Scalar × Scalar)) (key : Scalar)
    (ops : List Op) (stack : List Node) (reads : List Cell)
    (foundMap : items[slot]? = some (.map entries))
    (missingKey : entries.lookup key = none) :
    run (.mapIndex slot (field key) :: ops) ⟨.vector items :: stack, reads⟩ = none := by
  simp [run, step, field, foundMap, missingKey]

/-- A map index against a cell slot rejects even when the key is present in a
different state map. -/
theorem run_mapIndex_vector_wrongContainer (items : List Slot) (slot : Nat)
    (cell : Cell) (key : Scalar) (ops : List Op) (stack : List Node) (reads : List Cell)
    (foundCell : items[slot]? = some (.cell cell)) :
    run (.mapIndex slot (field key) :: ops) ⟨.vector items :: stack, reads⟩ = none := by
  simp [run, step, field, foundCell]

/-- Map-index requires the ledger's field-aligned scalar key encoding. A bit
cell cannot silently alias a field key with the same numeric payload. -/
theorem run_mapIndex_vector_wrongKeyAlignment (items : List Slot) (slot : Nat)
    (key : Bool)
    (ops : List Op) (stack : List Node) (reads : List Cell) :
    run (.mapIndex slot (boolean key) :: ops) ⟨.vector items :: stack, reads⟩ = none := by
  simp [run, step, boolean]

theorem run_insert_vector_cell (items : List Slot) (slot : Nat) (old value : Cell)
    (ops : List Op) (stack : List Node) (reads : List Cell)
    (found : items[slot]? = some (.cell old))
    (canonicalSlot : slot < Field.modulus) :
    run (.insert 1 :: ops)
      ⟨.cell value :: .cell (field (scalar slot)) :: .vector items :: stack, reads⟩ =
      run ops ⟨.vector (items.set slot (.cell value)) :: stack, reads⟩ := by
  have inserted :
      insert 1 (.cell value) (.cell (field (scalar slot)) :: .vector items :: stack) =
        some (.vector (items.set slot (.cell value)) :: stack) := by
    simp [insert, field, scalar_no_wrap slot canonicalSlot, found]
  simp [run, step, inserted]

theorem run_insert_vector_map (items : List Slot) (slot : Nat)
    (old : List (Scalar × Scalar)) (key value : Scalar)
    (ops : List Op) (stack : List Node) (reads : List Cell)
    (found : items[slot]? = some (.map old))
    (canonicalSlot : slot < Field.modulus) :
    run (.insert 2 :: ops)
      ⟨.cell (field value) :: .cell (field key) :: .map old ::
        .cell (field (scalar slot)) :: .vector items :: stack, reads⟩ =
      run ops ⟨.vector (items.set slot (.map ((key, value) :: old.filter (fun p => p.1 != key)))) ::
        stack, reads⟩ := by
  have inserted :
      insert 2 (.cell (field value))
        (.cell (field key) :: .map old :: .cell (field (scalar slot)) :: .vector items :: stack) =
        some (.vector (items.set slot (.map ((key, value) :: old.filter (fun p => p.1 != key)))) :: stack) := by
    simp [insert, field, scalar_no_wrap slot canonicalSlot, found]
  simp [run, step, inserted]

/-- Every executed prefix is checked, including the exact final stack and read
stream. An adversarial trace is accepted only when every transition holds. -/
inductive Trace : List Op → Machine → Machine → Prop where
  | nil (machine) : Trace [] machine machine
  | cons {op ops before middle after} : step op before = some middle →
      Trace ops middle after → Trace (op :: ops) before after

theorem trace_iff_run (ops : List Op) (before after : Machine) :
    Trace ops before after ↔ run ops before = some after := by
  constructor
  · intro trace
    induction trace with
    | nil => rfl
    | cons h _ ih => simp only [run, h, Option.bind_some, ih]
  · induction ops generalizing before with
    | nil => intro h; cases Option.some.inj h; exact .nil _
    | cons op ops ih =>
      intro h
      cases hs : step op before with
      | none => simp [run, hs] at h
      | some middle => exact .cons hs (ih middle (by simpa [run, hs] using h))

def Cell.fields (value : Cell) : List Scalar :=
  [one, if value.alignment = .field then scalar (Field.modulus - 2) else one, value.value]

def Op.fields : Op → List Scalar
  | .push value storage => [scalar (if storage then 0x11 else 0x10), one] ++ value.fields
  | .popeq value => scalar 0x0c :: value.fields
  | .dup => [scalar 0x30]
  | .index slot path => scalar (if path then 0x70 else 0x50) :: (field (scalar slot)).fields
  | .mapIndex slot key => scalar 0x51 :: (field (scalar slot)).fields ++ key.fields
  | .member => [scalar 0x18]
  | .insert levels => [scalar (0x90 + levels)]

/-- All groups are active, so there are no skip/activity choices in this subset.
Binding groups as lists preserves opcode boundaries, not merely concatenation. -/
def groups (ops : List Op) : List (List Scalar) := ops.map Op.fields

def initial (root campaign : Scalar) (entries : List (Scalar × Scalar)) : Machine :=
  ⟨[.array [field root, field campaign] entries], []⟩

/-- A symbolic bound for the formal machine. Mapping these units to pinned
ledger cost/size limits is an explicit implementation admission obligation. -/
structure Budget where
  operations : Nat
  entries : Nat

def Admitted (budget : Budget) (ops : List Op) (entries : List (Scalar × Scalar)) : Prop :=
  ops.length ≤ budget.operations ∧ entries.length + 1 ≤ budget.entries

end Noctium.Verification.NativeState
