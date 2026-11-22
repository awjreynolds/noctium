import Noctium.Verification.GenericStateEncoding
import Noctium.Verification.SourceEffects

namespace Noctium.Verification.GenericStateVM
open NativeRelation NativeState GenericStateEncoding

def readCellOps (slot : Nat) (expected : Cell) : List Op :=
  [.dup, .index slot false, .popeq expected]

def requireAbsentOps (slot : Nat) (key : Scalar) : List Op :=
  [.dup, .index slot false, .push (field key) false, .member,
    .popeq (boolean false)]

def writeCellOps (slot : Nat) (value : Cell) : List Op :=
  [.push (field (scalar slot)) false, .push value true, .insert 1]

def writeMapOps (slot : Nat) (key value : Scalar) : List Op :=
  [.index slot true, .push (field key) false, .push (field value) true, .insert 2]

/-- A successful whole VM transcript has one successful intermediate machine
per emitted operation chunk, with no skipped or reordered segment. -/
inductive RunsChunks : List (List Op) → Machine → Machine → Prop where
  | nil (machine : Machine) : RunsChunks [] machine machine
  | cons (segment : List Op) (remaining : List (List Op))
      (before middle after : Machine)
      (first : run segment before = some middle)
      (later : RunsChunks remaining middle after) :
      RunsChunks (segment :: remaining) before after

theorem run_chunks_iff (chunks : List (List Op))
    (before after : Machine) :
    run chunks.flatten before = some after ↔
      RunsChunks chunks before after := by
  induction chunks generalizing before with
  | nil =>
    constructor
    · intro accepted
      change some before = some after at accepted
      cases accepted
      exact RunsChunks.nil _
    · intro trace
      cases trace
      rfl
  | cons segment remaining ih =>
    simp only [List.flatten_cons, run_append]
    constructor
    · intro accepted
      cases first : run segment before with
      | none => simp [first] at accepted
      | some middle =>
        simp only [first, Option.bind_some] at accepted
        exact RunsChunks.cons segment remaining before middle after first
          ((ih middle).mp accepted)
    · intro trace
      cases trace with
      | cons _ _ _ middle _ first later =>
        rw [first]
        exact (ih middle).mpr later

theorem run_input_pair (value : Cell) (stack : List Node) (reads : List Cell) :
    run [.push value false, .popeq value] ⟨stack, reads⟩ =
      some ⟨stack, reads ++ [value]⟩ := by
  simp [run, step]

theorem run_input_pairs (values : List Cell)
    (stack : List Node) (reads : List Cell) :
    run (values.flatMap (fun value => [.push value false, .popeq value]))
      ⟨stack, reads⟩ = some ⟨stack, reads ++ values⟩ := by
  induction values generalizing reads with
  | nil => simp [run]
  | cons value rest ih =>
    simp only [List.flatMap_cons, run_append]
    rw [run_input_pair]
    simp only [Option.bind_some]
    rw [ih]
    simp [List.append_assoc]

/-- An arbitrary successful read observes the current native slot, including
a value written by any earlier VM prefix. -/
theorem readCell_sound (items : List Slot) (slot : Nat) (expected : Cell)
    (after : Machine)
    (accepted : run (readCellOps slot expected) (GenericStateEncoding.initial items) = some after) :
    items[slot]? = some (.cell expected) ∧
      after = ⟨[.vector items], [expected]⟩ := by
  cases found : items[slot]? with
  | none => simp [readCellOps, run, step, GenericStateEncoding.initial, found] at accepted
  | some child =>
    cases child with
    | map entries => simp [readCellOps, run, step, GenericStateEncoding.initial, Slot.toNode, found] at accepted
    | cell actual =>
      by_cases same : actual = expected
      · subst actual
        simp [readCellOps, run, step, GenericStateEncoding.initial, Slot.toNode, found] at accepted
        cases accepted
        exact ⟨rfl, rfl⟩
      · simp [readCellOps, run, step, GenericStateEncoding.initial, Slot.toNode, found, same] at accepted

theorem readCell_exact (items : List Slot) (slot : Nat) (value : Cell)
    (reads : List Cell) (found : items[slot]? = some (.cell value)) :
    run (readCellOps slot value) ⟨[.vector items], reads⟩ =
      some ⟨[.vector items], reads ++ [value]⟩ := by
  simp only [readCellOps]
  rw [run_dup, run_index_vector items slot false (.cell value)
    [.popeq value] [.vector items] reads found]
  simp [Slot.toNode, run_popeq, run_nil]

theorem readCell_sound_prefix (items : List Slot) (slot : Nat) (expected : Cell)
    (reads : List Cell) (after : Machine)
    (accepted : run (readCellOps slot expected) ⟨[.vector items], reads⟩ = some after) :
    items[slot]? = some (.cell expected) ∧
      after = ⟨[.vector items], reads ++ [expected]⟩ := by
  cases found : items[slot]? with
  | none => simp [readCellOps, run, step, found] at accepted
  | some child =>
    cases child with
    | map entries => simp [readCellOps, run, step, Slot.toNode, found] at accepted
    | cell actual =>
      by_cases same : actual = expected
      · subst actual
        rw [readCell_exact items slot expected reads found] at accepted
        cases accepted
        exact ⟨rfl, rfl⟩
      · simp [readCellOps, run, step, Slot.toNode, found, same] at accepted

/-- A checked native read of a declared cell identifies the original source
ledger value at that slot, including after any earlier state transition whose
current encoding is supplied. -/
theorem readCell_source (declarations : List StateDecl) (state : LedgerState)
    (items : List Slot) (slot : Nat) (name : String) (ty : Ty)
    (expected : Cell) (reads : List Cell) (after : Machine)
    (declaration : declarations[slot]? = some {name, kind := .cell ty})
    (encoded : encodeState declarations state = some items)
    (accepted : run (readCellOps slot expected) ⟨[.vector items], reads⟩ = some after) :
    ∃ raw,
      state.cells.lookup name = some raw ∧
      decodeValue ty expected = some raw ∧
      after = ⟨[.vector items], reads ++ [expected]⟩ := by
  obtain ⟨found, final⟩ := readCell_sound_prefix items slot expected reads after accepted
  have slotEncoding := encodeState_slot declarations state items slot encoded
  rw [declaration] at slotEncoding
  simp only [Option.bind_some] at slotEncoding
  rw [found] at slotEncoding
  have fromSource := encoded_cell_source state name ty expected slotEncoding.symm
  rcases fromSource with ⟨raw, lookup, decoded⟩
  exact ⟨raw, lookup, decoded, final⟩

theorem readCell_source_typed (declarations : List StateDecl) (state : LedgerState)
    (items : List Slot) (slot : Nat) (name : String) (ty : Ty)
    (expected : Cell) (reads : List Cell) (after : Machine)
    (declaration : declarations[slot]? = some {name, kind := .cell ty})
    (encoded : encodeState declarations state = some items)
    (accepted : run (readCellOps slot expected) ⟨[.vector items], reads⟩ = some after) :
    ∃ value,
      state.cells.lookup name = some (Value.pack ty value) ∧
      ScalarNormalization.Canonical ty value ∧
      expected = field (scalar (number ty value)) ∧
      after = ⟨[.vector items], reads ++ [expected]⟩ := by
  obtain ⟨found, final⟩ := readCell_sound_prefix items slot expected reads after accepted
  have slotEncoding := encodeState_slot declarations state items slot encoded
  rw [declaration] at slotEncoding
  simp only [Option.bind_some] at slotEncoding
  rw [found] at slotEncoding
  obtain ⟨value, lookup, canonical, fieldValue⟩ :=
    encoded_cell_typed state name ty expected slotEncoding.symm
  exact ⟨value, lookup, canonical, fieldValue, final⟩

private theorem sourceCanonical (ctx : EvalContext) (ty : Ty)
    (value : ty.Denote) (modulus : ctx.modulus = Field.modulus)
    (canonical : ScalarNormalization.Canonical ty value) :
    SourceEffects.canonicalValue ctx ty value = true := by
  cases ty with
  | native =>
    simpa [SourceEffects.canonicalValue, ScalarNormalization.Canonical,
      ScalarNormalization.sourceNumber?, modulus] using canonical.1
  | bool => rfl
  | uint maximum =>
    rcases canonical with ⟨bound, maximumBound, valueBound⟩
    have fieldBound : value < Field.modulus := by
      simpa [ScalarNormalization.Canonical, ScalarNormalization.sourceNumber?] using bound
    simp [SourceEffects.canonicalValue, modulus, fieldBound, maximumBound, valueBound]
  | bytes _ | opaqueBytes | opaqueString | jubjubScalar | jubjubPoint | foreign _ =>
    simp [ScalarNormalization.Canonical, ScalarNormalization.sourceNumber?] at canonical

/-- A successful checked read segment executes the corresponding original
source effect with the same typed value and unchanged tentative ledger state. -/
theorem readCell_source_step (ctx : EvalContext) (env : EvalEnv)
    (declarations : List StateDecl) (state : LedgerState)
    (items : List Slot) (slot : Nat) (name destination : String) (ty : Ty)
    (expected : Cell) (reads : List Cell) (after : Machine)
    (modulus : ctx.modulus = Field.modulus)
    (declaration : declarations[slot]? = some {name, kind := .cell ty})
    (encoded : encodeState declarations state = some items)
    (accepted : run (readCellOps slot expected) ⟨[.vector items], reads⟩ = some after) :
    ∃ value,
      SourceEffects.step ctx (.readCell name destination ty) (env, state) =
        .ok ((destination, Value.pack ty value) :: env, state) ∧
      expected = field (scalar (number ty value)) ∧
      after = ⟨[.vector items], reads ++ [expected]⟩ := by
  obtain ⟨value, lookup, canonical, fieldValue, final⟩ :=
    readCell_source_typed declarations state items slot name ty expected reads after
      declaration encoded accepted
  have checked := sourceCanonical ctx ty value modulus canonical
  refine ⟨value, ?_, fieldValue, final⟩
  simp only [SourceEffects.step, runEffectWithEnv, lookup]
  rw [ScalarNormalization.number_pack_as ty value canonical]
  simp only []
  change (if !(SourceEffects.canonicalValue ctx ty value) then _ else _) = _
  simp [checked]
  rfl

/-- A successful absence check observes a map slot with no matching key and
leaves the native root unchanged. -/
theorem requireAbsent_sound (items : List Slot) (slot : Nat) (key : Scalar)
    (after : Machine)
    (accepted : run (requireAbsentOps slot key) (GenericStateEncoding.initial items) = some after) :
    (∃ entries, items[slot]? = some (.map entries) ∧
      entries.any (fun p => p.1 == key) = false) ∧
      after = ⟨[.vector items], [boolean false]⟩ := by
  cases found : items[slot]? with
  | none => simp [requireAbsentOps, run, step, GenericStateEncoding.initial, found] at accepted
  | some child =>
    cases child with
    | cell value =>
      simp [requireAbsentOps, run, step, GenericStateEncoding.initial, Slot.toNode, found] at accepted
    | map entries =>
      simp only [requireAbsentOps, GenericStateEncoding.initial] at accepted
      rw [run_dup, run_index_vector items slot false (.map entries)
        [.push (field key) false, .member, .popeq (boolean false)]
        [.vector items] [] found] at accepted
      simp only [Slot.toNode, Bool.false_eq_true, ↓reduceIte,
        run_push, run_member, run_popeq, run_nil] at accepted
      cases present : entries.any (fun p => p.1 == key) with
      | true =>
        simp [present, boolean_ne] at accepted
      | false =>
        simp [present] at accepted
        cases accepted
        exact ⟨⟨entries, rfl, present⟩, rfl⟩

theorem requireAbsent_exact (items : List Slot) (slot : Nat)
    (entries : List (Scalar × Scalar)) (key : Scalar)
    (reads : List Cell) (found : items[slot]? = some (.map entries))
    (absent : entries.any (fun p => p.1 == key) = false) :
    run (requireAbsentOps slot key) ⟨[.vector items], reads⟩ =
      some ⟨[.vector items], reads ++ [boolean false]⟩ := by
  simp only [requireAbsentOps]
  rw [run_dup, run_index_vector items slot false (.map entries)
    [.push (field key) false, .member, .popeq (boolean false)]
    [.vector items] reads found]
  simp [Slot.toNode, run_push, run_member, absent, run_popeq, run_nil]

theorem requireAbsent_sound_prefix (items : List Slot) (slot : Nat) (key : Scalar)
    (reads : List Cell) (after : Machine)
    (accepted : run (requireAbsentOps slot key) ⟨[.vector items], reads⟩ = some after) :
    (∃ entries, items[slot]? = some (.map entries) ∧
      entries.any (fun p => p.1 == key) = false) ∧
      after = ⟨[.vector items], reads ++ [boolean false]⟩ := by
  cases found : items[slot]? with
  | none => simp [requireAbsentOps, run, step, found] at accepted
  | some child =>
    cases child with
    | cell value => simp [requireAbsentOps, run, step, Slot.toNode, found] at accepted
    | map entries =>
      simp only [requireAbsentOps] at accepted
      rw [run_dup, run_index_vector items slot false (.map entries)
        [.push (field key) false, .member, .popeq (boolean false)]
        [.vector items] reads found] at accepted
      simp only [Slot.toNode, Bool.false_eq_true, ↓reduceIte,
        run_push, run_member, run_popeq, run_nil] at accepted
      cases present : entries.any (fun p => p.1 == key) with
      | true => simp [present, boolean_ne] at accepted
      | false =>
        simp [present] at accepted
        cases accepted
        exact ⟨⟨entries, rfl, present⟩, rfl⟩

/-- A native membership rejection on a declared map entails the same source
absence check. The key expression is evaluated by the source semantics. -/
theorem requireAbsent_source_step (ctx : EvalContext) (env : EvalEnv)
    (declarations : List StateDecl) (state : LedgerState)
    (items : List Slot) (slot : Nat) (name : String)
    (keyTy valueTy : Ty) (keyExpr : Expr keyTy)
    (key : keyTy.Denote) (reads : List Cell) (after : Machine)
    (declaration : declarations[slot]? = some
      {name, kind := .map keyTy valueTy})
    (encoded : encodeState declarations state = some items)
    (keyEval : keyExpr.eval ctx env = .ok key)
    (canonical : ScalarNormalization.Canonical keyTy key)
    (accepted : run (requireAbsentOps slot (scalar (number keyTy key)))
      ⟨[.vector items], reads⟩ = some after) :
    SourceEffects.step ctx (.requireAbsent name keyTy keyExpr) (env, state) =
      .ok (env, state) ∧
    after = ⟨[.vector items], reads ++ [boolean false]⟩ := by
  obtain ⟨⟨encodedEntries, found, absent⟩, final⟩ :=
    requireAbsent_sound_prefix items slot (scalar (number keyTy key)) reads after accepted
  have slotEncoding := encodeState_slot declarations state items slot encoded
  rw [declaration] at slotEncoding
  simp only [Option.bind_some] at slotEncoding
  rw [found] at slotEncoding
  obtain ⟨entries, mapLookup, mapped⟩ :=
    encoded_map_source state name keyTy valueTy encodedEntries slotEncoding.symm
  have sourceAbsent := encodedMap_absent keyTy valueTy entries encodedEntries key
    canonical mapped absent
  constructor
  · simp [SourceEffects.step, runEffectWithEnv, keyEval, mapLookup, sourceAbsent,
      bind, Except.bind, Except.pure]
    rfl
  · exact final

theorem require_source_step (ctx : EvalContext) (env : EvalEnv)
    (state : LedgerState) (condition : Expr .bool)
    (evaluated : condition.eval ctx env = .ok true) :
    SourceEffects.step ctx (.require condition) (env, state) = .ok (env, state) := by
  simp [SourceEffects.step, runEffectWithEnv, evaluated, bind, Except.bind, Except.pure]
  rfl

theorem writeCell_exact (items : List Slot) (slot : Nat) (old value : Cell)
    (reads : List Cell) (found : items[slot]? = some (.cell old))
    (canonicalSlot : slot < Field.modulus) :
    run (writeCellOps slot value) ⟨[.vector items], reads⟩ =
      some ⟨[.vector (items.set slot (.cell value))], reads⟩ := by
  simp only [writeCellOps, run_push]
  rw [run_insert_vector_cell items slot old value [] [] reads found canonicalSlot]
  rfl

/-- A checked cell write has the same successor as the original source
effect, for any admitted current encoding and distinct declaration names. -/
theorem writeCell_source_step (ctx : EvalContext) (env : EvalEnv)
    (declarations : List StateDecl) (state : LedgerState)
    (items : List Slot) (slot : Nat) (name : String) (ty : Ty)
    (expression : Expr ty) (value : ty.Denote) (reads : List Cell)
    (declaration : declarations[slot]? = some {name, kind := .cell ty})
    (distinct : declarations.Pairwise (fun left right => left.name ≠ right.name))
    (encoded : encodeState declarations state = some items)
    (slotBound : declarations.length < Field.modulus)
    (evaluated : expression.eval ctx env = .ok value)
    (canonical : ScalarNormalization.Canonical ty value) :
    ∃ next,
      SourceEffects.step ctx (.writeCell name ty expression) (env, state) =
        .ok (env, next) ∧
      encodeState declarations next =
        some (items.set slot (.cell (field (scalar (number ty value))))) ∧
      run (writeCellOps slot (field (scalar (number ty value))))
        ⟨[.vector items], reads⟩ =
        some ⟨[.vector (items.set slot
          (.cell (field (scalar (number ty value)))))], reads⟩ := by
  have slotEncoding := encodeState_slot declarations state items slot encoded
  rw [declaration] at slotEncoding
  simp only [Option.bind_some] at slotEncoding
  have inRange : slot < declarations.length := by
    by_cases inside : slot < declarations.length
    · exact inside
    · have missing := List.getElem?_eq_none (l := declarations) (i := slot)
        (Nat.le_of_not_gt inside)
      rw [missing] at declaration
      contradiction
  have itemRange : slot < items.length := by
    rw [encodeState_length declarations state items encoded]
    exact inRange
  have sourceExists : encodeDeclaration state {name, kind := .cell ty} ≠ none := by
    intro absent
    rw [absent] at slotEncoding
    exact (Nat.not_le_of_gt itemRange) (List.getElem?_eq_none_iff.mp slotEncoding)
  have oldFound : ∃ old : Cell, items[slot]? = some (.cell old) := by
    cases rawLookup : state.cells.lookup name with
    | none => simp [encodeDeclaration, rawLookup] at sourceExists
    | some rawValue =>
      cases cellEncoding : encodeValue ty rawValue with
      | none => simp [encodeDeclaration, rawLookup, cellEncoding] at sourceExists
      | some old =>
        exact ⟨old, by simpa [encodeDeclaration, rawLookup, cellEncoding] using slotEncoding⟩
  obtain ⟨old, found⟩ := oldFound
  have oldEncoded : encodeDeclaration state {name, kind := .cell ty} = some (.cell old) := by
    simpa [found] using slotEncoding.symm
  obtain ⟨oldValue, oldLookup, oldCanonical, _⟩ :=
    encoded_cell_typed state name ty old oldEncoded
  let next : LedgerState := {state with cells := SourceEffects.updateEntry name (Value.pack ty value) state.cells}
  refine ⟨next, ?_, ?_, ?_⟩
  · simp only [SourceEffects.step, runEffectWithEnv, oldLookup, evaluated]
    rw [ScalarNormalization.number_pack_as ty oldValue oldCanonical]
    simp [next, SourceEffects.updateEntry, updateAssoc]
    rfl
  · exact encodeState_updateCell_at declarations state items slot name ty value
      encoded declaration distinct canonical
  · have bound : slot < Field.modulus := Nat.lt_trans inRange slotBound
    exact writeCell_exact items slot old _ reads found bound

theorem writeMap_exact (items : List Slot) (slot : Nat)
    (old : List (Scalar × Scalar)) (key value : Scalar)
    (reads : List Cell) (found : items[slot]? = some (.map old))
    (canonicalSlot : slot < Field.modulus) :
    run (writeMapOps slot key value) ⟨[.vector items], reads⟩ =
      some ⟨[.vector (items.set slot (.map
        ((key, value) :: old.filter (fun p => p.1 != key))))], reads⟩ := by
  simp only [writeMapOps]
  rw [run_index_vector items slot true (.map old)
    [.push (field key) false, .push (field value) true, .insert 2] [] reads found]
  simp only [Slot.toNode, ↓reduceIte, run_push]
  rw [run_insert_vector_map items slot old key value [] [] reads found canonicalSlot]
  rfl

private theorem mapEntries_typeCheck (entries : List (Value × Value))
    (keyTy valueTy : Ty) (name : String)
    (typed : ∀ entry ∈ entries,
      ∃ key value, entry.1.as keyTy = some key ∧ entry.2.as valueTy = some value) :
    (forIn entries PUnit.unit fun entry _ =>
      if (entry.1.as keyTy).isNone || (entry.2.as valueTy).isNone then
        (fun _ => ForInStep.yield PUnit.unit) <$>
          (throw s!"state map type mismatch '{name}'" : Except String PUnit)
      else pure (.yield PUnit.unit) : Except String PUnit) = .ok .unit := by
  induction entries with
  | nil => rfl
  | cons entry rest ih =>
    obtain ⟨key, value, keyTyped, valueTyped⟩ := typed entry (by simp)
    have restTyped : ∀ item ∈ rest,
        ∃ key value, item.1.as keyTy = some key ∧ item.2.as valueTy = some value := by
      intro item member
      exact typed item (by simp [member])
    rcases entry with ⟨oldKey, oldValue⟩
    simpa [List.forIn_cons, keyTyped, valueTyped] using ih restTyped

theorem writeMap_source_step (ctx : EvalContext) (env : EvalEnv)
    (declarations : List StateDecl) (state : LedgerState)
    (items : List Slot) (slot : Nat) (name : String)
    (keyTy valueTy : Ty) (keyExpr : Expr keyTy) (valueExpr : Expr valueTy)
    (key : keyTy.Denote) (value : valueTy.Denote) (reads : List Cell)
    (declaration : declarations[slot]? = some {name, kind := .map keyTy valueTy})
    (distinct : declarations.Pairwise (fun left right => left.name ≠ right.name))
    (encoded : encodeState declarations state = some items)
    (slotBound : declarations.length < Field.modulus)
    (keyEval : keyExpr.eval ctx env = .ok key)
    (valueEval : valueExpr.eval ctx env = .ok value)
    (keyCanonical : ScalarNormalization.Canonical keyTy key)
    (valueCanonical : ScalarNormalization.Canonical valueTy value) :
    ∃ (next : LedgerState) (encodedEntries : List (Scalar × Scalar)),
      SourceEffects.step ctx (.writeMap name keyTy valueTy keyExpr valueExpr) (env, state) =
        .ok (env, next) ∧
      encodeState declarations next =
        some (items.set slot (.map ((scalar (number keyTy key), scalar (number valueTy value)) ::
          encodedEntries.filter (fun pair => pair.1 != scalar (number keyTy key))))) ∧
      run (writeMapOps slot (scalar (number keyTy key)) (scalar (number valueTy value)))
        ⟨[.vector items], reads⟩ =
        some ⟨[.vector (items.set slot (.map ((scalar (number keyTy key),
          scalar (number valueTy value)) ::
          encodedEntries.filter (fun pair => pair.1 != scalar (number keyTy key)))))], reads⟩ := by
  have slotEncoding := encodeState_slot declarations state items slot encoded
  rw [declaration] at slotEncoding
  simp only [Option.bind_some] at slotEncoding
  have inRange : slot < declarations.length := by
    by_cases inside : slot < declarations.length
    · exact inside
    · have missing := List.getElem?_eq_none (l := declarations) (i := slot)
        (Nat.le_of_not_gt inside)
      rw [missing] at declaration
      contradiction
  have itemRange : slot < items.length := by
    rw [encodeState_length declarations state items encoded]
    exact inRange
  have sourceExists : encodeDeclaration state {name, kind := .map keyTy valueTy} ≠ none := by
    intro absent
    rw [absent] at slotEncoding
    exact (Nat.not_le_of_gt itemRange) (List.getElem?_eq_none_iff.mp slotEncoding)
  have oldFound : ∃ encodedEntries, items[slot]? = some (.map encodedEntries) := by
    cases mapLookup : state.maps.lookup name with
    | none => simp [encodeDeclaration, mapLookup] at sourceExists
    | some entries =>
      cases mapped : entries.mapM (encodeMapEntry keyTy valueTy) with
      | none => simp [encodeDeclaration, mapLookup, mapped] at sourceExists
      | some encodedEntries =>
        by_cases duplicate :
            (encodedEntries.map Prod.fst).eraseDups.length != encodedEntries.length
        · have mismatch := bne_iff_ne.mp duplicate
          simp [encodeDeclaration, mapLookup, mapped] at sourceExists
          exact False.elim (mismatch sourceExists)
        · refine ⟨encodedEntries, ?_⟩
          have sameLength : (encodedEntries.map Prod.fst).eraseDups.length =
              encodedEntries.length := by
            by_cases same : (encodedEntries.map Prod.fst).eraseDups.length =
                encodedEntries.length
            · exact same
            · exact False.elim (duplicate (bne_iff_ne.mpr same))
          simpa [encodeDeclaration, mapLookup, mapped, sameLength] using slotEncoding
  obtain ⟨encodedEntries, found⟩ := oldFound
  have oldEncoded : encodeDeclaration state {name, kind := .map keyTy valueTy} =
      some (.map encodedEntries) := by simpa [found] using slotEncoding.symm
  obtain ⟨entries, mapLookup, mapped⟩ :=
    encoded_map_source state name keyTy valueTy encodedEntries oldEncoded
  let next : LedgerState := {state with maps := (SourceEffects.updateEntry name
    (SourceEffects.updateEntry (Value.pack keyTy key) (Value.pack valueTy value) entries) state.maps)}
  refine ⟨next, encodedEntries, ?_, ?_, ?_⟩
  · have typed := encodedMapEntries_typed keyTy valueTy entries encodedEntries mapped
    have checked := mapEntries_typeCheck entries keyTy valueTy name typed
    simp only [SourceEffects.step, runEffectWithEnv, keyEval, valueEval, mapLookup,
      bind, Except.bind]
    change ((fun _ : PUnit => (env, next)) <$>
      (forIn entries PUnit.unit fun entry _ =>
        if (entry.1.as keyTy).isNone || (entry.2.as valueTy).isNone then
          (fun _ => ForInStep.yield PUnit.unit) <$>
            (throw s!"state map type mismatch '{name}'" : Except String PUnit)
        else pure (.yield PUnit.unit) : Except String PUnit)) = .ok (env, next)
    rw [checked]
    rfl
  · exact encodeState_updateMap_at declarations state items slot name keyTy valueTy
      entries encodedEntries key value encoded declaration distinct mapped
      (encoded_map_nodup state name keyTy valueTy encodedEntries oldEncoded)
      keyCanonical valueCanonical
  · exact writeMap_exact items slot encodedEntries _ _ reads found
      (Nat.lt_trans inRange slotBound)

end Noctium.Verification.GenericStateVM
