import Noctium.Verification.GenericStateVM
import Noctium.Verification.GenericStateEvaluationCanonical

namespace Noctium.Verification.GenericStateSchemaSpans
open GenericStateEncoding NativeState

/-- Normalize source-only metadata for the legacy scalar proof schema.
Spans and sealing do not affect slot encoding. Direct cell alignment remains
intact because it controls whether a cell has a supported scalar encoding. -/
def eraseSpan (declaration : StateDecl) : StateDecl :=
  { declaration with
    sealed := false
    span := {}
    cellAlignment? := match declaration.kind with
      | .cell _ => declaration.cellAlignment?
      | _ => none }

def eraseSpans (declarations : List StateDecl) : List StateDecl :=
  declarations.map eraseSpan

theorem encodeDeclaration_eraseSpan (state : LedgerState) (declaration : StateDecl) :
    encodeDeclaration state (eraseSpan declaration) =
      encodeDeclaration state declaration := by
  cases declaration with
  | mk name kind sealed span cellAlignment? =>
    cases kind <;> cases cellAlignment? <;> rfl

theorem encodeState_eraseSpans (declarations : List StateDecl)
    (state : LedgerState) :
    encodeState (eraseSpans declarations) state =
      encodeState declarations state := by
  induction declarations with
  | nil => rfl
  | cons head tail ih =>
    have tailEq : (tail.map eraseSpan).mapM (encodeDeclaration state) =
        tail.mapM (encodeDeclaration state) := by
      simpa only [eraseSpans, encodeState] using ih
    simp only [eraseSpans, List.map_cons, encodeState, List.mapM_cons]
    rw [encodeDeclaration_eraseSpan, tailEq]

theorem eraseSpans_length (declarations : List StateDecl) :
    (eraseSpans declarations).length = declarations.length := by
  simp [eraseSpans]

theorem eraseSpans_at (declarations : List StateDecl) (slot : Nat)
    (declaration : StateDecl)
    (found : declarations[slot]? = some declaration) :
    (eraseSpans declarations)[slot]? = some (eraseSpan declaration) := by
  simp [eraseSpans, List.getElem?_map, found]

theorem eraseSpans_distinct (declarations : List StateDecl)
    (distinct : declarations.Pairwise
      (fun left right => left.name ≠ right.name)) :
    (eraseSpans declarations).Pairwise
      (fun left right => left.name ≠ right.name) := by
  induction declarations with
  | nil => exact List.Pairwise.nil
  | cons head tail ih =>
    cases distinct with
    | cons headDistinct tailDistinct =>
      apply List.Pairwise.cons
      · intro item member
        obtain ⟨original, present, equal⟩ := List.mem_map.mp member
        subst item
        exact headDistinct original present
      · exact ih tailDistinct

theorem erased_at_cell (declarations : List StateDecl) (slot : Nat)
    (declaration : StateDecl) (name : String) (ty : Ty)
    (found : declarations[slot]? = some declaration)
    (named : declaration.name = name)
    (kind : declaration.kind = .cell ty)
    (alignment : declaration.cellAlignment? = none) :
    (eraseSpans declarations)[slot]? = some {name, kind := .cell ty} := by
  rw [eraseSpans_at declarations slot declaration found]
  cases declaration with
  | mk actual actualKind sealed span cellAlignment? =>
    simp only at named kind alignment
    subst actual
    subst actualKind
    subst cellAlignment?
    rfl

/-- Source lookup and Impact slot lookup select the same declaration. -/
theorem find_declaration_slot (declarations : List StateDecl) (name : String)
    (declaration : StateDecl)
    (found : declarations.find? (·.name == name) = some declaration) :
    ∃ slot, declarations.findIdx? (·.name == name) = some slot ∧
      declarations[slot]? = some declaration := by
  rw [List.find?_eq_bind_findIdx?_getElem?] at found
  cases located : declarations.findIdx? (·.name == name) with
  | none => simp [located] at found
  | some slot => exact ⟨slot, rfl, by simpa [located] using found⟩

theorem encoded_cell_alignment_none (declarations : List StateDecl)
    (state : LedgerState) (items : List Slot) (slot : Nat)
    (declaration : StateDecl) (ty : Ty)
    (found : declarations[slot]? = some declaration)
    (kind : declaration.kind = .cell ty)
    (encoded : encodeState declarations state = some items) :
    declaration.cellAlignment? = none := by
  have inRange : slot < declarations.length := by
    by_cases inside : slot < declarations.length
    · exact inside
    · have missing := List.getElem?_eq_none (l := declarations) (i := slot)
        (Nat.le_of_not_gt inside)
      rw [missing] at found
      contradiction
  have itemRange : slot < items.length := by
    rw [encodeState_length declarations state items encoded]
    exact inRange
  have slotEncoding := encodeState_slot declarations state items slot encoded
  rw [found] at slotEncoding
  simp only [Option.bind_some] at slotEncoding
  cases alignment : declaration.cellAlignment? with
  | none => rfl
  | some value =>
    have absent : items[slot]? = none := by
      simpa [encodeDeclaration, kind, alignment] using slotEncoding
    exact False.elim ((Nat.not_le_of_gt itemRange)
      (List.getElem?_eq_none_iff.mp absent))

/-- A successfully encoded source cell selected by name uses scalar alignment. -/
theorem encoded_named_cell_alignment_none (declarations : List StateDecl)
    (state : LedgerState) (items : List Slot) (name : String)
    (declaration : StateDecl) (ty : Ty)
    (found : declarations.find? (·.name == name) = some declaration)
    (kind : declaration.kind = .cell ty)
    (encoded : encodeState declarations state = some items) :
    declaration.cellAlignment? = none := by
  obtain ⟨slot, _, atSlot⟩ := find_declaration_slot declarations name declaration found
  exact encoded_cell_alignment_none declarations state items slot declaration ty atSlot kind encoded

theorem erased_at_map (declarations : List StateDecl) (slot : Nat)
    (declaration : StateDecl) (name : String) (keyTy valueTy : Ty)
    (found : declarations[slot]? = some declaration)
    (named : declaration.name = name)
    (kind : declaration.kind = .map keyTy valueTy) :
    (eraseSpans declarations)[slot]? =
      some {name, kind := .map keyTy valueTy} := by
  rw [eraseSpans_at declarations slot declaration found]
  cases declaration with
  | mk actual actualKind sealed span cellAlignment? =>
    simp only at named kind
    subst actual
    subst actualKind
    rfl

/-- The legacy typed read lemma applies to every source span carried by an
accepted declaration. -/
theorem readCell_source_typed (declarations : List StateDecl)
    (state : LedgerState) (items : List Slot) (slot : Nat)
    (declaration : StateDecl) (name : String) (ty : Ty)
    (expected : Cell) (reads : List Cell) (after : Machine)
    (found : declarations[slot]? = some declaration)
    (named : declaration.name = name)
    (kind : declaration.kind = .cell ty)
    (encoded : encodeState declarations state = some items)
    (accepted : run (GenericStateVM.readCellOps slot expected)
      ⟨[.vector items], reads⟩ = some after) :
    ∃ value,
      state.cells.lookup name = some (Value.pack ty value) ∧
      ScalarNormalization.Canonical ty value ∧
      expected = field (NativeRelation.scalar (number ty value)) ∧
      after = ⟨[.vector items], reads ++ [expected]⟩ := by
  have alignment := encoded_cell_alignment_none declarations state items slot
    declaration ty found kind encoded
  exact GenericStateVM.readCell_source_typed (eraseSpans declarations)
    state items slot name ty expected reads after
    (erased_at_cell declarations slot declaration name ty found named kind alignment)
    (by rw [encodeState_eraseSpans]; exact encoded) accepted

/-- A checked scalar map read authenticates its value against the current
source map. The encoded root stays intact and the exact value enters the tape. -/
theorem readMap_source_step (ctx : EvalContext) (env : EvalEnv)
    (declarations : List StateDecl) (state : LedgerState)
    (items : List Slot) (slot : Nat) (declaration : StateDecl)
    (name destination : String) (keyTy valueTy : Ty) (keyExpr : Expr keyTy)
    (key : keyTy.Denote) (expected : NativeRelation.Scalar) (reads : List Cell) (after : Machine)
    (found : declarations[slot]? = some declaration)
    (named : declaration.name = name)
    (kind : declaration.kind = .map keyTy valueTy)
    (encoded : encodeState declarations state = some items)
    (modulus : ctx.modulus = Field.modulus)
    (keyEval : keyExpr.eval ctx env = .ok key)
    (keyCanonical : ScalarNormalization.Canonical keyTy key)
    (accepted : run (GenericStateVM.readMapOps slot (NativeRelation.scalar (number keyTy key)) expected)
      ⟨[.vector items], reads⟩ = some after) :
    ∃ value : valueTy.Denote,
      SourceEffects.step ctx (.readMap name destination keyTy valueTy keyExpr) (env, state) =
        .ok ((destination, Value.pack valueTy value) :: env, state) ∧
      ScalarNormalization.Canonical valueTy value ∧
      expected = NativeRelation.scalar (number valueTy value) ∧
      after = ⟨[.vector items], reads ++ [field expected]⟩ := by
  obtain ⟨nativeEntries, nativeSlot, nativeLookup, nativeAfter⟩ :=
    GenericStateVM.readMap_sound items slot (NativeRelation.scalar (number keyTy key))
      expected reads after accepted
  have slotEncoding := encodeState_slot declarations state items slot encoded
  rw [found, nativeSlot] at slotEncoding
  have encodedMap : encodeDeclaration state {name, kind := .map keyTy valueTy} =
      some (.map nativeEntries) := by
    simpa [encodeDeclaration, kind, named] using slotEncoding.symm
  obtain ⟨entries, mapLookup, mapped⟩ := encoded_map_source
    state name keyTy valueTy nativeEntries encodedMap
  have matching := sourceMap_lookup keyTy valueTy entries nativeEntries key keyCanonical mapped
  rw [nativeLookup] at matching
  cases sourceLookup : entries.lookup (Value.pack keyTy key) with
  | none => simp [sourceLookup] at matching
  | some raw =>
    cases valueEncoding : encodeValue valueTy raw with
    | none => simp [sourceLookup, valueEncoding] at matching
    | some cell =>
      simp only [sourceLookup, Option.bind_some, valueEncoding, Option.map_some] at matching
      obtain ⟨value, typed, canonical, cellShape⟩ := encodeValue_source valueTy raw cell valueEncoding
      have valueMatches : expected = NativeRelation.scalar (number valueTy value) := by
        exact (Option.some.inj matching).symm.trans (congrArg Cell.value cellShape)
      refine ⟨value, ?_, canonical, valueMatches, nativeAfter⟩
      cases valueTy with
      | native =>
        have bound : value < ctx.modulus := by
          rw [modulus]
          exact canonical.1
        simp [SourceEffects.step, runEffectWithEnv, keyEval, mapLookup, sourceLookup,
          typed, canonical_eq, bound, bind, Except.bind, pure, Except.pure]
      | bool =>
        simp [SourceEffects.step, runEffectWithEnv, keyEval, mapLookup, sourceLookup,
          typed, canonical_eq, bind, Except.bind, pure, Except.pure]
      | uint maximum =>
        rcases canonical with ⟨bounded, maximumBound, valueBound⟩
        have fieldBound : value < ctx.modulus := by
          rw [modulus]
          exact bounded
        simp [SourceEffects.step, runEffectWithEnv, keyEval, mapLookup, sourceLookup,
          typed, canonical_eq, maximumBound, valueBound, fieldBound, bind, Except.bind,
          pure, Except.pure]
      | bytes _ | opaqueBytes | opaqueString | jubjubScalar | jubjubPoint | foreign _ =>
        simp [ScalarNormalization.Canonical, ScalarNormalization.sourceNumber?] at canonical

private theorem source_readMap_step_result (ctx : EvalContext) (env : EvalEnv)
    (state : LedgerState) (name destination : String)
    (keyTy valueTy : Ty) (keyExpr : Expr keyTy)
    (sourceAfter : SourceEffects.Frame)
    (sourceStep : SourceEffects.step ctx (.readMap name destination keyTy valueTy keyExpr)
      (env, state) = .ok sourceAfter) :
    ∃ key entries raw value,
      keyExpr.eval ctx env = .ok key ∧
      state.maps.lookup name = some entries ∧
      entries.lookup (Value.pack keyTy key) = some raw ∧
      raw.as valueTy = some value ∧
      sourceAfter = ((destination, Value.pack valueTy value) :: env, state) := by
  cases keyEval : keyExpr.eval ctx env with
  | error message =>
    simp [SourceEffects.step, runEffectWithEnv, keyEval, bind, Bind.bind,
      Except.bind] at sourceStep
  | ok key =>
    cases mapFound : state.maps.lookup name with
    | none =>
      simp [SourceEffects.step, runEffectWithEnv, keyEval, mapFound, bind,
        Bind.bind, Except.bind, pure, Pure.pure, Except.pure, throw, throwThe] at sourceStep
    | some entries =>
      cases mapLookup : entries.lookup (Value.pack keyTy key) with
      | none =>
        simp [SourceEffects.step, runEffectWithEnv, keyEval, mapFound, mapLookup, bind,
          Bind.bind, Except.bind, pure, Pure.pure, Except.pure, throw, throwThe] at sourceStep
      | some raw =>
        cases typed : raw.as valueTy with
        | none =>
          simp [SourceEffects.step, runEffectWithEnv, keyEval, mapFound,
            mapLookup, typed, bind, Bind.bind, Except.bind, pure, Pure.pure,
            Except.pure, throw, throwThe] at sourceStep
        | some value =>
          have reduced := sourceStep
          simp only [SourceEffects.step, runEffectWithEnv, keyEval, mapFound,
            mapLookup, typed, bind, Bind.bind, Except.bind, pure, Pure.pure,
            Except.pure, throw, throwThe] at reduced
          split at reduced
          · simp at reduced
          ·
            have frame : sourceAfter =
                ((destination, Value.pack valueTy value) :: env, state) := by
              exact (Except.ok.inj reduced).symm
            exact ⟨key, entries, raw, value, rfl, rfl, mapLookup, typed, frame⟩

/-- A successful source map read determines the scalar key and stored value
and constructs the exact native read over the same encoded root. -/
theorem readMap_source_native (ctx : EvalContext) (env : EvalEnv)
    (declarations : List StateDecl) (state : LedgerState)
    (items : List Slot) (slot : Nat) (declaration : StateDecl)
    (name destination : String) (keyTy valueTy : Ty) (keyExpr : Expr keyTy)
    (sourceAfter : SourceEffects.Frame) (reads : List Cell)
    (found : declarations[slot]? = some declaration)
    (named : declaration.name = name)
    (kind : declaration.kind = .map keyTy valueTy)
    (encoded : encodeState declarations state = some items)
    (keyAdmission : ScalarNormalization.ScalarExpression keyExpr)
    (modulus : ctx.modulus = Field.modulus)
    (sourceStep : SourceEffects.step ctx
      (.readMap name destination keyTy valueTy keyExpr) (env, state) = .ok sourceAfter) :
    ∃ key value,
      keyExpr.eval ctx env = .ok key ∧
      ScalarNormalization.Canonical keyTy key ∧
      ScalarNormalization.Canonical valueTy value ∧
      sourceAfter = ((destination, Value.pack valueTy value) :: env, state) ∧
      run (GenericStateVM.readMapOps slot
        (NativeRelation.scalar (number keyTy key))
        (NativeRelation.scalar (number valueTy value)))
        ⟨[.vector items], reads⟩ =
          some ⟨[.vector items], reads ++
            [field (NativeRelation.scalar (number valueTy value))]⟩ := by
  obtain ⟨key, sourceEntries, raw, sourceValue, keyEval, sourceMap, sourceLookup,
      sourceTyped, sourceFrame⟩ :=
    source_readMap_step_result ctx env state name destination keyTy valueTy keyExpr
      sourceAfter sourceStep
  have keyCanonical :=
    GenericStateEvaluationCanonical.expression_eval_canonical ctx env keyExpr
      keyAdmission key modulus keyEval
  obtain ⟨nativeEntries, mapped, nativeSlot⟩ := encoded_map_slot declarations
    state items slot declaration name keyTy valueTy sourceEntries found named kind encoded sourceMap
  obtain ⟨valueCell, valueEncoding⟩ := GenericStateEncoding.encodedMap_lookup_value
    keyTy valueTy sourceEntries nativeEntries (Value.pack keyTy key) raw
    mapped sourceLookup
  obtain ⟨encodedValue, encodedTyped, valueCanonical, valueShape⟩ :=
    encodeValue_source valueTy raw valueCell valueEncoding
  have sameValue : sourceValue = encodedValue :=
    Option.some.inj (sourceTyped.symm.trans encodedTyped)
  subst sourceValue
  have valueScalar : valueCell.value = NativeRelation.scalar (number valueTy encodedValue) :=
    congrArg Cell.value valueShape
  have mapLookup := sourceMap_lookup keyTy valueTy sourceEntries nativeEntries
    key keyCanonical mapped
  rw [sourceLookup] at mapLookup
  simp only [Option.bind_some, valueEncoding, Option.map_some, valueScalar] at mapLookup
  have nativeLookup : nativeEntries.lookup
      (NativeRelation.scalar (number keyTy key)) =
        some (NativeRelation.scalar (number valueTy encodedValue)) := mapLookup.symm
  have read := GenericStateVM.readMap_exact items slot nativeEntries
    (NativeRelation.scalar (number keyTy key))
    (NativeRelation.scalar (number valueTy encodedValue)) reads nativeSlot nativeLookup
  exact ⟨key, encodedValue, keyEval, keyCanonical, valueCanonical, sourceFrame, read⟩

/-- A source absence check has the same checked native result for arbitrary
declaration source spans. -/
theorem requireAbsent_source_step (ctx : EvalContext) (env : EvalEnv)
    (declarations : List StateDecl) (state : LedgerState)
    (items : List Slot) (slot : Nat) (declaration : StateDecl)
    (name : String) (keyTy valueTy : Ty) (keyExpr : Expr keyTy)
    (key : keyTy.Denote) (reads : List Cell) (after : Machine)
    (found : declarations[slot]? = some declaration)
    (named : declaration.name = name)
    (kind : declaration.kind = .map keyTy valueTy)
    (encoded : encodeState declarations state = some items)
    (keyEval : keyExpr.eval ctx env = .ok key)
    (canonical : ScalarNormalization.Canonical keyTy key)
    (accepted : run (GenericStateVM.requireAbsentOps slot
      (NativeRelation.scalar (number keyTy key)))
      ⟨[.vector items], reads⟩ = some after) :
    SourceEffects.step ctx (.requireAbsent name keyTy keyExpr) (env, state) =
      .ok (env, state) ∧
    after = ⟨[.vector items], reads ++ [boolean false]⟩ := by
  exact GenericStateVM.requireAbsent_source_step ctx env (eraseSpans declarations)
    state items slot name keyTy valueTy keyExpr key reads after
    (erased_at_map declarations slot declaration name keyTy valueTy found named kind)
    (by rw [encodeState_eraseSpans]; exact encoded) keyEval canonical accepted

/-- The existing cell-write transition proof transfers across arbitrary
source locations without altering its source or native semantics. -/
theorem writeCell_source_step (ctx : EvalContext) (env : EvalEnv)
    (declarations : List StateDecl) (state : LedgerState)
    (items : List Slot) (slot : Nat) (declaration : StateDecl)
    (name : String) (ty : Ty) (expression : Expr ty)
    (value : ty.Denote) (reads : List Cell)
    (found : declarations[slot]? = some declaration)
    (named : declaration.name = name)
    (kind : declaration.kind = .cell ty)
    (distinct : declarations.Pairwise
      (fun left right => left.name ≠ right.name))
    (encoded : encodeState declarations state = some items)
    (slotBound : declarations.length < Field.modulus)
    (evaluated : expression.eval ctx env = .ok value)
    (canonical : ScalarNormalization.Canonical ty value) :
    ∃ next,
      SourceEffects.step ctx (.writeCell name ty expression) (env, state) =
        .ok (env, next) ∧
      encodeState declarations next =
        some (items.set slot (.cell (field
          (NativeRelation.scalar (number ty value))))) ∧
      run (GenericStateVM.writeCellOps slot
        (field (NativeRelation.scalar (number ty value))))
        ⟨[.vector items], reads⟩ =
        some ⟨[.vector (items.set slot (.cell (field
          (NativeRelation.scalar (number ty value)))))], reads⟩ := by
  have alignment := encoded_cell_alignment_none declarations state items slot
    declaration ty found kind encoded
  obtain ⟨next, source, successor, native⟩ :=
    GenericStateVM.writeCell_source_step ctx env (eraseSpans declarations)
      state items slot name ty expression value reads
      (erased_at_cell declarations slot declaration name ty found named kind alignment)
      (eraseSpans_distinct declarations distinct)
      (by rw [encodeState_eraseSpans]; exact encoded)
      (by simpa [eraseSpans_length] using slotBound) evaluated canonical
  exact ⟨next, source, by simpa only [encodeState_eraseSpans] using successor,
    native⟩

/-- The existing map-write transition proof transfers across arbitrary
declaration source locations. -/
theorem writeMap_source_step (ctx : EvalContext) (env : EvalEnv)
    (declarations : List StateDecl) (state : LedgerState)
    (items : List Slot) (slot : Nat) (declaration : StateDecl)
    (name : String) (keyTy valueTy : Ty)
    (keyExpr : Expr keyTy) (valueExpr : Expr valueTy)
    (key : keyTy.Denote) (value : valueTy.Denote) (reads : List Cell)
    (found : declarations[slot]? = some declaration)
    (named : declaration.name = name)
    (kind : declaration.kind = .map keyTy valueTy)
    (distinct : declarations.Pairwise
      (fun left right => left.name ≠ right.name))
    (encoded : encodeState declarations state = some items)
    (slotBound : declarations.length < Field.modulus)
    (keyEval : keyExpr.eval ctx env = .ok key)
    (valueEval : valueExpr.eval ctx env = .ok value)
    (keyCanonical : ScalarNormalization.Canonical keyTy key)
    (valueCanonical : ScalarNormalization.Canonical valueTy value) :
    ∃ (next : LedgerState)
      (encodedEntries : List (NativeRelation.Scalar × NativeRelation.Scalar)),
      SourceEffects.step ctx (.writeMap name keyTy valueTy keyExpr valueExpr)
        (env, state) = .ok (env, next) ∧
      encodeState declarations next =
        some (items.set slot (.map
          ((NativeRelation.scalar (number keyTy key),
            NativeRelation.scalar (number valueTy value)) ::
          encodedEntries.filter (fun pair => pair.1 !=
            NativeRelation.scalar (number keyTy key))))) ∧
      run (GenericStateVM.writeMapOps slot
        (NativeRelation.scalar (number keyTy key))
        (NativeRelation.scalar (number valueTy value)))
        ⟨[.vector items], reads⟩ =
        some ⟨[.vector (items.set slot (.map
          ((NativeRelation.scalar (number keyTy key),
            NativeRelation.scalar (number valueTy value)) ::
          encodedEntries.filter (fun pair => pair.1 !=
            NativeRelation.scalar (number keyTy key)))))], reads⟩ := by
  obtain ⟨next, entries, source, successor, native⟩ :=
    GenericStateVM.writeMap_source_step ctx env (eraseSpans declarations)
      state items slot name keyTy valueTy keyExpr valueExpr key value reads
      (erased_at_map declarations slot declaration name keyTy valueTy found named kind)
      (eraseSpans_distinct declarations distinct)
      (by rw [encodeState_eraseSpans]; exact encoded)
      (by simpa [eraseSpans_length] using slotBound)
      keyEval valueEval keyCanonical valueCanonical
  exact ⟨next, entries, source,
    by simpa only [encodeState_eraseSpans] using successor, native⟩

end Noctium.Verification.GenericStateSchemaSpans
