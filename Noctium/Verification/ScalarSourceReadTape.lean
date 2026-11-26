import Noctium.Verification.GuardedSourceEffects
import Noctium.Verification.ImpactTypedEnvironment
import Noctium.Verification.GenericStateEncoding
import Noctium.Verification.ScalarCellSourceReads

namespace Noctium.Verification.ScalarSourceReadTape

open Backend NativeRelation ScalarNormalization

private def checkedScalarValue (ty : Ty) (raw : Option Value) :
    Except String NativeRelation.Scalar :=
  match raw with
  | none => .error "missing scalar source read value"
  | some raw =>
    match raw.as ty with
    | none => .error "mismatched scalar source read value"
    | some value =>
      if (ImpactTypedEnvironment.packedCanonical? ty raw).isSome then
        .ok (NativeRelation.scalar (GenericStateEncoding.number ty value))
      else .error "noncanonical scalar source read value"

private theorem packedCanonical_sound {ty : Ty} {raw : Value}
    (accepted : (ImpactTypedEnvironment.packedCanonical? ty raw).isSome = true) :
    ∃ value : ty.Denote,
      raw = Value.pack ty value ∧ Canonical ty value := by
  cases result : ImpactTypedEnvironment.packedCanonical? ty raw with
  | none => simp [result] at accepted
  | some packed =>
    simp [result] at accepted
    rcases packed with ⟨value, evidence⟩
    rcases evidence with ⟨packedValue, canonical⟩
    exact ⟨value, packedValue, canonical⟩

private theorem checkedScalarValue_sound {ty : Ty} {raw : Option Value}
    {scalarValue : NativeRelation.Scalar}
    (success : checkedScalarValue ty raw = .ok scalarValue) :
    ∃ value : ty.Denote,
      raw = some (Value.pack ty value) ∧ Canonical ty value ∧
      scalarValue = NativeRelation.scalar (GenericStateEncoding.number ty value) := by
  cases raw with
  | none => simp [checkedScalarValue] at success
  | some raw =>
    cases typed : raw.as ty with
    | none => simp [checkedScalarValue, typed] at success
    | some value =>
      cases accepted : (ImpactTypedEnvironment.packedCanonical? ty raw).isSome with
      | false => simp [checkedScalarValue, typed, accepted] at success
      | true =>
        simp only [checkedScalarValue, typed, accepted, ite_true,
          Except.ok.injEq] at success
        cases success
        obtain ⟨canonicalValue, packedRaw, canonical⟩ := packedCanonical_sound accepted
        have packedAs : (Value.pack ty canonicalValue).as ty = some value := by
          rw [← packedRaw]
          exact typed
        have sameValue : canonicalValue = value := by
          rw [ScalarNormalization.number_pack_as ty canonicalValue canonical] at packedAs
          exact Option.some.inj packedAs
        subst value
        exact ⟨canonicalValue, by simpa using packedRaw, canonical, rfl⟩

/-- Read inputs recorded from the frame produced by one guarded source step.
Cell and map values must have the declared scalar type and be canonical.
Absence reads are accepted only without a guard. -/
private def effectEntries (guard : Option (Expr .bool)) (effect : Effect)
    (ordinal : Nat) (after : SourceEffects.Frame) :
    Except String (List (Impact.Read × NativeRelation.Scalar)) :=
  match effect with
  | .readCell _ destination ty =>
    match checkedScalarValue ty (after.1.lookup destination) with
    | .error message => .error message
    | .ok value => .ok [({name := destination, ty}, value)]
  | .readMap _ destination _ ty _ =>
    match checkedScalarValue ty (after.1.lookup destination) with
    | .error message => .error message
    | .ok value => .ok [({name := destination, ty}, value)]
  | .requireAbsent _ _ _ =>
    match guard with
    | none => .ok [({name := "_noctium_absence_" ++ toString ordinal, ty := .bool}, zero)]
    | some _ => .error "guarded requireAbsent is not supported by the scalar source read tape"
  | .require _ | .writeCell .. | .writeMap .. => .ok []
  | _ => .error "unsupported effect in the scalar source read tape"

private theorem effectEntries_properties (guard : Option (Expr .bool))
    (effect : Effect) (ordinal : Nat) (after : SourceEffects.Frame)
    (entries : List (Impact.Read × NativeRelation.Scalar))
    (success : effectEntries guard effect ordinal after = .ok entries) :
    ((entries.map Prod.fst).map GenericStateCheckedReadTrace.readMetadata =
      GenericStateCheckedReadTrace.effectReadChunk effect ordinal) ∧
    (∀ record ∈ entries, ScalarCellSourceReads.CanonicalReadRecord record) := by
  cases effect with
  | readCell name destination ty =>
    cases checked : checkedScalarValue ty (after.1.lookup destination) with
    | error message => simp [effectEntries, checked] at success
    | ok value =>
      simp only [effectEntries, checked, Except.ok.injEq] at success
      cases success
      have checkedCanonical := checkedScalarValue_sound checked
      constructor
      · simp [GenericStateCheckedReadTrace.effectReadChunk,
          GenericStateCheckedReadTrace.readMetadata]
      · intro record member
        simp only [List.mem_singleton] at member
        subst record
        obtain ⟨typedValue, _, canonical, scalarValue⟩ := checkedCanonical
        exact ⟨typedValue, canonical, scalarValue⟩
  | readMap name destination keyTy valueTy key =>
    cases checked : checkedScalarValue valueTy (after.1.lookup destination) with
    | error message => simp [effectEntries, checked] at success
    | ok value =>
      simp only [effectEntries, checked, Except.ok.injEq] at success
      cases success
      have checkedCanonical := checkedScalarValue_sound checked
      constructor
      · simp [GenericStateCheckedReadTrace.effectReadChunk,
          GenericStateCheckedReadTrace.readMetadata]
      · intro record member
        simp only [List.mem_singleton] at member
        subst record
        obtain ⟨typedValue, _, canonical, scalarValue⟩ := checkedCanonical
        exact ⟨typedValue, canonical, scalarValue⟩
  | requireAbsent name keyTy key =>
    cases guard with
    | none =>
      simp only [effectEntries, Except.ok.injEq] at success
      cases success
      constructor
      · simp [GenericStateCheckedReadTrace.effectReadChunk,
          GenericStateCheckedReadTrace.readMetadata]
      · intro record member
        simp only [List.mem_singleton] at member
        subst record
        refine ⟨false, ?_, ?_⟩
        · change ScalarNormalization.Canonical .bool false
          change 0 < Field.modulus ∧ True
          exact ⟨Nat.lt_of_le_of_lt (Nat.zero_le ScalarPolicy.maxUint)
            ScalarPolicy.maxUint_lt_native, trivial⟩
        · simp [NativeRelation.zero, NativeRelation.scalar, GenericStateEncoding.number]
    | some condition => simp [effectEntries] at success
  | require condition =>
    simp [effectEntries] at success
    subst entries
    constructor
    · rfl
    · intro record member
      simp at member
  | writeCell name ty value =>
    simp [effectEntries] at success
    subst entries
    constructor
    · rfl
    · intro record member
      simp at member
  | writeMap name keyTy valueTy key value =>
    simp [effectEntries] at success
    subst entries
    constructor
    · rfl
    · intro record member
      simp at member
  | _ => simp [effectEntries] at success

/-- Run each indexed singleton source step before recording its read values.
The guard lookup matches the production guarded fold, including out-of-range
indices. -/
def sourceReadInputs (ctx : EvalContext) (guards : List (Option (Expr .bool))) :
    List (Effect × Nat) → Nat → SourceEffects.Frame →
      Except String (List (Impact.Read × NativeRelation.Scalar) × SourceEffects.Frame)
  | [], _, frame => .ok ([], frame)
  | item :: rest, ordinal, before => do
      let guard := guards[item.2]?.getD none
      let middle ← GuardedSourceEffects.step ctx guard item.1 before
      let head ← effectEntries guard item.1 ordinal middle
      let (tail, final) ← sourceReadInputs ctx guards rest (ordinal + head.length) middle
      pure (head ++ tail, final)

private theorem sourceReadInputs_cons (ctx : EvalContext)
    (guards : List (Option (Expr .bool))) (item : Effect × Nat)
    (rest : List (Effect × Nat)) (ordinal : Nat) (before after : SourceEffects.Frame)
    (entries : List (Impact.Read × NativeRelation.Scalar))
    (success : sourceReadInputs ctx guards (item :: rest) ordinal before =
      .ok (entries, after)) :
    ∃ middle head tail,
      GuardedSourceEffects.step ctx (guards[item.2]?.getD none) item.1 before = .ok middle ∧
      effectEntries (guards[item.2]?.getD none) item.1 ordinal middle = .ok head ∧
      sourceReadInputs ctx guards rest (ordinal + head.length) middle = .ok (tail, after) ∧
      entries = head ++ tail := by
  cases first : GuardedSourceEffects.step ctx (guards[item.2]?.getD none) item.1 before with
  | error message => simp [sourceReadInputs, first, bind, Except.bind] at success
  | ok middle =>
    cases recorded : effectEntries (guards[item.2]?.getD none) item.1 ordinal middle with
    | error message => simp [sourceReadInputs, first, recorded, bind, Except.bind] at success
    | ok head =>
      cases later : sourceReadInputs ctx guards rest (ordinal + head.length) middle with
      | error message => simp [sourceReadInputs, first, recorded, later, bind, Except.bind] at success
      | ok pair =>
        rcases pair with ⟨tail, final⟩
        simp only [sourceReadInputs, first, recorded, later, bind, Except.bind,
          Pure.pure, Except.pure] at success
        cases success
        exact ⟨middle, head, tail, rfl, recorded, later, rfl⟩

/-- Successful scalar source recording follows the guarded source fold,
matches the compiler's generated read metadata and retains canonical typed
values for every record. -/
theorem sourceReadInputs_sound (ctx : EvalContext)
    (guards : List (Option (Expr .bool))) (items : List (Effect × Nat))
    (ordinal : Nat) (initial final : SourceEffects.Frame)
    (entries : List (Impact.Read × NativeRelation.Scalar))
    (success : sourceReadInputs ctx guards items ordinal initial = .ok (entries, final)) :
    GuardedSourceEffects.fold ctx guards items initial = .ok final ∧
      (entries.map Prod.fst).map GenericStateCheckedReadTrace.readMetadata =
        (GenericStateCheckedReadTrace.readChunks (items.map Prod.fst) ordinal).flatten ∧
      (∀ record ∈ entries, ScalarCellSourceReads.CanonicalReadRecord record) := by
  induction items generalizing ordinal initial final entries with
  | nil =>
    simp only [sourceReadInputs] at success
    cases success
    constructor
    · rfl
    constructor
    · rfl
    · intro record member
      simp at member
  | cons item rest ih =>
    obtain ⟨middle, head, tail, first, recorded, later, entriesShape⟩ :=
      sourceReadInputs_cons ctx guards item rest ordinal initial final entries success
    obtain ⟨foldLater, metadataLater, canonicalLater⟩ :=
      ih (ordinal + head.length) middle final tail later
    have ⟨headMetadata, headCanonical⟩ := effectEntries_properties
      (guards[item.2]?.getD none) item.1 ordinal middle head recorded
    have headLength : head.length =
        (GenericStateCheckedReadTrace.effectReadChunk item.1 ordinal).length := by
      have lengthEquality := congrArg List.length headMetadata
      simpa only [List.length_map] using lengthEquality
    constructor
    · rw [GuardedSourceEffects.fold_cons, first]
      exact foldLater
    constructor
    · simp only [entriesShape, List.map_append]
      rw [headMetadata, metadataLater, headLength]
      rfl
    · intro record member
      rw [entriesShape] at member
      rcases List.mem_append.mp member with headMember | tailMember
      · exact headCanonical record headMember
      · exact canonicalLater record tailMember

end Noctium.Verification.ScalarSourceReadTape
