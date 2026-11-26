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

private theorem checkedScalarValue_complete {ty : Ty} {value : ty.Denote}
    (canonical : Canonical ty value) :
    checkedScalarValue ty (some (Value.pack ty value)) =
      .ok (NativeRelation.scalar (GenericStateEncoding.number ty value)) := by
  have typed : (Value.pack ty value).as ty = some value :=
    ScalarNormalization.number_pack_as ty value canonical
  have packed : (ImpactTypedEnvironment.packedCanonical? ty
      (Value.pack ty value)).isSome = true := by
    have scalarType : ScalarNormalization.ScalarType ty := by
      cases ty with
      | native => exact .native
      | bool => exact .bool
      | uint maximum => exact .uint maximum
      | bytes length => simp [ScalarNormalization.Canonical,
          ScalarNormalization.sourceNumber?] at canonical
      | opaqueBytes => simp [ScalarNormalization.Canonical,
          ScalarNormalization.sourceNumber?] at canonical
      | opaqueString => simp [ScalarNormalization.Canonical,
          ScalarNormalization.sourceNumber?] at canonical
      | jubjubScalar => simp [ScalarNormalization.Canonical,
          ScalarNormalization.sourceNumber?] at canonical
      | jubjubPoint => simp [ScalarNormalization.Canonical,
          ScalarNormalization.sourceNumber?] at canonical
      | foreign kind => simp [ScalarNormalization.Canonical,
          ScalarNormalization.sourceNumber?] at canonical
    cases scalarType with
    | native =>
      have valueBound : value < Field.modulus := by
        simpa [ScalarNormalization.Canonical,
          ScalarNormalization.sourceNumber?] using canonical
      simp [ImpactTypedEnvironment.packedCanonical?, Value.pack, valueBound]
    | bool => simp [ImpactTypedEnvironment.packedCanonical?, Value.pack]
    | uint maximum =>
      have bounds : value < Field.modulus ∧
          maximum ≤ ScalarPolicy.maxUint ∧ value ≤ maximum := by
        simpa [ScalarNormalization.Canonical,
          ScalarNormalization.sourceNumber?] using canonical
      simp [ImpactTypedEnvironment.packedCanonical?, Value.pack, bounds.1,
        bounds.2.1, bounds.2.2]
  simp [checkedScalarValue, typed, packed]

/-- A read's value evidence is attached to the destination in the frame
reached after that guarded source step. Non-read effects need no value claim. -/
def CanonicalReadAt (effect : Effect) (after : SourceEffects.Frame) : Prop :=
  match effect with
  | .readCell _ destination ty | .readMap _ destination _ ty _ =>
    ∃ value : ty.Denote,
      after.1.lookup destination = some (Value.pack ty value) ∧ Canonical ty value
  | _ => True

/-- Canonical-value evidence along the actual successful guarded steps. An
error contributes no later frame; fold success is supplied independently to
the completeness theorem. -/
def sourceReadValuesCanonical (ctx : EvalContext)
    (guards : List (Option (Expr .bool))) :
    List (Effect × Nat) → SourceEffects.Frame → Prop
  | [], _ => True
  | item :: rest, before =>
    match GuardedSourceEffects.step ctx (guards[item.2]?.getD none) item.1 before with
    | .error _ => True
    | .ok middle =>
      CanonicalReadAt item.1 middle ∧
        sourceReadValuesCanonical ctx guards rest middle

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

private theorem effectEntries_complete (guard : Option (Expr .bool))
    (effect : Effect) (ordinal : Nat) (after : SourceEffects.Frame)
    (scope : GenericStateCheckedReadTrace.GuardedScalarReadEffect guard effect)
    (canonical : CanonicalReadAt effect after) :
    ∃ entries, effectEntries guard effect ordinal after = .ok entries := by
  cases scope with
  | unguarded scalarScope =>
    cases scalarScope with
    | readCell name destination ty =>
      obtain ⟨value, lookup, valueCanonical⟩ := canonical
      refine ⟨[({name := destination, ty},
        NativeRelation.scalar (GenericStateEncoding.number ty value))], ?_⟩
      simp [effectEntries, lookup, checkedScalarValue_complete valueCanonical]
    | readMap name destination keyTy valueTy key =>
      obtain ⟨value, lookup, valueCanonical⟩ := canonical
      refine ⟨[({name := destination, ty := valueTy},
        NativeRelation.scalar (GenericStateEncoding.number valueTy value))], ?_⟩
      simp [effectEntries, lookup, checkedScalarValue_complete valueCanonical]
    | requireAbsent name keyTy key =>
      let read : Impact.Read :=
        {name := "_noctium_absence_" ++ toString ordinal, ty := .bool}
      refine ⟨[(read, NativeRelation.zero)], ?_⟩
      simp [effectEntries, read]
    | require condition => exact ⟨[], by simp [effectEntries]⟩
    | writeCell name ty value => exact ⟨[], by simp [effectEntries]⟩
    | writeMap name keyTy valueTy key value => exact ⟨[], by simp [effectEntries]⟩
  | require condition => exact ⟨[], by simp [effectEntries]⟩
  | readCell condition name destination ty =>
    obtain ⟨value, lookup, valueCanonical⟩ := canonical
    refine ⟨[({name := destination, ty},
      NativeRelation.scalar (GenericStateEncoding.number ty value))], ?_⟩
    simp [effectEntries, lookup, checkedScalarValue_complete valueCanonical]
  | readMap condition name destination keyTy valueTy key =>
    obtain ⟨value, lookup, valueCanonical⟩ := canonical
    refine ⟨[({name := destination, ty := valueTy},
      NativeRelation.scalar (GenericStateEncoding.number valueTy value))], ?_⟩
    simp [effectEntries, lookup, checkedScalarValue_complete valueCanonical]
  | writeCell condition name ty value => exact ⟨[], by simp [effectEntries]⟩
  | writeMap condition name keyTy valueTy key value => exact ⟨[], by simp [effectEntries]⟩

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

/-- Exact value recorded for a scalar cell or map read. The value comes from
the destination in the frame after the guarded source step. Other effects do
not produce a scalar value claim. -/
def SourceReadHeadValue (effect : Effect) (after : SourceEffects.Frame)
    (head : List (Impact.Read × NativeRelation.Scalar)) : Prop :=
  match effect with
  | .readCell _ destination ty =>
    ∃ value : ty.Denote,
      after.1.lookup destination = some (Value.pack ty value) ∧
      Canonical ty value ∧ CanonicalReadAt effect after ∧
      head = [({name := destination, ty},
        NativeRelation.scalar (GenericStateEncoding.number ty value))]
  | .readMap _ destination _ ty _ =>
    ∃ value : ty.Denote,
      after.1.lookup destination = some (Value.pack ty value) ∧
      Canonical ty value ∧ CanonicalReadAt effect after ∧
      head = [({name := destination, ty},
        NativeRelation.scalar (GenericStateEncoding.number ty value))]
  | _ => True

private theorem effectEntries_sourceReadHeadValue (guard : Option (Expr .bool))
    (effect : Effect) (ordinal : Nat) (after : SourceEffects.Frame)
    (head : List (Impact.Read × NativeRelation.Scalar))
    (success : effectEntries guard effect ordinal after = .ok head) :
    SourceReadHeadValue effect after head := by
  cases effect with
  | readCell name destination ty =>
    cases checked : checkedScalarValue ty (after.1.lookup destination) with
    | error message => simp [effectEntries, checked] at success
    | ok scalarValue =>
      simp only [effectEntries, checked, Except.ok.injEq] at success
      cases success
      obtain ⟨value, lookup, canonical, recordedScalar⟩ :=
        checkedScalarValue_sound checked
      refine ⟨value, lookup, canonical, ⟨value, lookup, canonical⟩, ?_⟩
      simp [recordedScalar]
  | readMap name destination keyTy valueTy key =>
    cases checked : checkedScalarValue valueTy (after.1.lookup destination) with
    | error message => simp [effectEntries, checked] at success
    | ok scalarValue =>
      simp only [effectEntries, checked, Except.ok.injEq] at success
      cases success
      obtain ⟨value, lookup, canonical, recordedScalar⟩ :=
        checkedScalarValue_sound checked
      refine ⟨value, lookup, canonical, ⟨value, lookup, canonical⟩, ?_⟩
      simp [recordedScalar]
  | _ => simp [SourceReadHeadValue]

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

/-- Completeness for one reached guarded step. Scalar cell and map reads need
their canonical destination value. Requirements and writes need no value
evidence. Absence recording is available only through the unguarded scope
constructor. -/
theorem sourceReadInputs_step_complete (ctx : EvalContext)
    (guards : List (Option (Expr .bool))) (effect : Effect) (index ordinal : Nat)
    (before after : SourceEffects.Frame)
    (scope : GenericStateCheckedReadTrace.GuardedScalarReadEffect
      (guards[index]?.getD none) effect)
    (stepSuccess : GuardedSourceEffects.step ctx (guards[index]?.getD none)
      effect before = .ok after)
    (canonical : CanonicalReadAt effect after) :
    ∃ entries,
      sourceReadInputs ctx guards [(effect, index)] ordinal before =
        .ok (entries, after) := by
  obtain ⟨entries, recorded⟩ := effectEntries_complete
    (guards[index]?.getD none) effect ordinal after scope canonical
  refine ⟨entries, ?_⟩
  simp only [sourceReadInputs, stepSuccess, recorded, bind, Except.bind,
    Pure.pure, Except.pure, List.append_nil]

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

/-- Invert one successful recorder cons. The returned successor ordinal is
the exact ordinal used for the tail fold. For cell and map reads, the head
record names the canonical packed value at the destination in the frame
returned by the successful guarded step. -/
theorem sourceReadInputs_cons_inversion (ctx : EvalContext)
    (guards : List (Option (Expr .bool))) (item : Effect × Nat)
    (rest : List (Effect × Nat)) (ordinal : Nat) (before after : SourceEffects.Frame)
    (entries : List (Impact.Read × NativeRelation.Scalar))
    (success : sourceReadInputs ctx guards (item :: rest) ordinal before =
      .ok (entries, after)) :
    ∃ middle head tail nextOrdinal,
      GuardedSourceEffects.step ctx (guards[item.2]?.getD none) item.1 before =
        .ok middle ∧
      nextOrdinal = ordinal + head.length ∧
      sourceReadInputs ctx guards rest nextOrdinal middle = .ok (tail, after) ∧
      entries = head ++ tail ∧
      (head.map Prod.fst).map GenericStateCheckedReadTrace.readMetadata =
        GenericStateCheckedReadTrace.effectReadChunk item.1 ordinal ∧
      (∀ record ∈ head, ScalarCellSourceReads.CanonicalReadRecord record) ∧
      SourceReadHeadValue item.1 middle head := by
  obtain ⟨middle, head, tail, first, recorded, later, entriesShape⟩ :=
    sourceReadInputs_cons ctx guards item rest ordinal before after entries success
  have ⟨headMetadata, headCanonical⟩ := effectEntries_properties
    (guards[item.2]?.getD none) item.1 ordinal middle head recorded
  have headValue := effectEntries_sourceReadHeadValue
    (guards[item.2]?.getD none) item.1 ordinal middle head recorded
  refine ⟨middle, head, tail, ordinal + head.length, first, rfl, ?_,
    entriesShape, headMetadata, headCanonical, headValue⟩
  simpa using later

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

/-- A successful supported guarded fold has a successful scalar source-read
tape when every reached read destination contains a typed canonical value.
The fold result and per-frame value evidence remain separate premises. -/
theorem sourceReadInputs_complete (ctx : EvalContext)
    (guards : List (Option (Expr .bool))) (items : List (Effect × Nat))
    (ordinal : Nat) (initial final : SourceEffects.Frame)
    (scope : GenericStateCheckedReadTrace.GuardedScalarReadEffects guards items)
    (foldSuccess : GuardedSourceEffects.fold ctx guards items initial = .ok final)
    (canonical : sourceReadValuesCanonical ctx guards items initial) :
    ∃ entries,
      sourceReadInputs ctx guards items ordinal initial = .ok (entries, final) ∧
      (entries.map Prod.fst).map GenericStateCheckedReadTrace.readMetadata =
        (GenericStateCheckedReadTrace.readChunks (items.map Prod.fst) ordinal).flatten ∧
      (∀ record ∈ entries, ScalarCellSourceReads.CanonicalReadRecord record) := by
  induction items generalizing ordinal initial final with
  | nil =>
    simp only [GuardedSourceEffects.fold_nil] at foldSuccess
    cases foldSuccess
    simp only [sourceReadInputs]
    refine ⟨[], rfl, ?_, ?_⟩
    · rfl
    · intro record member
      simp at member
  | cons item rest ih =>
    have scopeHead :
        GenericStateCheckedReadTrace.GuardedScalarReadEffect
          (guards[item.2]?.getD none) item.1 :=
      scope item (by simp)
    have scopeTail :
        GenericStateCheckedReadTrace.GuardedScalarReadEffects guards rest := by
      intro next member
      exact scope next (by simp [member])
    rw [GuardedSourceEffects.fold_cons] at foldSuccess
    cases first : GuardedSourceEffects.step ctx
        (guards[item.2]?.getD none) item.1 initial with
    | error message =>
      simp only [first, Except.bind] at foldSuccess
      cases foldSuccess
    | ok middle =>
      simp only [first, Except.bind] at foldSuccess
      have canonicalAtMiddle : CanonicalReadAt item.1 middle := by
        simp [sourceReadValuesCanonical, first] at canonical
        exact canonical.1
      have canonicalLater :
          sourceReadValuesCanonical ctx guards rest middle := by
        have evidence := canonical
        simp [sourceReadValuesCanonical, first] at evidence
        exact evidence.2
      obtain ⟨head, headSuccess⟩ := effectEntries_complete
        (guards[item.2]?.getD none) item.1 ordinal middle scopeHead canonicalAtMiddle
      obtain ⟨tail, tailSuccess, _, _⟩ := ih (ordinal := ordinal + head.length)
        (initial := middle) (final := final) scopeTail foldSuccess canonicalLater
      have recordSuccess :
          sourceReadInputs ctx guards (item :: rest) ordinal initial =
            .ok (head ++ tail, final) := by
        simp only [sourceReadInputs, first, headSuccess, tailSuccess, bind,
          Except.bind, Pure.pure, Except.pure]
      obtain ⟨_, metadata, canonicalRecords⟩ := sourceReadInputs_sound
        ctx guards (item :: rest) ordinal initial final (head ++ tail) recordSuccess
      exact ⟨head ++ tail, recordSuccess, metadata, canonicalRecords⟩

end Noctium.Verification.ScalarSourceReadTape
