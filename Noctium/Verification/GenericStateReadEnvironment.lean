import Noctium.Verification.GenericStateInputValues

namespace Noctium.Verification.GenericStateReadEnvironment
open NativeRelation ScalarNormalization Backend.Native
open GenericStateInputValues GenericStateAliases

private theorem lookup_snoc_none (items : List (String × α))
    (name fresh : String) (value : α)
    (absent : items.lookup name = none) (different : name ≠ fresh) :
    (items ++ [(fresh, value)]).lookup name = none := by
  have unequal : (name == fresh) = false := by simp [different]
  simp only [List.lookup_append, absent, List.lookup_cons, unequal,
    List.lookup_nil, Option.none_or]

/-- Add one candidate read value when the exact production alias already
exists. Freshness concerns source values and types, since Impact includes all
read aliases before normalizing ledger expressions. -/
theorem typedEnvironment_snoc_existing (hash : Hash) (witness : Assignment)
    (aliases : AliasEnvironment) (values : EvalEnv) (types : TypeEnv)
    (name : String) (ty : Ty) (value : ty.Denote) (term : Term)
    (environment : TypedEnvironment hash witness aliases values types)
    (freshValue : values.lookup name = none)
    (freshType : types.lookup name = none)
    (alias : aliases.lookup name = some term)
    (canonical : Canonical ty value)
    (meaning : interpret hash witness term = sourceScalar? ty value) :
    TypedEnvironment hash witness aliases
      (values ++ [(name, Value.pack ty value)])
      (types ++ [(name, ty)]) := by
  constructor
  · intro found foundTy raw result lookup typed
    by_cases same : found = name
    · subst found
      simp [List.lookup_append, freshValue] at lookup
      cases lookup
      obtain ⟨foundCanonical, sourceMeaning⟩ :=
        packed_as_canonical ty foundTy value result canonical typed
      exact ⟨foundCanonical, term, alias, meaning.trans sourceMeaning.symm⟩
    · have unequal : (found == name) = false := by simp [same]
      simp only [List.lookup_append, List.lookup_cons, unequal,
        List.lookup_nil, Option.or_none] at lookup
      obtain ⟨oldCanonical, oldTerm, oldLookup, oldMeaning⟩ :=
        environment.aliases found foundTy raw result lookup typed
      exact ⟨oldCanonical, oldTerm, oldLookup, oldMeaning⟩
  · intro found foundTy lookup
    by_cases same : found = name
    · subst found
      simp [List.lookup_append, freshType] at lookup
      cases lookup
      exact ⟨Value.pack ty value, value,
        by simp [List.lookup_append, freshValue], number_pack_as ty value canonical⟩
    · have unequal : (found == name) = false := by simp [same]
      simp only [List.lookup_append, List.lookup_cons, unequal,
        List.lookup_nil, Option.or_none] at lookup
      obtain ⟨raw, result, oldLookup, typed⟩ :=
        environment.complete found foundTy lookup
      exact ⟨raw, result, by simp [List.lookup_append, oldLookup], typed⟩

/-- Candidate read values extend a typed alias environment in production
input order. Freshness concerns only declared names, not a desired read or
source transition result. Checked VM segments authenticate these candidates. -/
theorem appendDecodedReads (reads : List Backend.Impact.Read)
    (hash : Hash) (witness : Assignment)
    (aliases : AliasEnvironment) (values : EvalEnv) (types : TypeEnv)
    (environment : TypedEnvironment hash witness aliases values types)
    (decodedValues : EvalEnv)
    (decoded : decodeReads reads witness = .ok decodedValues)
    (fresh : ∀ read ∈ reads,
      aliases.lookup read.name = none ∧
      values.lookup read.name = none ∧
      types.lookup read.name = none)
    (distinct : reads.Pairwise (fun left right => left.name ≠ right.name))
    (typed : ∀ read ∈ reads,
      read.ty.validate {poseidon2 := true, stateCells := true, stateMaps := true} = .ok ())
    (bounded : ∀ read ∈ reads,
      (witness ("%input_" ++ read.name)).val ≤ sourceMaximum read.ty) :
    TypedEnvironment hash witness (aliases ++ readAliases reads)
      (values ++ decodedValues) (types ++ readTypes reads) := by
  induction reads generalizing aliases values types decodedValues with
  | nil =>
    simp [decodeReads] at decoded
    cases decoded
    simpa [readAliases, readTypes] using environment
  | cons read rest ih =>
    simp only [List.pairwise_cons] at distinct
    obtain ⟨first, tailValues, firstSuccess, tailSuccess, decodedShape⟩ :=
      decodeReads_cons_success read rest witness decodedValues decoded
    obtain ⟨supported, firstShape⟩ :=
      decodeRead_success read witness first firstSuccess
    cases firstShape
    have headFresh := fresh read (by simp)
    obtain ⟨canonical, meaning⟩ := sourceValue_canonical supported
      (witness ("%input_" ++ read.name))
      (typed read (by simp)) (bounded read (by simp))
    have next := typedEnvironment_snoc hash witness aliases values types
      read.name read.ty
      (sourceValue supported (witness ("%input_" ++ read.name)))
      (.input ("%input_" ++ read.name)) environment
      headFresh.1 headFresh.2.1 headFresh.2.2 canonical
      (by simpa only [interpret_input] using meaning.symm)
    have restFresh : ∀ item ∈ rest,
        (aliases ++ [(read.name, Term.input ("%input_" ++ read.name))]).lookup
          item.name = none ∧
        (values ++ [(read.name, Value.pack read.ty
          (sourceValue supported (witness ("%input_" ++ read.name))))]).lookup
          item.name = none ∧
        (types ++ [(read.name, read.ty)]).lookup item.name = none := by
      intro item member
      have base := fresh item (by simp [member])
      have different : item.name ≠ read.name :=
        (distinct.1 item member).symm
      exact ⟨lookup_snoc_none aliases item.name read.name _ base.1 different,
        lookup_snoc_none values item.name read.name _ base.2.1 different,
        lookup_snoc_none types item.name read.name _ base.2.2 different⟩
    have restTyped : ∀ item ∈ rest,
        item.ty.validate {poseidon2 := true, stateCells := true, stateMaps := true} = .ok () := by
      intro item member
      exact typed item (by simp [member])
    have restBounded : ∀ item ∈ rest,
        (witness ("%input_" ++ item.name)).val ≤ sourceMaximum item.ty := by
      intro item member
      exact bounded item (by simp [member])
    have later := ih _ _ _ next tailValues tailSuccess restFresh distinct.2
      restTyped restBounded
    rw [decodedShape]
    simpa [readAliases, readTypes, List.append_assoc] using later

/-- Production read aliases are present before the output fold. Extend only
the source value and type environments with bounded, typed candidates. -/
theorem appendDecodedReads_existing (reads : List Backend.Impact.Read)
    (hash : Hash) (witness : Assignment)
    (aliases : AliasEnvironment) (values : EvalEnv) (types : TypeEnv)
    (environment : TypedEnvironment hash witness aliases values types)
    (decodedValues : EvalEnv)
    (decoded : decodeReads reads witness = .ok decodedValues)
    (fresh : ∀ read ∈ reads,
      values.lookup read.name = none ∧ types.lookup read.name = none)
    (distinct : reads.Pairwise (fun left right => left.name ≠ right.name))
    (existing : ∀ read ∈ reads,
      aliases.lookup read.name = some (.input ("%input_" ++ read.name)))
    (typed : ∀ read ∈ reads,
      read.ty.validate {poseidon2 := true, stateCells := true, stateMaps := true} = .ok ())
    (bounded : ∀ read ∈ reads,
      (witness ("%input_" ++ read.name)).val ≤ sourceMaximum read.ty) :
    TypedEnvironment hash witness aliases
      (values ++ decodedValues) (types ++ readTypes reads) := by
  induction reads generalizing values types decodedValues with
  | nil =>
    simp [decodeReads] at decoded
    cases decoded
    simpa [readTypes] using environment
  | cons read rest ih =>
    simp only [List.pairwise_cons] at distinct
    obtain ⟨first, tailValues, firstSuccess, tailSuccess, decodedShape⟩ :=
      decodeReads_cons_success read rest witness decodedValues decoded
    obtain ⟨supported, firstShape⟩ :=
      decodeRead_success read witness first firstSuccess
    cases firstShape
    have headFresh := fresh read (by simp)
    obtain ⟨canonical, meaning⟩ := sourceValue_canonical supported
      (witness ("%input_" ++ read.name))
      (typed read (by simp)) (bounded read (by simp))
    have next := typedEnvironment_snoc_existing hash witness aliases values types
      read.name read.ty
      (sourceValue supported (witness ("%input_" ++ read.name)))
      (.input ("%input_" ++ read.name)) environment
      headFresh.1 headFresh.2 (existing read (by simp)) canonical
      (by simpa only [interpret_input] using meaning.symm)
    have restFresh : ∀ item ∈ rest,
        (values ++ [(read.name, Value.pack read.ty
          (sourceValue supported (witness ("%input_" ++ read.name))))]).lookup
          item.name = none ∧
        (types ++ [(read.name, read.ty)]).lookup item.name = none := by
      intro item member
      have base := fresh item (by simp [member])
      have different : item.name ≠ read.name :=
        (distinct.1 item member).symm
      exact ⟨lookup_snoc_none values item.name read.name _ base.1 different,
        lookup_snoc_none types item.name read.name _ base.2 different⟩
    have later := ih _ _ next tailValues tailSuccess restFresh distinct.2
      (fun item member => existing item (by simp [member]))
      (fun item member => typed item (by simp [member]))
      (fun item member => bounded item (by simp [member]))
    rw [decodedShape]
    simpa [readTypes, List.append_assoc] using later

end Noctium.Verification.GenericStateReadEnvironment
