import Noctium.Verification.GenericStateInputValues

namespace Noctium.Verification.ScalarWitnessConstruction

open Backend NativeRelation ScalarNormalization GenericStateInputValues

theorem round_trip_scalar_read {ty : Ty} (scalarType : ScalarType ty)
    (value : ty.Denote) (canonical : Canonical ty value) :
    sourceValue scalarType (scalar (number scalarType value)) = value := by
  have encoded := scalar_no_wrap _ (scalar_number_canonical scalarType value canonical)
  cases scalarType with
  | native => exact encoded
  | bool =>
    change ((scalar (number .bool value)).val == 1) = value
    rw [encoded]
    cases value <;> rfl
  | uint maximum => exact encoded

/-- The decoded read environment contains the canonical source values in
production read order. Each value keeps its lowered descriptor and seed. -/
theorem decode_seeded_scalar_reads (reads : List Impact.Read) (inputs : Assignment)
    (facts : ∀ read ∈ reads, ∃ (value : read.ty.Denote) (scalarType : ScalarType read.ty),
      Canonical read.ty value ∧ inputs ("%input_" ++ read.name) = scalar (number scalarType value)) :
    ∃ readValues, decodeReads reads inputs = .ok readValues ∧
      ∀ pair ∈ readValues, ∃ read ∈ reads, ∃ value : read.ty.Denote,
        pair = (read.name, Value.pack read.ty value) ∧ Canonical read.ty value ∧
          sourceScalar? read.ty value = some (inputs ("%input_" ++ read.name)) := by
  induction reads with
  | nil => exact ⟨[], rfl, by simp⟩
  | cons read rest ih =>
    obtain ⟨value, scalarType, canonical, seeded⟩ := facts read (by simp)
    have first : decodeRead read inputs = .ok (read.name, Value.pack read.ty value) := by
      simp only [decodeRead, scalarType?_supported scalarType, seeded,
        round_trip_scalar_read scalarType value canonical]
    obtain ⟨tail, tailDecoded, tailFacts⟩ :=
      ih (fun item member => facts item (List.mem_cons_of_mem _ member))
    refine ⟨(read.name, Value.pack read.ty value) :: tail, ?_, ?_⟩
    · change ((read :: rest).mapM (fun item => decodeRead item inputs)) = _
      rw [List.mapM_cons, first, show rest.mapM (fun item => decodeRead item inputs) = .ok tail from tailDecoded]
      rfl
    · intro pair member
      rcases List.mem_cons.mp member with rfl | member
      · exact ⟨read, by simp, value, rfl, canonical,
          (sourceScalar_number scalarType value).trans (congrArg some seeded.symm)⟩
      · obtain ⟨item, present, result, equal, bounded, relation⟩ := tailFacts pair member
        exact ⟨item, List.mem_cons_of_mem _ present, result, equal, bounded, relation⟩

/-- Extend source alias meaning with canonical read bindings. Earlier
source bindings keep first-match precedence. -/
theorem AliasAgreement.appendCanonicalReadValues (hash : Hash) (inputs : Assignment)
    (normalAliases : Native.AliasEnvironment) (values readValues : EvalEnv)
    (agreement : AliasAgreement hash inputs normalAliases values)
    (reads : ∀ pair ∈ readValues, ∃ (ty : Ty) (value : ty.Denote),
      pair.2 = Value.pack ty value ∧ Canonical ty value ∧
        normalAliases.lookup pair.1 = some (.input ("%input_" ++ pair.1)) ∧
        sourceScalar? ty value = some (inputs ("%input_" ++ pair.1))) :
    AliasAgreement hash inputs normalAliases (values ++ readValues) := by
  intro name ty raw value lookup typed
  rw [List.lookup_append] at lookup
  cases found : values.lookup name with
  | some first =>
    simp only [found, Option.some_or] at lookup
    exact agreement name ty raw value (found.trans lookup) typed
  | none =>
    simp only [found, Option.none_or] at lookup
    obtain ⟨before, after, eq, _⟩ := List.lookup_eq_some_iff.mp lookup
    have member : (name, raw) ∈ readValues := by rw [eq]; simp
    obtain ⟨sourceType, sourceValue, packed, canonical, normalized, scalarValue⟩ := reads (name, raw) member
    rw [show raw = Value.pack sourceType sourceValue from packed] at typed
    obtain ⟨bounded, related⟩ :=
      GenericStateAliases.packed_as_canonical sourceType ty sourceValue value canonical typed
    exact ⟨bounded, .input ("%input_" ++ name), normalized,
      by rw [interpret_input, related, scalarValue]⟩

end Noctium.Verification.ScalarWitnessConstruction
