import Noctium.Verification.GenericStateReadEnvironment

namespace Noctium.Verification.GenericStateCandidateDecode

open Backend NativeRelation ScalarNormalization GenericStateInputValues
open GenericStateReadEnvironment

/-- Candidate relation inputs produce a checked source-value list only when
every production read type has an explicit scalar decoder. `mapM` preserves
the read order, and unsupported byte or foreign values remain outside this
boundary. -/
theorem decodeReads_supported_success (reads : List Backend.Impact.Read)
    (witness : Assignment)
    (supported : ∀ read ∈ reads, (scalarType? read.ty).isSome = true) :
    ∃ decodedValues, decodeReads reads witness = .ok decodedValues := by
  induction reads with
  | nil => exact ⟨[], rfl⟩
  | cons read rest ih =>
    have headSupported : (scalarType? read.ty).isSome = true := supported read (by simp)
    have tailSupported : ∀ item ∈ rest, (scalarType? item.ty).isSome = true := by
      intro item member
      exact supported item (by simp [member])
    obtain ⟨first, firstSuccess⟩ : ∃ first, decodeRead read witness = .ok first := by
      cases decodedType : scalarType? read.ty with
      | none => simp [decodedType] at headSupported
      | some scalarType =>
        exact ⟨(read.name, Value.pack read.ty
          (sourceValue scalarType (witness ("%input_" ++ read.name)))), by
          simp [decodeRead, decodedType]⟩
    obtain ⟨tail, tailSuccess⟩ := ih tailSupported
    refine ⟨first :: tail, ?_⟩
    have tailMapped : List.mapM (fun item => decodeRead item witness) rest =
        .ok tail := tailSuccess
    change List.mapM (fun item => decodeRead item witness) (read :: rest) =
      .ok (first :: tail)
    rw [List.mapM_cons, firstSuccess, tailMapped]
    rfl

/-- Successful candidate decoding preserves production read lookup order and
the exact canonical scalar represented by each supported source type. -/
theorem decodeReads_candidate_meaning (reads : List Backend.Impact.Read)
    (witness : Assignment)
    (supported : ∀ read ∈ reads, (scalarType? read.ty).isSome = true)
    (distinct : reads.Pairwise (fun left right => left.name ≠ right.name))
    (typed : ∀ read ∈ reads,
      read.ty.validate {poseidon2 := true, stateCells := true, stateMaps := true} = .ok ())
    (bounded : ∀ read ∈ reads,
      (witness ("%input_" ++ read.name)).val ≤ Native.sourceMaximum read.ty) :
    ∃ decodedValues, decodeReads reads witness = .ok decodedValues ∧
      ∀ read ∈ reads,
        (∃ decoder : ScalarType read.ty,
          decodedValues.lookup read.name = some (Value.pack read.ty
            (sourceValue decoder (witness ("%input_" ++ read.name))))) ∧
        (∃ decoder : ScalarType read.ty,
          Canonical read.ty (sourceValue decoder (witness ("%input_" ++ read.name))) ∧
          sourceScalar? read.ty (sourceValue decoder
            (witness ("%input_" ++ read.name))) =
              some (witness ("%input_" ++ read.name))) := by
  obtain ⟨decodedValues, success⟩ :=
    decodeReads_supported_success reads witness supported
  refine ⟨decodedValues, success, ?_⟩
  intro read member
  obtain ⟨decoder, lookup⟩ :=
    decodeReads_lookup reads witness decodedValues success distinct read member
  obtain ⟨meaningDecoder, canonical, meaning⟩ :=
    decodeReads_canonical reads witness decodedValues success typed bounded read member
  exact ⟨⟨decoder, lookup⟩, ⟨meaningDecoder, canonical, meaning⟩⟩

/-- Append relation candidates to an existing source-output environment only
after the scalar decoder has returned a checked value list. -/
theorem appendSupportedReads_existing (reads : List Backend.Impact.Read)
    (hash : Hash) (witness : Assignment)
    (aliases : Backend.Native.AliasEnvironment) (values : EvalEnv) (types : TypeEnv)
    (environment : TypedEnvironment hash witness aliases values types)
    (supported : ∀ read ∈ reads, (scalarType? read.ty).isSome = true)
    (fresh : ∀ read ∈ reads,
      values.lookup read.name = none ∧ types.lookup read.name = none)
    (distinct : reads.Pairwise (fun left right => left.name ≠ right.name))
    (existing : ∀ read ∈ reads,
      aliases.lookup read.name = some (.input ("%input_" ++ read.name)))
    (typed : ∀ read ∈ reads,
      read.ty.validate {poseidon2 := true, stateCells := true, stateMaps := true} = .ok ())
    (bounded : ∀ read ∈ reads,
      (witness ("%input_" ++ read.name)).val ≤ Native.sourceMaximum read.ty) :
    ∃ decodedValues,
      decodeReads reads witness = .ok decodedValues ∧
      TypedEnvironment hash witness aliases
        (values ++ decodedValues) (types ++ readTypes reads) := by
  obtain ⟨decodedValues, decoded⟩ :=
    decodeReads_supported_success reads witness supported
  exact ⟨decodedValues, decoded,
    appendDecodedReads_existing reads hash witness aliases values types environment
      decodedValues decoded fresh distinct existing typed bounded⟩

end Noctium.Verification.GenericStateCandidateDecode
