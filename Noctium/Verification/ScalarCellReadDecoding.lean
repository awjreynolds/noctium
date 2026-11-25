import Noctium.Verification.ScalarCellWitnessReadSeed
import Noctium.Verification.ScalarLedgerWitnessReadValues
import Noctium.Verification.GenericStateCheckedReadTrace

namespace Noctium.Verification.ScalarCellReadDecoding

open Backend NativeRelation ScalarNormalization GenericStateInputValues
open Noctium.Verification.ScalarCellSourceReads
open Noctium.Verification.ScalarCellWitnessReadSeed
open Noctium.Verification.ScalarWitnessConstruction

private def readIdentifier (read : Impact.Read) : String := "%input_" ++ read.name

private def readIdentifiers (entries : List (Impact.Read × Scalar)) : List String :=
  entries.map (fun item => readIdentifier item.1)

private theorem readIdentifiers_nodup (entries : List (Impact.Read × Scalar))
    (names : (entries.map (fun item => item.1.name)).Nodup) :
    (readIdentifiers entries).Nodup := by
  have pairwiseNames := List.nodup_iff_pairwise_ne.mp names
  have pairwiseIdentifiers :
      List.Pairwise (fun left right : String => left ≠ right)
        ((entries.map (fun item => item.1.name)).map
          (fun name => "%input_" ++ name)) := List.Pairwise.map
    (fun name : String => "%input_" ++ name)
    (fun left right different => by
      intro same
      exact different ((String.append_right_inj "%input_").mp same))
    pairwiseNames
  apply List.nodup_iff_pairwise_ne.mpr
  simpa only [readIdentifiers, readIdentifier, List.map_map, Function.comp_def]
    using pairwiseIdentifiers

private theorem entries_names_eq_reads_names (reads : List Impact.Read)
    (entries : List (Impact.Read × Scalar))
    (metadata : reads.map GenericStateCheckedReadTrace.readMetadata =
      (entries.map Prod.fst).map GenericStateCheckedReadTrace.readMetadata) :
    entries.map (fun item => item.1.name) = reads.map (·.name) := by
  have projected := congrArg (List.map Prod.fst) metadata
  simpa only [GenericStateCheckedReadTrace.readMetadata,
    List.map_map, Function.comp_def] using projected.symm

private theorem read_names_pairwise (reads : List Impact.Read)
    (distinct : (reads.map (·.name)).Nodup) :
    reads.Pairwise (fun left right => left.name ≠ right.name) := by
  induction reads with
  | nil => simp
  | cons head rest ih =>
    simp only [List.map_cons, List.nodup_cons, List.pairwise_cons] at distinct ⊢
    constructor
    · intro read member
      intro same
      exact distinct.1 (List.mem_map.mpr ⟨read, member, same.symm⟩)
    · exact ih distinct.2

private theorem decodeReads_map_names (reads : List Impact.Read)
    (witness : Assignment) (values : EvalEnv)
    (success : decodeReads reads witness = .ok values) :
    values.map Prod.fst = reads.map (·.name) := by
  induction reads generalizing values with
  | nil =>
    simp only [decodeReads] at success
    cases success
    rfl
  | cons read rest ih =>
    obtain ⟨first, tail, firstSuccess, tailSuccess, valuesEq⟩ :=
      decodeReads_cons_success read rest witness values success
    obtain ⟨support, firstEq⟩ := decodeRead_success read witness first firstSuccess
    rw [valuesEq, firstEq]
    simp [ih tail tailSuccess]

private theorem matching_record (reads : List Impact.Read)
    (entries : List (Impact.Read × Scalar))
    (metadata : reads.map GenericStateCheckedReadTrace.readMetadata =
      (entries.map Prod.fst).map GenericStateCheckedReadTrace.readMetadata)
    (record : Impact.Read × Scalar) (member : record ∈ entries) :
    ∃ read ∈ reads,
      GenericStateCheckedReadTrace.readMetadata record.1 =
        GenericStateCheckedReadTrace.readMetadata read := by
  have recordReadMember : record.1 ∈ entries.map Prod.fst :=
    List.mem_map.mpr ⟨record, member, rfl⟩
  have recordMetadataMember :
      GenericStateCheckedReadTrace.readMetadata record.1 ∈
        (entries.map Prod.fst).map GenericStateCheckedReadTrace.readMetadata :=
    List.mem_map.mpr ⟨record.1, recordReadMember, rfl⟩
  rw [← metadata] at recordMetadataMember
  obtain ⟨read, readMember, sameMetadata⟩ := List.mem_map.mp recordMetadataMember
  exact ⟨read, readMember, sameMetadata.symm⟩

private theorem seed_read_facts (reads : List Impact.Read)
    (inputs : Assignment) (entries : List (Impact.Read × Scalar))
    (metadata : reads.map GenericStateCheckedReadTrace.readMetadata =
      (entries.map Prod.fst).map GenericStateCheckedReadTrace.readMetadata)
    (canonical : ∀ record ∈ entries, CanonicalReadRecord record)
    (readNamesDistinct : (reads.map (·.name)).Nodup) :
    ∀ read ∈ reads,
      ∃ (value : read.ty.Denote) (scalarType : ScalarType read.ty),
        Canonical read.ty value ∧
          seedReadValues inputs entries ("%input_" ++ read.name) =
            scalar (ScalarNormalization.number scalarType value) := by
  have entriesNames := entries_names_eq_reads_names reads entries metadata
  have entriesDistinct : (entries.map (fun item => item.1.name)).Nodup := by
    rw [entriesNames]
    exact readNamesDistinct
  have identifiersDistinct := readIdentifiers_nodup entries entriesDistinct
  intro read readMember
  have readMetadataMember : GenericStateCheckedReadTrace.readMetadata read ∈
      reads.map GenericStateCheckedReadTrace.readMetadata :=
    List.mem_map.mpr ⟨read, readMember, rfl⟩
  rw [metadata] at readMetadataMember
  obtain ⟨recordRead, recordReadMember, sameMetadata⟩ :=
    List.mem_map.mp readMetadataMember
  obtain ⟨record, recordMember, sameRecordRead⟩ :=
    List.mem_map.mp recordReadMember
  have sourceMetadata : GenericStateCheckedReadTrace.readMetadata record.1 =
      GenericStateCheckedReadTrace.readMetadata read := by
    rw [sameRecordRead]
    exact sameMetadata
  obtain ⟨value, valueCanonical, fieldValue⟩ := canonical record recordMember
  have assignedValue := seedReadValues_member inputs entries identifiersDistinct
    record.1 record.2 recordMember
  rcases record with ⟨recordRead, recordValue⟩
  rcases recordRead with ⟨recordName, recordTy, recordComponents, recordSchema,
    recordGuard, recordRootCellRead⟩
  rcases read with ⟨readName, readTy, readComponents, readSchema, readGuard,
    readRootCellRead⟩
  simp only [GenericStateCheckedReadTrace.readMetadata, Prod.mk.injEq]
    at sourceMetadata
  rcases sourceMetadata with ⟨sameName, sameTy⟩
  cases sameName
  cases sameTy
  refine ⟨value, scalarTypeOfCanonicalInput valueCanonical, valueCanonical, ?_⟩
  have assignedByName :
      seedReadValues inputs entries ("%input_" ++ recordName) = recordValue := by
    change seedReadValues inputs entries ("%input_" ++ recordName) = recordValue
    exact assignedValue
  have recordField :
      recordValue = scalar (GenericStateEncoding.number recordTy value) := by
    simpa using fieldValue
  rw [assignedByName, recordField]
  have numberEq : ScalarNormalization.number
      (scalarTypeOfCanonicalInput valueCanonical) value =
        GenericStateEncoding.number recordTy value := by
    cases scalarTypeOfCanonicalInput valueCanonical <;> rfl
  rw [← numberEq]

private theorem scalarNumber_eq_stateEncoding {ty : Ty}
    (scalarType : ScalarType ty) (value : ty.Denote) :
    ScalarNormalization.number scalarType value =
      GenericStateEncoding.number ty value := by
  cases scalarType <;> rfl

/-- Decoding the seeded production read inputs preserves read order and gives
each source record the canonical typed value recorded by its source step. -/
theorem decode_seeded_source_cell_reads (reads : List Impact.Read)
    (inputs : Assignment) (entries : List (Impact.Read × Scalar))
    (metadata : reads.map GenericStateCheckedReadTrace.readMetadata =
      (entries.map Prod.fst).map GenericStateCheckedReadTrace.readMetadata)
    (canonical : ∀ record ∈ entries, CanonicalReadRecord record)
    (readNamesDistinct : (reads.map (·.name)).Nodup) :
    ∃ readValues,
      decodeReads reads (seedReadValues inputs entries) = .ok readValues ∧
      readValues.map Prod.fst = entries.map (fun record => record.1.name) ∧
      ∀ record ∈ entries, ∃ support : ScalarType record.1.ty,
        Canonical record.1.ty (sourceValue support record.2) ∧
        readValues.lookup record.1.name =
          some (Value.pack record.1.ty (sourceValue support record.2)) := by
  have facts := seed_read_facts reads inputs entries metadata canonical readNamesDistinct
  obtain ⟨readValues, decoded, _⟩ :=
    ScalarWitnessConstruction.decode_seeded_scalar_reads reads
      (seedReadValues inputs entries) facts
  have order := decodeReads_map_names reads (seedReadValues inputs entries)
    readValues decoded
  have entriesNames := entries_names_eq_reads_names reads entries metadata
  have entriesDistinct : (entries.map (fun item => item.1.name)).Nodup := by
    rw [entriesNames]
    exact readNamesDistinct
  have identifiersDistinct := readIdentifiers_nodup entries entriesDistinct
  have distinctReads := read_names_pairwise reads readNamesDistinct
  refine ⟨readValues, decoded, ?_, ?_⟩
  · rw [order, ← entriesNames]
  · intro record member
    obtain ⟨read, readMember, sourceMetadata⟩ :=
      matching_record reads entries metadata record member
    obtain ⟨support, readLookup⟩ := decodeReads_lookup reads
      (seedReadValues inputs entries) readValues decoded distinctReads read readMember
    have assignedValue := seedReadValues_member inputs entries identifiersDistinct
      record.1 record.2 member
    obtain ⟨value, valueCanonical, fieldValue⟩ := canonical record member
    rcases record with ⟨recordRead, recordValue⟩
    rcases recordRead with ⟨recordName, recordTy, recordComponents, recordSchema,
      recordGuard, recordRootCellRead⟩
    rcases read with ⟨readName, readTy, readComponents, readSchema, readGuard,
      readRootCellRead⟩
    simp only [GenericStateCheckedReadTrace.readMetadata, Prod.mk.injEq]
      at sourceMetadata
    rcases sourceMetadata with ⟨sameName, sameTy⟩
    cases sameName
    cases sameTy
    have assignedByName :
        seedReadValues inputs entries ("%input_" ++ recordName) = recordValue := by
      change seedReadValues inputs entries ("%input_" ++ recordName) = recordValue
      exact assignedValue
    have recordField :
        recordValue = scalar (GenericStateEncoding.number recordTy value) := by
      simpa using fieldValue
    refine ⟨support, ?_, ?_⟩
    · have decodedValue : sourceValue support recordValue = value := by
        rw [recordField, ← scalarNumber_eq_stateEncoding support value]
        exact ScalarWitnessConstruction.round_trip_scalar_read support value valueCanonical
      rw [decodedValue]
      exact valueCanonical
    · rw [assignedByName] at readLookup
      exact readLookup

end Noctium.Verification.ScalarCellReadDecoding
