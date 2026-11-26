import Noctium.Verification.ScalarCellSourceReads
import Noctium.Verification.ScalarWitnessLedgerReads
import Noctium.Verification.GenericStateEffectValidation
import Noctium.Passes

namespace Noctium.Verification.ScalarCellWitnessReadSeed

open Backend NativeRelation ScalarNormalization
open NativeRelationJson
open Noctium.Verification.ScalarWitnessConstruction

private def readIdentifier (read : Impact.Read) : String := "%input_" ++ read.name

private def readIdentifiers (entries : List (Impact.Read × Scalar)) : List String :=
  entries.map (fun item => readIdentifier item.1)

/-- Add each actual post-public source read value under its compiler input
identifier. Other assignment keys keep their original values. -/
def seedReadValues (inputs : NativeRelation.Assignment)
    (entries : List (Impact.Read × Scalar)) : NativeRelation.Assignment :=
  fun name =>
    ((entries.map (fun item => (readIdentifier item.1, item.2))).lookup name).getD
      (inputs name)

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

private theorem seedReadValues_fresh (inputs : NativeRelation.Assignment)
    (entries : List (Impact.Read × Scalar)) (name : String)
    (fresh : name ∉ readIdentifiers entries) :
    seedReadValues inputs entries name = inputs name := by
  unfold seedReadValues
  have missing : (entries.map (fun item => (readIdentifier item.1, item.2))).lookup
      name = none := by
    apply List.lookup_eq_none_iff.mpr
    intro pair member
    obtain ⟨entry, present, equal⟩ := List.mem_map.mp member
    subst pair
    have different : name ≠ readIdentifier entry.1 := by
      intro same
      exact fresh (List.mem_map.mpr ⟨entry, present, same.symm⟩)
    simp [different]
  rw [missing]
  rfl

theorem seedReadValues_member (inputs : NativeRelation.Assignment)
    (entries : List (Impact.Read × Scalar))
    (distinct : (readIdentifiers entries).Nodup)
    (read : Impact.Read) (value : Scalar)
    (member : (read, value) ∈ entries) :
    seedReadValues inputs entries (readIdentifier read) = value := by
  induction entries with
  | nil => cases member
  | cons head tail ih =>
    simp only [readIdentifiers, List.map_cons, List.nodup_cons] at distinct
    rcases List.mem_cons.mp member with same | later
    · subst head
      simp [seedReadValues, readIdentifier]
    · have different : readIdentifier read ≠ readIdentifier head.1 := by
        intro same
        exact distinct.1 (List.mem_map.mpr
          ⟨(read, value), later, by simpa [readIdentifiers, readIdentifier] using same⟩)
      have unequal : (readIdentifier read == readIdentifier head.1) = false := by
        simp [different]
      simp only [seedReadValues, List.map_cons, List.lookup_cons, unequal]
      exact ih distinct.2 later

private theorem record_names_eq_suffix_names (entry : Entrypoint)
    (plan : Impact.Plan) (entries : List (Impact.Read × Scalar))
    (metadata : (plan.reads.drop (Impact.publicInputReadCount entry.circuit.inputs)).map
        GenericStateCheckedReadTrace.readMetadata =
      (entries.map Prod.fst).map GenericStateCheckedReadTrace.readMetadata) :
    (entries.map (fun item => item.1.name)) =
      (plan.reads.drop (Impact.publicInputReadCount entry.circuit.inputs)).map (·.name) := by
  have projected := congrArg (List.map Prod.fst) metadata
  simpa only [GenericStateCheckedReadTrace.readMetadata,
    List.map_map, Function.comp_def] using projected.symm

private theorem record_names_fresh (entry : Entrypoint) (plan : Impact.Plan)
    (entries : List (Impact.Read × Scalar))
    (metadata : (plan.reads.drop (Impact.publicInputReadCount entry.circuit.inputs)).map
        GenericStateCheckedReadTrace.readMetadata =
      (entries.map Prod.fst).map GenericStateCheckedReadTrace.readMetadata)
    (fresh : ∀ read ∈ plan.reads.drop (Impact.publicInputReadCount entry.circuit.inputs),
      read.name ∉ entry.circuit.inputs.map (·.name)) :
    ∀ record ∈ entries, record.1.name ∉ entry.circuit.inputs.map (·.name) := by
  intro record member
  have entryMember : record.1 ∈ entries.map Prod.fst :=
    List.mem_map.mpr ⟨record, member, rfl⟩
  have metadataMember : GenericStateCheckedReadTrace.readMetadata record.1 ∈
      (entries.map Prod.fst).map GenericStateCheckedReadTrace.readMetadata :=
    List.mem_map.mpr ⟨record.1, entryMember, rfl⟩
  rw [← metadata] at metadataMember
  obtain ⟨read, readMember, sameMetadata⟩ := List.mem_map.mp metadataMember
  simp only [GenericStateCheckedReadTrace.readMetadata] at sameMetadata
  have sameName : record.1.name = read.name := (congrArg Prod.fst sameMetadata).symm
  intro present
  exact fresh read readMember (by rw [← sameName]; exact present)

private theorem seedReadValues_preserves_circuit_inputs (inputs : NativeRelation.Assignment)
    (entry : Entrypoint) (entries : List (Impact.Read × Scalar))
    (fresh : ∀ record ∈ entries,
      record.1.name ∉ entry.circuit.inputs.map (·.name)) :
    ∀ input ∈ entry.circuit.inputs,
      seedReadValues inputs entries ("%input_" ++ input.name) =
        inputs ("%input_" ++ input.name) := by
  intro input member
  apply seedReadValues_fresh
  intro collision
  obtain ⟨record, recordMember, sameIdentifier⟩ := List.mem_map.mp collision
  have sameName : record.1.name = input.name :=
    (String.append_right_inj "%input_").mp sameIdentifier
  exact fresh record recordMember
    (List.mem_map.mpr ⟨input, member, sameName.symm⟩)

/-- Seeding a checked source tape leaves the separate circuit input bindings
intact when the accepted post-public read names are fresh. -/
theorem seedReadValues_preserves_lowered_inputs (inputs : NativeRelation.Assignment)
    (entry : Entrypoint) (plan : Impact.Plan) (entries : List (Impact.Read × Scalar))
    (metadata : (plan.reads.drop (Impact.publicInputReadCount entry.circuit.inputs)).map
        GenericStateCheckedReadTrace.readMetadata =
      (entries.map Prod.fst).map GenericStateCheckedReadTrace.readMetadata)
    (fresh : ∀ read ∈ plan.reads.drop (Impact.publicInputReadCount entry.circuit.inputs),
      read.name ∉ entry.circuit.inputs.map (·.name)) :
    ∀ input ∈ entry.circuit.inputs,
      seedReadValues inputs entries ("%input_" ++ input.name) =
        inputs ("%input_" ++ input.name) :=
  seedReadValues_preserves_circuit_inputs inputs entry entries
    (record_names_fresh entry plan entries metadata fresh)

private theorem scalarNumber_eq_stateEncoding {ty : Ty}
    (scalarType : ScalarType ty) (value : ty.Denote) :
    ScalarNormalization.number scalarType value = GenericStateEncoding.number ty value := by
  cases scalarType <;> rfl

theorem scalarStateEffects_of_cells (state : List StateDecl)
    (effects : List Effect)
    (cellScope : ScalarCellSourceReads.ScalarCellEffects state effects) :
    GenericStateEffectValidation.ScalarStateEffects effects := by
  induction effects with
  | nil => exact .nil
  | cons effect rest ih =>
    have headCell := cellScope effect (by simp)
    have head : GenericStateEffectValidation.ScalarStateEffect effect := by
      cases headCell <;> constructor
    have tailScope : ScalarCellSourceReads.ScalarCellEffects state rest := by
      intro next member
      exact cellScope next (List.mem_cons_of_mem effect member)
    exact .cons head (ih tailScope)

private theorem readChunks_destinations (state : List StateDecl)
    (effects : List Effect) (ordinal : Nat)
    (cellScope : ScalarCellSourceReads.ScalarCellEffects state effects) :
    (ScalarCellSourceReads.readChunks effects ordinal).flatten.map (·.name) =
      GenericStateEffectValidation.scalarReadDestinations effects := by
  induction effects generalizing ordinal with
  | nil => rfl
  | cons effect rest ih =>
    have tailScope : ScalarCellSourceReads.ScalarCellEffects state rest := by
      intro next member
      exact cellScope next (List.mem_cons_of_mem effect member)
    cases cellScope effect (by simp) with
    | readCell name destination ty _ _ =>
      simpa [ScalarCellSourceReads.readChunks,
        ScalarCellSourceReads.effectReadChunk,
        GenericStateEffectValidation.scalarReadDestinations] using
          congrArg (List.cons destination) (ih (ordinal + 1) tailScope)
    | writeCell name ty value _ _ =>
      simpa [ScalarCellSourceReads.readChunks,
        ScalarCellSourceReads.effectReadChunk,
        GenericStateEffectValidation.scalarReadDestinations] using
          ih ordinal tailScope

/-- Accepted source cell effects keep the lowered post-public read names
distinct and fresh against declared circuit inputs. The proof uses effect
validation, without the stale generic admission wrapper. -/
theorem lower_source_cell_read_names (state : List StateDecl)
    (entry : Entrypoint) (plan : Impact.Plan) (entries : List (Impact.Read × Scalar))
    (before after : ScalarCellSourceReads.Frame) (ctx : EvalContext)
    (cellScope : ScalarCellSourceReads.ScalarCellEffects state entry.effects)
    (lowered : Impact.lower state (Passes.pruneEntrypoint entry) = .ok plan)
    (metadata : (plan.reads.drop (Impact.publicInputReadCount entry.circuit.inputs)).map
        GenericStateCheckedReadTrace.readMetadata =
      (entries.map Prod.fst).map GenericStateCheckedReadTrace.readMetadata)
    (source : ScalarCellSourceReads.sourceReadInputs ctx entry.effects
      (Impact.publicInputReadCount entry.circuit.inputs) before = .ok (entries, after)) :
    ((plan.reads.drop (Impact.publicInputReadCount entry.circuit.inputs)).map (·.name)).Nodup ∧
      ∀ read ∈ plan.reads.drop (Impact.publicInputReadCount entry.circuit.inputs),
        read.name ∉ (GenericStateEffectValidation.initialEffectTypeEnv
          (Passes.pruneEntrypoint entry)).map Prod.fst := by
  have entriesNames := ScalarCellSourceReads.sourceReadInputs_names ctx entry.effects
    (Impact.publicInputReadCount entry.circuit.inputs) before after entries source
  have sourceNames : (entries.map (fun item => item.1.name)) =
      GenericStateEffectValidation.scalarReadDestinations entry.effects := by
    calc
      entries.map (fun item => item.1.name) =
          (entries.map Prod.fst).map (·.name) := by simp
      _ = (ScalarCellSourceReads.readChunks entry.effects
          (Impact.publicInputReadCount entry.circuit.inputs)).flatten.map (·.name) := by
        rw [entriesNames]
      _ = GenericStateEffectValidation.scalarReadDestinations entry.effects :=
        readChunks_destinations state entry.effects _ cellScope
  have namesEq := record_names_eq_suffix_names entry plan entries metadata
  have suffixNames :
      (plan.reads.drop (Impact.publicInputReadCount entry.circuit.inputs)).map (·.name) =
        GenericStateEffectValidation.scalarReadDestinations entry.effects := by
    rw [← namesEq, sourceNames]
  have prunedCellScope : ScalarCellSourceReads.ScalarCellEffects state
      (Passes.pruneEntrypoint entry).effects := by
    simpa [Passes.pruneEntrypoint] using cellScope
  have validationNames :=
    GenericStateEffectValidation.lower_scalar_read_destinations_fresh_unique state
      (Passes.pruneEntrypoint entry) plan lowered
      (scalarStateEffects_of_cells state (Passes.pruneEntrypoint entry).effects
        prunedCellScope)
  constructor
  · rw [suffixNames]
    exact validationNames.1
  · intro read member
    have sourceMember : read.name ∈
        GenericStateEffectValidation.scalarReadDestinations entry.effects := by
      rw [← suffixNames]
      exact List.mem_map.mpr ⟨read, member, rfl⟩
    exact validationNames.2 read.name sourceMember

private theorem seedReadValues_facts (inputs : NativeRelation.Assignment)
    (entry : Entrypoint) (plan : Impact.Plan) (entries : List (Impact.Read × Scalar))
    (metadata : (plan.reads.drop (Impact.publicInputReadCount entry.circuit.inputs)).map
        GenericStateCheckedReadTrace.readMetadata =
      (entries.map Prod.fst).map GenericStateCheckedReadTrace.readMetadata)
    (recordsDistinct : (entries.map (fun item => item.1.name)).Nodup)
    (canonical : ∀ record ∈ entries, ScalarCellSourceReads.CanonicalReadRecord record) :
    ∀ read ∈ plan.reads.drop (Impact.publicInputReadCount entry.circuit.inputs),
      ∃ (value : read.ty.Denote) (scalarType : ScalarType read.ty),
        Canonical read.ty value ∧
          seedReadValues inputs entries ("%input_" ++ read.name) =
            scalar (ScalarNormalization.number scalarType value) := by
  intro read member
  have metadataMember : GenericStateCheckedReadTrace.readMetadata read ∈
      (plan.reads.drop (Impact.publicInputReadCount entry.circuit.inputs)).map
        GenericStateCheckedReadTrace.readMetadata :=
    List.mem_map.mpr ⟨read, member, rfl⟩
  rw [metadata] at metadataMember
  obtain ⟨recordRead, recordReadMember, sameMetadata⟩ :=
    List.mem_map.mp metadataMember
  obtain ⟨record, recordMember, sameRecordRead⟩ :=
    List.mem_map.mp recordReadMember
  have sourceMetadata : GenericStateCheckedReadTrace.readMetadata record.1 =
      GenericStateCheckedReadTrace.readMetadata read := by
    rw [sameRecordRead]
    exact sameMetadata
  obtain ⟨value, valueCanonical, fieldValue⟩ := canonical record recordMember
  let scalarType := scalarTypeOfCanonicalInput valueCanonical
  have distinctKeys := readIdentifiers_nodup entries recordsDistinct
  have assignedValue := seedReadValues_member inputs entries distinctKeys
    record.1 record.2 recordMember
  rcases record with ⟨recordRead, recordValue⟩
  rcases recordRead with ⟨recordName, recordTy, recordComponents, recordSchema,
    recordGuard, recordRootCellRead⟩
  rcases read with ⟨readName, readTy, readComponents, readSchema, readGuard,
    readRootCellRead⟩
  simp only [GenericStateCheckedReadTrace.readMetadata, Prod.mk.injEq] at sourceMetadata
  rcases sourceMetadata with ⟨sameName, sameTy⟩
  cases sameName
  cases sameTy
  refine ⟨value, scalarType, valueCanonical, ?_⟩
  have assignedByName :
      seedReadValues inputs entries ("%input_" ++ recordName) = recordValue := by
    simpa [readIdentifier] using assignedValue
  have recordField :
      recordValue = scalar (GenericStateEncoding.number recordTy value) := by
    simpa using fieldValue
  rw [assignedByName, recordField, ← scalarNumber_eq_stateEncoding scalarType value]

/-- Seed actual source reads into the initial circuit assignment. The metadata
equality identifies each lowered post-public read, while uniqueness and
freshness keep additions separate from one another and from circuit inputs. -/
theorem seed_source_cell_read_assignment
    (inputs : NativeRelation.Assignment) (entry : Entrypoint) (plan : Impact.Plan)
    (entries : List (Impact.Read × Scalar))
    (metadata : (plan.reads.drop (Impact.publicInputReadCount entry.circuit.inputs)).map
        GenericStateCheckedReadTrace.readMetadata =
      (entries.map Prod.fst).map GenericStateCheckedReadTrace.readMetadata)
    (canonical : ∀ record ∈ entries, ScalarCellSourceReads.CanonicalReadRecord record)
    (readNamesDistinct :
      ((plan.reads.drop (Impact.publicInputReadCount entry.circuit.inputs)).map (·.name)).Nodup)
    (readNamesFresh : ∀ read ∈
      plan.reads.drop (Impact.publicInputReadCount entry.circuit.inputs),
      read.name ∉ entry.circuit.inputs.map (·.name)) :
    let readInputs := seedReadValues inputs entries
    (∀ input ∈ entry.circuit.inputs,
        readInputs ("%input_" ++ input.name) = inputs ("%input_" ++ input.name)) ∧
      (∀ read ∈ plan.reads.drop (Impact.publicInputReadCount entry.circuit.inputs),
        ∃ (value : read.ty.Denote) (scalarType : ScalarType read.ty),
          Canonical read.ty value ∧
            readInputs ("%input_" ++ read.name) =
              scalar (ScalarNormalization.number scalarType value)) := by
  have recordNames := record_names_eq_suffix_names entry plan entries metadata
  have recordsDistinct : (entries.map (fun item => item.1.name)).Nodup := by
    rw [recordNames]
    exact readNamesDistinct
  have preserved := seedReadValues_preserves_lowered_inputs inputs entry plan entries
    metadata readNamesFresh
  have facts := seedReadValues_facts inputs entry plan entries metadata recordsDistinct canonical
  exact ⟨preserved, facts⟩

/-- Derive suffix-name uniqueness and input freshness from accepted source
cell validation, then seed the assignment from the actual successful tape. -/
theorem seed_source_cell_read_assignment_from_tape
    (state : List StateDecl) (ctx : EvalContext)
    (inputs : NativeRelation.Assignment) (entry : Entrypoint) (plan : Impact.Plan)
    (entries : List (Impact.Read × Scalar)) (before after : ScalarCellSourceReads.Frame)
    (cellScope : ScalarCellSourceReads.ScalarCellEffects state entry.effects)
    (lowered : Impact.lower state (Passes.pruneEntrypoint entry) = .ok plan)
    (metadata : (plan.reads.drop (Impact.publicInputReadCount entry.circuit.inputs)).map
        GenericStateCheckedReadTrace.readMetadata =
      (entries.map Prod.fst).map GenericStateCheckedReadTrace.readMetadata)
    (canonical : ∀ record ∈ entries, ScalarCellSourceReads.CanonicalReadRecord record)
    (source : ScalarCellSourceReads.sourceReadInputs ctx entry.effects
      (Impact.publicInputReadCount entry.circuit.inputs) before = .ok (entries, after)) :
    let readInputs := seedReadValues inputs entries
    (∀ input ∈ entry.circuit.inputs,
        readInputs ("%input_" ++ input.name) = inputs ("%input_" ++ input.name)) ∧
      (∀ read ∈ plan.reads.drop (Impact.publicInputReadCount entry.circuit.inputs),
        ∃ (value : read.ty.Denote) (scalarType : ScalarType read.ty),
          Canonical read.ty value ∧
            readInputs ("%input_" ++ read.name) =
              scalar (ScalarNormalization.number scalarType value)) := by
  obtain ⟨distinct, freshInitial⟩ := lower_source_cell_read_names state entry plan entries
    before after ctx cellScope lowered metadata source
  have freshInputs : ∀ read ∈
      plan.reads.drop (Impact.publicInputReadCount entry.circuit.inputs),
      read.name ∉ entry.circuit.inputs.map (·.name) := by
    intro read member inputMember
    apply freshInitial read member
    simp only [GenericStateEffectValidation.initialEffectTypeEnv,
      List.map_append, List.map_map, Function.comp_def]
    apply List.mem_append_left
    simpa [Passes.pruneEntrypoint, Passes.pruneCircuit] using inputMember
  exact seed_source_cell_read_assignment inputs entry plan entries metadata canonical
    distinct freshInputs

end Noctium.Verification.ScalarCellWitnessReadSeed
