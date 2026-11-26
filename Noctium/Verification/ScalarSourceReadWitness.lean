import Noctium.Verification.ScalarCellReadDecoding
import Noctium.Verification.ScalarGuardedReadAdmission
import Noctium.Verification.ScalarSourceReadTape
import Noctium.Verification.ScalarLedgerWitnessSource

namespace Noctium.Verification.ScalarSourceReadWitness

open Backend NativeRelation
open GenericStateCheckedReadTrace (readMetadata)
open ScalarGuardedPlanAdmission (ScalarEffect)
open ScalarCellWitnessReadSeed (seedReadValues)

/-- A successful source call exposes the guarded fold scheduled by its
accepted plan, using the entrypoint's reset frame and actual circuit outputs. -/
theorem accepted_entrypoint_source_fold (state : List StateDecl) (entry : Entrypoint)
    (plan : Impact.Plan) (ctx : EvalContext) (values result : EvalEnv)
    (initial next : LedgerState)
    (lowered : Impact.lower state (Passes.pruneEntrypoint entry) = .ok plan)
    (effects : ∀ effect ∈ entry.effects, ScalarEffect state effect)
    (success : entry.run ctx values initial = .ok (result, next)) :
    ∃ outputs finalEnv returned,
      entry.circuit.run ctx values = .ok outputs ∧
      GuardedSourceEffects.fold ctx entry.effectGuards entry.effects.zipIdx
        (outputs ++ values,
          {initial with unshieldedInputs := [], unshieldedOutputs := [], unshieldedSpendClaims := []}) =
        .ok (finalEnv, next) ∧
      entry.evalReturns ctx finalEnv = .ok returned ∧ result = outputs ++ returned := by
  obtain ⟨outputs, finalEnv, returned, circuit, runEffects, returns, resultEq⟩ :=
    ScalarLedgerWitnessSource.entrypoint_run_steps ctx entry values result initial next success
  let ep := Passes.pruneEntrypoint entry
  have scope := ScalarGuardedActivityAdmission.lower_guarded_scalar_read_scope
    state ep plan lowered effects
  have guardMetadata := GenericStateEffectValidation.lower_guard_metadata_valid
    state ep plan lowered
  let frame : SourceEffects.Frame :=
    (outputs ++ values,
      {initial with unshieldedInputs := [], unshieldedOutputs := [], unshieldedSpendClaims := []})
  have exactFold := GuardedSourceEffects.runEffectsWithGuardsAndEnv_eq_fold
    ctx ep.effects ep.effectGuards frame (by simpa using guardMetadata) scope
  have folded := exactFold.symm.trans runEffects
  exact ⟨outputs, finalEnv, returned, circuit, folded, returns, resultEq⟩

/-- Seed the witness bindings for the accepted plan with the reads recorded
from source execution. The production descriptors fix the order and types.
Circuit inputs remain separate from the recorded ledger reads. -/
theorem lower_source_read_witness (state : List StateDecl) (ep : Entrypoint)
    (plan : Impact.Plan) (ctx : EvalContext) (inputs : Assignment)
    (initial final : SourceEffects.Frame) (records : List (Impact.Read × Scalar))
    (lowered : Impact.lower state ep = .ok plan)
    (effects : ∀ effect ∈ ep.effects, ScalarEffect state effect)
    (recorded : ScalarSourceReadTape.sourceReadInputs ctx ep.effectGuards ep.effects.zipIdx
      (Impact.publicInputReadCount ep.circuit.inputs) initial = .ok (records, final)) :
    let reads := plan.reads.drop (Impact.publicInputReadCount ep.circuit.inputs)
    runEffectsWithGuardsAndEnv ctx ep.effects ep.effectGuards initial.1 initial.2 = .ok final ∧
    reads.map readMetadata = (records.map Prod.fst).map readMetadata ∧
    (∀ input ∈ ep.circuit.inputs,
      seedReadValues inputs records ("%input_" ++ input.name) = inputs ("%input_" ++ input.name)) ∧
    ∃ readValues,
      GenericStateInputValues.decodeReads reads (seedReadValues inputs records) = .ok readValues ∧
      readValues.map Prod.fst = records.map (fun record => record.1.name) ∧
      ∀ record ∈ records, ∃ support : ScalarNormalization.ScalarType record.1.ty,
        ScalarNormalization.Canonical record.1.ty
          (GenericStateInputValues.sourceValue support record.2) ∧
        readValues.lookup record.1.name =
          some (Value.pack record.1.ty (GenericStateInputValues.sourceValue support record.2)) := by
  let ordinal := Impact.publicInputReadCount ep.circuit.inputs
  let reads := plan.reads.drop ordinal
  have scope := ScalarGuardedActivityAdmission.lower_guarded_scalar_read_scope
    state ep plan lowered effects
  obtain ⟨folded, order, canonical⟩ := ScalarSourceReadTape.sourceReadInputs_sound
    ctx ep.effectGuards ep.effects.zipIdx ordinal initial final records recorded
  have loweredOrder := ScalarEffectReadFacts.lower_postPublic_read_metadata
    state ep plan lowered scope
  have metadata : reads.map readMetadata = (records.map Prod.fst).map readMetadata :=
    loweredOrder.trans (by simpa only [List.zipIdx_map_fst] using order.symm)
  obtain ⟨_, fresh, distinct⟩ :=
    ScalarGuardedReadAdmission.lower_read_admission state ep plan lowered effects
  have unique : (reads.map (·.name)).Nodup :=
    List.nodup_iff_pairwise_ne.mpr
      (List.Pairwise.map (fun descriptor : Impact.Read => descriptor.name)
        (fun _ _ different => different) distinct)
  have preserved := ScalarCellWitnessReadSeed.seedReadValues_preserves_lowered_inputs
    inputs ep plan records metadata
    (fun descriptor present collision => fresh descriptor present (List.mem_append_left _ collision))
  have effectGuardsValid := GenericStateEffectValidation.lower_guard_metadata_valid state ep plan lowered
  rw [GuardedSourceEffects.runEffectsWithGuardsAndEnv_eq_fold ctx ep.effects ep.effectGuards
    initial (by simpa using effectGuardsValid) scope]
  exact ⟨folded, metadata, preserved, ScalarCellReadDecoding.decode_seeded_source_cell_reads
    reads inputs records metadata canonical unique⟩

/-- A successful admitted source call supplies the witness's ordered read
values when the reached scalar read bindings are canonical. -/
theorem accepted_entrypoint_source_read_witness (state : List StateDecl) (entry : Entrypoint)
    (plan : Impact.Plan) (ctx : EvalContext) (inputs : Assignment) (values result : EvalEnv)
    (initial next : LedgerState)
    (lowered : Impact.lower state (Passes.pruneEntrypoint entry) = .ok plan)
    (effects : ∀ effect ∈ entry.effects, ScalarEffect state effect)
    (success : entry.run ctx values initial = .ok (result, next))
    (canonicalReads : ∀ outputs, entry.circuit.run ctx values = .ok outputs →
      ScalarSourceReadTape.sourceReadValuesCanonical ctx entry.effectGuards entry.effects.zipIdx
        (outputs ++ values,
          {initial with unshieldedInputs := [], unshieldedOutputs := [], unshieldedSpendClaims := []})) :
    let cutoff := Impact.publicInputReadCount entry.circuit.inputs
    let reads := plan.reads.drop cutoff
    ∃ outputs finalEnv returned records readValues,
      entry.circuit.run ctx values = .ok outputs ∧
      entry.evalReturns ctx finalEnv = .ok returned ∧ result = outputs ++ returned ∧
      ScalarSourceReadTape.sourceReadInputs ctx entry.effectGuards entry.effects.zipIdx cutoff
        (outputs ++ values,
          {initial with unshieldedInputs := [], unshieldedOutputs := [], unshieldedSpendClaims := []}) =
        .ok (records, (finalEnv, next)) ∧
      reads.map readMetadata = (records.map Prod.fst).map readMetadata ∧
      (∀ input ∈ entry.circuit.inputs,
        seedReadValues inputs records ("%input_" ++ input.name) = inputs ("%input_" ++ input.name)) ∧
      GenericStateInputValues.decodeReads reads (seedReadValues inputs records) = .ok readValues ∧
      readValues.map Prod.fst = records.map (fun record => record.1.name) := by
  obtain ⟨outputs, finalEnv, returned, circuit, folded, returns, resultEq⟩ :=
    accepted_entrypoint_source_fold state entry plan ctx values result initial next
      lowered effects success
  let ep := Passes.pruneEntrypoint entry
  let frame : SourceEffects.Frame :=
    (outputs ++ values,
      {initial with unshieldedInputs := [], unshieldedOutputs := [], unshieldedSpendClaims := []})
  have scope := ScalarGuardedActivityAdmission.lower_guarded_scalar_read_scope
    state ep plan lowered effects
  have reached := canonicalReads outputs circuit
  obtain ⟨records, recorded, _, _⟩ := ScalarSourceReadTape.sourceReadInputs_complete
    ctx entry.effectGuards entry.effects.zipIdx (Impact.publicInputReadCount entry.circuit.inputs)
    frame (finalEnv, next) scope folded reached
  obtain ⟨_, metadata, preserved, readValues, decoded, order, _⟩ :=
    lower_source_read_witness state ep plan ctx inputs frame (finalEnv, next) records
      lowered effects recorded
  exact ⟨outputs, finalEnv, returned, records, readValues, circuit, returns, resultEq,
    recorded, metadata, preserved, decoded, order⟩

end Noctium.Verification.ScalarSourceReadWitness
