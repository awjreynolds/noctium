import Noctium.Verification.ScalarCellReadDecoding
import Noctium.Verification.ScalarGuardedReadAdmission
import Noctium.Verification.ScalarSourceReadTape

namespace Noctium.Verification.ScalarSourceReadWitness

open Backend NativeRelation
open GenericStateCheckedReadTrace (readMetadata)
open ScalarGuardedPlanAdmission (ScalarEffect)
open ScalarCellWitnessReadSeed (seedReadValues)

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

end Noctium.Verification.ScalarSourceReadWitness
