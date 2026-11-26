import Noctium.Verification.GenericStateConverseEffectFold
import Noctium.Verification.GenericStateConverseCheckedPlan
import Noctium.Verification.GenericStateConversePublicPrefix

namespace Noctium.Verification.GenericStateConverseNativeTrace

open Backend NativeRelation ScalarNormalization NativeState
open GenericStateEffectValidation GenericStateCheckedReadTrace
open ScalarCellWitnessReadSeed (seedReadValues)
open ScalarGuardedPlanAdmission (ScalarEffect)

/-- A successful source call constructs the ordered scalar read lanes and a
checked run of its actual emitted guarded plan. The final native root encodes
the source successor. -/
theorem source_call_native_trace (state : List StateDecl)
    (sourceEntry : Entrypoint) (plan : Impact.Plan)
    (ctx : EvalContext) (values result : EvalEnv)
    (inputs : Assignment) (initial next : LedgerState) (slots : List Slot)
    (admittedInputs : CanonicalInputs sourceEntry.circuit values inputs)
    (admittedState : GenericStateEncoding.AdmittedState state initial slots)
    (lowered : Impact.lower state (Passes.pruneEntrypoint sourceEntry) = .ok plan)
    (effects : ∀ effect ∈ sourceEntry.effects, ScalarEffect state effect)
    (modulus : ctx.modulus = Field.modulus)
    (success : sourceEntry.run ctx values initial = .ok (result, next)) :
    let cutoff := Impact.publicInputReadCount sourceEntry.circuit.inputs
    let reads := plan.reads.drop cutoff
    ∃ outputs finalEnv returned records readValues finalSlots finalReads,
      sourceEntry.circuit.run ctx values = .ok outputs ∧
      sourceEntry.evalReturns ctx finalEnv = .ok returned ∧ result = outputs ++ returned ∧
      ScalarSourceReadTape.sourceReadInputs ctx sourceEntry.effectGuards sourceEntry.effects.zipIdx cutoff
        (outputs ++ values,
          {initial with unshieldedInputs := [], unshieldedOutputs := [], unshieldedSpendClaims := []}) =
        .ok (records, (finalEnv, next)) ∧
      reads.map readMetadata = (records.map Prod.fst).map readMetadata ∧
      (∀ record ∈ records, ScalarCellSourceReads.CanonicalReadRecord record) ∧
      (∀ input ∈ sourceEntry.circuit.inputs,
        seedReadValues inputs records ("%input_" ++ input.name) = inputs ("%input_" ++ input.name)) ∧
      GenericStateInputValues.decodeReads reads (seedReadValues inputs records) = .ok readValues ∧
      GenericStateCheckedSchedule.CheckedPlan ctx (Passes.pruneEntrypoint sourceEntry)
        plan values (seedReadValues inputs records) slots ⟨[.vector finalSlots], finalReads⟩ ∧
      GenericStateEncoding.encodeState state next = some finalSlots := by
  let ep := Passes.pruneEntrypoint sourceEntry
  obtain ⟨outputs, finalEnv, returned, records, readValues, circuit, returns, resultShape,
    recorded, metadata, preserved, decoded, _⟩ :=
    GenericStateConverseSource.source_assignment_of_entry_run ctx state sourceEntry plan
      values result initial next slots inputs lowered effects admittedState modulus success
  have canonical := (ScalarSourceReadTape.sourceReadInputs_sound ctx sourceEntry.effectGuards
    sourceEntry.effects.zipIdx (Impact.publicInputReadCount sourceEntry.circuit.inputs) _
    (finalEnv, next) records recorded).2.2
  have prunedRun : ep.circuit.run ctx values = .ok outputs := by
    simpa only [ep, Passes.pruneEntrypoint, Passes.pruneCircuit_run] using circuit
  have prunedInputs : CanonicalInputs ep.circuit values inputs := by
    exact ⟨admittedInputs.unique, admittedInputs.declared, admittedInputs.complete,
      admittedInputs.binding⟩
  have circuitValid := lower_circuit_validated_source state ep plan lowered
  rw [GenericStateCaps.circuit_validate_source_crypto] at circuitValid
  have scope := ScalarGuardedActivityAdmission.lower_guarded_scalar_read_scope
    state ep plan lowered effects
  have scalarEffects := ScalarGuardedActivityAdmission.scalar_state_effects_of_admitted
    state ep.effects effects
  obtain ⟨finalTypes, validated, _⟩ :=
    lower_validated_guarded_effects_and_returns state ep plan lowered scalarEffects
  let descriptors := plan.reads.drop (Impact.publicInputReadCount ep.circuit.inputs)
  obtain ⟨_, fresh, distinct⟩ :=
    ScalarGuardedReadAdmission.lower_read_admission state ep plan lowered effects
  have freshTypes : ∀ descriptor ∈ descriptors, descriptor.name ∉ (initialEffectTypeEnv ep).map Prod.fst := by
    simpa only [initialEffectTypeEnv, List.map_append, List.map_map, Function.comp_def] using fresh
  have namesDistinct : (descriptors.map (·.name)).Nodup :=
    List.nodup_iff_pairwise_ne.mpr
      (List.Pairwise.map (fun descriptor : Impact.Read => descriptor.name)
        (fun _ _ different => different) distinct)
  obtain ⟨initialAgrees, _, candidates⟩ :=
    ScalarCellEffectEvaluation.call_candidate_scope ctx ep values outputs readValues inputs
      descriptors records prunedInputs circuitValid prunedRun metadata canonical namesDistinct
      freshTypes decoded
  obtain ⟨_, inputPlan, publicNative, publicCells, _, prefixAccepted, _,
    prefixEval, _, prefixRun⟩ :=
    GenericStateConversePublicPrefix.source_public_prefix state ep plan ctx values outputs
      readValues inputs [.vector slots] [] lowered prunedInputs prunedRun modulus
  obtain ⟨offsets, chunkPrefix, chunks, _, chunkPrefixAccepted, compiled, _⟩ :=
    GuardedPlanActivity.lower_field_guards state ep plan lowered scope
  have prefixEq := Except.ok.inj (chunkPrefixAccepted.symm.trans prefixAccepted)
  subst chunkPrefix
  have admittedItems : ∀ item ∈ ep.effects.zipIdx, ScalarEffect state item.1 := by
    intro item present
    apply effects
    change item.1 ∈ ep.effects
    rw [← List.zipIdx_map_fst 0 ep.effects]
    exact List.mem_map_of_mem present
  obtain ⟨groups, finalSlots, finalReads, evaluated, trace, encoded, _⟩ :=
    GenericStateConverseEffectFold.source_effects_native ctx state ep ep.effects.zipIdx
      (initialEffectTypeEnv ep) finalTypes _ (finalEnv, next)
      (Impact.publicInputReadCount ep.circuit.inputs) records ((outputs ++ values) ++ readValues)
      slots publicCells inputPlan plan offsets chunks validated compiled admittedItems scope
      recorded candidates initialAgrees admittedState.encoded admittedState.distinctDeclarations
      admittedState.slotBound modulus
  have checked := GenericStateConverseCheckedPlan.checked_of_constructed_trace state ep plan ctx
    values (seedReadValues inputs records) outputs readValues slots
    ⟨[.vector finalSlots], finalReads⟩ offsets inputPlan chunks publicNative groups publicCells
    scope prunedRun decoded prefixAccepted compiled prefixEval evaluated prefixRun trace
  exact ⟨outputs, finalEnv, returned, records, readValues, finalSlots, finalReads,
    circuit, returns, resultShape, recorded, metadata, canonical, preserved, decoded, checked, encoded⟩

end Noctium.Verification.GenericStateConverseNativeTrace
