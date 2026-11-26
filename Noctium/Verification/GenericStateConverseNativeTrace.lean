import Noctium.Verification.GenericStateConverseEffectFold
import Noctium.Verification.GenericStateConverseCheckedPlan
import Noctium.Verification.GenericStateConversePublicPrefix
import Noctium.Verification.GuardedScalarWitness

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

private theorem admitted_unshielded_frame (state : List StateDecl)
    (initial : LedgerState) (slots : List Slot)
    (admitted : GenericStateEncoding.AdmittedState state initial slots) :
    {initial with unshieldedInputs := [], unshieldedOutputs := [], unshieldedSpendClaims := []} = initial := by
  have accepted := admitted.initialEncoded
  unfold GenericStateEncoding.encodeInitialState at accepted
  split at accepted
  · rename_i shape
    simp only [GenericStateEncoding.initialShapeValid, Bool.and_eq_true, List.isEmpty_iff] at shape
    have empty : initial.unshieldedInputs = [] ∧ initial.unshieldedOutputs = [] ∧
        initial.unshieldedSpendClaims = [] := by
      grind
    cases initial
    simp_all
  · cases accepted

local instance : ReflBEq Ty where
  rfl := by
    intro ty
    cases ty with
    | foreign kind => cases kind <;> rename_i curve <;> cases curve <;> rfl
    | _ => simp [BEq.beq, instBEqTy.beq]

/-- On an admitted successful source call, the executable builder reaches
the checked artifact assembly with exactly the source read seed and native
trace. Assembly itself still has to satisfy the emitted rows. -/
theorem source_call_build_reduces_to_artifact (state : List StateDecl)
    (sourceEntry : Entrypoint) (ctx : EvalContext) (hash : Hash)
    (values result : EvalEnv) (inputs : Assignment)
    (initial next : LedgerState) (slots : List Slot) (bytes : ArtifactBytes.Bytes)
    (rewrites : Zkir.Rewrites) (artifact : Lean.Json)
    (admittedInputs : CanonicalInputs sourceEntry.circuit values inputs)
    (admittedState : GenericStateEncoding.AdmittedState state initial slots)
    (loweredArtifact : Zkir.lowerEntrypoint state sourceEntry rewrites = .ok artifact)
    (effects : ∀ effect ∈ sourceEntry.effects, ScalarEffect state effect)
    (modulus : ctx.modulus = Field.modulus)
    (success : sourceEntry.run ctx values initial = .ok (result, next)) :
    ∃ plan outputs finalEnv records base readValues operations finalSlots finalReads,
      let ep := Passes.pruneEntrypoint sourceEntry
      let seed := seedReadValues base records
      let transcript : GuardedStatementConsumption.Inputs :=
        ⟨operations.flatMap ImpactStatementScalar.opFields, finalReads.map Cell.value⟩
      sourceEntry.circuit.run ctx values = .ok outputs ∧
      ScalarSourceReadTape.sourceReadInputs ctx ep.effectGuards ep.effects.zipIdx
        (Impact.publicInputReadCount ep.circuit.inputs) (outputs ++ values, initial) =
        .ok (records, (finalEnv, next)) ∧
      CanonicalInputs sourceEntry.circuit values base ∧
      Impact.lower state ep = .ok plan ∧
      GenericStateInputValues.decodeReads
        (plan.reads.drop (Impact.publicInputReadCount ep.circuit.inputs)) seed = .ok readValues ∧
      GuardedPlanExecution.evalPlan ctx ((outputs ++ values) ++ readValues) plan = .ok operations ∧
      NativeState.run operations (GenericStateEncoding.initial slots) =
        some ⟨[.vector finalSlots], finalReads⟩ ∧
      GenericStateEncoding.encodeState state next = some finalSlots ∧
      GuardedScalarWitness.buildSourceCall ctx hash state sourceEntry values initial bytes rewrites =
        (GuardedScalarWitness.build hash seed bytes artifact transcript).map
          (fun built => ⟨artifact, seed, transcript, built⟩) := by
  let ep := Passes.pruneEntrypoint sourceEntry
  have prunedInputs : CanonicalInputs ep.circuit values inputs :=
    ⟨admittedInputs.unique, admittedInputs.declared, admittedInputs.complete, admittedInputs.binding⟩
  obtain ⟨sourceInputs, sourceInputsRun, runtimeInputs⟩ :=
    GuardedScalarWitness.source_inputs_seed_canonical ep values inputs prunedInputs
  let base : Assignment := fun name => (sourceInputs.lookup name).getD zero
  have baseAdmitted : CanonicalInputs sourceEntry.circuit values base :=
    ⟨runtimeInputs.unique, runtimeInputs.declared, runtimeInputs.complete, runtimeInputs.binding⟩
  obtain ⟨plan, _, lowered, _, _, _⟩ :=
    Zkir.lowerEntrypoint_validation_and_instructions_with_rewrites state sourceEntry
      rewrites artifact loweredArtifact
  obtain ⟨outputs, finalEnv, _, records, readValues, finalSlots, finalReads,
    circuit, _, _, recorded, metadata, _, _, decoded, checked, encoded⟩ :=
    source_call_native_trace state sourceEntry plan ctx values result base initial next slots
      baseAdmitted admittedState lowered effects modulus success
  have prunedRun : ep.circuit.run ctx values = .ok outputs := by
    simpa only [ep, Passes.pruneEntrypoint, Passes.pruneCircuit_run] using circuit
  obtain ⟨operations, evaluated, nativeRun⟩ :=
    GuardedScalarCandidateState.run_of_checked_candidates ctx ep plan values
      (seedReadValues base records) slots outputs readValues ⟨[.vector finalSlots], finalReads⟩
      prunedRun decoded checked
  rw [admitted_unshielded_frame state initial slots admittedState] at recorded
  refine ⟨plan, outputs, finalEnv, records, base, readValues, operations, finalSlots, finalReads,
    circuit, recorded, baseAdmitted, lowered, decoded, evaluated, nativeRun, encoded, ?_⟩
  change ScalarSourceReadTape.sourceReadInputs ctx ep.effectGuards ep.effects.zipIdx
    (Impact.publicInputReadCount ep.circuit.inputs) (outputs ++ values, initial) =
    .ok (records, (finalEnv, next)) at recorded
  change (plan.reads.drop (Impact.publicInputReadCount ep.circuit.inputs)).map readMetadata =
    (records.map Prod.fst).map readMetadata at metadata
  change GenericStateInputValues.decodeReads
    (plan.reads.drop (Impact.publicInputReadCount ep.circuit.inputs))
    (seedReadValues base records) = .ok readValues at decoded
  dsimp only [ep, base] at sourceInputsRun recorded metadata decoded
  unfold GuardedScalarWitness.buildSourceCall
  simp only [loweredArtifact, lowered, sourceInputsRun, circuit, recorded,
    List.map_map, metadata, beq_self_eq_true, ite_true,
    base, decoded, evaluated, admittedState.initialEncoded,
    nativeRun, encoded, Except.mapError, Bind.bind, Except.bind, Pure.pure, Except.pure,
    Except.map, GenericStateEncoding.initial]

end Noctium.Verification.GenericStateConverseNativeTrace
