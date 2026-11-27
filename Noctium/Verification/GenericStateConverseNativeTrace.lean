import Noctium.Verification.GenericStateConverseEffectFold
import Noctium.Verification.GenericStateConverseCheckedPlan
import Noctium.Verification.GenericStateConversePublicPrefix
import Noctium.Verification.GuardedScalarWitness
import Noctium.Verification.GuardedVmReadTranscript
import Noctium.Verification.GuardedPlanAssertions

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
      (∀ input ∈ sourceEntry.circuit.inputs,
        seed ("%input_" ++ input.name) = base ("%input_" ++ input.name)) ∧
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
    circuit, _, _, recorded, metadata, _, preserved, decoded, checked, encoded⟩ :=
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
    circuit, recorded, baseAdmitted, preserved, lowered, decoded, evaluated, nativeRun, encoded, ?_⟩
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

private theorem expected_scalar_input_source (state : List StateDecl)
    (ep : Entrypoint) (plan : Impact.Plan) (shape : Native.Expected)
    (values : EvalEnv) (base : Assignment)
    (admitted : CanonicalInputs ep.circuit values base)
    (lowered : Impact.lower state ep = .ok plan)
    (expected : Native.expectedEntrypoint state ep = .ok shape)
    (effects : ∀ effect ∈ ep.effects, ScalarEffect state effect) :
    ∀ requirement ∈ shape.rawInputs ++ shape.inputs, ∃ name,
      requirement.identifier = "%input_" ++ name ∧
      name ∈ ep.circuit.inputs.map (·.name) ++
        (plan.reads.drop (Impact.publicInputReadCount ep.circuit.inputs)).map (·.name) := by
  let reads := plan.reads.drop (Impact.publicInputReadCount ep.circuit.inputs)
  have initialName (input : Input) (present : input ∈ ep.circuit.inputs)
      (requirement : Native.InputRequirement)
      (ordinary : requirement ∈ Native.Input.requirements input ∨
        requirement ∈ Native.Input.callArgumentRequirements input) :
      requirement.identifier = "%input_" ++ input.name := by
    obtain ⟨_, _, canonical⟩ := admitted.complete input present
    obtain ⟨supported⟩ := GenericStateWriteEvaluation.scalarType_of_canonical canonical
    cases input with
    | mk name ty visibility span =>
      change ScalarType ty at supported
      cases supported <;>
        simp only [Native.Input.requirements, Native.Input.callArgumentRequirements,
          List.mem_singleton, or_self] at ordinary <;>
        cases ordinary <;> rfl
  intro requirement present
  rcases List.mem_append.mp present with raw | body
  · rw [GenericStateCircuitParts.expectedEntrypoint_rawInputs state ep shape expected] at raw
    obtain ⟨input, argMember, presentInSource⟩ := List.mem_flatMap.mp raw
    obtain ⟨_, _, found⟩ := List.mem_filterMap.mp argMember
    have inputPresent := List.mem_of_find?_eq_some found
    exact ⟨input.name, initialName input inputPresent requirement (.inr presentInSource),
      List.mem_append_left _ (List.mem_map_of_mem inputPresent)⟩
  · let core := GenericStateCircuitParts.inputRequirementCore
    have included : core requirement ∈ shape.inputs.map core := List.mem_map_of_mem body
    rw [GenericStateCircuitParts.expectedEntrypoint_inputRequirementCoreMap
      state ep shape plan expected lowered] at included
    obtain ⟨source, sourcePresent, equal⟩ := List.mem_map.mp included
    have identifier : source.identifier = requirement.identifier := congrArg Prod.fst equal
    rcases List.mem_append.mp sourcePresent with circuit | ledger
    · obtain ⟨input, filterPresent, presentInSource⟩ := List.mem_flatMap.mp circuit
      have inputPresent := (List.mem_filter.mp filterPresent).1
      exact ⟨input.name, identifier.symm.trans (initialName input inputPresent source (.inl presentInSource)),
        List.mem_append_left _ (List.mem_map_of_mem inputPresent)⟩
    · obtain ⟨readSpec, readPresent, presentInSource⟩ := List.mem_flatMap.mp ledger
      obtain ⟨⟨name, ty⟩, binding, sourceEq⟩ := List.mem_map.mp presentInSource
      have plain := (ScalarGuardedReadAdmission.lower_read_admission state ep plan lowered effects).1
        readSpec readPresent
      have singleton := GenericStateCheckedReadDecode.supported_plain_read_bindings
        readSpec plain.1 plain.2.1
      rw [singleton] at binding
      cases List.mem_singleton.mp binding
      refine ⟨readSpec.name, identifier.symm.trans ?_,
        List.mem_append_right _ (List.mem_map_of_mem (l := reads) readPresent)⟩
      rw [← sourceEq]
      cases readSpec.ty <;> rfl

/-- A satisfying extension of the source read seed also consumes the transcript
from the actual source and native executions. The source witness builder
therefore succeeds without a separate transcript acceptance premise. -/
theorem source_call_build_of_satisfying_extension (state : List StateDecl)
    (sourceEntry : Entrypoint) (ctx : EvalContext) (hash : Hash)
    (implementation : HashAgreement ctx hash)
    (values result : EvalEnv)
    (initial next : LedgerState) (slots : List Slot) (bytes : ArtifactBytes.Bytes)
    (rewrites : Zkir.Rewrites) (json : Lean.Json)
    (view : GuardedZkirArtifact.View)
    (inputTypes : ∀ input ∈ sourceEntry.circuit.inputs, Nonempty (ScalarType input.ty))
    (admittedState : GenericStateEncoding.AdmittedState state initial slots)
    (emitted : Zkir.lowerEntrypoint state sourceEntry rewrites = .ok json)
    (parsed : (ArtifactBytes.parse bytes).map Lean.Json.compress = .ok json.compress)
    (artifact : GuardedZkirArtifact.check bytes json = .ok view.rows)
    (pinned : GuardedZkirArtifact.decodeView json = .ok view)
    (admitted : ScalarCircuitAdmission sourceEntry.circuit)
    (effects : ∀ effect ∈ sourceEntry.effects, ScalarEffect state effect)
    (guards : ∀ (condition : Expr .bool), some condition ∈ sourceEntry.effectGuards →
      ScalarExpression condition)
    (success : sourceEntry.run ctx values initial = .ok (result, next))
    (extension : ∀ plan outputs finalEnv records base,
      Impact.lower state (Passes.pruneEntrypoint sourceEntry) = .ok plan →
      sourceEntry.circuit.run ctx values = .ok outputs →
      ScalarSourceReadTape.sourceReadInputs ctx sourceEntry.effectGuards sourceEntry.effects.zipIdx
        (Impact.publicInputReadCount sourceEntry.circuit.inputs) (outputs ++ values, initial) =
          .ok (records, (finalEnv, next)) →
      CanonicalInputs sourceEntry.circuit values base →
      let seed := seedReadValues base records
      ∃ target,
        (∀ row ∈ view.rows, GuardedImpactTranscript.ordinaryHolds hash target row) ∧
        ∀ name ∈ sourceEntry.circuit.inputs.map (·.name) ++
          (plan.reads.drop (Impact.publicInputReadCount sourceEntry.circuit.inputs)).map (·.name),
          target ("%input_" ++ name) = seed ("%input_" ++ name)) :
    ∃ built,
      GuardedScalarWitness.buildSourceCall ctx hash state sourceEntry values initial bytes rewrites =
        .ok built := by
  obtain ⟨sourceOutputs, _, _, sourceCircuit, _, _, _⟩ :=
    ScalarLedgerWitnessSource.entrypoint_run_steps ctx sourceEntry values result initial next success
  obtain ⟨inputs, admittedInputs⟩ := canonicalInputs_of_run ctx sourceEntry.circuit values
    sourceOutputs implementation.modulus inputTypes sourceCircuit
  obtain ⟨plan, outputs, finalEnv, records, base, readValues, operations, finalSlots, finalReads,
    circuit, recorded, baseAdmitted, preserved, lowered, decoded, evaluated, nativeRun, _, build⟩ :=
    source_call_build_reduces_to_artifact state sourceEntry ctx hash values result inputs initial
      next slots bytes rewrites json admittedInputs admittedState emitted effects implementation.modulus success
  obtain ⟨target, ordinary, sourceAgreement⟩ :=
    extension plan outputs finalEnv records base lowered circuit recorded baseAdmitted
  let seed := seedReadValues base records
  have targetInputs : CanonicalInputs sourceEntry.circuit values target := by
    refine ⟨baseAdmitted.unique, baseAdmitted.declared, baseAdmitted.complete, ?_⟩
    intro input present value lookup canonical
    have agrees := sourceAgreement input.name
      (List.mem_append_left _ (List.mem_map_of_mem present))
    rw [agrees, preserved input present]
    exact baseAdmitted.binding input present value lookup canonical
  have targetDecoded : GenericStateInputValues.decodeReads
      (plan.reads.drop (Impact.publicInputReadCount sourceEntry.circuit.inputs)) target =
        .ok readValues :=
    (GenericStateInputValues.decodeReads_agree_on _ seed target
      (fun descriptor present => sourceAgreement descriptor.name
        (List.mem_append_right _ (List.mem_map_of_mem present)))).trans decoded
  let final : NativeState.Machine := ⟨[.vector finalSlots], finalReads⟩
  have checked : GuardedScalarCandidateState.runCheckedCandidates ctx sourceEntry plan
      values target slots = some final := by
    simpa [GuardedScalarCandidateState.runCheckedCandidates, circuit, targetDecoded, evaluated,
      Except.toOption, GenericStateEncoding.initial, final, -List.append_assoc] using nativeRun
  obtain ⟨_, shape, _, expectedAccepted, _, _⟩ :=
    Zkir.lowerEntrypoint_validation_and_instructions_with_rewrites state sourceEntry rewrites
      json emitted
  have schema := (GuardedScalarCandidateSchedule.lower_checked_guarded_source_frame
    state sourceEntry rewrites shape plan ctx hash implementation values target bytes json view.rows
    emitted artifact ordinary lowered expectedAccepted targetInputs admitted effects).2.1
  have scalarGuards := GuardedPlanAssertions.lower_plan_guards_scalar state
    (Passes.pruneEntrypoint sourceEntry) plan lowered effects guards
  have guardAdmission : plan.guards.all
      (fun guard => (ScalarExpressionAdmission.certify guard).isSome) = _root_.Bool.true :=
    List.all_eq_true.mpr (fun condition present =>
      ScalarExpressionAdmission.certify_complete (scalarGuards condition present))
  obtain ⟨_, actualOutputs, actualReads, actualOps, observations, actualCircuit, actualDecoded,
    actualEvaluated, _, _, _, consumed⟩ :=
    GuardedVmReadTranscript.lower_checked_guarded_statement_consumes
      state sourceEntry rewrites shape plan ctx hash implementation values target bytes json view.rows
      slots final emitted artifact ordinary lowered expectedAccepted targetInputs admitted effects
      guards guardAdmission checked
  have sameOutputs := Except.ok.inj (actualCircuit.symm.trans circuit)
  subst actualOutputs
  have sameReads := Except.ok.inj (actualDecoded.symm.trans targetDecoded)
  subst actualReads
  have sameOps := Except.ok.inj (actualEvaluated.symm.trans evaluated)
  subst actualOps
  have prunedBase :
      CanonicalInputs (Passes.pruneEntrypoint sourceEntry).circuit values base :=
    ⟨baseAdmitted.unique, baseAdmitted.declared, baseAdmitted.complete, baseAdmitted.binding⟩
  have inputSources := expected_scalar_input_source state (Passes.pruneEntrypoint sourceEntry)
    plan shape values base prunedBase lowered expectedAccepted effects
  have inputAgreement : ∀ requirement ∈ shape.rawInputs ++ shape.inputs,
      seed requirement.identifier = target requirement.identifier := by
    intro requirement required
    obtain ⟨name, identifier, present⟩ := inputSources requirement required
    rw [identifier]
    exact (sourceAgreement name present).symm
  obtain ⟨rawRows, raw, _⟩ := GuardedZkirArtifact.decodeView_rows pinned
  obtain ⟨_, built, _, assembled, _, _⟩ := GuardedScalarWitness.build_of_lowered_scalar_artifact
    hash seed target state sourceEntry rewrites shape json bytes
    ⟨operations.flatMap ImpactStatementScalar.opFields, finalReads.map Cell.value⟩ view rawRows
    emitted expectedAccepted schema parsed artifact pinned raw inputAgreement
    (fun _ present => ordinary _ present) observations consumed
  rw [build, assembled]
  exact ⟨_, rfl⟩


/-- The source and VM trace supply the seed, and the assembler supplies the
candidate values. Only constraints left after the deterministic SSA equations
need an independent proof about that candidate. -/
theorem source_call_build_of_remaining_constraints (state : List StateDecl)
    (sourceEntry : Entrypoint) (ctx : EvalContext) (hash : Hash)
    (implementation : HashAgreement ctx hash)
    (values result : EvalEnv)
    (initial next : LedgerState) (slots : List Slot) (bytes : ArtifactBytes.Bytes)
    (rewrites : Zkir.Rewrites) (json : Lean.Json)
    (view : GuardedZkirArtifact.View) (rawRows : Array Lean.Json)
    (inputTypes : ∀ input ∈ sourceEntry.circuit.inputs, Nonempty (ScalarType input.ty))
    (admittedState : GenericStateEncoding.AdmittedState state initial slots)
    (emitted : Zkir.lowerEntrypoint state sourceEntry rewrites = .ok json)
    (parsed : (ArtifactBytes.parse bytes).map Lean.Json.compress = .ok json.compress)
    (artifact : GuardedZkirArtifact.check bytes json = .ok view.rows)
    (pinned : GuardedZkirArtifact.decodeView json = .ok view)
    (raw : Native.arrayField json "instructions" = .ok rawRows)
    (admitted : ScalarCircuitAdmission sourceEntry.circuit)
    (effects : ∀ effect ∈ sourceEntry.effects, ScalarEffect state effect)
    (guards : ∀ (condition : Expr .bool), some condition ∈ sourceEntry.effectGuards →
      ScalarExpression condition)
    (success : sourceEntry.run ctx values initial = .ok (result, next))
    (remaining : ∀ outputs finalEnv records base,
      sourceEntry.circuit.run ctx values = .ok outputs →
      ScalarSourceReadTape.sourceReadInputs ctx sourceEntry.effectGuards sourceEntry.effects.zipIdx
        (Impact.publicInputReadCount sourceEntry.circuit.inputs) (outputs ++ values, initial) =
          .ok (records, (finalEnv, next)) →
      CanonicalInputs sourceEntry.circuit values base →
      ∀ candidate, GuardedScalarWitnessAssembly.assemble hash (seedReadValues base records)
          view.header.arguments rawRows.toList view.rows = .ok candidate →
        ∀ pair ∈ rawRows.toList.zip view.rows,
          GuardedScalarWitnessAssembly.RemainingConstraint hash candidate.val pair.1 pair.2) :
    ∃ built,
      GuardedScalarWitness.buildSourceCall ctx hash state sourceEntry values initial bytes rewrites =
        .ok built := by
  apply source_call_build_of_satisfying_extension state sourceEntry ctx hash implementation
    values result initial next slots bytes rewrites json view inputTypes admittedState emitted
    parsed artifact pinned admitted effects guards success
  intro plan outputs finalEnv records base lowered circuit recorded baseAdmitted
  let ep := Passes.pruneEntrypoint sourceEntry
  obtain ⟨_, shape, _, shapeAccepted, _, _⟩ :=
    Zkir.lowerEntrypoint_validation_and_instructions_with_rewrites state sourceEntry rewrites
      json emitted
  obtain ⟨scalarSchema, sourceLanes⟩ := GuardedScalarWitness.lowered_scalar_descriptor_scope
    state ep plan shape lowered shapeAccepted effects inputTypes
  obtain ⟨target, ordinary, frame⟩ := GuardedScalarWitness.assemble_of_lowered_scalar_constraints
    hash (seedReadValues base records) state sourceEntry rewrites shape json view rawRows emitted
    shapeAccepted scalarSchema pinned raw (remaining outputs finalEnv records base circuit recorded baseAdmitted)
  refine ⟨target, ordinary, ?_⟩
  intro name present
  exact frame _ (sourceLanes name present)

end Noctium.Verification.GenericStateConverseNativeTrace
