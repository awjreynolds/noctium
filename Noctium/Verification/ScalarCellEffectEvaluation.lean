import Noctium.Verification.GuardedEffectPrefix
import Noctium.Verification.GenericStateEffectValidation
import Noctium.Verification.GenericStatePrefixEnvironment
import Noctium.Verification.GenericStateCaps
import Noctium.Verification.ScalarCellReadDecoding
import Noctium.Verification.ScalarCellSourceReads
import Noctium.Verification.ScalarCellSourcePlanFields
import Noctium.Verification.ScalarLedgerWitnessReadValues
import Noctium.Verification.ScalarLedgerPlanValidation
import Noctium.Verification.ScalarWitnessEntrypointAliases

namespace Noctium.Verification.ScalarCellEffectEvaluation

open Backend NativeRelation ScalarNormalization GenericStateCellAdmission
open GenericStateEffectValidation GenericStatePrefixEnvironment ScalarCellSourceReads
open ScalarWitnessConstruction (round_trip_scalar_read)

/-- Each actual unguarded cell effect appends exactly its own checkable
operation chunk to the incoming plan. -/
theorem cell_chunk (state : List StateDecl) (effect : Effect)
    (admission : ScalarCellEffect state effect) (before next : Impact.Plan)
    (step : Impact.appendEffectWithActivity state effect none before = .ok next) :
    ∃ chunk, Impact.appendEffect state effect {} = .ok chunk ∧
      next.operations = before.operations ++ chunk.operations := by
  cases admission with
  | readCell name destination ty _ _ =>
    exact GuardedEffectPrefix.appendEffectWithActivity_unguarded_readCell_chunk
      state name destination ty before next step
  | writeCell name ty value _ _ =>
    exact GuardedEffectPrefix.appendEffectWithActivity_unguarded_writeCell_chunk
      state name ty value before next step

private theorem cell_trace_operations (state : List StateDecl) (effects : List Effect)
    (start : Nat) (before final : Impact.Plan) (offsets : List Nat)
    (admission : ScalarCellEffects state effects)
    (trace : Impact.GuardedEffectTrace state [] (effects.zipIdx start) before final offsets) :
    ∀ operation ∈ before.operations, operation ∈ final.operations := by
  induction effects generalizing start before offsets with
  | nil =>
    cases trace
    exact fun _ member => member
  | cons effect rest ih =>
    rw [List.zipIdx_cons] at trace
    cases trace with
    | cons step tail =>
      obtain ⟨chunk, _, operations⟩ :=
        cell_chunk state effect (admission effect (by simp)) _ _
          (by simpa using step)
      intro operation member
      apply ih _ _ _ (fun item found => admission item (List.mem_cons_of_mem _ found)) tail
      rw [operations]
      exact List.mem_append_left _ member

/-- The complete candidate environment retains the value of each actual
source read, including its declared type. -/
def ReadCandidates (complete : EvalEnv) (entries : List (Impact.Read × Scalar)) : Prop :=
  ∀ record ∈ entries, ∃ support : ScalarType record.1.ty,
    complete.lookup record.1.name = some (Value.pack record.1.ty
      (GenericStateInputValues.sourceValue support record.2))

private theorem lookup_present_of_key (values : EvalEnv) (name : String)
    (member : name ∈ values.map Prod.fst) : ∃ raw, values.lookup name = some raw := by
  obtain ⟨pair, present, same⟩ := List.mem_map.mp member
  cases lookup : values.lookup name with
  | some raw => exact ⟨raw, rfl⟩
  | none =>
    have different := List.lookup_eq_none_iff.mp lookup pair present
    simp [same] at different

private theorem initial_values_present (entry : Entrypoint) (values outputs : EvalEnv)
    (inputs : Assignment) (admitted : CanonicalInputs entry.circuit values inputs)
    (outputNames : outputs.map Prod.fst = entry.circuit.outputs.map Output.name) :
    ∀ name ty, (initialEffectTypeEnv entry).lookup name = some ty →
      ∃ raw, (outputs ++ values).lookup name = some raw := by
  intro name ty found
  obtain ⟨before, after, equal, _⟩ := List.lookup_eq_some_iff.mp found
  have key : name ∈ (initialEffectTypeEnv entry).map Prod.fst := by
    rw [equal]
    simp
  simp only [initialEffectTypeEnv, List.map_append, List.map_map, Function.comp_def,
    List.mem_append] at key
  rcases key with input | output
  · obtain ⟨declared, member, same⟩ := List.mem_map.mp input
    obtain ⟨value, lookup, _⟩ := admitted.complete declared member
    cases outputLookup : outputs.lookup name with
    | none =>
      refine ⟨Value.pack declared.ty value, ?_⟩
      simpa [List.lookup_append, outputLookup, same] using lookup
    | some raw => exact ⟨raw, by simp [List.lookup_append, outputLookup]⟩
  · rw [← outputNames] at output
    obtain ⟨raw, lookup⟩ := lookup_present_of_key outputs name output
    exact ⟨raw, by simp [List.lookup_append, lookup]⟩

private theorem base_lookup_none (entry : Entrypoint) (values outputs : EvalEnv)
    (inputs : Assignment) (admitted : CanonicalInputs entry.circuit values inputs)
    (outputNames : outputs.map Prod.fst = entry.circuit.outputs.map Output.name)
    (name : String) (fresh : name ∉ (initialEffectTypeEnv entry).map Prod.fst) :
    (outputs ++ values).lookup name = none := by
  apply List.lookup_eq_none_iff.mpr
  intro pair member
  have different : name ≠ pair.1 := by
    intro same
    apply fresh
    simp only [initialEffectTypeEnv, List.map_append, List.map_map, Function.comp_def,
      List.mem_append]
    rcases List.mem_append.mp member with output | input
    · right
      rw [← outputNames]
      exact List.mem_map.mpr ⟨pair, output, same.symm⟩
    · left
      obtain ⟨item, present, key⟩ := admitted.declared pair.1 pair.2 input
      exact List.mem_map.mpr ⟨item, present, key.trans same.symm⟩
  simp [different]

/-- Combine admitted call inputs and recorded source reads into the value
environment used to evaluate production ledger fields. -/
theorem call_candidate_scope (ctx : EvalContext) (entry : Entrypoint)
    (values outputs readValues : EvalEnv) (inputs : Assignment)
    (reads : List Impact.Read) (entries : List (Impact.Read × Scalar))
    (admitted : CanonicalInputs entry.circuit values inputs)
    (circuitValid : entry.circuit.validate Capabilities.crypto = .ok ())
    (circuitSuccess : entry.circuit.run ctx values = .ok outputs)
    (metadata : reads.map GenericStateCheckedReadTrace.readMetadata =
      (entries.map Prod.fst).map GenericStateCheckedReadTrace.readMetadata)
    (canonical : ∀ record ∈ entries, CanonicalReadRecord record)
    (distinct : (reads.map (·.name)).Nodup)
    (fresh : ∀ read ∈ reads, read.name ∉ (initialEffectTypeEnv entry).map Prod.fst)
    (decoded : GenericStateInputValues.decodeReads reads
      (ScalarCellWitnessReadSeed.seedReadValues inputs entries) = .ok readValues) :
    let complete := (outputs ++ values) ++ readValues
    AgreesOnTypes (initialEffectTypeEnv entry) (outputs ++ values) complete ∧
      (∀ input ∈ entry.circuit.inputs, complete.lookup input.name = values.lookup input.name) ∧
      ReadCandidates complete entries := by
  let complete := (outputs ++ values) ++ readValues
  have outputNames := ScalarWitnessConstruction.evalOutputs_names ctx values entry.circuit.outputs
    outputs (circuit_run_steps ctx entry.circuit values outputs circuitSuccess).2
  have present := initial_values_present entry values outputs inputs admitted outputNames
  have baseAgrees := initial_agreement (initialEffectTypeEnv entry) (outputs ++ values) readValues present
  have unshadowed :=
    (GenericStateAliases.validated_output_scope Capabilities.crypto entry.circuit circuitValid).2
  have outputUnused := GenericStateAliases.canonicalInputs_output_unused_of_scope
    entry.circuit values inputs admitted unshadowed
  have inputLookups : ∀ input ∈ entry.circuit.inputs,
      complete.lookup input.name = values.lookup input.name := by
    intro input member
    obtain ⟨value, found, _⟩ := admitted.complete input member
    have noOutput : outputs.lookup input.name = none := by
      apply List.lookup_eq_none_iff.mpr
      intro pair pairMember
      have different : input.name ≠ pair.1 := by
        intro same
        have hasKey : input.name ∈ outputs.map Prod.fst :=
          List.mem_map.mpr ⟨pair, pairMember, same.symm⟩
        rw [outputNames] at hasKey
        obtain ⟨output, present, nameEq⟩ := List.mem_map.mp hasKey
        have unused := outputUnused output present
        rw [nameEq, found] at unused
        cases unused
      simp [different]
    simp [complete, List.lookup_append, noOutput, found]
  obtain ⟨actual, success, _, candidates⟩ :=
    ScalarCellReadDecoding.decode_seeded_source_cell_reads reads inputs entries metadata canonical distinct
  have actualEq := Except.ok.inj (success.symm.trans decoded)
  subst actual
  refine ⟨baseAgrees, inputLookups, ?_⟩
  intro record member
  have metadataMember : GenericStateCheckedReadTrace.readMetadata record.1 ∈
      reads.map GenericStateCheckedReadTrace.readMetadata := by
    rw [metadata]
    exact List.mem_map_of_mem (List.mem_map_of_mem member)
  obtain ⟨read, readMember, equal⟩ := List.mem_map.mp metadataMember
  have sameName : read.name = record.1.name := congrArg Prod.fst equal
  have baseAbsent := base_lookup_none entry values outputs inputs admitted outputNames
    record.1.name (by rw [← sameName]; exact fresh read readMember)
  obtain ⟨support, _, found⟩ := candidates record member
  refine ⟨support, ?_⟩
  change ((outputs ++ values) ++ readValues).lookup record.1.name = _
  rw [List.lookup_append, baseAbsent]
  exact found

private theorem source_read_binding (ctx : EvalContext) (state : List StateDecl)
    (name destination : String) (ty : Ty) (before after : Frame) (ordinal : Nat)
    (admission : ScalarCellEffect state (.readCell name destination ty))
    (modulus : ctx.modulus = Field.modulus)
    (step : SourceEffects.step ctx (.readCell name destination ty) before = .ok after)
    (complete : EvalEnv)
    (candidates : ReadCandidates complete (effectEntries (.readCell name destination ty) ordinal after)) :
    ∃ value : ty.Denote, after = ((destination, Value.pack ty value) :: before.1, before.2) ∧
      complete.lookup destination = some (Value.pack ty value) := by
  obtain ⟨found, _, foundCanonical, frame⟩ := readCell_step_value ctx before.1 before.2
    state name destination ty admission after modulus step
  have member : ({name := destination, ty}, scalar (valueNumber (Value.pack ty found))) ∈
      effectEntries (.readCell name destination ty) ordinal after := by
    rw [frame]
    simp [effectEntries]
  obtain ⟨support, candidate⟩ := candidates _ member
  have packedNumber := valueNumber_pack_scalar ty found support
  refine ⟨found, frame, ?_⟩
  change complete.lookup destination =
    some (Value.pack ty (GenericStateInputValues.sourceValue support
      (scalar (valueNumber (Value.pack ty found))))) at candidate
  rw [packedNumber, round_trip_scalar_read support found foundCanonical] at candidate
  exact candidate

theorem cell_scope_step (ctx : EvalContext) (state : List StateDecl)
    (effect : Effect) (before after : Frame) (ordinal : Nat) (types nextTypes : TypeEnv)
    (admission : ScalarCellEffect state effect) (operand : ScalarCellOperand effect)
    (modulus : ctx.modulus = Field.modulus)
    (step : SourceEffects.step ctx effect before = .ok after)
    (validated : EffectValidation state types effect nextTypes)
    (complete : EvalEnv) (agrees : AgreesOnTypes types before.1 complete)
    (candidates : ReadCandidates complete (effectEntries effect ordinal after)) :
    AgreesOnTypes nextTypes after.1 complete ∧
      (∀ name destination ty, effect = .readCell name destination ty →
        complete.lookup destination = after.1.lookup destination) := by
  cases admission with
  | readCell name destination ty cell declaration =>
    cases validated with
    | readCell _ fresh =>
      obtain ⟨value, frame, candidate⟩ := source_read_binding ctx state name destination ty
        before after ordinal (.readCell name destination ty cell declaration)
        modulus step complete candidates
      subst after
      refine ⟨extend_read types before.1 complete destination ty
        (Value.pack ty value) agrees fresh candidate, ?_⟩
      intro foundName foundDestination foundType equal
      cases equal
      simpa using candidate
  | writeCell name ty expression cell declaration =>
    cases validated with
    | writeCell _ _ =>
      obtain ⟨_, _, _, _, _, frame⟩ := writeCell_step_value ctx before.1 before.2 state
        name ty expression (.writeCell name ty expression cell declaration) operand after modulus step
      subst after
      exact ⟨agrees, by intro _ _ _ impossible; cases impossible⟩

private def FieldsEvaluate (ctx : EvalContext) (values : EvalEnv) (operations : List Impact.Op) : Prop :=
  ∀ operation ∈ operations, ∀ fields ∈ operation.fieldGroups,
    ∀ field ∈ fields, ∃ value, field.eval ctx values = .ok value

private def FieldsValid (types : TypeEnv) (operations : List Impact.Op) : Prop :=
  ∀ operation ∈ operations, ∀ fields ∈ operation.fieldGroups,
    ∀ field ∈ fields, field.validate Capabilities.crypto types = .ok ()

/-- Follow the production operation chunks and the successful source steps
together. The validator's scope at each step bounds references to source
values already present at that point, including the step's own read. -/
private theorem cell_fields_fold (ctx : EvalContext) (state : List StateDecl)
    (effects : List Effect) (start ordinal : Nat)
    (prePlan plan : Impact.Plan) (offsets : List Nat) (planTypes types finalTypes : TypeEnv)
    (before after : Frame) (entries : List (Impact.Read × Scalar)) (complete : EvalEnv)
    (modulus : ctx.modulus = Field.modulus)
    (admission : ScalarCellEffects state effects)
    (operands : ∀ effect ∈ effects, ScalarCellOperand effect)
    (trace : Impact.GuardedEffectTrace state [] (effects.zipIdx start) prePlan plan offsets)
    (validated : ValidatedEffects state types effects finalTypes)
    (source : sourceReadInputs ctx effects ordinal before = .ok (entries, after))
    (candidates : ReadCandidates complete entries) (agrees : AgreesOnTypes types before.1 complete)
    (fieldsValid : FieldsValid planTypes plan.operations)
    (prefixEvaluates : FieldsEvaluate ctx complete prePlan.operations) :
    FieldsEvaluate ctx complete plan.operations ∧ AgreesOnTypes finalTypes after.1 complete := by
  induction effects generalizing start ordinal prePlan offsets types finalTypes before after entries with
  | nil =>
    cases trace
    cases validated
    simp only [sourceReadInputs, Except.ok.injEq, Prod.mk.injEq] at source
    rcases source with ⟨_, rfl⟩
    exact ⟨prefixEvaluates, agrees⟩
  | cons effect rest ih =>
    rw [List.zipIdx_cons] at trace
    cases trace with
    | @cons _ _ old next _ nextOffsets step tail =>
      have effectScope := admission effect (by simp)
      have operand := operands effect (by simp)
      have restScope : ScalarCellEffects state rest :=
        fun item member => admission item (List.mem_cons_of_mem _ member)
      have restOperands : ∀ item ∈ rest, ScalarCellOperand item :=
        fun item member => operands item (List.mem_cons_of_mem _ member)
      obtain ⟨chunk, chunkAccepted, operations⟩ :=
        cell_chunk state effect effectScope prePlan next (by simpa using step)
      obtain ⟨middle, readTail, sourceStep, tailSource, records⟩ :=
        sourceReadInputs_cons ctx effect rest ordinal before after entries source
      obtain ⟨nextTypes, localValid, tailValid⟩ := ValidatedEffects.uncons validated
      have headCandidates : ReadCandidates complete (effectEntries effect ordinal middle) := by
        intro record member
        apply candidates record
        rw [records]
        exact List.mem_append_left _ member
      obtain ⟨nextAgreement, readBinding⟩ := cell_scope_step ctx state effect before middle
        ordinal types nextTypes effectScope operand modulus sourceStep localValid complete agrees headCandidates
      have chunkValid : FieldsValid planTypes chunk.operations := by
        intro operation present
        apply fieldsValid operation
        apply cell_trace_operations state rest (start + 1) next plan nextOffsets restScope tail
        rw [operations]
        exact List.mem_append_right _ present
      obtain ⟨suffix, eqOperations, suffixEvaluates⟩ :=
        ScalarWitnessConstruction.append_cell_effect_group_fields_eval ctx state effect effectScope
          operand {} chunk planTypes types nextTypes chunkAccepted before middle modulus sourceStep
          localValid complete agrees readBinding (by simp) chunkValid
      have chunkEvaluated : FieldsEvaluate ctx complete chunk.operations := by
        rw [eqOperations]
        exact suffixEvaluates
      have nextPrefix : FieldsEvaluate ctx complete next.operations := by
        intro operation present
        rw [operations] at present
        rcases List.mem_append.mp present with member | member
        · exact prefixEvaluates operation member
        · exact chunkEvaluated operation member
      have tailCandidates : ReadCandidates complete readTail := by
        intro record member
        apply candidates record
        rw [records]
        exact List.mem_append_right _ member
      exact ih (start + 1) (ordinal + (effectEntries effect ordinal middle).length)
        next nextOffsets nextTypes finalTypes middle after readTail restScope restOperands tail
        tailValid tailSource tailCandidates nextAgreement nextPrefix

/-- Recover the real input prefix, compiled effect steps and their source
scope from the accepted plan and a successful decoded source read tape. -/
theorem lower_cell_evaluation_scope (ctx : EvalContext) (state : List StateDecl)
    (entry : Entrypoint) (plan : Impact.Plan) (values outputs readValues : EvalEnv)
    (inputs : Assignment) (before after : Frame) (entries : List (Impact.Read × Scalar))
    (baseShape : before.1 = outputs ++ values)
    (accepted : Impact.lower state (Passes.pruneEntrypoint entry) = .ok plan)
    (unguarded : entry.effectGuards = [])
    (admission : ScalarCellEffects state entry.effects)
    (inputAdmission : CanonicalInputs entry.circuit values inputs)
    (circuit : entry.circuit.run ctx values = .ok outputs)
    (source : sourceReadInputs ctx entry.effects
      (Impact.publicInputReadCount entry.circuit.inputs) before = .ok (entries, after))
    (metadata : (plan.reads.drop (Impact.publicInputReadCount entry.circuit.inputs)).map
        GenericStateCheckedReadTrace.readMetadata =
      (entries.map Prod.fst).map GenericStateCheckedReadTrace.readMetadata)
    (canonical : ∀ record ∈ entries, CanonicalReadRecord record)
    (decoded : GenericStateInputValues.decodeReads
      (plan.reads.drop (Impact.publicInputReadCount entry.circuit.inputs))
      (ScalarCellWitnessReadSeed.seedReadValues inputs entries) = .ok readValues) :
    let complete := (outputs ++ values) ++ readValues
    ∃ offsets inputPlan finalTypes,
      Impact.publicInputPlan entry.circuit.inputs {} = .ok inputPlan ∧
      Impact.GuardedEffectTrace state [] entry.effects.zipIdx inputPlan plan offsets ∧
      ValidatedEffects state (initialEffectTypeEnv (Passes.pruneEntrypoint entry))
        entry.effects finalTypes ∧
      AgreesOnTypes (initialEffectTypeEnv (Passes.pruneEntrypoint entry)) before.1 complete ∧
      (∀ input ∈ entry.circuit.inputs, complete.lookup input.name = values.lookup input.name) ∧
      ReadCandidates complete entries := by
  let ep := Passes.pruneEntrypoint entry
  have validatedCircuit := lower_circuit_validated_source state ep plan accepted
  have circuitCrypto : entry.circuit.validate Capabilities.crypto = .ok () := by
    rw [GenericStateCaps.circuit_validate_source_crypto] at validatedCircuit
    simpa only [ep, Passes.pruneEntrypoint, Passes.pruneCircuit_validate] using validatedCircuit
  obtain ⟨distinct, fresh⟩ := ScalarCellWitnessReadSeed.lower_source_cell_read_names
    state entry plan entries before after ctx admission accepted metadata source
  obtain ⟨baseAgrees, inputLookups, candidates⟩ := call_candidate_scope ctx entry values outputs
    readValues inputs _ entries inputAdmission circuitCrypto circuit metadata canonical distinct fresh decoded
  obtain ⟨offsets, inputPlan, _, inputAccepted, trace⟩ :=
    GenericStateAdmissionPrefix.lower_guarded_effect_trace state ep plan accepted
  have unconditional : Impact.GuardedEffectTrace state [] entry.effects.zipIdx inputPlan plan offsets := by
    simpa only [ep, Passes.pruneEntrypoint, unguarded] using trace
  obtain ⟨finalTypes, validated⟩ := lower_validated_effects state ep plan accepted
    (ScalarCellWitnessReadSeed.scalarStateEffects_of_cells state entry.effects admission)
  have baseAgreement : AgreesOnTypes (initialEffectTypeEnv ep) before.1
      ((outputs ++ values) ++ readValues) := by
    rw [baseShape]
    exact baseAgrees
  exact ⟨offsets, inputPlan, finalTypes, inputAccepted, unconditional, validated,
    baseAgreement, inputLookups, candidates⟩

/-- Apply the source-step fold to the exact accepted plan and its scalar
input prefix. The same complete environment feeds every emitted field. -/
theorem lower_cell_fields_fold (ctx : EvalContext) (state : List StateDecl)
    (entry : Entrypoint) (plan : Impact.Plan) (values outputs readValues : EvalEnv)
    (inputs : Assignment) (before after : Frame) (entries : List (Impact.Read × Scalar))
    (baseShape : before.1 = outputs ++ values)
    (accepted : Impact.lower state (Passes.pruneEntrypoint entry) = .ok plan)
    (unguarded : entry.effectGuards = [])
    (admission : ScalarCellEffects state entry.effects)
    (operands : ∀ effect ∈ entry.effects, ScalarCellOperand effect)
    (inputAdmission : CanonicalInputs entry.circuit values inputs)
    (circuit : entry.circuit.run ctx values = .ok outputs)
    (modulus : ctx.modulus = Field.modulus)
    (source : sourceReadInputs ctx entry.effects
      (Impact.publicInputReadCount entry.circuit.inputs) before = .ok (entries, after))
    (metadata : (plan.reads.drop (Impact.publicInputReadCount entry.circuit.inputs)).map
        GenericStateCheckedReadTrace.readMetadata =
      (entries.map Prod.fst).map GenericStateCheckedReadTrace.readMetadata)
    (canonical : ∀ record ∈ entries, CanonicalReadRecord record)
    (decoded : GenericStateInputValues.decodeReads
      (plan.reads.drop (Impact.publicInputReadCount entry.circuit.inputs))
      (ScalarCellWitnessReadSeed.seedReadValues inputs entries) = .ok readValues)
    (prefixEvaluates : ∀ inputPlan,
      Impact.publicInputPlan entry.circuit.inputs {} = .ok inputPlan →
      (∀ input ∈ entry.circuit.inputs,
        ((outputs ++ values) ++ readValues).lookup input.name = values.lookup input.name) →
      FieldsEvaluate ctx ((outputs ++ values) ++ readValues) inputPlan.operations) :
    FieldsEvaluate ctx ((outputs ++ values) ++ readValues) plan.operations ∧
      ∃ finalTypes, ValidatedEffects state (initialEffectTypeEnv (Passes.pruneEntrypoint entry))
        entry.effects finalTypes ∧ AgreesOnTypes finalTypes after.1 ((outputs ++ values) ++ readValues) := by
  let ep := Passes.pruneEntrypoint entry
  obtain ⟨offsets, inputPlan, finalTypes, inputAccepted, unconditional, validated,
    baseAgreement, inputLookups, candidates⟩ :=
    lower_cell_evaluation_scope ctx state entry plan values outputs readValues inputs before after
      entries baseShape accepted unguarded admission inputAdmission circuit source metadata canonical decoded
  obtain ⟨evaluated, finalAgrees⟩ := cell_fields_fold ctx state entry.effects 0
    (Impact.publicInputReadCount entry.circuit.inputs) inputPlan plan offsets
    (plan.typeEnvironment ep) (initialEffectTypeEnv ep) finalTypes before after entries _
    modulus admission operands unconditional validated source candidates baseAgreement
    (ScalarWitnessConstruction.lower_operation_group_members_validated state ep plan accepted)
    (prefixEvaluates inputPlan inputAccepted inputLookups)
  exact ⟨evaluated, finalTypes, validated, finalAgrees⟩

end Noctium.Verification.ScalarCellEffectEvaluation
