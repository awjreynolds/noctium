import Noctium.Verification.GuardedScalarCandidateTranscript
import Noctium.Verification.GuardedSourceReadTranscript
import Noctium.Verification.GuardedVmPublicPrefix
import Noctium.Verification.GuardedEffectReadTape
import Noctium.Verification.GuardedEffectReadValues
import Noctium.Verification.GuardedVmReadObservations

namespace Noctium.Verification.GuardedVmReadTranscript

open Lean Backend NativeRelation ScalarNormalization
open GenericStateCircuitParts
open GenericStateInputValues (decodeReads)
open GuardedImpactObservation GuardedImpactTranscript GuardedInputTranscript
open GuardedScalarInput GuardedSourceReadTranscript GuardedStatementConsumption
open GuardedScalarCandidateState (runCheckedCandidates)
open ScalarGuardedPlanAdmission (ScalarEffect)
open GuardedEffectReadTape GuardedVmReadObservations GenericStateCheckedReadTrace

private theorem activeReadValues_append (before after : List ReadObservation) :
    activeReadValues (before ++ after) =
      activeReadValues before ++ activeReadValues after := by
  induction before with
  | nil => rfl
  | cons row rest ih =>
    by_cases active : row.guard = one <;> simp [activeReadValues, active, ih]

private theorem expectedCells_append (prefixOps suffixOps : List NativeState.Op) :
    NativeStateReadTape.expectedCells (prefixOps ++ suffixOps) =
      NativeStateReadTape.expectedCells prefixOps ++ NativeStateReadTape.expectedCells suffixOps := by
  simp only [NativeStateReadTape.expectedCells, List.filterMap_append]

private theorem except_bind_ok {α β : Type} {first : Except ε α}
    {next : α → Except ε β} {result : β} :
    (first >>= next) = .ok result ↔
      ∃ value, first = .ok value ∧ next value = .ok result := by
  cases first <;> simp [Bind.bind, Except.bind]

private theorem evaluate_effect_read_tape
    (ctx : EvalContext) (assignment : Assignment) (values : EvalEnv)
    (modulus : ctx.modulus = Field.modulus)
    {state : List StateDecl} {guards : List (Option (Expr .bool))}
    {items : List (Effect × Nat)} {initial result : Impact.Plan}
    {offsets : List Nat} {chunks : List (List Impact.Op)}
    {descriptorChunks : List (List Impact.Read)}
    {groups : List (Option _root_.Bool × List NativeState.Op)}
    (compiled : GuardedEffectReadChunkTrace state guards items initial result offsets chunks
      descriptorChunks)
    (supported : ∀ item ∈ items, ScalarEffect state item.1)
    (evaluated : (items.zip chunks).mapM (fun (item, chunk) =>
      GuardedPlanExecution.evalChunk ctx values (guards[item.2]?.getD none) chunk) = .ok groups)
    (bound : ∀ descriptor ∈ descriptorChunks.flatten,
      ∃ value : descriptor.ty.Denote,
        values.lookup descriptor.name = some (Value.pack descriptor.ty value) ∧
        Canonical descriptor.ty value ∧
        sourceScalar? descriptor.ty value = some (assignment ("%input_" ++ descriptor.name)))
    (assertions : ∀ guard ∈ result.guards, guard.eval ctx values = .ok _root_.Bool.true) :
    ∃ observed,
      evaluateReadObservations ctx assignment values descriptorChunks.flatten = .ok observed ∧
      (NativeStateReadTape.expectedCells (groups.map Prod.snd).flatten).map NativeState.Cell.value =
        activeReadValues observed := by
  induction compiled generalizing groups with
  | nil initial =>
    cases evaluated
    exact ⟨[], rfl, rfl⟩
  | @cons item rest before next result offsets chunk chunks descriptors descriptorChunks
      step operations _readSuffix metadata readGuards guardSuffix tail ih =>
    let guard := guards[item.2]?.getD none
    simp only [List.zip_cons_cons, List.mapM_cons, except_bind_ok] at evaluated
    obtain ⟨⟨activity, nativeChunk⟩, headEval, tailGroups, tailEval, groupsEq⟩ := evaluated
    cases groupsEq
    have kept := GuardedEffectReadTape.guard_subset tail
    have headAssertions : ∀ expression ∈ GuardedPlanAssertions.guardedEffectAssertionChunk
        guard item.1 before.reads.length, expression.eval ctx values = .ok _root_.Bool.true := by
      intro expression present
      apply assertions expression
      apply kept
      rw [guardSuffix]
      exact List.mem_append_right _ present
    obtain ⟨firstObservations, firstObserved, headTape⟩ :=
      GuardedEffectReadValues.evaluated_chunk_reads ctx assignment values modulus
        state item.1 guard before next chunk descriptors activity nativeChunk
        (supported item (by simp)) step operations metadata readGuards
        (fun descriptor present =>
          bound descriptor (List.mem_append_left _ present))
        headAssertions headEval
    obtain ⟨tailObservations, restObserved, restTape⟩ :=
      ih (fun later present => supported later (List.mem_cons_of_mem _ present))
        tailEval (fun descriptor present => bound descriptor (List.mem_append_right _ present))
        assertions
    refine ⟨firstObservations ++ tailObservations, ?_, ?_⟩
    · rw [List.flatten_cons]
      unfold evaluateReadObservations at firstObserved restObserved ⊢
      rw [List.mapM_append, firstObserved, restObserved]
      rfl
    · rw [List.map_cons, List.flatten_cons, expectedCells_append, List.map_append,
        headTape, restTape, activeReadValues_append]

/-- An accepted scalar VM call consumes the exact guarded artifact statement.
The VM tape is derived from the same ordered source descriptors and guard
evaluations as the artifact rows, including the inactive zero slots. -/
theorem lower_checked_guarded_statement_consumes
    (state : List StateDecl) (sourceEntry : Entrypoint) (rewrites : Zkir.Rewrites)
    (expected : Native.Expected) (plan : Impact.Plan)
    (ctx : EvalContext) (hash : Hash) (implementation : HashAgreement ctx hash)
    (values : EvalEnv) (assignment : Assignment)
    (bytes : ArtifactBytes.Bytes) (json : Json) (rows : List GuardedScalarRows.Row)
    (slots : List NativeState.Slot) (final : NativeState.Machine)
    (emitted : Zkir.lowerEntrypoint state sourceEntry rewrites = .ok json)
    (artifact : GuardedZkirArtifact.check bytes json = .ok rows)
    (ordinary : ∀ row ∈ rows, ordinaryHolds hash assignment row)
    (planAccepted : Impact.lower state (Passes.pruneEntrypoint sourceEntry) = .ok plan)
    (expectedAccepted :
      Native.expectedEntrypoint state (Passes.pruneEntrypoint sourceEntry) = .ok expected)
    (inputs : CanonicalInputs sourceEntry.circuit values assignment)
    (admitted : ScalarCircuitAdmission sourceEntry.circuit)
    (effects : ∀ effect ∈ sourceEntry.effects, ScalarEffect state effect)
    (guardsAdmitted : ∀ condition, some condition ∈ sourceEntry.effectGuards →
      ScalarExpression condition)
    (guardAdmission : plan.guards.all
      (fun guard => (ScalarExpressionAdmission.certify guard).isSome) = _root_.Bool.true)
    (checked : runCheckedCandidates ctx sourceEntry plan values assignment slots = some final) :
    (GuardedZkirArtifact.decodeBytes bytes).map GuardedZkirArtifact.View.rows = .ok rows ∧
    ∃ (result candidates : EvalEnv) (operations : List NativeState.Op)
        (observations : List Observation),
      sourceEntry.circuit.run ctx values = .ok result ∧
      decodeReads (plan.reads.drop (Impact.publicInputReadCount sourceEntry.circuit.inputs))
        assignment = .ok candidates ∧
      GuardedPlanExecution.evalPlan ctx ((result ++ values) ++ candidates) plan = .ok operations ∧
      NativeState.run operations ⟨[.vector slots], []⟩ = some final ∧
      final.reads.map NativeState.Cell.value = activeReadValues (emittedPublicReads assignment rows) ∧
      (∀ observation ∈ emittedPublicReads assignment rows,
        observation.guard = one ∨ (observation.guard = zero ∧ observation.value = zero)) ∧
      consumeArtifact bytes assignment
        ⟨operations.flatMap ImpactStatementScalar.opFields, final.reads.map NativeState.Cell.value⟩ =
          some observations := by
  let ep := Passes.pruneEntrypoint sourceEntry
  let reads := plan.reads.drop (Impact.publicInputReadCount ep.circuit.inputs)
  obtain ⟨exactRows, result, candidates, operations, observations, executed, decoded,
    evaluated, vmRun, tape, _observed, _fields, consumes⟩ :=
    GuardedScalarCandidateTranscript.lower_checked_guarded_vm_transcript
      state sourceEntry rewrites expected plan ctx hash implementation values assignment
      bytes json rows slots final emitted artifact ordinary planAccepted expectedAccepted
      inputs admitted effects guardsAdmitted checked
  obtain ⟨_, _, _, readFrame, aliases, blocks, readObservations, readFrameAccepted,
    aliasesAccepted, blocksAccepted, _inputOrder, blockObservations, readOrder⟩ :=
    lower_checked_guarded_source_read_transcript
      state sourceEntry rewrites expected plan hash values assignment bytes json rows
      emitted artifact ordinary planAccepted expectedAccepted inputs effects
  obtain ⟨_, schema, compatible, plainReads, distinctReads, scalarReads, frame, actualResult,
    actualCandidates, frameAccepted, actualExecuted, actualDecoded, baseEnvironment,
    environment, fresh, readAliases, readAliasFold⟩ :=
    GuardedScalarCandidateSchedule.lower_checked_guarded_source_frame
      state sourceEntry rewrites expected plan ctx hash implementation values assignment
      bytes json rows emitted artifact ordinary planAccepted expectedAccepted inputs admitted effects
  have sameResult : result = actualResult := Except.ok.inj
    (executed.symm.trans (by
      simpa only [ep, Passes.pruneEntrypoint, Passes.pruneCircuit_run] using actualExecuted))
  subst actualResult
  have sameCandidates := Except.ok.inj (decoded.symm.trans actualDecoded)
  subst actualCandidates
  have sameFrame := Except.ok.inj (frameAccepted.symm.trans readFrameAccepted)
  subst readFrame
  have sameAliases := Except.ok.inj (readAliasFold.symm.trans aliasesAccepted)
  subst aliases
  have scope := ScalarGuardedActivityAdmission.lower_guarded_scalar_read_scope
    state ep plan planAccepted effects
  have readGuards (readSpec : Impact.Read) (present : readSpec ∈ reads)
      (condition : Expr .bool) (selected : readSpec.guard = some condition) :
      ScalarExpression condition :=
    guardsAdmitted condition (GuardedReadDescriptorTrace.lower_post_public_read_guard_mem
      state ep plan planAccepted scope readSpec present condition selected)
  have schemaFor (other : Native.Expected)
      (accepted : Native.expectedEntrypoint state ep = .ok other) :
      ∀ requirement ∈ other.rawInputs ++ other.inputs, requirement.ty.isForeign = _root_.Bool.false := by
    have same := Except.ok.inj (accepted.symm.trans expectedAccepted)
    subst other
    exact schema
  obtain ⟨_, instructions, parsed, decodedRows⟩ := GuardedZkirArtifact.check_sound artifact
  obtain ⟨otherExpected, otherAccepted, requirements⟩ :=
    GuardedZkirRequirements.lowerEntrypoint_guardedRows_sourceRequirements
      rewrites emitted parsed decodedRows schemaFor
  have sameExpected := Except.ok.inj (expectedAccepted.symm.trans otherAccepted)
  subst otherExpected
  obtain ⟨assertions, bounds, inputBounds⟩ := requirements ordinary
  have planGuardsAdmitted (condition : Expr .bool) (present : condition ∈ plan.guards) :
      ScalarExpression condition := by
    have certified := List.all_eq_true.mp guardAdmission condition present
    change (ScalarExpressionAdmission.certify condition).isSome = _root_.Bool.true at certified
    cases found : ScalarExpressionAdmission.certify condition with
    | none => simp [found] at certified
    | some proof => exact proof.down
  obtain ⟨guardValues, guardDecoded, _, readBounds, planAssertions⟩ :=
    ScalarPlanGuardSoundness.plan_guards_sound_of_requirements state ep ctx hash implementation
      assignment plan expected frame (result ++ values) planAccepted expectedAccepted frameAccepted
      baseEnvironment plainReads fresh distinctReads readAliases planGuardsAdmitted
      assertions bounds inputBounds
  have sameGuardValues := Except.ok.inj (decoded.symm.trans guardDecoded)
  subst guardValues
  obtain ⟨offsets, inputPlan, chunks, publicNative, groups, exactLower, publicAccepted,
    compiled, publicEvaluated, effectsEvaluated, operationsOrder⟩ :=
    GuardedPlanTrace.lower_scoped_active_chunks state ep plan ctx
      ((result ++ values) ++ candidates) operations planAccepted scope evaluated planAssertions

  have binding (descriptor : Impact.Read) (present : descriptor ∈ reads) :
      ∃ value : descriptor.ty.Denote,
        ((result ++ values) ++ candidates).lookup descriptor.name =
          some (Value.pack descriptor.ty value) ∧
        Canonical descriptor.ty value ∧
        sourceScalar? descriptor.ty value = some (assignment ("%input_" ++ descriptor.name)) :=
    GenericStateReadEnvironment.read_candidate_from_decoded_reads (result ++ values) reads
      assignment candidates decoded distinctReads descriptor present (fresh descriptor present).1
      (plainReads descriptor present).2.2 (readBounds descriptor present)

  have inactiveZero (descriptor : Impact.Read) (present : descriptor ∈ reads)
      (condition : Expr .bool) (selected : descriptor.guard = some condition)
      (inactive : condition.eval ctx ((result ++ values) ++ candidates) = .ok _root_.Bool.false) :
      assignment ("%input_" ++ descriptor.name) = zero :=
    GuardedZkirPlanSoundness.checked_inactive_read state ep ctx hash implementation
      assignment plan expected frame (result ++ values) candidates descriptor condition
      planAccepted expectedAccepted frameAccepted environment scalarReads decoded distinctReads
      present (plainReads descriptor present).1 selected (readGuards descriptor present condition selected)
      (fresh descriptor present).1 (plainReads descriptor present).2.2 (readBounds descriptor present)
      inactive assertions

  have canonical : CanonicalInputs ep.circuit values assignment :=
    ⟨inputs.unique, inputs.declared, inputs.complete, inputs.binding⟩
  obtain ⟨actualPublic, publicRun, publicTape⟩ :=
    GuardedVmPublicPrefix.source_candidate_public_input_prefix_expected_cells_values
      state ep plan inputPlan ctx values result candidates assignment canonical planAccepted
      actualExecuted compatible publicAccepted implementation.modulus
  change inputPlan.operations.mapM (GenericStateOps.evalOp ctx ((result ++ values) ++ candidates)) =
    .ok actualPublic at publicRun
  have samePublic := Except.ok.inj (publicEvaluated.symm.trans publicRun)
  subst actualPublic

  obtain ⟨descriptorChunks, readTrace⟩ := GuardedEffectReadTape.of_operation_chunks scope compiled
  have readSuffix : reads = descriptorChunks.flatten := by
    have prefixCount := GenericStateAdmissionPrefix.publicInputPlan_readCount
      ep.circuit.inputs inputPlan publicAccepted
    change plan.reads.drop (Impact.publicInputReadCount ep.circuit.inputs) = _
    rw [GuardedEffectReadTape.read_descriptors_append readTrace, ← prefixCount]
    simp
  have supported (item : Effect × Nat) (present : item ∈ ep.effects.zipIdx) :
      ScalarEffect state item.1 := by
    apply effects
    simpa only [List.zipIdx_map_fst, ep, Passes.pruneEntrypoint] using
      List.mem_map_of_mem (f := Prod.fst) present
  obtain ⟨sourceObservations, sourceObserved, effectTape⟩ :=
    evaluate_effect_read_tape ctx assignment ((result ++ values) ++ candidates)
      implementation.modulus readTrace supported effectsEvaluated
      (fun descriptor present => binding descriptor (readSuffix.symm ▸ present)) planAssertions
  rw [← readSuffix] at sourceObserved
  obtain ⟨normalizedObservations, normalizedObserved, sameEvaluation, guardFields⟩ :=
    guardedReadRequirements_observations ctx hash implementation assignment frame.1
      ((result ++ values) ++ candidates) (plan.typeEnvironment ep) environment
      reads blocks blocksAccepted
      (fun descriptor present => (plainReads descriptor present).1)
      (fun descriptor present => (plainReads descriptor present).2.1)
      readGuards (read_guard_evaluates_of_observations sourceObserved) inactiveZero
  have sameSource := Except.ok.inj (sourceObserved.symm.trans sameEvaluation)
  subst sourceObservations
  have sameObservations := Option.some.inj (blockObservations.symm.trans normalizedObserved)
  subst normalizedObservations
  have matchingTape :
      final.reads.map NativeState.Cell.value = activeReadValues (emittedPublicReads assignment rows) := by
    rw [tape, operationsOrder, expectedCells_append, List.map_append, publicTape, effectTape,
      readOrder, activeReadValues_append]
  have canonicalRows : ∀ observation ∈ emittedPublicReads assignment rows,
      observation.guard = one ∨ (observation.guard = zero ∧ observation.value = zero) := by
    rw [readOrder]
    intro observation present
    rcases List.mem_append.mp present with declared | descriptor
    · exact .inl (GuardedVmPublicPrefix.publicCircuitObservations_guard_one
        ep.circuit.inputs assignment observation declared)
    · exact guardFields observation descriptor
  exact ⟨exactRows, result, candidates, operations, observations, executed, decoded,
    evaluated, vmRun, matchingTape, canonicalRows, consumes.mpr ⟨matchingTape, canonicalRows⟩⟩

end Noctium.Verification.GuardedVmReadTranscript
