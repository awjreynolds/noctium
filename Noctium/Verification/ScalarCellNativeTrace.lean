import Noctium.Verification.ScalarCellEffectEvaluation
import Noctium.Verification.ScalarCellNativeStep

namespace Noctium.Verification.ScalarCellNativeTrace

open Backend NativeRelation NativeState ScalarNormalization
open GenericStateCellAdmission GenericStateEffectValidation GenericStatePrefixEnvironment
open ScalarCellEffectEvaluation ScalarCellSourceReads

/-- Native read equality cells in the order recorded by the source run. -/
def tapeCells (entries : List (Impact.Read × Scalar)) : List Cell :=
  entries.map fun entry => field entry.2

/-- Run the accepted Impact chunks in the VM model in lockstep with the successful source steps.
Each read extends the VM read tape by the cell observed by that source step.
Each write preserves the tape and encodes the new source state. -/
theorem cell_trace_run (ctx : EvalContext) (state : List StateDecl)
    (effects : List Effect) (start ordinal : Nat) (prePlan plan : Impact.Plan)
    (offsets : List Nat) (types finalTypes : TypeEnv)
    (before after : Frame) (entries : List (Impact.Read × Scalar)) (complete : EvalEnv)
    (initial : Machine) (slots : List Slot) (publicReads currentReads : List Cell)
    (nativePrefix : List Op)
    (admission : ScalarCellEffects state effects)
    (operands : ∀ effect ∈ effects, ScalarCellOperand effect)
    (trace : Impact.GuardedEffectTrace state [] (effects.zipIdx start) prePlan plan offsets)
    (validated : ValidatedEffects state types effects finalTypes)
    (source : sourceReadInputs ctx effects ordinal before = .ok (entries, after))
    (candidates : ReadCandidates complete entries)
    (agrees : AgreesOnTypes types before.1 complete)
    (encoded : GenericStateEncoding.encodeState state before.2 = some slots)
    (distinct : state.Pairwise (fun left right => left.name ≠ right.name))
    (stateBound : state.length < Field.modulus)
    (modulus : ctx.modulus = Field.modulus)
    (prefixEvaluated : GenericStateOps.evalPlan ctx complete prePlan = .ok nativePrefix)
    (prefixRun : NativeState.run nativePrefix initial = some ⟨[.vector slots], publicReads ++ currentReads⟩) :
    ∃ native finalSlots,
      GenericStateOps.evalPlan ctx complete plan = .ok native ∧
      GenericStateEncoding.encodeState state after.2 = some finalSlots ∧
      NativeState.run native initial =
        some ⟨[.vector finalSlots], publicReads ++ currentReads ++ tapeCells entries⟩ ∧
      AgreesOnTypes finalTypes after.1 complete := by
  induction effects generalizing start ordinal prePlan offsets types finalTypes before after entries
      slots currentReads nativePrefix with
  | nil =>
    cases trace
    cases validated
    simp only [sourceReadInputs, Except.ok.injEq, Prod.mk.injEq] at source
    rcases source with ⟨rfl, rfl⟩
    exact ⟨nativePrefix, slots, prefixEvaluated, encoded, by simpa [tapeCells] using prefixRun, agrees⟩
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
      obtain ⟨_, readBinding⟩ := cell_scope_step ctx state effect before middle
        ordinal types nextTypes effectScope operand modulus sourceStep localValid complete agrees headCandidates
      let headTape := tapeCells (effectEntries effect ordinal middle)
      obtain ⟨headNative, nextSlots, nextReads, headEvaluated, headRun, nextEncoded,
        readShape, nextAgreement⟩ :=
        ScalarCellNativeStep.scalar_cell_native_step ctx state types nextTypes effect
          before.1 complete before.2 middle slots (publicReads ++ currentReads) chunk ordinal
          effectScope operand localValid sourceStep agrees readBinding chunkAccepted encoded
          distinct stateBound modulus
      rw [readShape] at headRun
      change NativeState.run headNative ⟨[.vector slots], publicReads ++ currentReads⟩ =
        some ⟨[.vector nextSlots], (publicReads ++ currentReads) ++ headTape⟩ at headRun
      have nextEvaluated : GenericStateOps.evalPlan ctx complete next =
          .ok (nativePrefix ++ headNative) := by
        unfold GenericStateOps.evalPlan at prefixEvaluated ⊢
        rw [operations, List.mapM_append, prefixEvaluated, headEvaluated]
        rfl
      have nextRun : NativeState.run (nativePrefix ++ headNative) initial =
          some ⟨[.vector nextSlots], publicReads ++ (currentReads ++ headTape)⟩ := by
        rw [NativeState.run_append, prefixRun]
        simpa only [Option.bind_some, List.append_assoc, headTape] using headRun
      have tailCandidates : ReadCandidates complete readTail := by
        intro record member
        apply candidates record
        rw [records]
        exact List.mem_append_right _ member
      obtain ⟨native, finalSlots, evaluated, finalEncoded, finalRun, finalAgrees⟩ :=
        ih (start + 1) (ordinal + (effectEntries effect ordinal middle).length)
          next nextOffsets nextTypes finalTypes middle after readTail nextSlots
          (currentReads ++ headTape) (nativePrefix ++ headNative) restScope restOperands
          tail tailValid tailSource tailCandidates nextAgreement nextEncoded nextEvaluated nextRun
      refine ⟨native, finalSlots, evaluated, finalEncoded, ?_, finalAgrees⟩
      simpa only [records, tapeCells, List.map_append, List.append_assoc, headTape] using finalRun

end Noctium.Verification.ScalarCellNativeTrace
