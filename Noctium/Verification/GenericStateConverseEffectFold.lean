import Noctium.Verification.GenericStateConverseEffectStep
import Noctium.Verification.GuardedEffectEvaluation

namespace Noctium.Verification.GenericStateConverseEffectFold
open Backend NativeRelation NativeState
open GenericStatePrefixEnvironment GenericStateEffectValidation GenericStateCheckedReadTrace
open GuardedEffectEvaluation
open ScalarGuardedPlanAdmission (ScalarEffect)
open ScalarSourceReadTape (sourceReadInputs)
open ScalarCellEffectEvaluation (ReadCandidates)

/-- The recorded guarded source steps drive the corresponding emitted chunks.
Each chunk advances the native VM to the encoding of the same source frame. -/
theorem source_effects_native (ctx : EvalContext) (state : List StateDecl) (entry : Entrypoint)
    (items : List (Effect × Nat)) (types finalTypes : TypeEnv)
    (before after : SourceEffects.Frame) (ordinal : Nat) (entries : List (Impact.Read × Scalar))
    (complete : EvalEnv) (slots : List Slot) (reads : List Cell)
    (beforePlan afterPlan : Impact.Plan) (offsets : List Nat) (chunks : List (List Impact.Op))
    (validated : GuardValidatedEffects state entry types items finalTypes)
    (compiled : GuardedEffectOperationChunks state entry.effectGuards items beforePlan afterPlan offsets chunks)
    (admitted : ∀ item ∈ items, ScalarEffect state item.1)
    (scope : GuardedScalarReadEffects entry.effectGuards items)
    (recorded : sourceReadInputs ctx entry.effectGuards items ordinal before = .ok (entries, after))
    (candidates : ReadCandidates complete entries)
    (agrees : AgreesOnTypes types before.1 complete)
    (encoded : GenericStateEncoding.encodeState state before.2 = some slots)
    (distinct : state.Pairwise (fun left right => left.name ≠ right.name))
    (stateBound : state.length < Field.modulus) (modulus : ctx.modulus = Field.modulus) :
    ∃ groups finalSlots finalReads,
      (items.zip chunks).mapM (fun (item, chunk) =>
        GuardedPlanExecution.evalChunk ctx complete (entry.effectGuardAt item.2) chunk) = .ok groups ∧
      GenericStateVM.RunsChunks (groups.map Prod.snd) ⟨[.vector slots], reads⟩
        ⟨[.vector finalSlots], finalReads⟩ ∧
      GenericStateEncoding.encodeState state after.2 = some finalSlots ∧
      AgreesOnTypes finalTypes after.1 complete := by
  induction compiled generalizing types finalTypes before after ordinal entries slots reads with
  | nil _ =>
    cases validated
    change Except.ok ([], before) = .ok (entries, after) at recorded
    cases recorded
    exact ⟨[], slots, reads, rfl, .nil _, encoded, agrees⟩
  | @cons item rest start middlePlan result offsets chunk chunks compiled operationPrefix tail ih =>
    cases validated with
    | cons typed guardValid validatedTail =>
      obtain ⟨middle, head, remainder, nextOrdinal, sourceStep, _, recordedTail,
        entryShape, _, _, headValue⟩ := ScalarSourceReadTape.sourceReadInputs_cons_inversion
          ctx entry.effectGuards item rest ordinal before after entries recorded
      have headCandidates : ReadCandidates complete head := by
        intro record member
        apply candidates record
        rw [entryShape]
        exact List.mem_append_left _ member
      have tailCandidates : ReadCandidates complete remainder := by
        intro record member
        apply candidates record
        rw [entryShape]
        exact List.mem_append_right _ member
      have matched := GenericStateConverseSource.source_head_candidate_agreement
        item.1 middle head complete headValue headCandidates
      obtain ⟨activity, segment, nextSlots, nextReads, evaluated, nativeRun, nextEncoded, nextAgrees⟩ :=
        GenericStateConverseEffectStep.source_effect_native ctx state _ _ item.1
          (entry.effectGuards[item.2]?.getD none) before.1 complete before.2 middle slots reads
          start middlePlan typed guardValid (admitted item (by simp)) (scope item (by simp))
          sourceStep agrees matched compiled encoded distinct stateBound modulus
      rw [operationPrefix, List.drop_left] at evaluated
      obtain ⟨groups, finalSlots, finalReads, evaluatedTail, nativeTail, finalEncoded, finalAgrees⟩ :=
        ih _ finalTypes middle after nextOrdinal remainder nextSlots nextReads validatedTail
          (fun found member => admitted found (List.mem_cons_of_mem _ member))
          (fun found member => scope found (List.mem_cons_of_mem _ member))
          recordedTail tailCandidates nextAgrees nextEncoded
      have evaluatedHead : GuardedPlanExecution.evalChunk ctx complete
          (entry.effectGuardAt item.2) chunk = .ok (activity, segment) := by
        simpa [Entrypoint.effectGuardAt] using evaluated
      refine ⟨(activity, segment) :: groups, finalSlots, finalReads, ?_,
        .cons segment (groups.map Prod.snd) _ _ _ nativeRun nativeTail, finalEncoded, finalAgrees⟩
      simp [List.zip_cons_cons, List.mapM_cons, evaluatedHead, evaluatedTail,
        bind, pure, Except.bind, Except.pure]

end Noctium.Verification.GenericStateConverseEffectFold
