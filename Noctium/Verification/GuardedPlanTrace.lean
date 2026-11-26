import Noctium.Verification.GuardedOperationAlignment
import Noctium.Verification.GuardedPlanExecution
import Noctium.Verification.GuardedEffectChunkShape
import Noctium.Verification.GuardedOperationActivity
import Noctium.Verification.GuardedRequireActivity
import Noctium.Verification.GenericStateAdmissionPrefix

namespace Noctium.Verification.GuardedPlanTrace
open Backend GenericStateCheckedReadTrace GuardedEffectEvaluation
open GuardedOperationAlignment GuardedPlanActivity GuardedPlanExecution

private theorem bind_ok {α β : Type} {first : Except ε α}
    {next : α → Except ε β} {result : β} :
    (first >>= next) = .ok result ↔
      ∃ value, first = .ok value ∧ next value = .ok result := by
  cases first <;> simp [Bind.bind, Except.bind]

private theorem mapM_replicate_ok {f : α → Except ε β} {a : α} {b : β}
    (accepted : f a = .ok b) (count : Nat) :
    (List.replicate count a).mapM f = .ok (List.replicate count b) := by
  induction count with
  | zero => rfl
  | succ _ ih => simp [List.replicate_succ, accepted, ih, Bind.bind, Except.bind,
      Pure.pure, Except.pure]

private theorem chunks_length
    (trace : GuardedEffectOperationChunks state guards items before plan offsets chunks) :
    items.length = chunks.length := by
  induction trace with
  | nil _ => rfl
  | cons _ _ _ ih => simp [ih]

private theorem selected_chunk_step
    (trace : GuardedEffectOperationChunks state guards items before plan offsets chunks)
    (pair : (Effect × Nat) × List Impact.Op) (present : pair ∈ items.zip chunks) :
    ∃ start stop,
      Impact.appendEffectWithActivity state pair.1.1 (guards[pair.1.2]?.getD none)
        start = .ok stop ∧ stop.operations = start.operations ++ pair.2 := by
  induction trace with
  | nil _ => simp at present
  | @cons item rest start stop plan offsets chunk chunks step operations tail ih =>
    rw [List.zip_cons_cons] at present
    rcases List.mem_cons.mp present with same | later
    · subst pair
      exact ⟨start, stop, step, operations⟩
    · exact ih later

private theorem eval_chunks (ctx : EvalContext) (env : EvalEnv)
    (guards : List (Option (Expr .bool)))
    (pairs : List ((Effect × Nat) × List Impact.Op))
    (activities : List (Option Bool)) (outputs : List (List NativeState.Op))
    (guardsEvaluate : ∀ pair ∈ pairs, ∃ activity,
      evalActivity ctx env (guards[pair.1.2]?.getD none) = .ok activity)
    (evaluatedGuards : (pairs.flatMap fun (item, chunk) =>
      List.replicate chunk.length (guards[item.2]?.getD none)).mapM
        (evalActivity ctx env) = .ok activities)
    (evaluatedOps : ((pairs.map Prod.snd).flatten.zip activities).mapM
      (fun (operation, activity) => evalOperation ctx env activity operation) = .ok outputs) :
    ∃ groups, pairs.mapM (fun (item, chunk) =>
        evalChunk ctx env (guards[item.2]?.getD none) chunk) = .ok groups ∧
      outputs.flatten = (groups.map Prod.snd).flatten := by
  induction pairs generalizing activities outputs with
  | nil =>
    simp [Pure.pure, Except.pure] at evaluatedOps
    subst outputs
    exact ⟨[], rfl, rfl⟩
  | cons pair rest ih =>
    obtain ⟨activity, guardEval⟩ := guardsEvaluate pair (by simp)
    simp only [List.flatMap_cons, List.mapM_append, bind_ok] at evaluatedGuards
    obtain ⟨headActs, headGuardEval, tailActs, tailGuardEval, sameActs⟩ := evaluatedGuards
    have headActsEq := Except.ok.inj ((mapM_replicate_ok guardEval pair.2.length).symm.trans headGuardEval)
    subst headActs
    have actOrder : activities = List.replicate pair.2.length activity ++ tailActs :=
      (Except.ok.inj sameActs).symm
    simp only [List.map_cons, List.flatten_cons, actOrder,
      List.zip_append (List.length_replicate.symm), List.mapM_append, bind_ok] at evaluatedOps
    obtain ⟨headOps, headEval, tailOps, tailEval, sameOps⟩ := evaluatedOps
    obtain ⟨tailGroups, tailGroupsEval, tailOrder⟩ :=
      ih tailActs tailOps (fun found member => guardsEvaluate found (by simp [member]))
        tailGuardEval tailEval
    have headGroup := evalChunk_of_operations ctx env (guards[pair.1.2]?.getD none)
      pair.2 activity headOps guardEval headEval
    refine ⟨(activity, headOps.flatten) :: tailGroups, ?_, ?_⟩
    · simp [List.mapM_cons, headGroup, tailGroupsEval, Bind.bind, Except.bind,
        Pure.pure, Except.pure]
    · rw [← Except.ok.inj sameOps, List.flatten_append, tailOrder]
      rfl

/-- The guard-aware VM sequence partitions at the compiler's effect
boundaries. The operation schedule and successful plan assertions determine
the activity of every source effect, including empty operation groups. -/
theorem lower_scoped_active_chunks (state : List StateDecl) (entry : Entrypoint)
    (plan : Impact.Plan) (ctx : EvalContext) (env : EvalEnv) (native : List NativeState.Op)
    (lowered : Impact.lower state entry = .ok plan)
    (scope : GuardedScalarReadEffects entry.effectGuards entry.effects.zipIdx)
    (evaluated : evalPlan ctx env plan = .ok native)
    (assertions : ∀ expression ∈ plan.guards, expression.eval ctx env = .ok true) :
    ∃ offsets inputPlan chunks publicNative groups,
      Impact.lowerWithEffectBoundaries state entry = .ok (plan, offsets) ∧
      Impact.publicInputPlan entry.circuit.inputs {} = .ok inputPlan ∧
      GuardedEffectOperationChunks state entry.effectGuards entry.effects.zipIdx
        inputPlan plan offsets chunks ∧
      inputPlan.operations.mapM (GenericStateOps.evalOp ctx env) = .ok publicNative ∧
      (entry.effects.zipIdx.zip chunks).mapM (fun (item, chunk) =>
        evalChunk ctx env (entry.effectGuardAt item.2) chunk) = .ok groups ∧
      native = publicNative ++ (groups.map Prod.snd).flatten := by
  obtain ⟨offsets, inputPlan, chunks, accepted, publicAccepted, compiled, _⟩ :=
    lower_field_guards state entry plan lowered scope
  have empty := Impact.publicInputPlan_activity_guards entry.circuit.inputs {} inputPlan publicAccepted
  have inputGuards : operationGuards inputPlan = List.replicate inputPlan.operations.length none := by
    simp [operationGuards, empty]
  have prefixAligned : (operationGuards inputPlan).length = inputPlan.operations.length := by
    simp [inputGuards]
  have ⟨guardShape, _⟩ := operationGuards_of_chunks scope compiled prefixAligned
  have operations := guarded_chunks_plan_operations compiled
  obtain ⟨_, activities, perOp, guardEval, opEval, result⟩ := evalPlan_success ctx env plan native evaluated
  change (operationGuards plan).mapM (evalActivity ctx env) = .ok activities at guardEval
  rw [guardShape, inputGuards, List.mapM_append] at guardEval
  simp only [bind_ok] at guardEval
  obtain ⟨publicActs, publicGuardEval, effectActs, effectGuardEval, activityEq⟩ := guardEval
  have always : evalActivity ctx env none = .ok none := rfl
  have publicActEq := Except.ok.inj
    ((mapM_replicate_ok always inputPlan.operations.length).symm.trans publicGuardEval)
  subst publicActs
  have activityOrder : activities = List.replicate inputPlan.operations.length none ++ effectActs :=
    (Except.ok.inj activityEq).symm
  rw [operations, activityOrder, List.zip_append (List.length_replicate.symm), List.mapM_append] at opEval
  simp only [bind_ok] at opEval
  obtain ⟨publicOps, evalPublic, effectOps, evalEffects, outputEq⟩ := opEval
  have publicNative := evalOperations_unconditional ctx env inputPlan.operations publicOps evalPublic
  have equalLengths := chunks_length compiled
  have pairedOps := List.map_snd_zip (Nat.le_of_eq equalLengths.symm)
  have pairedItems := List.map_fst_zip (Nat.le_of_eq equalLengths)
  have pairedGuards : ∀ pair ∈ entry.effects.zipIdx.zip chunks, ∃ activity,
      evalActivity ctx env (entry.effectGuards[pair.1.2]?.getD none) = .ok activity := by
    intro pair member
    have present : pair.1 ∈ entry.effects.zipIdx := by
      simpa only [pairedItems] using List.mem_map_of_mem (f := Prod.fst) member
    change ∃ activity, evalActivity ctx env (entry.effectGuardAt pair.1.2) = .ok activity
    by_cases noOps : pair.2 = []
    · cases selected : entry.effectGuardAt pair.1.2 with
      | none => exact ⟨none, rfl⟩
      | some condition =>
        obtain ⟨start, stop, compiledStep, operationShape⟩ :=
          selected_chunk_step compiled pair member
        have selectedGuard : entry.effectGuards[pair.1.2]?.getD none = some condition := selected
        have headScope : GuardedScalarReadEffect (some condition) pair.1.1 := by
          simpa only [selectedGuard] using scope pair.1 present
        have headCompiled :
            Impact.appendEffectWithActivity state pair.1.1 (some condition) start = .ok stop := by
          simpa only [selectedGuard] using compiledStep
        obtain ⟨required, effectShape⟩ := GuardedEffectChunkShape.guarded_empty_effect_is_require
          state pair.1.1 condition headScope start stop headCompiled
          (by simpa only [noOps, List.append_nil] using operationShape)
        have requireMember : (Effect.require required, pair.1.2) ∈ entry.effects.zipIdx := by
          rw [show (Effect.require required, pair.1.2) = pair.1 from Prod.ext effectShape.symm rfl]
          exact present
        obtain ⟨active, gate⟩ := GuardedRequireActivity.lower_guarded_require_activity
          state entry plan ctx env required condition pair.1.2 lowered scope requireMember selected assertions
        exact ⟨some active, by simp [evalActivity, gate, Except.map, Functor.map]⟩
    · exact (GuardedOperationActivity.compiled_nonempty_chunk_guard_eval_success
        scope compiled prefixAligned ctx env native evaluated
        (item := pair.1) (chunk := pair.2) member noOps).2
  obtain ⟨groups, effectEval, effectSequence⟩ := eval_chunks ctx env entry.effectGuards
    (entry.effects.zipIdx.zip chunks) effectActs effectOps pairedGuards effectGuardEval
    (by simpa only [pairedOps] using evalEffects)
  refine ⟨offsets, inputPlan, chunks, publicOps.flatten, groups, accepted, publicAccepted,
    compiled, publicNative, effectEval, ?_⟩
  rw [result, ← Except.ok.inj outputEq, List.flatten_append, effectSequence]

/-- One successful scalar VM run provides a checked segment for each source
effect. Start at the machine left by the actual public-input prefix. -/
theorem lower_checked_effect_chunks (state : List StateDecl) (entry : Entrypoint)
    (plan : Impact.Plan) (ctx : EvalContext) (env : EvalEnv)
    (native : List NativeState.Op) (slots : List NativeState.Slot) (final : NativeState.Machine)
    (lowered : Impact.lower state entry = .ok plan)
    (scope : GuardedScalarReadEffects entry.effectGuards entry.effects.zipIdx)
    (compatible : ∀ input ∈ entry.circuit.inputs, Impact.publicInputScalarCompatible input)
    (evaluated : evalPlan ctx env plan = .ok native)
    (assertions : ∀ expression ∈ plan.guards, expression.eval ctx env = .ok true)
    (checked : NativeState.run native ⟨[.vector slots], []⟩ = some final) :
    ∃ offsets inputPlan chunks publicNative groups publicReads,
      Impact.lowerWithEffectBoundaries state entry = .ok (plan, offsets) ∧
      Impact.publicInputPlan entry.circuit.inputs {} = .ok inputPlan ∧
      GuardedEffectOperationChunks state entry.effectGuards entry.effects.zipIdx
        inputPlan plan offsets chunks ∧
      inputPlan.operations.mapM (GenericStateOps.evalOp ctx env) = .ok publicNative ∧
      (entry.effects.zipIdx.zip chunks).mapM (fun (item, chunk) =>
        evalChunk ctx env (entry.effectGuardAt item.2) chunk) = .ok groups ∧
      native = publicNative ++ (groups.map Prod.snd).flatten ∧
      NativeState.run publicNative ⟨[.vector slots], []⟩ = some ⟨[.vector slots], publicReads⟩ ∧
      GenericStateVM.RunsChunks (groups.map Prod.snd) ⟨[.vector slots], publicReads⟩ final := by
  obtain ⟨offsets, inputPlan, chunks, publicNative, groups, boundaries, publicAccepted,
    compiled, publicEvaluated, effectsEvaluated, sequence⟩ :=
    lower_scoped_active_chunks state entry plan ctx env native lowered scope evaluated assertions
  obtain ⟨publicReads, _, publicRun⟩ := GenericStateAdmissionPrefix.public_prefix_run
    entry.circuit.inputs inputPlan ctx env publicNative [.vector slots] []
    publicAccepted compatible publicEvaluated
  rw [sequence, NativeState.run_append, publicRun, Option.bind_some] at checked
  exact ⟨offsets, inputPlan, chunks, publicNative, groups, publicReads,
    boundaries, publicAccepted, compiled, publicEvaluated, effectsEvaluated, sequence,
    publicRun, (GenericStateVM.run_chunks_iff (groups.map Prod.snd) _ final).mp checked⟩

end Noctium.Verification.GuardedPlanTrace
