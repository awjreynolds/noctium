import Noctium.Verification.GuardedOperationAlignment
import Noctium.Verification.GuardedPlanExecution

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

/-- The guard-aware VM sequence partitions at the actual compiler effect
boundaries. Empty operation groups retain their source guard result. -/
theorem lower_scoped_active_chunks (state : List StateDecl) (entry : Entrypoint)
    (plan : Impact.Plan) (ctx : EvalContext) (env : EvalEnv) (native : List NativeState.Op)
    (lowered : Impact.lower state entry = .ok plan)
    (scope : GuardedScalarReadEffects entry.effectGuards entry.effects.zipIdx)
    (evaluated : evalPlan ctx env plan = .ok native)
    (guardsEvaluate : ∀ item ∈ entry.effects.zipIdx, ∃ activity,
      (entry.effectGuardAt item.2).mapM (Expr.eval ctx env) = .ok activity) :
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
  have ⟨guardShape, _⟩ := operationGuards_of_chunks scope compiled (by simp [inputGuards])
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
    exact guardsEvaluate pair.1 present
  obtain ⟨groups, effectEval, effectSequence⟩ := eval_chunks ctx env entry.effectGuards
    (entry.effects.zipIdx.zip chunks) effectActs effectOps pairedGuards effectGuardEval
    (by simpa only [pairedOps] using evalEffects)
  refine ⟨offsets, inputPlan, chunks, publicOps.flatten, groups, accepted, publicAccepted,
    compiled, publicNative, effectEval, ?_⟩
  rw [result, ← Except.ok.inj outputEq, List.flatten_append, effectSequence]

end Noctium.Verification.GuardedPlanTrace
