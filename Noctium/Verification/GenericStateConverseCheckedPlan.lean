import Noctium.Verification.GenericStateCheckedSchedule
import Noctium.Verification.GuardedEffectEvaluation
import Noctium.Verification.GuardedOperationAlignment
import Noctium.Verification.GuardedPlanActivity
import Noctium.Verification.GuardedPlanExecution
import Noctium.Verification.GenericStateVM

namespace Noctium.Verification.GenericStateConverseCheckedPlan

open Backend NativeRelation NativeState
open GenericStateCheckedReadTrace GenericStateInputValues
open GuardedEffectEvaluation GuardedOperationAlignment GuardedPlanActivity
open GuardedPlanExecution

private theorem bind_ok {α β : Type} {first : Except ε α}
    {next : α → Except ε β} {result : β} :
    (first >>= next) = .ok result ↔
      ∃ value, first = .ok value ∧ next value = .ok result := by
  cases first <;> simp [Bind.bind, Except.bind]

private theorem chunks_length
    (trace : GuardedEffectOperationChunks state guards items before plan offsets chunks) :
    items.length = chunks.length := by
  induction trace with
  | nil _ => rfl
  | cons _ _ _ ih => simp [ih]

private theorem mapM_replicate_ok {f : α → Except ε β} {a : α} {b : β}
    (accepted : f a = .ok b) (count : Nat) :
    (List.replicate count a).mapM f = .ok (List.replicate count b) := by
  induction count with
  | zero => rfl
  | succ count ih =>
    simp [List.replicate_succ, accepted, ih, Bind.bind, Except.bind,
      Pure.pure, Except.pure]

private theorem evalOperations_at_active (ctx : EvalContext) (env : EvalEnv)
    (operations : List Impact.Op) (activity : Option _root_.Bool)
    (native : List NativeState.Op)
    (enabled : activity.getD (_root_.Bool.true) = _root_.Bool.true)
    (evaluated : operations.mapM (GenericStateOps.evalOp ctx env) = .ok native) :
    ∃ outputs,
      (operations.zip (List.replicate operations.length activity)).mapM
        (fun (operation, selected) => evalOperation ctx env selected operation) =
          .ok outputs ∧ outputs.flatten = native := by
  induction operations generalizing native with
  | nil =>
    simp only [List.mapM_nil, Pure.pure, Except.pure, Except.ok.injEq] at evaluated
    subst native
    exact ⟨[], by rfl, rfl⟩
  | cons operation rest ih =>
    simp only [List.mapM_cons, bind_ok] at evaluated
    obtain ⟨value, headEval, tail, tailEval, same⟩ := evaluated
    cases same
    obtain ⟨tailOutputs, tailEvaluation, tailFlatten⟩ := ih tail tailEval
    have headOutput : evalOperation ctx env activity operation = .ok [value] := by
      simp only [evalOperation, enabled, headEval, Except.map]
      rfl
    refine ⟨[value] :: tailOutputs, ?_, ?_⟩
    · simp [List.replicate_succ, List.zip_cons_cons, List.mapM_cons,
        headOutput, tailEvaluation, Bind.bind, Except.bind, Pure.pure, Except.pure]
    · simp [List.flatten_cons, tailFlatten]

private theorem evalOperations_at_inactive (ctx : EvalContext) (env : EvalEnv)
    (operations : List Impact.Op) (activity : Option _root_.Bool)
    (inactive : activity.getD (_root_.Bool.true) = _root_.Bool.false) :
    (operations.zip (List.replicate operations.length activity)).mapM
      (fun (operation, selected) => evalOperation ctx env selected operation) =
        .ok (List.replicate operations.length []) := by
  induction operations with
  | nil => rfl
  | cons operation rest ih =>
    have zipShape :
        (operation :: rest).zip (List.replicate (operation :: rest).length activity) =
          (operation, activity) :: rest.zip (List.replicate rest.length activity) := by
      rw [List.length_cons, Nat.add_one, List.replicate_succ]
      rfl
    rw [zipShape, List.mapM_cons]
    change (evalOperation ctx env activity operation >>= fun head =>
      (rest.zip (List.replicate rest.length activity)).mapM
        (fun (next, selected) => evalOperation ctx env selected next) >>= fun tail =>
      pure (head :: tail)) = _
    simp only [List.length_cons, List.replicate_succ]
    have head : evalOperation ctx env activity operation = .ok [] := by
      simp [evalOperation, inactive]
    rw [head, ih]
    rfl

private theorem evalChunk_operation_groups (ctx : EvalContext) (env : EvalEnv)
    (guard : Option (Expr .bool)) (chunk : List Impact.Op)
    (activity : Option _root_.Bool) (native : List NativeState.Op)
    (accepted : evalChunk ctx env guard chunk = .ok (activity, native)) :
    ∃ outputs,
      (chunk.zip (List.replicate chunk.length activity)).mapM
        (fun (operation, selected) => evalOperation ctx env selected operation) =
          .ok outputs ∧ outputs.flatten = native := by
  have facts := evalChunk_success ctx env guard chunk activity native accepted
  by_cases active : activity.getD (_root_.Bool.true) = _root_.Bool.true
  · have chunkAccepted : chunk.mapM (GenericStateOps.evalOp ctx env) = .ok native := by
      simpa [active] using facts.2
    exact evalOperations_at_active ctx env chunk activity native active chunkAccepted
  · have nativeEmpty : native = [] := by
      have inactive : activity.getD (_root_.Bool.true) = _root_.Bool.false := by
        cases value : activity.getD (_root_.Bool.true)
        · rfl
        · exact False.elim (active value)
      simpa [inactive] using facts.2
    subst native
    have inactive : activity.getD (_root_.Bool.true) = _root_.Bool.false := by
      cases value : activity.getD (_root_.Bool.true)
      · rfl
      · exact False.elim (active value)
    exact ⟨List.replicate chunk.length [],
      evalOperations_at_inactive ctx env chunk activity inactive, by simp⟩

private theorem eval_guarded_chunks_operation_groups (ctx : EvalContext)
    (env : EvalEnv) (guards : List (Option (Expr .bool)))
    (pairs : List ((Effect × Nat) × List Impact.Op))
    (groups : List (Option _root_.Bool × List NativeState.Op))
    (accepted : pairs.mapM (fun (item, chunk) =>
      evalChunk ctx env (guards[item.2]?.getD none) chunk) = .ok groups) :
    ∃ activities outputs,
      (pairs.flatMap fun (item, chunk) =>
        List.replicate chunk.length (guards[item.2]?.getD none)).mapM
          (evalActivity ctx env) = .ok activities ∧
      ((pairs.map Prod.snd).flatten.zip activities).mapM
        (fun (operation, activity) => evalOperation ctx env activity operation) =
          .ok outputs ∧
      outputs.flatten = (groups.map Prod.snd).flatten := by
  induction pairs generalizing groups with
  | nil =>
    simp only [List.mapM_nil, Pure.pure, Except.pure, Except.ok.injEq] at accepted
    subst groups
    exact ⟨[], [], rfl, rfl, rfl⟩
  | cons pair rest ih =>
    simp only [List.mapM_cons, bind_ok] at accepted
    obtain ⟨group, headAccepted, tailGroups, tailAccepted, sameGroups⟩ := accepted
    have groupsEq : group :: tailGroups = groups := by
      have wrapped : (Except.ok (group :: tailGroups) : Except String _) = .ok groups := by
        simpa [Pure.pure, Except.pure] using sameGroups
      exact Except.ok.inj wrapped
    have headFacts := evalChunk_success ctx env (guards[pair.1.2]?.getD none)
      pair.2 group.1 group.2 headAccepted
    obtain ⟨headOutputs, headOperations, headFlatten⟩ :=
      evalChunk_operation_groups ctx env (guards[pair.1.2]?.getD none)
        pair.2 group.1 group.2 headAccepted
    have tailResult := ih tailGroups tailAccepted
    obtain ⟨tailActivities, tailOutputs, tailGuards, tailOperations, tailFlatten⟩ := tailResult
    have headGuardEval : evalActivity ctx env
        (guards[pair.1.2]?.getD none) = .ok group.1 := by
      simpa [evalActivity] using headFacts.1
    have headGuards' := mapM_replicate_ok headGuardEval pair.2.length
    refine ⟨List.replicate pair.2.length group.1 ++ tailActivities,
      headOutputs ++ tailOutputs, ?_, ?_, ?_⟩
    · simp only [List.flatMap_cons, List.mapM_append]
      rw [headGuards', tailGuards]
      simp [Bind.bind, Except.bind, Pure.pure, Except.pure]
    · have opsShape :
          (pair.2 ++ (rest.map Prod.snd).flatten).zip
            (List.replicate pair.2.length group.1 ++ tailActivities) =
          pair.2.zip (List.replicate pair.2.length group.1) ++
            (rest.map Prod.snd).flatten.zip tailActivities := by
        rw [List.zip_append (List.length_replicate.symm)]
      simp only [List.map_cons, List.flatten_cons]
      rw [opsShape, List.mapM_append]
      simp [headOperations, tailOperations, Bind.bind, Except.bind,
        Pure.pure, Except.pure]
    · rw [List.flatten_append, headFlatten, tailFlatten]
      have groupSegments : group.2 :: (tailGroups.map Prod.snd) =
          groups.map Prod.snd := congrArg (List.map Prod.snd) groupsEq
      calc
        group.2 ++ (tailGroups.map Prod.snd).flatten =
            (group.2 :: tailGroups.map Prod.snd).flatten := by simp
        _ = (groups.map Prod.snd).flatten := by rw [groupSegments]

/-- Compose the public-input prefix with production guarded chunks. Each chunk
is evaluated only when its accepted activity is true, so an inactive chunk
does not evaluate its operation operands. -/
theorem eval_plan_of_guarded_constructed_chunks (state : List StateDecl)
    (ep : Entrypoint) (plan : Impact.Plan)
    (ctx : EvalContext) (env : EvalEnv)
    (offsets : List Nat) (inputPlan : Impact.Plan)
    (chunks : List (List Impact.Op))
    (publicOps : List NativeState.Op)
    (groups : List (Option _root_.Bool × List NativeState.Op))
    (scope : GuardedScalarReadEffects ep.effectGuards ep.effects.zipIdx)
    (publicAccepted : Impact.publicInputPlan ep.circuit.inputs {} = .ok inputPlan)
    (compiled : GuardedEffectOperationChunks state ep.effectGuards
      ep.effects.zipIdx inputPlan plan offsets chunks)
    (prefixEval : inputPlan.operations.mapM
      (GenericStateOps.evalOp ctx env) = .ok publicOps)
    (chunksEval : (ep.effects.zipIdx.zip chunks).mapM (fun (item, chunk) =>
      evalChunk ctx env (ep.effectGuardAt item.2) chunk) = .ok groups) :
    GuardedPlanExecution.evalPlan ctx env plan =
      .ok (publicOps ++ (groups.map Prod.snd).flatten) := by
  have empty := Impact.publicInputPlan_activity_guards ep.circuit.inputs {}
    inputPlan publicAccepted
  have prefixGuards : operationGuards inputPlan =
      List.replicate inputPlan.operations.length none := by
    simp [operationGuards, empty]
  have prefixAligned : (operationGuards inputPlan).length = inputPlan.operations.length := by
    simp [prefixGuards]
  obtain ⟨guardShape, aligned⟩ := operationGuards_of_chunks scope compiled prefixAligned
  have operationsShape := guarded_chunks_plan_operations compiled
  have chunksAccepted : (ep.effects.zipIdx.zip chunks).mapM (fun (item, chunk) =>
      evalChunk ctx env (ep.effectGuards[item.2]?.getD none) chunk) = .ok groups := by
    simpa only [Entrypoint.effectGuardAt] using chunksEval
  obtain ⟨effectActivities, effectOutputs, effectGuardsEval,
      effectOperationsEval, effectOutputOrder⟩ :=
    eval_guarded_chunks_operation_groups ctx env ep.effectGuards
      (ep.effects.zipIdx.zip chunks) groups chunksAccepted
  have pairedChunks : (ep.effects.zipIdx.zip chunks).map Prod.snd = chunks :=
    List.map_snd_zip (Nat.le_of_eq (chunks_length compiled).symm)
  have effectOperationsEval' := effectOperationsEval
  rw [pairedChunks] at effectOperationsEval'
  have effectGuardSchedule :
      effectOperationGuards ep.effectGuards ep.effects.zipIdx chunks =
        (ep.effects.zipIdx.zip chunks).flatMap fun (item, chunk) =>
          List.replicate chunk.length (ep.effectGuards[item.2]?.getD none) := rfl
  have effectActivityEval :
      (effectOperationGuards ep.effectGuards ep.effects.zipIdx chunks).mapM
        (evalActivity ctx env) = .ok effectActivities := by
    simpa only [effectGuardSchedule] using effectGuardsEval
  have noneActivity : evalActivity ctx env (none : Option (Expr .bool)) =
      .ok (none : Option _root_.Bool) := rfl
  have prefixActivityEval := mapM_replicate_ok noneActivity inputPlan.operations.length
  have guardEval : (operationGuards plan).mapM (evalActivity ctx env) =
      .ok (List.replicate inputPlan.operations.length none ++ effectActivities) := by
    rw [guardShape, prefixGuards, List.mapM_append,
      prefixActivityEval, effectActivityEval]
    rfl
  obtain ⟨prefixOutputs, prefixOperationsEval, prefixOutputOrder⟩ :=
    evalOperations_at_active ctx env inputPlan.operations none publicOps rfl prefixEval
  have zippedOperations :
      (inputPlan.operations ++ chunks.flatten).zip
        (List.replicate inputPlan.operations.length none ++ effectActivities) =
      inputPlan.operations.zip (List.replicate inputPlan.operations.length none) ++
        chunks.flatten.zip effectActivities := by
    rw [List.zip_append (List.length_replicate.symm)]
  have operationEval :
      (plan.operations.zip
        (List.replicate inputPlan.operations.length none ++ effectActivities)).mapM
          (fun (operation, activity) => evalOperation ctx env activity operation) =
        .ok (prefixOutputs ++ effectOutputs) := by
    rw [operationsShape, zippedOperations, List.mapM_append]
    rw [prefixOperationsEval, effectOperationsEval']
    rfl
  have outputOrder : (prefixOutputs ++ effectOutputs).flatten =
      publicOps ++ (groups.map Prod.snd).flatten := by
    rw [List.flatten_append, prefixOutputOrder, effectOutputOrder]
  simp only [GuardedPlanExecution.evalPlan]
  rw [ite_eq_left aligned]
  change (match (operationGuards plan).mapM (evalActivity ctx env) with
    | Except.error message =>
      (Except.error message : Except String (List NativeState.Op))
    | Except.ok activities =>
      match (plan.operations.zip activities).mapM
          (fun (operation, activity) => evalOperation ctx env activity operation) with
      | Except.error message => Except.error message
      | Except.ok perOperation => Except.ok perOperation.flatten) = _
  simp only [guardEval]
  rw [operationEval]
  exact congrArg Except.ok outputOrder

/-- Compose an accepted public prefix and unconditional effect chunks into
the exact operation sequence returned by the production plan evaluator. -/
theorem eval_plan_of_constructed_chunks (state : List StateDecl)
    (ep : Entrypoint) (plan : Impact.Plan)
    (ctx : EvalContext) (env : EvalEnv)
    (offsets : List Nat) (inputPlan : Impact.Plan)
    (chunks : List (List Impact.Op))
    (publicOps : List NativeState.Op)
    (groups : List (Option _root_.Bool × List NativeState.Op))
    (allNone : ep.effectGuards.all Option.isNone = _root_.Bool.true)
    (effects : ScalarReadEffects ep.effects)
    (publicAccepted : Impact.publicInputPlan ep.circuit.inputs {} = .ok inputPlan)
    (compiled : GuardedEffectOperationChunks state ep.effectGuards
      ep.effects.zipIdx inputPlan plan offsets chunks)
    (prefixEval : inputPlan.operations.mapM
      (GenericStateOps.evalOp ctx env) = .ok publicOps)
    (chunksEval : (ep.effects.zipIdx.zip chunks).mapM (fun (item, chunk) =>
      evalChunk ctx env (ep.effectGuardAt item.2) chunk) = .ok groups) :
    GuardedPlanExecution.evalPlan ctx env plan =
      .ok (publicOps ++ (groups.map Prod.snd).flatten) := by
  have scope : GuardedScalarReadEffects ep.effectGuards ep.effects.zipIdx := by
    intro item belongs
    have guardNone := all_none_guard_at ep.effectGuards allNone item.2
    simpa [Entrypoint.effectGuardAt, guardNone] using
      (GuardedScalarReadEffect.unguarded
        (effects item.1 (List.fst_mem_of_mem_zipIdx belongs)))
  exact eval_plan_of_guarded_constructed_chunks state ep plan ctx env offsets inputPlan
    chunks publicOps groups scope publicAccepted compiled prefixEval chunksEval

/-- A source result and decoded read candidates execute the current checked
plan when its accepted unconditional prefix and constructed chunks form the
same native run. The theorem returns the current candidate checker result. -/
theorem checked_of_constructed_trace (state : List StateDecl)
    (ep : Entrypoint) (plan : Impact.Plan)
    (ctx : EvalContext) (values : EvalEnv) (assignment : Assignment)
    (result candidates : EvalEnv)
    (slots : List Slot) (final : NativeState.Machine)
    (offsets : List Nat) (inputPlan : Impact.Plan)
    (chunks : List (List Impact.Op))
    (publicNative : List NativeState.Op)
    (groups : List (Option _root_.Bool × List NativeState.Op))
    (publicCells : List NativeState.Cell)
    (scope : GuardedScalarReadEffects ep.effectGuards ep.effects.zipIdx)
    (source : ep.circuit.run ctx values = .ok result)
    (decoded : decodeReads
      (plan.reads.drop (Impact.publicInputReadCount ep.circuit.inputs)) assignment =
        .ok candidates)
    (publicAccepted : Impact.publicInputPlan ep.circuit.inputs {} = .ok inputPlan)
    (compiled : GuardedEffectOperationChunks state ep.effectGuards
      ep.effects.zipIdx inputPlan plan offsets chunks)
    (prefixEval : inputPlan.operations.mapM
      (GenericStateOps.evalOp ctx ((result ++ values) ++ candidates)) = .ok publicNative)
    (chunksEval : (ep.effects.zipIdx.zip chunks).mapM (fun (item, chunk) =>
      evalChunk ctx ((result ++ values) ++ candidates)
        (ep.effectGuardAt item.2) chunk) = .ok groups)
    (prefixRun : NativeState.run publicNative
      (GenericStateEncoding.initial slots) =
        some ⟨[.vector slots], publicCells⟩)
    (trace : GenericStateVM.RunsChunks (groups.map Prod.snd)
      ⟨[.vector slots], publicCells⟩ final) :
    GenericStateCheckedSchedule.CheckedPlan ctx ep plan values assignment
      slots final := by
  have evaluated := eval_plan_of_guarded_constructed_chunks state ep plan ctx
    ((result ++ values) ++ candidates) offsets inputPlan chunks publicNative groups
    scope publicAccepted compiled prefixEval chunksEval
  have effectRun := (GenericStateVM.run_chunks_iff (groups.map Prod.snd)
    ⟨[.vector slots], publicCells⟩ final).mpr trace
  have fullRun : NativeState.run
      (publicNative ++ (groups.map Prod.snd).flatten)
      (GenericStateEncoding.initial slots) = some final := by
    rw [NativeState.run_append, prefixRun, Option.bind_some]
    exact effectRun
  have evaluatedRight : GuardedPlanExecution.evalPlan ctx
      (result ++ (values ++ candidates)) plan =
        .ok (publicNative ++ (groups.map Prod.snd).flatten) := by
    simpa only [List.append_assoc] using evaluated
  have checkedRun : NativeState.run
      (publicNative ++ (groups.map Prod.snd).flatten)
      ⟨[.vector slots], []⟩ = some final := by
    simpa [GenericStateEncoding.initial] using fullRun
  unfold GenericStateCheckedSchedule.CheckedPlan
    GuardedScalarCandidateState.runCheckedCandidates
  simpa [source, decoded, evaluatedRight, Except.toOption, Option.bind,
    Bind.bind] using checkedRun

end Noctium.Verification.GenericStateConverseCheckedPlan
