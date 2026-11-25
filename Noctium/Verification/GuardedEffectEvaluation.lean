import Noctium.Verification.GenericStateAdmissionPrefix
import Noctium.Verification.GenericStateOps

namespace Noctium.Verification.GuardedEffectEvaluation
open Backend

private theorem bind_ok {α β : Type} {first : Except ε α}
    {next : α → Except ε β} {result : β} :
    (first >>= next) = .ok result ↔
      ∃ value, first = .ok value ∧ next value = .ok result := by
  cases first <;> simp [Bind.bind, Except.bind]

/-- One operation suffix for each accepted guarded source effect. -/
inductive GuardedEffectOperationChunks (state : List StateDecl)
    (guards : List (Option (Expr .bool))) :
    List (Effect × Nat) → Impact.Plan → Impact.Plan → List Nat →
      List (List Impact.Op) → Prop where
  | nil (before : Impact.Plan) :
      GuardedEffectOperationChunks state guards [] before before [] []
  | cons {item : Effect × Nat} {rest before next result offsets chunk chunks}
      (step : Impact.appendEffectWithActivity state item.1
        (guards[item.2]?.getD none) before = .ok next)
      (operationPrefix : next.operations = before.operations ++ chunk)
      (tail : GuardedEffectOperationChunks state guards rest
        next result offsets chunks) :
      GuardedEffectOperationChunks state guards (item :: rest) before result
        (next.operations.length :: offsets) (chunk :: chunks)

/-- All-none guard metadata makes every indexed guard lookup unguarded,
including indexes beyond the end of the list. -/
theorem all_none_guard_at (guards : List (Option (Expr .bool)))
    (allNone : guards.all Option.isNone = true) (index : Nat) :
    guards[index]?.getD none = none := by
  induction guards generalizing index with
  | nil => simp
  | cons guard rest ih =>
    simp only [List.all_cons, Bool.and_eq_true] at allNone
    cases index with
    | zero =>
      have headNone := allNone.1
      cases guard with
      | none => rfl
      | some value => simp [Option.isNone] at headNone
    | succ index =>
      simpa using ih allNone.2 index

/-- Replace all-none guarded source chunks with the equivalent unguarded
chunks while preserving their exact offsets and operation lists. -/
theorem unguarded_chunks_of_all_none {state : List StateDecl}
    {guards : List (Option (Expr .bool))}
    {items : List (Effect × Nat)} {initial result : Impact.Plan}
    {offsets : List Nat} {chunks : List (List Impact.Op)}
    (allNone : guards.all Option.isNone = true)
    (chunksShape : GuardedEffectOperationChunks state guards items
      initial result offsets chunks) :
    GuardedEffectOperationChunks state [] items initial result offsets chunks := by
  induction chunksShape with
  | nil before => exact .nil before
  | @cons item rest before next result offsets chunk chunks step operationPrefix tail ih =>
    have guardNone := all_none_guard_at guards allNone item.2
    have unguardedStep : Impact.appendEffectWithActivity state item.1 none before = .ok next := by
      simpa only [guardNone] using step
    exact .cons unguardedStep operationPrefix ih

/-- A well-formed guarded trace plus an explicit per-step operation-prefix
fact yields one exact operation chunk for every source effect. -/
theorem guarded_trace_operation_chunks {state : List StateDecl}
    {guards : List (Option (Expr .bool))}
    {items : List (Effect × Nat)} {initial result : Impact.Plan}
    {offsets : List Nat}
    (trace : Impact.GuardedEffectTrace state guards items initial result offsets)
    (stepPrefix : ∀ {item : Effect × Nat} {before next},
      item ∈ items →
      Impact.appendEffectWithActivity state item.1
        (guards[item.2]?.getD none) before = .ok next →
      ∃ operations, next.operations = before.operations ++ operations) :
    ∃ chunks,
      GuardedEffectOperationChunks state guards items initial result offsets chunks := by
  induction trace with
  | nil before => exact ⟨[], .nil before⟩
  | @cons item rest before next result offsets step tail ih =>
    obtain ⟨operations, operationShape⟩ := stepPrefix (by simp) step
    obtain ⟨chunks, chunksShape⟩ :=
      ih (fun member => stepPrefix (List.mem_cons_of_mem item member))
    exact ⟨operations :: chunks, .cons step operationShape chunksShape⟩

/-- Guarded source chunks partition the final plan's ordered operation list. -/
theorem guarded_chunks_plan_operations
    {state : List StateDecl} {guards : List (Option (Expr .bool))}
    {items : List (Effect × Nat)} {initial result : Impact.Plan}
    {offsets : List Nat} {chunks : List (List Impact.Op)}
    (chunksShape : GuardedEffectOperationChunks state guards items
      initial result offsets chunks) :
    result.operations = initial.operations ++ chunks.flatten := by
  induction chunksShape with
  | nil before => simp
  | @cons item rest before next result offsets chunk chunks step operationPrefix tail ih =>
    calc
      result.operations = next.operations ++ chunks.flatten := ih
      _ = (before.operations ++ chunk) ++ chunks.flatten := by rw [operationPrefix]
      _ = before.operations ++ (chunk :: chunks).flatten := by simp [List.append_assoc]

/-- Successful evaluation of a plan whose source trace has operation prefixes
splits into a prefix group and one native group list per guarded effect. -/
theorem eval_guarded_chunks {state : List StateDecl}
    {guards : List (Option (Expr .bool))}
    {items : List (Effect × Nat)} {initial result : Impact.Plan}
    {offsets : List Nat} {chunks : List (List Impact.Op)}
    (ctx : EvalContext) (env : EvalEnv) (native : List NativeState.Op)
    (chunksShape : GuardedEffectOperationChunks state guards items
      initial result offsets chunks)
    (evaluated : result.operations.mapM
      (GenericStateOps.evalOp ctx env) = .ok native) :
    ∃ publicNative groups,
      initial.operations.mapM (GenericStateOps.evalOp ctx env) = .ok publicNative ∧
      chunks.mapM (fun chunk => chunk.mapM
        (GenericStateOps.evalOp ctx env)) = .ok groups ∧
      native = publicNative ++ groups.flatten := by
  have operationsShape := guarded_chunks_plan_operations chunksShape
  rw [operationsShape, List.mapM_append] at evaluated
  simp only [bind_ok] at evaluated
  rcases evaluated with ⟨publicNative, publicEval, remaining, chunksEval, joined⟩
  obtain ⟨groups, groupsEval, groupFlat⟩ :=
    GenericStateOps.evalOperations_chunks ctx env chunks remaining chunksEval
  have outputEq : publicNative ++ remaining = native := Except.ok.inj joined
  exact ⟨publicNative, groups, publicEval, groupsEval, by
    calc
      native = publicNative ++ remaining := outputEq.symm
      _ = publicNative ++ groups.flatten := by rw [groupFlat]⟩

/-- Production lowering supplies the accepted public prefix and guarded source
trace. The explicit step-prefix premise isolates per-effect operation shape
from evaluation and sequence decomposition. -/
theorem lower_guarded_evaluation {state : List StateDecl}
    {entry : Entrypoint} {plan : Impact.Plan}
    (ctx : EvalContext) (env : EvalEnv) (native : List NativeState.Op)
    (lowered : Impact.lower state entry = .ok plan)
    (evaluated : GenericStateOps.evalPlan ctx env plan = .ok native)
    (stepPrefix : ∀ {item : Effect × Nat} {before next},
      item ∈ entry.effects.zipIdx →
      Impact.appendEffectWithActivity state item.1
        (entry.effectGuards[item.2]?.getD none) before = .ok next →
      ∃ operations, next.operations = before.operations ++ operations) :
    ∃ boundaries inputPlan chunks publicNative groups,
      Impact.lowerWithEffectBoundaries state entry = .ok (plan, boundaries) ∧
      Impact.publicInputPlan entry.circuit.inputs {} = .ok inputPlan ∧
      Impact.GuardedEffectTrace state entry.effectGuards entry.effects.zipIdx
        inputPlan plan boundaries ∧
      GuardedEffectOperationChunks state entry.effectGuards entry.effects.zipIdx
        inputPlan plan boundaries chunks ∧
      inputPlan.operations.mapM (GenericStateOps.evalOp ctx env) = .ok publicNative ∧
      chunks.mapM (fun chunk => chunk.mapM
        (GenericStateOps.evalOp ctx env)) = .ok groups ∧
      native = publicNative ++ groups.flatten := by
  obtain ⟨boundaries, inputPlan, lowerAccepted, inputAccepted, trace⟩ :=
    GenericStateAdmissionPrefix.lower_guarded_effect_trace state entry plan lowered
  obtain ⟨chunks, chunksShape⟩ := guarded_trace_operation_chunks trace stepPrefix
  obtain ⟨publicNative, groups, publicEval, groupsEval, sequence⟩ :=
    eval_guarded_chunks ctx env native chunksShape
      (by simpa only [GenericStateOps.evalPlan] using evaluated)
  exact ⟨boundaries, inputPlan, chunks, publicNative, groups, lowerAccepted,
    inputAccepted, trace, chunksShape, publicEval, groupsEval, sequence⟩

end Noctium.Verification.GuardedEffectEvaluation
