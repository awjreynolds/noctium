import Noctium.Verification.GuardedOperationAlignment
import Noctium.Verification.GuardedPlanExecution

namespace Noctium.Verification.GuardedOperationActivity

open Backend
open GuardedEffectEvaluation
open GuardedOperationAlignment
open GuardedPlanActivity
open GuardedPlanExecution
open GenericStateCheckedReadTrace

private theorem except_bind_ok {α β : Type} {ε : Type}
    {first : Except ε α} {next : α → Except ε β} {result : β}
    (accepted : first >>= next = .ok result) :
    ∃ value, first = .ok value ∧ next value = .ok result := by
  cases first with
  | error message => simp [Bind.bind, Except.bind] at accepted
  | ok value =>
    simp only [Bind.bind, Except.bind] at accepted
    exact ⟨value, rfl, accepted⟩

private theorem mapM_member_ok {α β : Type} {function : α → Except String β}
    {values : List α} {results : List β} {value : α}
    (accepted : values.mapM function = .ok results)
    (member : value ∈ values) :
    ∃ result, function value = .ok result := by
  induction values generalizing results with
  | nil => simp at member
  | cons head tail ih =>
    simp only [List.mapM_cons] at accepted
    cases headAccepted : function head with
    | error message => simp [headAccepted, Bind.bind, Except.bind] at accepted
    | ok headResult =>
      cases tailAccepted : tail.mapM function with
      | error message =>
        simp [headAccepted, tailAccepted, Bind.bind, Except.bind] at accepted
      | ok tailResults =>
        simp [headAccepted, tailAccepted, Bind.bind, Except.bind] at accepted
        rcases List.mem_cons.mp member with equal | tailMember
        · subst value
          exact ⟨headResult, headAccepted⟩
        · obtain ⟨result, resultAccepted⟩ := ih tailAccepted tailMember
          exact ⟨result, resultAccepted⟩

/-- Successful plan evaluation means every guard in the aligned plan guard
list evaluates successfully. -/
theorem operationGuard_eval_success (ctx : EvalContext) (env : EvalEnv)
    (plan : Impact.Plan) (native : List NativeState.Op)
    (accepted : evalPlan ctx env plan = .ok native)
    {guard : Option (Expr .bool)}
    (member : guard ∈ operationGuards plan) :
    ∃ activity, evalActivity ctx env guard = .ok activity := by
  obtain ⟨_, activities, _, guardsAccepted, _, _⟩ :=
    evalPlan_success ctx env plan native accepted
  change (operationGuards plan).mapM (evalActivity ctx env) = .ok activities at guardsAccepted
  exact mapM_member_ok guardsAccepted member

/-- A nonempty compiler chunk contributes its source guard to the final
plan's effective operation guards. -/
theorem compiled_nonempty_chunk_guard_mem {state : List StateDecl}
    {guards : List (Option (Expr .bool))} {items : List (Effect × Nat)}
    {before plan : Impact.Plan} {offsets : List Nat}
    {chunks : List (List Impact.Op)}
    (scope : GuardedScalarReadEffects guards items)
    (chunksShape : GuardedEffectOperationChunks state guards items
      before plan offsets chunks)
    (aligned : (operationGuards before).length = before.operations.length)
    {item : Effect × Nat} {chunk : List Impact.Op}
    (member : (item, chunk) ∈ items.zip chunks)
    (nonempty : chunk ≠ []) :
    guards[item.2]?.getD none ∈ operationGuards plan := by
  obtain ⟨guardShape, _⟩ := operationGuards_of_chunks scope chunksShape aligned
  have guardReplicated : guards[item.2]?.getD none ∈
      List.replicate chunk.length (guards[item.2]?.getD none) := by
    cases chunk with
    | nil => cases nonempty rfl
    | cons operation rest => simp
  have guardInChunks : guards[item.2]?.getD none ∈
      effectOperationGuards guards items chunks := by
    unfold effectOperationGuards
    apply List.mem_flatMap.mpr
    exact ⟨(item, chunk), member, guardReplicated⟩
  rw [guardShape]
  exact List.mem_append_right _ guardInChunks

/-- Every nonempty compiler chunk has a source guard that succeeds under the
same environment whenever guard-aware plan evaluation succeeds. -/
theorem compiled_nonempty_chunk_guard_eval_success {state : List StateDecl}
    {guards : List (Option (Expr .bool))} {items : List (Effect × Nat)}
    {before plan : Impact.Plan} {offsets : List Nat}
    {chunks : List (List Impact.Op)}
    (scope : GuardedScalarReadEffects guards items)
    (chunksShape : GuardedEffectOperationChunks state guards items
      before plan offsets chunks)
    (aligned : (operationGuards before).length = before.operations.length)
    (ctx : EvalContext) (env : EvalEnv) (native : List NativeState.Op)
    (accepted : evalPlan ctx env plan = .ok native)
    {item : Effect × Nat} {chunk : List Impact.Op}
    (member : (item, chunk) ∈ items.zip chunks)
    (nonempty : chunk ≠ []) :
    guards[item.2]?.getD none ∈ operationGuards plan ∧
      ∃ activity,
        evalActivity ctx env (guards[item.2]?.getD none) = .ok activity := by
  have guardMember := compiled_nonempty_chunk_guard_mem scope chunksShape aligned
    member nonempty
  exact ⟨guardMember,
    operationGuard_eval_success ctx env plan native accepted guardMember⟩

end Noctium.Verification.GuardedOperationActivity
