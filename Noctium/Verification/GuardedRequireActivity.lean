import Noctium.Verification.GuardedPlanAssertions

namespace Noctium.Verification.GuardedRequireActivity

open Backend
open GenericStateCheckedReadTrace

private theorem guarded_require_occurrence_totalized_assertion
    (guards : List (Option (Expr .bool))) (items : List (Effect × Nat))
    (ordinal : Nat) (condition guard : Expr .bool) (index : Nat)
    (occurrence : (Effect.require condition, index) ∈ items)
    (selected : guards[index]?.getD none = some guard) :
    Impact.totalizeActivityCondition guard condition ∈
      (GuardedPlanAssertions.guardedAssertionChunks guards items ordinal).flatten := by
  induction items generalizing ordinal with
  | nil => cases occurrence
  | cons item rest ih =>
    rcases List.mem_cons.mp occurrence with same | later
    · cases item with
      | mk effect itemIndex =>
        simp only [Prod.mk.injEq] at same
        rcases same with ⟨rfl, rfl⟩
        simp only [GuardedPlanAssertions.guardedAssertionChunks,
          List.flatten_cons, List.mem_append]
        left
        simp [GuardedPlanAssertions.guardedEffectAssertionChunk, selected]
    · simp only [GuardedPlanAssertions.guardedAssertionChunks,
        List.flatten_cons, List.mem_append]
      exact Or.inr (ih (ordinal +
        (GenericStateCheckedReadTrace.effectReadChunk item.1 ordinal).length)
        later)

private theorem lower_guarded_require_assertion (state : List StateDecl)
    (entry : Entrypoint) (plan : Impact.Plan) (condition guard : Expr .bool)
    (index : Nat) (lowered : Impact.lower state entry = .ok plan)
    (scope : GuardedScalarReadEffects entry.effectGuards entry.effects.zipIdx)
    (occurrence : (Effect.require condition, index) ∈ entry.effects.zipIdx)
    (selected : entry.effectGuards[index]?.getD none = some guard) :
    Impact.totalizeActivityCondition guard condition ∈ plan.guards := by
  obtain ⟨_, inputPlan, _, _, trace⟩ :=
    GenericStateAdmissionPrefix.lower_guarded_effect_trace state entry plan lowered
  have assertions := GuardedPlanAssertions.guarded_trace_plan_assertions state
    entry.effectGuards entry.effects.zipIdx inputPlan plan _ scope trace
  rw [assertions]
  exact List.mem_append_right _ (guarded_require_occurrence_totalized_assertion
    entry.effectGuards entry.effects.zipIdx inputPlan.reads.length condition guard index
    occurrence selected)

/-- Every successfully evaluated assertion set from actual lowering contains
the selected guarded requirement's totalized assertion. Evaluating that
assertion successfully forces the selected source guard to evaluate. -/
theorem lower_guarded_require_activity (state : List StateDecl)
    (entry : Entrypoint) (plan : Impact.Plan) (ctx : EvalContext) (env : EvalEnv)
    (condition guard : Expr .bool) (index : Nat)
    (lowered : Impact.lower state entry = .ok plan)
    (scope : GuardedScalarReadEffects entry.effectGuards entry.effects.zipIdx)
    (occurrence : (Effect.require condition, index) ∈ entry.effects.zipIdx)
    (selected : entry.effectGuards[index]?.getD none = some guard)
    (asserts : ∀ assertion ∈ plan.guards, assertion.eval ctx env = .ok true) :
    ∃ active, guard.eval ctx env = .ok active := by
  have assertionMember := lower_guarded_require_assertion state entry plan
    condition guard index lowered scope occurrence selected
  have assertionEval := asserts _ assertionMember
  obtain ⟨name, shape, _, _⟩ :=
    Impact.totalizeActivityCondition_shape guard condition
  rw [shape] at assertionEval
  cases guardResult : guard.eval ctx env with
  | error message =>
    simp [Expr.eval, guardResult, Bind.bind, Except.bind] at assertionEval
  | ok active => exact ⟨active, rfl⟩

end Noctium.Verification.GuardedRequireActivity
