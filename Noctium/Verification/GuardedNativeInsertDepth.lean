import Noctium.Verification.GuardedPlanExecution

namespace Noctium.Verification.GuardedNativeInsertDepth

open Backend
open Noctium.Verification.GuardedPlanExecution

private theorem mapM_member {α β : Type} {function : α → Except String β}
    {values : List α} {results : List β}
    (success : values.mapM function = .ok results) (result : β)
    (member : result ∈ results) :
    ∃ value ∈ values, function value = .ok result := by
  induction values generalizing results with
  | nil => cases success; simp at member
  | cons value rest ih =>
      simp only [List.mapM_cons] at success
      cases first : function value with
      | error message => simp [first, Bind.bind, Except.bind] at success
      | ok firstResult =>
          cases tail : rest.mapM function with
          | error message => simp [first, tail, Bind.bind, Except.bind] at success
          | ok tailResults =>
              have resultEq : results = firstResult :: tailResults := by
                simpa [first, tail, Bind.bind, Except.bind, Pure.pure, Except.pure] using success.symm
              subst results
              rcases List.mem_cons.mp member with same | later
              · subst result
                exact ⟨value, by simp, first⟩
              · obtain ⟨found, foundMember, foundEval⟩ := ih tail later
                exact ⟨found, List.mem_cons_of_mem _ foundMember, foundEval⟩

private theorem evalOp_insert_source (ctx : EvalContext) (env : EvalEnv)
    (operation : Impact.Op) (depth : Nat)
    (evaluated : GenericStateOps.evalOp ctx env operation = .ok (.insert depth)) :
    operation = Impact.Op.insert depth := by
  unfold GenericStateOps.evalOp at evaluated
  split at evaluated
  all_goals simp_all [Pure.pure, Except.pure, Bind.bind, Except.bind]
  all_goals split at evaluated <;> simp_all

private theorem active_insert_source (ctx : EvalContext) (env : EvalEnv)
    (activity : Option Bool) (operation : Impact.Op) (outputs : List NativeState.Op)
    (depth : Nat)
    (evaluated : evalOperation ctx env activity operation = .ok outputs)
    (member : NativeState.Op.insert depth ∈ outputs) :
    operation = Impact.Op.insert depth := by
  unfold evalOperation at evaluated
  by_cases active : activity.getD true
  · rw [ite_eq_left active] at evaluated
    cases source : GenericStateOps.evalOp ctx env operation with
    | error message =>
      rw [source] at evaluated
      cases evaluated
    | ok result =>
      rw [source] at evaluated
      have outputEq : [result] = outputs := by injection evaluated
      rw [← outputEq] at member
      simp only [List.mem_singleton] at member
      subst result
      exact evalOp_insert_source ctx env operation depth source
  · rw [ite_eq_right active] at evaluated
    cases evaluated
    simp at member

/-- Executed insert depths come from that same plan. Skipped operations emit nothing. -/
theorem evalPlan_inserts_fit (ctx : EvalContext) (env : EvalEnv)
    (plan : Impact.Plan) (ops : List NativeState.Op)
    (evaluated : GuardedPlanExecution.evalPlan ctx env plan = .ok ops)
    (fit : ∀ depth, Impact.Op.insert depth ∈ plan.operations → depth < 16) :
    ∀ depth, NativeState.Op.insert depth ∈ ops → depth < 16 := by
  intro depth member
  obtain ⟨_aligned, activities, perOperation, _guardEval, operationEval, opsEq⟩ :=
    GuardedPlanExecution.evalPlan_success ctx env plan ops evaluated
  rw [opsEq] at member
  obtain ⟨group, groupMember, outputMember⟩ := List.mem_flatten.mp member
  obtain ⟨item, itemMember, itemEval⟩ := mapM_member operationEval group groupMember
  rcases item with ⟨operation, activity⟩
  have operationMember := (List.of_mem_zip itemMember).1
  rw [active_insert_source ctx env activity operation group depth itemEval outputMember]
    at operationMember
  exact fit depth operationMember

end Noctium.Verification.GuardedNativeInsertDepth
