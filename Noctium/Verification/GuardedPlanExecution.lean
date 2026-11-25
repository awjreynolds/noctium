import Noctium.Verification.GuardedPlanActivity
import Noctium.Verification.GenericStateOps

namespace Noctium.Verification.GuardedPlanExecution

open Backend
open Noctium.Verification.GuardedEffectEvaluation
open Noctium.Verification.GuardedPlanActivity
open Noctium.Verification.GenericStateOps

private theorem bind_ok {α β : Type} {first : Except ε α}
    {next : α → Except ε β} {result : β} :
    (first >>= next) = .ok result ↔
      ∃ value, first = .ok value ∧ next value = .ok result := by
  cases first <;> simp [Bind.bind, Except.bind]

/-- Evaluate a compiler effect chunk under one effective guard. The first
component records the exact guard result. Evaluating the guard before the
chunk also handles zero-operation effects such as guarded requirements. -/
def evalChunk (ctx : EvalContext) (complete : EvalEnv)
    (guard : Option (Expr .bool)) (chunk : List Impact.Op) :
    Except String (Option Bool × List NativeState.Op) :=
  match guard.mapM (fun condition => condition.eval ctx complete) with
  | .error message => .error message
  | .ok activity =>
    if activity.getD true then
      (chunk.mapM (GenericStateOps.evalOp ctx complete)).map
        (fun operations => (activity, operations))
    else .ok (activity, [])

/-- Evaluate one operation under its already evaluated activity guard. A
false activity returns no native operations without evaluating operands. -/
def evalOperation (ctx : EvalContext) (complete : EvalEnv)
    (activity : Option Bool) (operation : Impact.Op) : Except String (List NativeState.Op) :=
  if activity.getD true then
    (GenericStateOps.evalOp ctx complete operation).map List.singleton
  else .ok []

def evalActivity (ctx : EvalContext) (complete : EvalEnv)
    (guard : Option (Expr .bool)) : Except String (Option Bool) :=
  guard.mapM (fun condition => condition.eval ctx complete)

private def evalPlanBody (ctx : EvalContext) (complete : EvalEnv)
    (plan : Impact.Plan) : Except String (List NativeState.Op) :=
  match (GuardedPlanActivity.operationGuards plan).mapM (evalActivity ctx complete) with
  | .error message => .error message
  | .ok activities =>
    match (plan.operations.zip activities).mapM (fun (operation, activity) =>
        evalOperation ctx complete activity operation) with
    | .error message => .error message
    | .ok perOperation => .ok perOperation.flatten

/-- Evaluate the operation list using its effective per-operation activity
metadata. Malformed nonempty metadata rejects instead of truncating at `zip`.
An empty guard list expands to unconditional entries through `operationGuards`. -/
def evalPlan (ctx : EvalContext) (complete : EvalEnv) (plan : Impact.Plan) :
    Except String (List NativeState.Op) :=
  if (GuardedPlanActivity.operationGuards plan).length = plan.operations.length then
    evalPlanBody ctx complete plan
  else .error "Impact operation activity guard count mismatch"

/-- Successful guard-aware plan evaluation exposes the aligned Boolean
activity schedule, each per-operation output list, and their VM order. -/
theorem evalPlan_success (ctx : EvalContext) (complete : EvalEnv)
    (plan : Impact.Plan) (native : List NativeState.Op)
    (accepted : evalPlan ctx complete plan = .ok native) :
    (GuardedPlanActivity.operationGuards plan).length = plan.operations.length ∧
    ∃ activities perOperation,
      (GuardedPlanActivity.operationGuards plan).mapM (fun guard =>
        guard.mapM (fun condition => condition.eval ctx complete)) = .ok activities ∧
      (plan.operations.zip activities).mapM (fun (operation, activity) =>
        evalOperation ctx complete activity operation) = .ok perOperation ∧
      native = perOperation.flatten := by
  by_cases aligned : (GuardedPlanActivity.operationGuards plan).length = plan.operations.length
  · simp only [evalPlan, aligned, ite_true] at accepted
    unfold evalPlanBody at accepted
    cases activitiesEval :
        (GuardedPlanActivity.operationGuards plan).mapM (evalActivity ctx complete) with
    | error message => simp [activitiesEval] at accepted
    | ok activities =>
      cases operationsEval : (plan.operations.zip activities).mapM
          (fun (operation, activity) => evalOperation ctx complete activity operation) with
      | error message => simp [activitiesEval, operationsEval] at accepted
      | ok perOperation =>
        simp only [activitiesEval, operationsEval] at accepted
        have resultEq := Except.ok.inj accepted
        exact ⟨aligned, activities, perOperation, activitiesEval, operationsEval, resultEq.symm⟩
  · simp [evalPlan, aligned] at accepted

/-- Successful chunk evaluation exposes the exact guard evaluation and the
active-or-empty operation segment. -/
theorem evalChunk_success (ctx : EvalContext) (complete : EvalEnv)
    (guard : Option (Expr .bool)) (chunk : List Impact.Op)
    (activity : Option Bool) (operations : List NativeState.Op)
    (accepted : evalChunk ctx complete guard chunk = .ok (activity, operations)) :
    guard.mapM (fun condition => condition.eval ctx complete) = .ok activity ∧
      (if activity.getD true then
        chunk.mapM (GenericStateOps.evalOp ctx complete)
      else .ok []) = .ok operations := by
  unfold evalChunk at accepted
  cases guardResult : guard.mapM (fun condition => condition.eval ctx complete) with
  | error message => simp [guardResult] at accepted
  | ok foundActivity =>
    cases active : foundActivity.getD true with
    | false =>
      simp only [guardResult, active] at accepted
      have pairEq := Except.ok.inj accepted
      have activityEq : foundActivity = activity := congrArg Prod.fst pairEq
      have operationsEq : ([] : List NativeState.Op) = operations := congrArg Prod.snd pairEq
      subst activity
      subst operations
      exact ⟨by simp, by simp [active]⟩
    | true =>
      cases chunkResult : chunk.mapM (GenericStateOps.evalOp ctx complete) with
      | error message => simp [guardResult, active, chunkResult, Except.map] at accepted
      | ok foundOperations =>
        simp only [guardResult, active, chunkResult, Except.map] at accepted
        have pairEq := Except.ok.inj accepted
        have activityEq : foundActivity = activity := congrArg Prod.fst pairEq
        have operationsEq : foundOperations = operations := congrArg Prod.snd pairEq
        subst activity
        subst operations
        exact ⟨by simp, by simp [active]⟩

/-- Evaluate a chunk from one already evaluated activity result per operation. -/
theorem evalChunk_of_operations (ctx : EvalContext) (complete : EvalEnv)
    (guard : Option (Expr .bool)) (chunk : List Impact.Op)
    (activity : Option Bool) (outputs : List (List NativeState.Op))
    (activityEval : evalActivity ctx complete guard = .ok activity)
    (operationsEval :
      (chunk.zip (List.replicate chunk.length activity)).mapM
        (fun (operation, selected) => evalOperation ctx complete selected operation) =
          .ok outputs) :
    evalChunk ctx complete guard chunk = .ok (activity, outputs.flatten) := by
  have flattenEval :
      (if activity.getD true then
        chunk.mapM (GenericStateOps.evalOp ctx complete)
      else .ok []) = .ok outputs.flatten := by
    induction chunk generalizing outputs with
    | nil =>
      simp at operationsEval
      have outputsEq : outputs = [] := (Except.ok.inj operationsEval).symm
      subst outputs
      cases active : activity.getD true <;> rfl
    | cons operation chunk ih =>
      simp only [List.length_cons, List.replicate_succ, List.zip_cons_cons,
        List.mapM_cons] at operationsEval
      have operationBind :
          (evalOperation ctx complete activity operation >>= fun headOutput =>
            do
              let tailOutput ← (chunk.zip (List.replicate chunk.length activity)).mapM
                (fun (operation, selected) => evalOperation ctx complete selected operation)
              pure (headOutput :: tailOutput)) = .ok outputs := by
        simpa only [List.mapM_cons] using operationsEval
      rcases bind_ok.mp operationBind with ⟨headOutput, headEval, tailOutputMapEval⟩
      cases tailEval :
          (chunk.zip (List.replicate chunk.length activity)).mapM
            (fun (operation, selected) => evalOperation ctx complete selected operation) with
      | error message =>
        rw [tailEval] at tailOutputMapEval
        change (Except.error message : Except String (List (List NativeState.Op))) = .ok outputs at tailOutputMapEval
        cases tailOutputMapEval
      | ok tailOutput =>
        rw [tailEval] at tailOutputMapEval
        change Except.ok (headOutput :: tailOutput) = .ok outputs at tailOutputMapEval
        have outputsEq : outputs = headOutput :: tailOutput := by
          exact (Except.ok.inj tailOutputMapEval).symm
        subst outputs
        cases active : activity.getD true with
        | false =>
          have headOutputEq : headOutput = [] := by
            simpa [evalOperation, active, Except.map] using headEval
          rw [headOutputEq]
          have tailEmpty : tailOutput.flatten = [] := by
            simpa [active] using ih tailOutput tailEval
          simp [tailEmpty]
        | true =>
          cases nativeOutputEval : GenericStateOps.evalOp ctx complete operation with
          | error message => simp [evalOperation, active, nativeOutputEval, Except.map] at headEval
          | ok nativeOutput =>
            have headOutputEq : List.singleton nativeOutput = headOutput := by
              simpa [evalOperation, active, nativeOutputEval, Except.map] using headEval
            rw [← headOutputEq]
            have tailFlatten := ih tailOutput tailEval
            have tailResult : chunk.mapM (GenericStateOps.evalOp ctx complete) =
                .ok tailOutput.flatten := by
              simpa [active] using tailFlatten
            simp [nativeOutputEval, tailResult, List.mapM_cons,
              Except.map, Functor.map, List.singleton]
            rfl
  change guard.mapM (fun condition => condition.eval ctx complete) = .ok activity at activityEval
  unfold evalChunk
  rw [activityEval]
  cases active : activity.getD true with
  | false =>
    have tailEmpty : outputs.flatten = [] := by
      simpa [active] using flattenEval
    simp [active, tailEmpty]
  | true =>
    have outputEval : chunk.mapM (GenericStateOps.evalOp ctx complete) = .ok outputs.flatten := by
      simpa [active] using flattenEval
    simp [active, outputEval, Except.map]

/-- Unconditional per-operation evaluation agrees with ordinary chunk evaluation. -/
theorem evalOperations_unconditional (ctx : EvalContext) (complete : EvalEnv)
    (chunk : List Impact.Op) (outputs : List (List NativeState.Op))
    (operationsEval :
      (chunk.zip (List.replicate chunk.length (none : Option Bool))).mapM
        (fun (operation, activity) => evalOperation ctx complete activity operation) =
          .ok outputs) :
    chunk.mapM (GenericStateOps.evalOp ctx complete) = .ok outputs.flatten := by
  have chunkEval := evalChunk_of_operations ctx complete none chunk none outputs
    (by rfl) operationsEval
  simpa using (evalChunk_success ctx complete none chunk none outputs.flatten chunkEval).2

end Noctium.Verification.GuardedPlanExecution
