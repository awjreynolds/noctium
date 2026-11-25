import Noctium.Verification.GuardedPlanExecution
import Noctium.Verification.ImpactStatementScalar

namespace Noctium.Verification.GuardedStatementWidths

open Backend
open Noctium.Verification.GuardedPlanActivity
open Noctium.Verification.GuardedPlanExecution
open Noctium.Verification.GenericStateOps
open Noctium.Verification.ImpactStatementScalar

private theorem bind_ok {α β : Type} {first : Except String α}
    {next : α → Except String β} {result : β} :
    (first >>= next) = .ok result ↔
      ∃ value, first = .ok value ∧ next value = .ok result := by
  cases first <;> simp [Bind.bind, Except.bind]

private theorem mapM_length {α β : Type} {function : α → Except String β}
    {values : List α} {results : List β}
    (success : values.mapM function = .ok results) : results.length = values.length := by
  induction values generalizing results with
  | nil => cases success; rfl
  | cons value rest ih =>
      simp only [List.mapM_cons, bind_ok] at success
      rcases success with ⟨first, firstResult, tail, tailResult, equal⟩
      cases equal
      simp only [List.length_cons, ih tailResult]

private theorem evalFields_length (ctx : EvalContext) (env : EvalEnv)
    (fields : List Impact.Scalar) (values : List NativeRelation.Scalar)
    (accepted : GenericStateOps.evalFields ctx env fields = .ok values) :
    values.length = fields.length := by
  unfold GenericStateOps.evalFields at accepted
  exact mapM_length accepted

private theorem opFields_native_fields_length (operation : NativeState.Op) :
    (ImpactStatementScalar.opFields operation).length =
      (NativeState.Op.fields operation).length := by
  rw [ImpactStatementScalar.opFields_length]
  cases operation <;>
    simp [ImpactStatementScalar.opFieldWidth, NativeState.Op.fields,
      NativeState.Cell.fields]

private theorem evalOp_field_width (ctx : EvalContext) (env : EvalEnv)
    (operation : Impact.Op) (native : NativeState.Op)
    (modulus : ctx.modulus = Field.modulus)
    (admitted : GenericStateOps.FieldAdmitted operation)
    (accepted : GenericStateOps.evalOp ctx env operation = .ok native) :
    (ImpactStatementScalar.opFields native).length = operation.fields.length := by
  have fields := GenericStateOps.evalOp_fields ctx env operation native
    modulus admitted accepted
  rw [opFields_native_fields_length]
  exact evalFields_length ctx env operation.fields
    (NativeState.Op.fields native) fields

private theorem evalOperation_widths (ctx : EvalContext) (env : EvalEnv)
    (activity : Option _root_.Bool) (operation : Impact.Op)
    (native : List NativeState.Op)
    (modulus : ctx.modulus = Field.modulus)
    (admitted : GenericStateOps.FieldAdmitted operation)
    (accepted : evalOperation ctx env activity operation = .ok native) :
    native.map (fun op => (ImpactStatementScalar.opFields op).length) =
      if activity.getD true then [operation.fields.length] else [] := by
  by_cases active : activity.getD true
  · cases evaluated : GenericStateOps.evalOp ctx env operation with
    | error message =>
        simp [GuardedPlanExecution.evalOperation, active, evaluated] at accepted
        cases accepted
    | ok op =>
        have accepted' : List.singleton op = native := by
          simpa [GuardedPlanExecution.evalOperation, active, evaluated,
            Except.map] using accepted
        have nativeEq : native = [op] := by
          simpa only [List.singleton] using accepted'.symm
        have width := evalOp_field_width ctx env operation op modulus admitted evaluated
        rw [nativeEq]
        change [(ImpactStatementScalar.opFields op).length] =
          if activity.getD true then [operation.fields.length] else []
        rw [width]
        simp [active]
  · have accepted' :
        (Except.ok [] : Except String (List NativeState.Op)) = .ok native := by
      simpa [GuardedPlanExecution.evalOperation, active] using accepted
    have nativeEq : native = [] := (Except.ok.inj accepted').symm
    rw [nativeEq]
    simp [active]

private theorem evalScheduled_widths (ctx : EvalContext) (env : EvalEnv)
    (operations : List Impact.Op) (activities : List (Option _root_.Bool))
    (perOperation : List (List NativeState.Op))
    (modulus : ctx.modulus = Field.modulus)
    (admitted : ∀ operation ∈ operations, GenericStateOps.FieldAdmitted operation)
    (accepted : (operations.zip activities).mapM (fun item =>
      evalOperation ctx env item.2 item.1) = .ok perOperation) :
    perOperation.flatten.map (fun op => (ImpactStatementScalar.opFields op).length) =
      ((operations.zip activities).filter (fun item => item.2.getD true)).map
        (fun item => item.1.fields.length) := by
  induction operations generalizing activities perOperation with
  | nil =>
      change (Except.ok [] : Except String (List (List NativeState.Op))) =
        .ok perOperation at accepted
      have perOperationEq : perOperation = [] := (Except.ok.inj accepted).symm
      subst perOperation
      simp
  | cons operation rest ih =>
      cases activities with
      | nil =>
          change (Except.ok [] : Except String (List (List NativeState.Op))) =
            .ok perOperation at accepted
          have perOperationEq : perOperation = [] := (Except.ok.inj accepted).symm
          subst perOperation
          simp
      | cons activity activities =>
          simp only [List.zip_cons_cons, List.mapM_cons] at accepted
          cases head : evalOperation ctx env activity operation with
          | error message =>
              simp [head, Bind.bind, Except.bind] at accepted
          | ok headOps =>
              cases tail : (rest.zip activities).mapM (fun item =>
                  evalOperation ctx env item.2 item.1) with
              | error message =>
                  simp [head, tail, Bind.bind, Except.bind] at accepted
              | ok tailOps =>
                  have accepted' :
                      (Except.ok (headOps :: tailOps) :
                        Except String (List (List NativeState.Op))) = .ok perOperation := by
                    simpa [head, tail, Bind.bind, Except.bind,
                      Pure.pure, Except.pure] using accepted
                  have perOperationEq : perOperation = headOps :: tailOps :=
                    (Except.ok.inj accepted').symm
                  subst perOperation
                  have headWidths := evalOperation_widths ctx env activity operation
                    headOps modulus (admitted operation (by simp)) head
                  have tailAdmitted : ∀ item ∈ rest,
                      GenericStateOps.FieldAdmitted item := by
                    intro item member
                    exact admitted item (by simp [member])
                  have tailWidths := ih activities tailOps tailAdmitted tail
                  by_cases active : activity.getD true
                  · simp [List.flatten_cons, List.map_append, active,
                      headWidths, tailWidths]
                  · simp [List.flatten_cons, List.map_append, active,
                      headWidths, tailWidths]

/-- Successful guard-aware evaluation preserves source field widths for each
active source operation, in order, under scalar field-domain admission. -/
theorem evalPlan_active_field_widths (ctx : EvalContext) (env : EvalEnv)
    (plan : Impact.Plan) (native : List NativeState.Op)
    (accepted : GuardedPlanExecution.evalPlan ctx env plan = .ok native)
    (modulus : ctx.modulus = Field.modulus)
    (fieldAdmitted : ∀ operation ∈ plan.operations,
      GenericStateOps.FieldAdmitted operation)
    (activities : List (Option _root_.Bool))
    (activityEval : (GuardedPlanActivity.operationGuards plan).mapM
      (GuardedPlanExecution.evalActivity ctx env) = .ok activities) :
    native.map (fun op => (ImpactStatementScalar.opFields op).length) =
      ((plan.operations.zip activities).filter (fun item => item.2.getD true)).map
        (fun item => item.1.fields.length) := by
  obtain ⟨_aligned, evaluatedActivities, perOperation, evaluated, operationsEval,
    nativeEq⟩ := GuardedPlanExecution.evalPlan_success ctx env plan native accepted
  have activitiesEq : evaluatedActivities = activities :=
    Except.ok.inj (evaluated.symm.trans activityEval)
  subst evaluatedActivities
  rw [nativeEq]
  exact evalScheduled_widths ctx env plan.operations activities perOperation
    modulus fieldAdmitted operationsEval

end Noctium.Verification.GuardedStatementWidths
