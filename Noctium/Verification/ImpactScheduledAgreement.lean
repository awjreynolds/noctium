import Noctium.Verification.ImpactOperationAgreement
import Noctium.Verification.GuardedPlanExecution

namespace Noctium.Verification.ImpactScheduledAgreement

open Lean Backend NativeState
open ImpactExpressionEvaluation ImpactExpressionAgreement ImpactExpressionSchedule
open ImpactOperationAgreement ImpactReferenceEvaluation ImpactWireDecoder
open ImpactWireSoundness ScalarNormalization GuardedPlanExecution

/-- Evaluate an optional activity guard from its decoded wire JSON. An absent
guard activates the operation. Malformed, failed, and non-Boolean guards reject. -/
def evaluateActivityGuard (fuel : Nat) (ctx : EvalContext) (env : EvalEnv)
    (guard : Option Json) : Option (Option _root_.Bool) :=
  match guard with
  | none => some none
  | some raw =>
      match ImpactExpressionEvaluation.evaluate fuel ctx env raw with
      | some (.bool activity) => some (some activity)
      | _ => none

/-- Evaluate a decoded schedule item. The operand evaluator runs only after a
missing or true guard. A false guard returns an empty operation list. -/
def evaluateScheduledOperation (fuel : Nat) (ctx : EvalContext) (env : EvalEnv)
    (scheduled : ImpactWireDecoder.ScheduledOperation) : Option (List NativeState.Op) :=
  match evaluateActivityGuard fuel ctx env scheduled.guard with
  | none => none
  | some activity =>
      if activity.getD _root_.Bool.true then
        (ImpactOperationAgreement.evaluateOperation fuel ctx env scheduled.operation).map
          List.singleton
      else some []

/-- Run only successfully decoded schedules. Decoder errors remain rejection. -/
def evaluateDecodedOperation (fuel : Nat) (ctx : EvalContext) (env : EvalEnv)
    (decoded : Except String ImpactWireDecoder.ScheduledOperation) :
    Option (List NativeState.Op) :=
  decoded.toOption.bind (evaluateScheduledOperation fuel ctx env)

@[simp] theorem evaluateDecodedOperation_rejectsDecoderError (fuel : Nat)
    (ctx : EvalContext) (env : EvalEnv) (message : String) :
    evaluateDecodedOperation fuel ctx env
      (.error message : Except String ImpactWireDecoder.ScheduledOperation) = none := rfl

theorem evaluateActivityGuard_rejectsFailure (fuel : Nat) (ctx : EvalContext)
    (env : EvalEnv) (raw : Json)
    (rejected : ImpactExpressionEvaluation.evaluate fuel ctx env raw = none) :
    evaluateActivityGuard fuel ctx env (some raw) = none := by
  unfold evaluateActivityGuard
  simp [rejected]

private theorem evaluateActivityGuard_toJson (ctx : EvalContext)
    (modulus : ctx.modulus = Field.modulus) {types : TypeEnv} {env : EvalEnv}
    (guard : Option (Expr .bool))
    (supported : ∀ expression, guard = some expression → ScalarExpression expression)
    (valid : ∀ expression, guard = some expression →
      expression.validate Capabilities.scalarFragment types = .ok ())
    (typed : TypedScalarEnv types env) :
    ∃ minimum, ∀ fuel, minimum ≤ fuel →
      evaluateActivityGuard fuel ctx env (guard.map NativeExpression.toJson) =
        (GuardedPlanExecution.evalActivity ctx env guard).toOption := by
  cases guard with
  | none =>
      refine ⟨0, ?_⟩
      intro fuel enough
      simp [evaluateActivityGuard, GuardedPlanExecution.evalActivity,
        Except.toOption, Pure.pure, Except.pure]
  | some expression =>
      have expressionSupported : ScalarExpression expression := supported expression rfl
      have expressionValid :
          expression.validate Capabilities.scalarFragment types = .ok () := valid expression rfl
      obtain ⟨minimum, agrees⟩ := ImpactExpressionAgreement.evaluate_toJson
        ctx modulus expressionSupported
      refine ⟨minimum, ?_⟩
      intro fuel enough
      have expressionAgrees := agrees fuel enough types env expressionValid typed
      unfold evaluateActivityGuard
      simp only [Option.map_some]
      rw [expressionAgrees]
      cases evaluated : expression.eval ctx env <;>
        simp [GuardedPlanExecution.evalActivity, evaluated, Value.pack,
          Except.toOption, Except.map, Functor.map]

/-- Executing the compiler's encoded single operation gives exactly the
guarded source operation result. The bound covers both guard and operand
evaluation. -/
theorem evaluate_nativeOperationJson_agrees (ctx : EvalContext)
    (modulus : ctx.modulus = Field.modulus)
    {types : TypeEnv} {env : EvalEnv} {guard : Option (Expr .bool)}
    {operation : Impact.Op} {projected : ImpactWireDecoder.Operation}
    (projects : ImpactWireSoundness.Projects operation projected)
    (admitted : ScalarOperandAdmission operation)
    (operandsValid : ImpactOperationAgreement.SourceOperandsValid types operation)
    (guardSupported : ∀ expression, guard = some expression → ScalarExpression expression)
    (guardValid : ∀ expression, guard = some expression →
      expression.validate Capabilities.scalarFragment types = .ok ())
    (typed : TypedScalarEnv types env) :
    ∃ minimum, ∀ fuel, minimum ≤ fuel →
      evaluateDecodedOperation fuel ctx env
          (ImpactWireDecoder.decodeOperation (Compiler.nativeOperationJson guard operation)) =
        (GuardedPlanExecution.evalActivity ctx env guard >>= fun activity =>
          GuardedPlanExecution.evalOperation ctx env activity operation).toOption := by
  have guardNonNull : ∀ expression, guard = some expression →
      (NativeExpression.toJson expression).isNull = Bool.false := by
    intro expression present
    exact ImpactExpressionSoundness.toJson_nonNull (guardSupported expression present)
  have decoded := ImpactWireSoundness.decode_operation projects guard guardNonNull
  obtain ⟨guardMinimum, guardAgrees⟩ := evaluateActivityGuard_toJson
    ctx modulus guard guardSupported guardValid typed
  obtain ⟨operationMinimum, operationAgrees⟩ :=
    ImpactOperationAgreement.evaluateOperation_projects ctx modulus projects admitted
      operandsValid typed
  refine ⟨max guardMinimum operationMinimum, ?_⟩
  intro fuel enough
  have guardEnough : guardMinimum ≤ fuel := by omega
  have operationEnough : operationMinimum ≤ fuel := by omega
  have guardResult := guardAgrees fuel guardEnough
  have operationResult := operationAgrees fuel operationEnough
  rw [decoded]
  change evaluateScheduledOperation fuel ctx env
      ⟨guard.map NativeExpression.toJson, projected⟩ =
    (GuardedPlanExecution.evalActivity ctx env guard >>= fun activity =>
      GuardedPlanExecution.evalOperation ctx env activity operation).toOption
  unfold evaluateScheduledOperation
  rw [guardResult]
  cases activityResult : GuardedPlanExecution.evalActivity ctx env guard with
  | error message =>
      simp [Except.toOption, Bind.bind, Except.bind]
  | ok activity =>
      cases active : activity.getD _root_.Bool.true with
      | «false» =>
          simp [active, GuardedPlanExecution.evalOperation, Except.toOption,
            Bind.bind, Except.bind]
      | «true» =>
          cases operandEval : GenericStateOps.evalOp ctx env operation with
          | error message =>
              simp [active, operationResult,
                GuardedPlanExecution.evalOperation, operandEval,
                Except.toOption, Except.map, Bind.bind, Except.bind]
          | ok native =>
              simp [active, operationResult,
                GuardedPlanExecution.evalOperation, operandEval,
                Except.toOption, Except.map, Bind.bind, Except.bind]

end Noctium.Verification.ImpactScheduledAgreement
