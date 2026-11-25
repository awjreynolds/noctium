import Noctium.Verification.GuardedScalarExpressionScope
import Noctium.Verification.GuardedScalarTotalization
import Noctium.Verification.GenericStateConverseRequire

namespace Noctium.Verification.GuardedRequireSemantics

open Backend ScalarNormalization

private theorem select_true_eval (ctx : EvalContext) (env : EvalEnv)
    (guard value : Expr .bool)
    (guardEval : guard.eval ctx env = .ok true) :
    (Expr.select guard value (.bool true)).eval ctx env = value.eval ctx env := by
  cases valueEval : value.eval ctx env with
  | error message => simp [Expr.eval, guardEval, valueEval, Bind.bind, Except.bind]
  | ok result =>
    simp [Expr.eval, guardEval, valueEval, Bind.bind, Except.bind,
      Pure.pure, Except.pure]

/-- Appending a guarded require emits exactly one plan guard. It preserves the
operation and read lists. -/
theorem appendEffectWithActivity_require_shape (state : List StateDecl)
    (gate required : Expr .bool) (before after : Impact.Plan)
    (accepted : Impact.appendEffectWithActivity state (.require required)
      (some gate) before = .ok after) :
    after = {before with
      guards := before.guards ++ [Impact.totalizeActivityCondition gate required]} := by
  rw [Impact.appendEffectWithActivity_require] at accepted
  have appended := accepted
  simp only [Impact.appendEffect] at appended
  exact (Except.ok.inj appended).symm

/-- With a true gate, the production rewrite evaluates exactly like the source
require condition, including its original errors. -/
theorem totalizeActivityCondition_active_eval (ctx : EvalContext) (env : EvalEnv)
    (gate required : Expr .bool) (requiredSupported : ScalarExpression required)
    (modulus : ctx.modulus = Field.modulus)
    (gateEval : gate.eval ctx env = .ok true) :
    (Impact.totalizeActivityCondition gate required).eval ctx env =
      required.eval ctx env := by
  obtain ⟨name, shape, gateFresh, requiredFresh⟩ :=
    Impact.totalizeActivityCondition_shape gate required
  rw [shape]
  let boundEnv : EvalEnv := (name, Value.pack .bool true) :: env
  rw [Expr.eval]
  rw [gateEval]
  simp only [Bind.bind, Except.bind]
  have refEval : (Expr.ref name : Expr .bool).eval ctx boundEnv = .ok true := by
    simp [boundEnv, Expr.eval, Value.as, Value.pack, canonical_eq] <;> rfl
  have totalizedEval := GuardedScalarTotalization.eval_totalize_active
    required requiredSupported ctx boundEnv name modulus requiredFresh refEval
  have requiredStable := GuardedScalarExpressionScope.eval_fresh_cons
    ctx required requiredSupported env name (Value.pack .bool true) requiredFresh
  calc
    (Expr.select (.ref name)
        (GuardedExpression.totalize (.ref name) required) (.bool true)).eval ctx boundEnv
        = (GuardedExpression.totalize (.ref name) required).eval ctx boundEnv :=
          select_true_eval ctx boundEnv (.ref name)
            (GuardedExpression.totalize (.ref name) required) refEval
    _ = required.eval ctx boundEnv := totalizedEval
    _ = required.eval ctx env := by simpa [boundEnv] using requiredStable

/-- An inactive generated requirement succeeds when its eagerly evaluated
totalized condition succeeds. This premise is explicit because totalization
does not guarantee success for arbitrary oracle inputs. -/
theorem totalizeActivityCondition_inactive_eval (ctx : EvalContext)
    (env : EvalEnv) (gate required : Expr .bool) (name : String)
    (shape : Impact.totalizeActivityCondition gate required =
      .letE name gate
        (.select (.ref name)
          (GuardedExpression.totalize (.ref name) required) (.bool true)))
    (gateEval : gate.eval ctx env = .ok false)
    {value : Bool}
    (totalizedEval :
      (GuardedExpression.totalize (.ref name) required).eval ctx
        ((name, Value.pack .bool false) :: env) = .ok value) :
    (Impact.totalizeActivityCondition gate required).eval ctx env = .ok true := by
  rw [shape]
  rw [Expr.eval]
  rw [gateEval]
  simp only [Bind.bind, Except.bind]
  have refEval : (Expr.ref name : Expr .bool).eval ctx
      ((name, Value.pack .bool false) :: env) = .ok false := by
    simp [Expr.eval, Value.as, Value.pack, canonical_eq] <;> rfl
  simp [Expr.eval, refEval, totalizedEval, Bind.bind, Except.bind,
    Pure.pure, Except.pure]

/-- The guarded source evaluator checks the same requirement when active
and bypasses the source condition completely when inactive. -/
theorem run_guarded_require (ctx : EvalContext) (env : EvalEnv) (state : LedgerState)
    (gate required : Expr .bool) (active : Bool) (gateEval : gate.eval ctx env = .ok active) :
    runEffectsWithGuardsAndEnv ctx [.require required] [some gate] env state =
      if active then SourceEffects.step ctx (.require required) (env, state)
      else .ok (env, state) := by
  dsimp [runEffectsWithGuardsAndEnv, List.zipIdx, List.all,
    List.isEmpty, List.length, Option.isNone, Option.getD, Option.isSome,
    Bind.bind, Except.bind, Pure.pure, Except.pure]
  rw [List.forIn_cons]
  dsimp [List.getElem?_cons_zero, Option.getD, Option.isSome,
    Bind.bind, Except.bind, Pure.pure, Except.pure]
  rw [gateEval]
  cases active with
  | false => rfl
  | true =>
    dsimp [SourceEffects.step, runEffectWithEnv, Bind.bind, Except.bind, Pure.pure, Except.pure]
    cases evaluated : required.eval ctx env with
    | error message => rfl
    | ok passes => cases passes <;> rfl

/-- The active assertion emitted by the actual compiler succeeds exactly
when the guarded source requirement preserves the source frame. -/
theorem active_guarded_require_agreement (ctx : EvalContext) (env : EvalEnv)
    (ledger : LedgerState) (state : List StateDecl) (gate required : Expr .bool)
    (before after : Impact.Plan) (admitted : ScalarExpression required)
    (modulus : ctx.modulus = Field.modulus) (active : gate.eval ctx env = .ok true)
    (compiled : Impact.appendEffectWithActivity state (.require required)
      (some gate) before = .ok after) :
    (after.guards.drop before.guards.length).mapM (Expr.eval ctx env) = .ok [true] ↔
      runEffectsWithGuardsAndEnv ctx [.require required] [some gate] env ledger =
        .ok (env, ledger) := by
  have shape := appendEffectWithActivity_require_shape state gate required before after compiled
  have condition := totalizeActivityCondition_active_eval ctx env gate required admitted modulus active
  rw [shape, run_guarded_require ctx env ledger gate required true active]
  change ((before.guards ++ [Impact.totalizeActivityCondition gate required]).drop
      before.guards.length).mapM (Expr.eval ctx env) = .ok [true] ↔
    SourceEffects.step ctx (.require required) (env, ledger) = .ok (env, ledger)
  rw [List.drop_left]
  have exactAssertion : [Impact.totalizeActivityCondition gate required].mapM (Expr.eval ctx env) =
      ((required.eval ctx env).map fun result => [result]) := by
    simp only [List.mapM_cons, List.mapM_nil, condition]
    cases required.eval ctx env <;> rfl
  rw [exactAssertion]
  constructor
  · intro checked
    have holds : required.eval ctx env = .ok true := by
      cases evaluated : required.eval ctx env with
      | error message => simp [evaluated, Except.map] at checked
      | ok value => simpa [evaluated, Except.map] using checked
    exact GenericStateVM.require_source_step ctx env ledger required holds
  · intro checked
    obtain ⟨holds, _⟩ := GenericStateConverseRequire.source_require_true
      ctx env ledger required (env, ledger) checked
    simp [holds, Except.map]

/-- A false gate makes the appended source require a no-op, provided the
production totalized operand met its eager-evaluation premise. -/
theorem inactive_guarded_require_step (ctx : EvalContext) (env : EvalEnv)
    (state : LedgerState) (gate required : Expr .bool) (name : String)
    (shape : Impact.totalizeActivityCondition gate required =
      .letE name gate
        (.select (.ref name)
          (GuardedExpression.totalize (.ref name) required) (.bool true)))
    (gateEval : gate.eval ctx env = .ok false)
    {value : Bool}
    (totalizedEval :
      (GuardedExpression.totalize (.ref name) required).eval ctx
        ((name, Value.pack .bool false) :: env) = .ok value) :
    SourceEffects.step ctx (.require (Impact.totalizeActivityCondition gate required))
      (env, state) = .ok (env, state) := by
  exact GenericStateVM.require_source_step ctx env state
    (Impact.totalizeActivityCondition gate required)
    (totalizeActivityCondition_inactive_eval ctx env gate required name shape
      gateEval totalizedEval)

end Noctium.Verification.GuardedRequireSemantics
