import Noctium.Verification.GuardedScalarExpressionScope
import Noctium.Verification.GuardedScalarTotalization
import Noctium.Verification.GenericStateConverseRequire
import Noctium.Verification.GuardedPlanExecution

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

private theorem bind_ok {α β : Type} {first : Except ε α} {next : α → Except ε β}
    {result : β} : (first >>= next) = .ok result ↔
      ∃ value, first = .ok value ∧ next value = .ok result := by
  cases first <;> simp [Bind.bind, Except.bind]

private theorem require_operations (state : List StateDecl) (required : Expr .bool)
    (guard : Option (Expr .bool)) (before after : Impact.Plan)
    (compiled : Impact.appendEffectWithActivity state (.require required) guard before = .ok after) :
    after.operations = before.operations := by
  cases guard with
  | none =>
    obtain ⟨raw, appended, operations, _⟩ := GuardedEffectPrefix.appendEffectWithActivity_none_result
      state (.require required) before after compiled
    have equal := Except.ok.inj appended
    rw [operations, ← equal]
  | some condition =>
    unfold Impact.appendEffectWithActivity at compiled
    simp only [bind_ok] at compiled
    obtain ⟨lowered, loweredAccepted, result, appendAccepted, wrapperAccepted⟩ := compiled
    have effectShape : ∃ guardedRequired : Expr .bool, lowered = .require guardedRequired := by
      simp only [Pure.pure, Except.pure] at loweredAccepted
      cases loweredAccepted
      exact ⟨_, rfl⟩
    obtain ⟨guardedRequired, rfl⟩ := effectShape
    have resultAccepted := Except.ok.inj appendAccepted
    have resultOperations : result.operations = before.operations := by rw [← resultAccepted]
    have projected := congrArg (Except.map Impact.Plan.operations) wrapperAccepted
    simp only [Pure.pure, Except.pure, Except.map] at projected
    exact (Except.ok.inj projected).symm.trans resultOperations

/-- The emitted requirement chunk records the evaluated guard and preserves
its source frame. The assertion itself occupies no native operations. -/
theorem source_guarded_require_chunk (ctx : EvalContext) (state : List StateDecl)
    (env candidate : EvalEnv) (current : LedgerState) (after : SourceEffects.Frame)
    (required : Expr .bool) (guard : Option (Expr .bool)) (beforePlan afterPlan : Impact.Plan)
    (agree : ∀ condition, guard = some condition →
      condition.eval ctx candidate = condition.eval ctx env)
    (compiled : Impact.appendEffectWithActivity state (.require required) guard beforePlan = .ok afterPlan)
    (success : GuardedSourceEffects.step ctx guard (.require required) (env, current) = .ok after) :
    ∃ activity,
      GuardedPlanExecution.evalChunk ctx candidate guard
        (afterPlan.operations.drop beforePlan.operations.length) = .ok (activity, []) ∧
      after = (env, current) := by
  rw [require_operations state required guard beforePlan afterPlan compiled]
  simp only [List.drop_length]
  cases guard with
  | none =>
    rw [GuardedSourceEffects.step_unguarded] at success
    exact ⟨none, rfl, (GenericStateConverseRequire.source_require_true ctx env current required after success).2⟩
  | some condition =>
    cases evaluated : condition.eval ctx env with
    | error message =>
      rw [GuardedSourceEffects.step_guard_error ctx condition (.require required) (env, current)
        message (.require condition required) evaluated] at success
      cases success
    | ok selected =>
      have candidateSelected := (agree condition rfl).trans evaluated
      change runEffectsWithGuardsAndEnv ctx [.require required] [some condition]
        env current = .ok after at success
      rw [GuardedRequireSemantics.run_guarded_require ctx env current condition required
        selected evaluated] at success
      refine ⟨some selected, ?_, ?_⟩
      · have activity : (some condition).mapM (fun condition => condition.eval ctx candidate) =
            Except.ok (some selected) := by
          change some <$> condition.eval ctx candidate = .ok (some selected)
          rw [candidateSelected]
          rfl
        unfold GuardedPlanExecution.evalChunk
        rw [activity]
        cases selected <;> rfl
      · cases selected with
        | false => exact (Except.ok.inj success).symm
        | true => exact (GenericStateConverseRequire.source_require_true ctx env current required after success).2

end Noctium.Verification.GuardedRequireSemantics
