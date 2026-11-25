import Noctium.Verification.ImpactExpressionEvaluation

namespace Noctium.Verification.ImpactArithmeticAgreement

open Lean
open Noctium.Verification.ImpactExpressionEvaluation
open Noctium.Verification.ImpactScalarPrimitives
open Noctium.Verification.ScalarNormalization

private theorem native_value_canonical (ctx : EvalContext)
    (modulus : ctx.modulus = Field.modulus) (expression : Expr .native)
    (admitted : ScalarExpression expression) (value : Nat)
    (evaluated : expression.eval ctx env = .ok value) :
    ImpactScalarPrimitives.canonical ctx.modulus (.native value) = true := by
  have canonical := GenericStateEvaluationCanonical.expression_eval_canonical
    ctx env expression admitted value modulus evaluated
  exact (ImpactScalarPrimitives.canonical_pack_iff ctx modulus .native value).2 canonical

private theorem uint_value_canonical (ctx : EvalContext)
    (modulus : ctx.modulus = Field.modulus) (maximum : Nat)
    (expression : Expr (.uint maximum)) (admitted : ScalarExpression expression)
    (value : Nat) (evaluated : expression.eval ctx env = .ok value) :
    ImpactScalarPrimitives.canonical ctx.modulus (.uint maximum value) = true := by
  have canonical := GenericStateEvaluationCanonical.expression_eval_canonical
    ctx env expression admitted value modulus evaluated
  exact (ImpactScalarPrimitives.canonical_pack_iff ctx modulus (.uint maximum) value).2 canonical

theorem add_agrees (ctx : EvalContext) (modulus : ctx.modulus = Field.modulus)
    (run : Runner) (env : EvalEnv) (left right : Expr .native)
    (leftRaw rightRaw : Json)
    (leftAdmitted : ScalarExpression left) (rightAdmitted : ScalarExpression right)
    (leftAgrees : run env leftRaw =
      (left.eval ctx env).toOption.map (Value.pack .native))
    (rightAgrees : run env rightRaw =
      (right.eval ctx env).toOption.map (Value.pack .native)) :
    evaluateNode ctx run env (.binary .add leftRaw rightRaw) =
      ((Expr.add left right).eval ctx env).toOption.map (Value.pack .native) := by
  have modulusPositive : 0 < ctx.modulus := by rw [modulus]; decide
  have modulusNeZero : ctx.modulus ≠ 0 := Nat.ne_of_gt modulusPositive
  cases leftEval : left.eval ctx env with
  | error reason =>
      have leftRun : run env leftRaw = none := by
        simpa [leftEval, Value.pack, Except.toOption] using leftAgrees
      simp [evaluateNode, leftRun, Expr.eval, leftEval, modulusNeZero] <;> rfl
  | ok a =>
      have leftRun : run env leftRaw = some (.native a) := by
        simpa [leftEval, Value.pack, Except.toOption] using leftAgrees
      have leftCanonical := native_value_canonical ctx modulus left leftAdmitted a leftEval
      cases rightEval : right.eval ctx env with
      | error reason =>
          have rightRun : run env rightRaw = none := by
            simpa [rightEval, Value.pack, Except.toOption] using rightAgrees
          simp [evaluateNode, leftRun, rightRun, Expr.eval, leftEval, rightEval, modulusNeZero] <;> rfl
      | ok b =>
          have rightRun : run env rightRaw = some (.native b) := by
            simpa [rightEval, Value.pack, Except.toOption] using rightAgrees
          have rightCanonical := native_value_canonical ctx modulus right rightAdmitted b rightEval
          have leftBound : a < ctx.modulus := by
            simpa [ImpactScalarPrimitives.canonical] using leftCanonical
          have rightBound : b < ctx.modulus := by
            simpa [ImpactScalarPrimitives.canonical] using rightCanonical
          simp [evaluateNode, leftRun, rightRun, ImpactScalarPrimitives.nativeBinary,
            ImpactScalarPrimitives.canonical, leftBound, rightBound, modulusPositive, modulusNeZero,
            Expr.eval, leftEval, rightEval] <;> rfl

theorem mul_agrees (ctx : EvalContext) (modulus : ctx.modulus = Field.modulus)
    (run : Runner) (env : EvalEnv) (left right : Expr .native)
    (leftRaw rightRaw : Json)
    (leftAdmitted : ScalarExpression left) (rightAdmitted : ScalarExpression right)
    (leftAgrees : run env leftRaw =
      (left.eval ctx env).toOption.map (Value.pack .native))
    (rightAgrees : run env rightRaw =
      (right.eval ctx env).toOption.map (Value.pack .native)) :
    evaluateNode ctx run env (.binary .mul leftRaw rightRaw) =
      ((Expr.mul left right).eval ctx env).toOption.map (Value.pack .native) := by
  have modulusPositive : 0 < ctx.modulus := by rw [modulus]; decide
  have modulusNeZero : ctx.modulus ≠ 0 := Nat.ne_of_gt modulusPositive
  cases leftEval : left.eval ctx env with
  | error reason =>
      have leftRun : run env leftRaw = none := by
        simpa [leftEval, Value.pack, Except.toOption] using leftAgrees
      simp [evaluateNode, leftRun, Expr.eval, leftEval, modulusNeZero] <;> rfl
  | ok a =>
      have leftRun : run env leftRaw = some (.native a) := by
        simpa [leftEval, Value.pack, Except.toOption] using leftAgrees
      have leftCanonical := native_value_canonical ctx modulus left leftAdmitted a leftEval
      cases rightEval : right.eval ctx env with
      | error reason =>
          have rightRun : run env rightRaw = none := by
            simpa [rightEval, Value.pack, Except.toOption] using rightAgrees
          simp [evaluateNode, leftRun, rightRun, Expr.eval, leftEval, rightEval, modulusNeZero] <;> rfl
      | ok b =>
          have rightRun : run env rightRaw = some (.native b) := by
            simpa [rightEval, Value.pack, Except.toOption] using rightAgrees
          have rightCanonical := native_value_canonical ctx modulus right rightAdmitted b rightEval
          have leftBound : a < ctx.modulus := by
            simpa [ImpactScalarPrimitives.canonical] using leftCanonical
          have rightBound : b < ctx.modulus := by
            simpa [ImpactScalarPrimitives.canonical] using rightCanonical
          simp [evaluateNode, leftRun, rightRun, ImpactScalarPrimitives.nativeBinary,
            ImpactScalarPrimitives.canonical, leftBound, rightBound, modulusPositive, modulusNeZero,
            Expr.eval, leftEval, rightEval] <;> rfl

theorem sub_agrees (ctx : EvalContext) (modulus : ctx.modulus = Field.modulus)
    (run : Runner) (env : EvalEnv) (left right : Expr .native)
    (leftRaw rightRaw : Json)
    (leftAdmitted : ScalarExpression left) (rightAdmitted : ScalarExpression right)
    (leftAgrees : run env leftRaw =
      (left.eval ctx env).toOption.map (Value.pack .native))
    (rightAgrees : run env rightRaw =
      (right.eval ctx env).toOption.map (Value.pack .native)) :
    evaluateNode ctx run env (.binary .sub leftRaw rightRaw) =
      ((Expr.sub left right).eval ctx env).toOption.map (Value.pack .native) := by
  have modulusPositive : 0 < ctx.modulus := by rw [modulus]; decide
  have modulusNeZero : ctx.modulus ≠ 0 := Nat.ne_of_gt modulusPositive
  cases leftEval : left.eval ctx env with
  | error reason =>
      have leftRun : run env leftRaw = none := by
        simpa [leftEval, Value.pack, Except.toOption] using leftAgrees
      simp [evaluateNode, leftRun, Expr.eval, leftEval, modulusNeZero] <;> rfl
  | ok a =>
      have leftRun : run env leftRaw = some (.native a) := by
        simpa [leftEval, Value.pack, Except.toOption] using leftAgrees
      have leftCanonical := native_value_canonical ctx modulus left leftAdmitted a leftEval
      cases rightEval : right.eval ctx env with
      | error reason =>
          have rightRun : run env rightRaw = none := by
            simpa [rightEval, Value.pack, Except.toOption] using rightAgrees
          simp [evaluateNode, leftRun, rightRun, Expr.eval, leftEval, rightEval, modulusNeZero] <;> rfl
      | ok b =>
          have rightRun : run env rightRaw = some (.native b) := by
            simpa [rightEval, Value.pack, Except.toOption] using rightAgrees
          have rightCanonical := native_value_canonical ctx modulus right rightAdmitted b rightEval
          have leftBound : a < ctx.modulus := by
            simpa [ImpactScalarPrimitives.canonical] using leftCanonical
          have rightBound : b < ctx.modulus := by
            simpa [ImpactScalarPrimitives.canonical] using rightCanonical
          simp [evaluateNode, leftRun, rightRun, ImpactScalarPrimitives.nativeBinary,
            ImpactScalarPrimitives.canonical, leftBound, rightBound, modulusPositive, modulusNeZero,
            Expr.eval, leftEval, rightEval] <;> rfl

theorem uadd_agrees (ctx : EvalContext) (modulus : ctx.modulus = Field.modulus)
    (run : Runner) (env : EvalEnv) {m n : Nat}
    (left : Expr (.uint m)) (right : Expr (.uint n))
    (leftRaw rightRaw : Json)
    (leftAdmitted : ScalarExpression left) (rightAdmitted : ScalarExpression right)
    (leftAgrees : run env leftRaw =
      (left.eval ctx env).toOption.map (Value.pack (.uint m)))
    (rightAgrees : run env rightRaw =
      (right.eval ctx env).toOption.map (Value.pack (.uint n))) :
    evaluateNode ctx run env (.unsigned .add (toString (m + n)) leftRaw rightRaw) =
      ((Expr.uadd left right).eval ctx env).toOption.map (Value.pack (.uint (m + n))) := by
  have modulusPositive : 0 < ctx.modulus := by rw [modulus]; decide
  cases leftEval : left.eval ctx env with
  | error reason =>
      have leftRun : run env leftRaw = none := by
        simpa [leftEval, Value.pack, Except.toOption] using leftAgrees
      simp [evaluateNode, leftRun, Expr.eval, leftEval] <;> rfl
  | ok a =>
      have leftRun : run env leftRaw = some (.uint m a) := by
        simpa [leftEval, Value.pack, Except.toOption] using leftAgrees
      have leftCanonical := uint_value_canonical ctx modulus m left leftAdmitted a leftEval
      cases rightEval : right.eval ctx env with
      | error reason =>
          have rightRun : run env rightRaw = none := by
            simpa [rightEval, Value.pack, Except.toOption] using rightAgrees
          simp [evaluateNode, leftRun, rightRun, Expr.eval, leftEval, rightEval] <;> rfl
      | ok b =>
          have rightRun : run env rightRaw = some (.uint n b) := by
            simpa [rightEval, Value.pack, Except.toOption] using rightAgrees
          have sourceEval : (Expr.uadd left right).eval ctx env =
              ScalarNormalization.scalarCast ctx (.uint (m + n)) (.uint (m + n)) (a + b) := by
            simp only [Expr.eval, leftEval, rightEval, Bind.bind, Except.bind]
            rfl
          rw [sourceEval]
          have rightCanonical := uint_value_canonical ctx modulus n right rightAdmitted b rightEval
          have leftBounds : (m ≤ ScalarPolicy.maxUint ∧ a ≤ m) ∧ a < Field.modulus := by
            simpa [ImpactScalarPrimitives.canonical, modulus] using leftCanonical
          have rightBounds : (n ≤ ScalarPolicy.maxUint ∧ b ≤ n) ∧ b < Field.modulus := by
            simpa [ImpactScalarPrimitives.canonical, modulus] using rightCanonical
          rcases leftBounds with ⟨⟨leftMaximumBound, leftValueBound⟩, leftFieldBound⟩
          rcases rightBounds with ⟨⟨rightMaximumBound, rightValueBound⟩, rightFieldBound⟩
          have leftFieldContext : a < ctx.modulus := by simpa [modulus] using leftFieldBound
          have rightFieldContext : b < ctx.modulus := by simpa [modulus] using rightFieldBound
          have resultMaximum : a + b ≤ m + n := Nat.add_le_add leftValueBound rightValueBound
          by_cases outputMaximum : m + n ≤ ScalarPolicy.maxUint
          · have resultField : a + b < ctx.modulus := by
              rw [modulus]
              exact Nat.lt_of_le_of_lt resultMaximum
                (Nat.lt_of_le_of_lt outputMaximum ScalarPolicy.maxUint_lt_native)
            simp [evaluateNode, leftRun, rightRun, ImpactScalarPrimitives.unsignedBinary,
              ImpactScalarPrimitives.canonical, leftMaximumBound, leftValueBound,
              leftFieldContext, rightMaximumBound, rightValueBound, rightFieldContext,
              outputMaximum, resultMaximum, resultField,
              ImpactDecimal.parseCanonical, ScalarNormalization.scalarCast,
              Bind.bind, Except.toOption,
              guard, Value.pack] <;> simp_all
          · simp [evaluateNode, leftRun, rightRun, ImpactScalarPrimitives.unsignedBinary,
              ImpactScalarPrimitives.canonical, leftMaximumBound, leftValueBound,
              leftFieldContext, rightMaximumBound, rightValueBound, rightFieldContext,
              outputMaximum, ImpactDecimal.parseCanonical, ScalarNormalization.scalarCast,
              Bind.bind, Except.toOption, guard] <;> simp_all

theorem usub_agrees (ctx : EvalContext) (modulus : ctx.modulus = Field.modulus)
    (run : Runner) (env : EvalEnv) {m n : Nat}
    (left : Expr (.uint m)) (right : Expr (.uint n))
    (leftRaw rightRaw : Json)
    (leftAdmitted : ScalarExpression left) (rightAdmitted : ScalarExpression right)
    (leftAgrees : run env leftRaw =
      (left.eval ctx env).toOption.map (Value.pack (.uint m)))
    (rightAgrees : run env rightRaw =
      (right.eval ctx env).toOption.map (Value.pack (.uint n))) :
    evaluateNode ctx run env (.unsigned .sub (toString m) leftRaw rightRaw) =
      ((Expr.usub left right).eval ctx env).toOption.map (Value.pack (.uint m)) := by
  have modulusPositive : 0 < ctx.modulus := by rw [modulus]; decide
  cases leftEval : left.eval ctx env with
  | error reason =>
      have leftRun : run env leftRaw = none := by
        simpa [leftEval, Value.pack, Except.toOption] using leftAgrees
      simp [evaluateNode, leftRun, Expr.eval, leftEval] <;> rfl
  | ok a =>
      have leftRun : run env leftRaw = some (.uint m a) := by
        simpa [leftEval, Value.pack, Except.toOption] using leftAgrees
      have leftCanonical := uint_value_canonical ctx modulus m left leftAdmitted a leftEval
      cases rightEval : right.eval ctx env with
      | error reason =>
          have rightRun : run env rightRaw = none := by
            simpa [rightEval, Value.pack, Except.toOption] using rightAgrees
          simp [evaluateNode, leftRun, rightRun, Expr.eval, leftEval, rightEval] <;> rfl
      | ok b =>
          have rightRun : run env rightRaw = some (.uint n b) := by
            simpa [rightEval, Value.pack, Except.toOption] using rightAgrees
          have rightCanonical := uint_value_canonical ctx modulus n right rightAdmitted b rightEval
          have leftBounds : (m ≤ ScalarPolicy.maxUint ∧ a ≤ m) ∧ a < Field.modulus := by
            simpa [ImpactScalarPrimitives.canonical, modulus] using leftCanonical
          have rightBounds : (n ≤ ScalarPolicy.maxUint ∧ b ≤ n) ∧ b < Field.modulus := by
            simpa [ImpactScalarPrimitives.canonical, modulus] using rightCanonical
          rcases leftBounds with ⟨⟨leftMaximumBound, leftValueBound⟩, leftFieldBound⟩
          rcases rightBounds with ⟨⟨rightMaximumBound, rightValueBound⟩, rightFieldBound⟩
          have leftFieldContext : a < ctx.modulus := by simpa [modulus] using leftFieldBound
          have rightFieldContext : b < ctx.modulus := by simpa [modulus] using rightFieldBound
          have resultMaximum : a - b ≤ m := Nat.le_trans (Nat.sub_le a b) leftValueBound
          have resultField : a - b < ctx.modulus := by
            rw [modulus]
            exact Nat.lt_of_le_of_lt resultMaximum
              (Nat.lt_of_le_of_lt leftMaximumBound ScalarPolicy.maxUint_lt_native)
          have sourceEval : (Expr.usub left right).eval ctx env =
              (if a < b then .error "unsigned subtraction underflow"
              else ScalarNormalization.scalarCast ctx (.uint m) (.uint m) (a - b)) := by
            simp only [Expr.eval, leftEval, rightEval, Bind.bind, Except.bind]
            rfl
          rw [sourceEval]
          by_cases underflow : a < b
          · simp [evaluateNode, leftRun, rightRun, ImpactScalarPrimitives.unsignedBinary,
              ImpactScalarPrimitives.canonical, leftMaximumBound, leftValueBound,
              leftFieldContext, rightMaximumBound, rightValueBound, rightFieldContext,
              underflow, ImpactDecimal.parseCanonical, Bind.bind,
              Except.toOption, guard] <;> simp_all
          · simp [evaluateNode, leftRun, rightRun, ImpactScalarPrimitives.unsignedBinary,
              ImpactScalarPrimitives.canonical, leftMaximumBound, leftValueBound,
              leftFieldContext, rightMaximumBound, rightValueBound, rightFieldContext,
              underflow, resultMaximum, resultField,
              ImpactDecimal.parseCanonical, ScalarNormalization.scalarCast,
              Bind.bind, Except.toOption,
              guard, Value.pack] <;> simp_all

theorem umul_agrees (ctx : EvalContext) (modulus : ctx.modulus = Field.modulus)
    (run : Runner) (env : EvalEnv) {m n : Nat}
    (left : Expr (.uint m)) (right : Expr (.uint n))
    (leftRaw rightRaw : Json)
    (leftAdmitted : ScalarExpression left) (rightAdmitted : ScalarExpression right)
    (leftAgrees : run env leftRaw =
      (left.eval ctx env).toOption.map (Value.pack (.uint m)))
    (rightAgrees : run env rightRaw =
      (right.eval ctx env).toOption.map (Value.pack (.uint n))) :
    evaluateNode ctx run env (.unsigned .mul (toString (m * n)) leftRaw rightRaw) =
      ((Expr.umul left right).eval ctx env).toOption.map (Value.pack (.uint (m * n))) := by
  have modulusPositive : 0 < ctx.modulus := by rw [modulus]; decide
  cases leftEval : left.eval ctx env with
  | error reason =>
      have leftRun : run env leftRaw = none := by
        simpa [leftEval, Value.pack, Except.toOption] using leftAgrees
      simp [evaluateNode, leftRun, Expr.eval, leftEval] <;> rfl
  | ok a =>
      have leftRun : run env leftRaw = some (.uint m a) := by
        simpa [leftEval, Value.pack, Except.toOption] using leftAgrees
      have leftCanonical := uint_value_canonical ctx modulus m left leftAdmitted a leftEval
      cases rightEval : right.eval ctx env with
      | error reason =>
          have rightRun : run env rightRaw = none := by
            simpa [rightEval, Value.pack, Except.toOption] using rightAgrees
          simp [evaluateNode, leftRun, rightRun, Expr.eval, leftEval, rightEval] <;> rfl
      | ok b =>
          have rightRun : run env rightRaw = some (.uint n b) := by
            simpa [rightEval, Value.pack, Except.toOption] using rightAgrees
          have sourceEval : (Expr.umul left right).eval ctx env =
              ScalarNormalization.scalarCast ctx (.uint (m * n)) (.uint (m * n)) (a * b) := by
            simp only [Expr.eval, leftEval, rightEval, Bind.bind, Except.bind]
            rfl
          rw [sourceEval]
          have rightCanonical := uint_value_canonical ctx modulus n right rightAdmitted b rightEval
          have leftBounds : (m ≤ ScalarPolicy.maxUint ∧ a ≤ m) ∧ a < Field.modulus := by
            simpa [ImpactScalarPrimitives.canonical, modulus] using leftCanonical
          have rightBounds : (n ≤ ScalarPolicy.maxUint ∧ b ≤ n) ∧ b < Field.modulus := by
            simpa [ImpactScalarPrimitives.canonical, modulus] using rightCanonical
          rcases leftBounds with ⟨⟨leftMaximumBound, leftValueBound⟩, leftFieldBound⟩
          rcases rightBounds with ⟨⟨rightMaximumBound, rightValueBound⟩, rightFieldBound⟩
          have leftFieldContext : a < ctx.modulus := by simpa [modulus] using leftFieldBound
          have rightFieldContext : b < ctx.modulus := by simpa [modulus] using rightFieldBound
          have resultMaximum : a * b ≤ m * n := Nat.mul_le_mul leftValueBound rightValueBound
          by_cases outputMaximum : m * n ≤ ScalarPolicy.maxUint
          · have resultField : a * b < ctx.modulus := by
              rw [modulus]
              exact Nat.lt_of_le_of_lt resultMaximum
                (Nat.lt_of_le_of_lt outputMaximum ScalarPolicy.maxUint_lt_native)
            simp [evaluateNode, leftRun, rightRun, ImpactScalarPrimitives.unsignedBinary,
              ImpactScalarPrimitives.canonical, leftMaximumBound, leftValueBound,
              leftFieldContext, rightMaximumBound, rightValueBound, rightFieldContext,
              outputMaximum, resultMaximum, resultField,
              ImpactDecimal.parseCanonical, ScalarNormalization.scalarCast,
              Bind.bind, Except.toOption,
              guard, Value.pack] <;> simp_all
          · simp [evaluateNode, leftRun, rightRun, ImpactScalarPrimitives.unsignedBinary,
              ImpactScalarPrimitives.canonical, leftMaximumBound, leftValueBound,
              leftFieldContext, rightMaximumBound, rightValueBound, rightFieldContext,
              outputMaximum, ImpactDecimal.parseCanonical, ScalarNormalization.scalarCast,
              Bind.bind, Except.toOption, guard] <;> simp_all

end Noctium.Verification.ImpactArithmeticAgreement
