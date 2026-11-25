import Noctium.GuardedExpression
import Noctium.Backend.Impact
import Noctium.Verification.GenericStateEvaluationCanonical
import Noctium.Verification.ScalarNormalization

namespace Noctium.Verification.GuardedScalarTotalization

open ScalarNormalization

private theorem ref_eval_true_cons (ctx : EvalContext) (env : EvalEnv)
    (guardName binder : String) (raw : Value) (notShadow : binder ≠ guardName)
    (guardEval : (Expr.ref guardName : Expr .bool).eval ctx env = .ok true) :
    (Expr.ref guardName : Expr .bool).eval ctx ((binder, raw) :: env) = .ok true := by
  have unequal : (guardName == binder) = false := by
    simp [Ne.symm notShadow]
  simpa [Expr.eval, List.lookup_cons, unequal] using guardEval

private theorem not_mem_append_parts {α : Type} (name : α)
    (left right : List α) (notMember : name ∉ left ++ right) :
    name ∉ left ∧ name ∉ right := by
  constructor
  · intro member
    exact notMember (List.mem_append_left _ member)
  · intro member
    exact notMember (List.mem_append_right _ member)

private theorem select_true_eval (ctx : EvalContext) (env : EvalEnv)
    (guard : Expr .bool) (value fallback : Expr ty)
    (guardEval : guard.eval ctx env = .ok true)
    (fallbackSafe : ∀ result, value.eval ctx env = .ok result →
      ∃ fallbackResult, fallback.eval ctx env = .ok fallbackResult) :
    (Expr.select guard value fallback).eval ctx env = value.eval ctx env := by
  cases valueEval : value.eval ctx env with
  | error message => simp [Expr.eval, guardEval, valueEval, Bind.bind, Except.bind]
  | ok result =>
    obtain ⟨fallbackResult, fallbackEval⟩ := fallbackSafe result valueEval
    simp [Expr.eval, guardEval, valueEval, fallbackEval, Bind.bind, Except.bind,
      Pure.pure, Except.pure]

private theorem cast_eval_congr {source target : Ty} (ctx : EvalContext) (env : EvalEnv)
    (left right : Expr source)
    (agree : left.eval ctx env = right.eval ctx env) :
    (Expr.cast target left).eval ctx env = (Expr.cast target right).eval ctx env := by
  simp only [Expr.eval, agree]

private theorem zeroValue_eval_of_success {ty : Ty}
    (support : ScalarType ty) (expression : Expr ty)
    (supported : ScalarExpression expression) (ctx : EvalContext) (env : EvalEnv)
    (value : ty.Denote) (modulus : ctx.modulus = Field.modulus)
    (evaluated : expression.eval ctx env = .ok value) :
    ∃ zero, (GuardedExpression.zeroValue ty).eval ctx env = .ok zero := by
  cases support with
  | native =>
    refine ⟨0, ?_⟩
    simp [GuardedExpression.zeroValue, Expr.eval, modulus, Field.modulus,
      Pure.pure, Except.pure]
  | bool => exact ⟨false, by simp [GuardedExpression.zeroValue, Expr.eval]⟩
  | uint maximum =>
    have canonical := GenericStateEvaluationCanonical.expression_eval_canonical
      ctx env expression supported value modulus evaluated
    have maximumBound : maximum ≤ ScalarPolicy.maxUint := canonical.2.1
    refine ⟨0, ?_⟩
    simp [GuardedExpression.zeroValue, Expr.eval, canonical_eq, maximumBound,
      modulus, Field.modulus, Pure.pure, Except.pure]

/-- On an active stable guard, totalize preserves exact source evaluation,
including errors. The let-name condition prevents nested lets from capturing
the guard reference. -/
theorem eval_totalize_active {ty : Ty} (expression : Expr ty)
    (supported : ScalarExpression expression) (ctx : EvalContext) (env : EvalEnv)
    (guardName : String) (modulus : ctx.modulus = Field.modulus)
    (noShadow : guardName ∉ Noctium.Backend.Impact.expressionNames expression)
    (guardEval : (Expr.ref guardName : Expr .bool).eval ctx env = .ok true) :
    (GuardedExpression.totalize (.ref guardName) expression).eval ctx env =
      expression.eval ctx env := by
  revert env noShadow guardEval
  induction supported with
  | native value => intro env _ _; simp [GuardedExpression.totalize]
  | bool value => intro env _ _; simp [GuardedExpression.totalize]
  | uint maximum value => intro env _ _; simp [GuardedExpression.totalize]
  | ref name support => intro env _ _; simp [GuardedExpression.totalize]
  | add left right leftSupported rightSupported ihLeft ihRight =>
    intro env noShadow guardEval
    simp only [Noctium.Backend.Impact.expressionNames] at noShadow
    have childrenNo := not_mem_append_parts guardName
      (Noctium.Backend.Impact.expressionNames left)
      (Noctium.Backend.Impact.expressionNames right) noShadow
    simp [GuardedExpression.totalize, Expr.eval,
      ihLeft env childrenNo.1 guardEval, ihRight env childrenNo.2 guardEval]
  | mul left right leftSupported rightSupported ihLeft ihRight =>
    intro env noShadow guardEval
    simp only [Noctium.Backend.Impact.expressionNames] at noShadow
    have childrenNo := not_mem_append_parts guardName
      (Noctium.Backend.Impact.expressionNames left)
      (Noctium.Backend.Impact.expressionNames right) noShadow
    simp [GuardedExpression.totalize, Expr.eval,
      ihLeft env childrenNo.1 guardEval, ihRight env childrenNo.2 guardEval]
  | sub left right leftSupported rightSupported ihLeft ihRight =>
    intro env noShadow guardEval
    simp only [Noctium.Backend.Impact.expressionNames] at noShadow
    have childrenNo := not_mem_append_parts guardName
      (Noctium.Backend.Impact.expressionNames left)
      (Noctium.Backend.Impact.expressionNames right) noShadow
    simp [GuardedExpression.totalize, Expr.eval,
      ihLeft env childrenNo.1 guardEval, ihRight env childrenNo.2 guardEval]
  | uadd left right leftSupported rightSupported ihLeft ihRight =>
    intro env noShadow guardEval
    simp only [Noctium.Backend.Impact.expressionNames] at noShadow
    have childrenNo := not_mem_append_parts guardName
      (Noctium.Backend.Impact.expressionNames left)
      (Noctium.Backend.Impact.expressionNames right) noShadow
    simp [GuardedExpression.totalize, Expr.eval,
      ihLeft env childrenNo.1 guardEval, ihRight env childrenNo.2 guardEval]
  | usub left right leftSupported rightSupported ihLeft ihRight =>
    rename_i m n
    intro env noShadow guardEval
    simp only [Noctium.Backend.Impact.expressionNames] at noShadow
    have childrenNo := not_mem_append_parts guardName
      (Noctium.Backend.Impact.expressionNames left)
      (Noctium.Backend.Impact.expressionNames right) noShadow
    have leftEval := ihLeft env childrenNo.1 guardEval
    have rightEval := ihRight env childrenNo.2 guardEval
    have leftSafe : ∀ result, (GuardedExpression.totalize (.ref guardName) left).eval
        ctx env = .ok result →
        ∃ fallbackValue, (Expr.uint m 0).eval ctx env = .ok fallbackValue := by
      intro result totalEval
      have sourceEval : left.eval ctx env = .ok result := leftEval.symm.trans totalEval
      exact zeroValue_eval_of_success (.uint m) left leftSupported ctx env result
        modulus sourceEval
    have rightSafe : ∀ result, (GuardedExpression.totalize (.ref guardName) right).eval
        ctx env = .ok result →
        ∃ fallbackValue, (Expr.uint n 0).eval ctx env = .ok fallbackValue := by
      intro result totalEval
      have sourceEval : right.eval ctx env = .ok result := rightEval.symm.trans totalEval
      exact zeroValue_eval_of_success (.uint n) right rightSupported ctx env result
        modulus sourceEval
    have leftSelect := select_true_eval ctx env (.ref guardName)
      (GuardedExpression.totalize (.ref guardName) left) (.uint m 0) guardEval leftSafe
    have rightSelect := select_true_eval ctx env (.ref guardName)
      (GuardedExpression.totalize (.ref guardName) right) (.uint n 0) guardEval rightSafe
    simp [GuardedExpression.totalize, Expr.eval, leftSelect, rightSelect,
      leftEval, rightEval]
  | umul left right leftSupported rightSupported ihLeft ihRight =>
    intro env noShadow guardEval
    simp only [Noctium.Backend.Impact.expressionNames] at noShadow
    have childrenNo := not_mem_append_parts guardName
      (Noctium.Backend.Impact.expressionNames left)
      (Noctium.Backend.Impact.expressionNames right) noShadow
    simp [GuardedExpression.totalize, Expr.eval,
      ihLeft env childrenNo.1 guardEval, ihRight env childrenNo.2 guardEval]
  | cast value sourceSupport targetSupport valueSupported ihValue =>
    rename_i source target
    intro env noShadow guardEval
    simp only [Noctium.Backend.Impact.expressionNames] at noShadow
    have valueEval := ihValue env noShadow guardEval
    simp only [GuardedExpression.totalize]
    split
    · have valueSafe : ∀ result,
          (GuardedExpression.totalize (.ref guardName) value).eval ctx env = .ok result →
          ∃ fallbackValue,
            (GuardedExpression.zeroValue source).eval ctx env = .ok fallbackValue := by
        intro result totalEval
        have sourceEval : value.eval ctx env = .ok result := valueEval.symm.trans totalEval
        exact zeroValue_eval_of_success sourceSupport value valueSupported ctx env result
          modulus sourceEval
      have valueSelect := select_true_eval ctx env (.ref guardName)
        (GuardedExpression.totalize (.ref guardName) value)
        (GuardedExpression.zeroValue source) guardEval valueSafe
      exact cast_eval_congr (target := target) ctx env
        (.select (.ref guardName) (GuardedExpression.totalize (.ref guardName) value)
          (GuardedExpression.zeroValue source)) value (valueSelect.trans valueEval)
    · exact cast_eval_congr (target := target) ctx env
        (GuardedExpression.totalize (.ref guardName) value) value valueEval
  | letE binder value body sourceSupport valueSupported bodySupported ihValue ihBody =>
    intro env noShadow guardEval
    simp only [Noctium.Backend.Impact.expressionNames] at noShadow
    have binderNe : binder ≠ guardName := by
      intro same
      subst binder
      apply noShadow
      simp
    have valueNo : guardName ∉ Noctium.Backend.Impact.expressionNames value := by
      intro member
      apply noShadow
      exact List.mem_cons_of_mem binder (List.mem_append_left _ member)
    have bodyNo : guardName ∉ Noctium.Backend.Impact.expressionNames body := by
      intro member
      apply noShadow
      exact List.mem_cons_of_mem binder (List.mem_append_right _ member)
    have valueEval := ihValue env valueNo guardEval
    simp only [GuardedExpression.totalize, Expr.eval, valueEval]
    cases evaluated : value.eval ctx env with
    | error message => simp [Bind.bind, Except.bind]
    | ok raw =>
      let packed := Value.pack _ raw
      have bodyGuard := ref_eval_true_cons ctx env guardName binder packed
        binderNe guardEval
      have bodyEval := ihBody ((binder, packed) :: env) bodyNo bodyGuard
      simp [packed, bodyEval, Bind.bind, Except.bind]
  | assertE condition body conditionSupported bodySupported ihCondition ihBody =>
    intro env noShadow guardEval
    simp only [Noctium.Backend.Impact.expressionNames] at noShadow
    have childrenNo := not_mem_append_parts guardName
      (Noctium.Backend.Impact.expressionNames condition)
      (Noctium.Backend.Impact.expressionNames body) noShadow
    have conditionEval := ihCondition env childrenNo.1 guardEval
    have conditionSafe : ∀ result,
        (GuardedExpression.totalize (.ref guardName) condition).eval ctx env = .ok result →
        ∃ fallbackValue, (Expr.bool true).eval ctx env = .ok fallbackValue := by
      intro result _
      exact ⟨true, by simp [Expr.eval]⟩
    have conditionSelect := select_true_eval ctx env (.ref guardName)
      (GuardedExpression.totalize (.ref guardName) condition) (.bool true)
      guardEval conditionSafe
    simp [GuardedExpression.totalize, Expr.eval,
      conditionSelect, conditionEval,
      ihBody env childrenNo.2 guardEval]
  | copyValue value valueSupported ihValue =>
    intro env noShadow guardEval
    simp [Noctium.Backend.Impact.expressionNames] at noShadow
    simp [GuardedExpression.totalize, Expr.eval,
      ihValue env noShadow guardEval]
  | disclose span value valueSupported ihValue =>
    intro env noShadow guardEval
    simp [Noctium.Backend.Impact.expressionNames] at noShadow
    simp [GuardedExpression.totalize, Expr.eval,
      ihValue env noShadow guardEval]
  | eq left right scalarType leftSupported rightSupported ihLeft ihRight =>
    intro env noShadow guardEval
    simp only [Noctium.Backend.Impact.expressionNames] at noShadow
    have childrenNo := not_mem_append_parts guardName
      (Noctium.Backend.Impact.expressionNames left)
      (Noctium.Backend.Impact.expressionNames right) noShadow
    simp [GuardedExpression.totalize, Expr.eval,
      ihLeft env childrenNo.1 guardEval, ihRight env childrenNo.2 guardEval]
  | select condition yes no scalarType conditionSupported yesSupported noSupported
      ihCondition ihYes ihNo =>
    intro env noShadow guardEval
    simp only [Noctium.Backend.Impact.expressionNames] at noShadow
    have conditionYesNo := not_mem_append_parts guardName
      (Noctium.Backend.Impact.expressionNames condition ++
        Noctium.Backend.Impact.expressionNames yes)
      (Noctium.Backend.Impact.expressionNames no) noShadow
    have conditionYes := not_mem_append_parts guardName
      (Noctium.Backend.Impact.expressionNames condition)
      (Noctium.Backend.Impact.expressionNames yes) conditionYesNo.1
    simp [GuardedExpression.totalize, Expr.eval,
      ihCondition env conditionYes.1 guardEval,
      ihYes env conditionYes.2 guardEval,
      ihNo env conditionYesNo.2 guardEval]
  | poseidon2 domain left right leftSupported rightSupported ihLeft ihRight =>
    intro env noShadow guardEval
    simp only [Noctium.Backend.Impact.expressionNames] at noShadow
    have childrenNo := not_mem_append_parts guardName
      (Noctium.Backend.Impact.expressionNames left)
      (Noctium.Backend.Impact.expressionNames right) noShadow
    simp [GuardedExpression.totalize, Expr.eval,
      ihLeft env childrenNo.1 guardEval, ihRight env childrenNo.2 guardEval]

end Noctium.Verification.GuardedScalarTotalization
