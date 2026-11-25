import Noctium.Backend.Impact
import Noctium.Verification.ScalarNormalization

namespace Noctium.Verification.GuardedScalarExpressionScope
open Backend ScalarNormalization

/-- Scalar evaluation depends only on names collected from the expression
by Impact's activity rewrite. Local lets extend both environments alike. -/
theorem eval_agree_of_names (ctx : EvalContext) (expression : Expr ty)
    (admitted : ScalarExpression expression) (left right : EvalEnv)
    (agrees : ∀ name ∈ Impact.expressionNames expression,
      left.lookup name = right.lookup name) :
    expression.eval ctx left = expression.eval ctx right := by
  induction admitted generalizing left right with
  | native value => simp only [Expr.eval]
  | bool value => simp only [Expr.eval]
  | uint maximum value => simp only [Expr.eval]
  | ref name typed =>
    have lookup : left.lookup name = right.lookup name :=
      agrees name (by simp [Impact.expressionNames])
    simp [Expr.eval, lookup]
  | letE name value body valueType valueScope bodyScope ihValue ihBody =>
    simp only [Impact.expressionNames, List.mem_cons, List.mem_append] at agrees
    have valueEval := ihValue left right (fun used member => agrees used (.inr (.inl member)))
    simp only [Expr.eval, valueEval]
    cases evaluated : value.eval ctx right with
    | error message => rfl
    | ok result =>
      simp only [Bind.bind, Except.bind]
      apply ihBody
      intro used member
      by_cases bound : used = name
      · subst used
        simp
      · have unequal : (used == name) = false := by simp [bound]
        simpa only [List.lookup_cons, unequal] using agrees used (.inr (.inr member))
  | add first second firstScope secondScope ihFirst ihSecond =>
    simp only [Impact.expressionNames, List.mem_append] at agrees
    simp only [Expr.eval, ihFirst left right (fun used member => agrees used (.inl member)),
      ihSecond left right (fun used member => agrees used (.inr member))]
  | mul first second firstScope secondScope ihFirst ihSecond =>
    simp only [Impact.expressionNames, List.mem_append] at agrees
    simp only [Expr.eval, ihFirst left right (fun used member => agrees used (.inl member)),
      ihSecond left right (fun used member => agrees used (.inr member))]
  | sub first second firstScope secondScope ihFirst ihSecond =>
    simp only [Impact.expressionNames, List.mem_append] at agrees
    simp only [Expr.eval, ihFirst left right (fun used member => agrees used (.inl member)),
      ihSecond left right (fun used member => agrees used (.inr member))]
  | uadd first second firstScope secondScope ihFirst ihSecond =>
    simp only [Impact.expressionNames, List.mem_append] at agrees
    simp only [Expr.eval, ihFirst left right (fun used member => agrees used (.inl member)),
      ihSecond left right (fun used member => agrees used (.inr member))]
  | usub first second firstScope secondScope ihFirst ihSecond =>
    simp only [Impact.expressionNames, List.mem_append] at agrees
    simp only [Expr.eval, ihFirst left right (fun used member => agrees used (.inl member)),
      ihSecond left right (fun used member => agrees used (.inr member))]
  | umul first second firstScope secondScope ihFirst ihSecond =>
    simp only [Impact.expressionNames, List.mem_append] at agrees
    simp only [Expr.eval, ihFirst left right (fun used member => agrees used (.inl member)),
      ihSecond left right (fun used member => agrees used (.inr member))]
  | cast value sourceType targetType valueScope ihValue =>
    simp only [Impact.expressionNames] at agrees
    simp only [Expr.eval, ihValue left right agrees]
  | assertE condition body conditionScope bodyScope ihCondition ihBody =>
    simp only [Impact.expressionNames, List.mem_append] at agrees
    simp only [Expr.eval,
      ihCondition left right (fun used member => agrees used (.inl member)),
      ihBody left right (fun used member => agrees used (.inr member))]
  | copyValue value scope ih =>
    simp only [Impact.expressionNames] at agrees
    simp only [Expr.eval, ih left right agrees]
  | disclose span value scope ih =>
    simp only [Impact.expressionNames] at agrees
    simp only [Expr.eval, ih left right agrees]
  | eq first second typed firstScope secondScope ihFirst ihSecond =>
    simp only [Impact.expressionNames, List.mem_append] at agrees
    simp only [Expr.eval, ihFirst left right (fun used member => agrees used (.inl member)),
      ihSecond left right (fun used member => agrees used (.inr member))]
  | select condition yes no typed conditionScope yesScope noScope ihCondition ihYes ihNo =>
    simp only [Impact.expressionNames, List.mem_append] at agrees
    simp only [Expr.eval,
      ihCondition left right (fun used member => agrees used (.inl (.inl member))),
      ihYes left right (fun used member => agrees used (.inl (.inr member))),
      ihNo left right (fun used member => agrees used (.inr member))]
  | poseidon2 domain first second firstScope secondScope ihFirst ihSecond =>
    simp only [Impact.expressionNames, List.mem_append] at agrees
    simp only [Expr.eval, ihFirst left right (fun used member => agrees used (.inl member)),
      ihSecond left right (fun used member => agrees used (.inr member))]

/-- The fresh binder installed by guarded lowering leaves source evaluation
unchanged, even when unused names are present in the environment. -/
theorem eval_fresh_cons (ctx : EvalContext) (expression : Expr ty)
    (admitted : ScalarExpression expression) (env : EvalEnv)
    (binder : String) (raw : Value) (fresh : binder ∉ Impact.expressionNames expression) :
    expression.eval ctx ((binder, raw) :: env) = expression.eval ctx env := by
  apply eval_agree_of_names ctx expression admitted
  intro name member
  have distinct : name ≠ binder := by
    intro same
    exact fresh (same ▸ member)
  have unequal : (name == binder) = false := by simp [distinct]
  simp only [List.lookup_cons, unequal]

end Noctium.Verification.GuardedScalarExpressionScope
