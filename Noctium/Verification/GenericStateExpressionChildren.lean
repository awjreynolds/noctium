import Noctium.Semantics

namespace Noctium.Verification.GenericStateExpressionChildren

open Noctium

/-- Evaluate homogeneous child expressions in order. This isolates the list
recursion used by vector and hash expressions from the outer expression proof. -/
def evalList {ty : Ty} (ctx : EvalContext) (env : EvalEnv)
    (values : List (Expr ty)) : Except String (List ty.Denote) :=
  values.mapM (fun value => value.eval ctx env)

/-- Pointwise evaluator agreement lifts through an ordered expression list. -/
theorem evalList_congr {ty : Ty} (ctx : EvalContext) (left right : EvalEnv)
    (values : List (Expr ty))
    (same : ∀ value ∈ values, value.eval ctx left = value.eval ctx right) :
    evalList ctx left values = evalList ctx right values := by
  induction values with
  | nil => rfl
  | cons head tail ih =>
    simp only [evalList, List.mapM_cons]
    rw [same head (by simp)]
    have tailAgreement := ih (by
      intro value member
      exact same value (by simp [member]))
    dsimp only [evalList] at tailAgreement
    rw [tailAgreement]

/-- Evaluate a dependent list of expressions while preserving each source
type in its packed result. FAB hash constructors use this shape. -/
def evalSigmaList (ctx : EvalContext) (env : EvalEnv)
    (values : List (Sigma Expr)) : Except String (List Value) :=
  values.mapM fun item => do
    let value ← item.2.eval ctx env
    pure (Value.pack item.1 value)

/-- Pointwise agreement lifts through dependent expression lists without
erasing their heterogeneous source types. -/
theorem evalSigmaList_congr (ctx : EvalContext) (left right : EvalEnv)
    (values : List (Sigma Expr))
    (same : ∀ item ∈ values, item.2.eval ctx left = item.2.eval ctx right) :
    evalSigmaList ctx left values = evalSigmaList ctx right values := by
  induction values with
  | nil => rfl
  | cons head tail ih =>
    simp only [evalSigmaList, List.mapM_cons]
    rw [same head (by simp)]
    have tailAgreement := ih (by
      intro item member
      exact same item (by simp [member]))
    dsimp only [evalSigmaList] at tailAgreement
    rw [tailAgreement]

end Noctium.Verification.GenericStateExpressionChildren
