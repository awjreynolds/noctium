import Noctium.Semantics

namespace Noctium.Verification.GenericStateExpressionChildren

open Noctium

private theorem forIn_extract {α ε : Type}
    (body : α → PUnit → Except ε (ForInStep PUnit))
    (property : α → Prop) (values : List α)
    (actions : ∀ value step, body value .unit = .ok step →
      step = .yield .unit ∧ property value)
    (success : forIn values PUnit.unit body = .ok .unit) :
    ∀ value ∈ values, property value := by
  induction values with
  | nil => simp
  | cons value rest ih =>
    rw [List.forIn_cons] at success
    cases checked : body value .unit with
    | error message => simp [checked, bind, Except.bind] at success
    | ok step =>
      obtain ⟨equal, holds⟩ := actions value step checked
      subst step
      simp only [checked, bind, Except.bind] at success
      intro found member
      rcases List.mem_cons.mp member with equal | member
      · simpa [equal] using holds
      · exact ih success found member

/-- Successful validation loops retain the exact checked result for every
homogeneous child expression. -/
theorem validateList_members {ty : Ty} (caps : Capabilities) (env : TypeEnv)
    (values : List (Expr ty))
    (success : forIn values PUnit.unit (fun (value : Expr ty) (_ : PUnit) => do
      value.validate caps env
      pure (.yield .unit)) = .ok .unit) :
    ∀ value ∈ values, value.validate caps env = .ok () := by
  refine forIn_extract
    (fun (value : Expr ty) _ => do
      value.validate caps env
      pure (.yield .unit))
    (fun value => value.validate caps env = .ok ()) values ?_ ?_
  · intro value step checked
    cases valid : value.validate caps env with
    | error message =>
      simp [valid, Functor.map, Except.map] at checked
    | ok result =>
      cases result
      simp [valid, Functor.map, Except.map] at checked
      cases checked
      exact ⟨rfl, by simpa using valid⟩
  · exact success

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

/-- Successful validation of a dependent FAB expression loop retains each
typed child validation in declaration order. -/
theorem validateSigmaList_members (caps : Capabilities) (env : TypeEnv)
    (values : List (Sigma Expr))
    (success : forIn values PUnit.unit (fun (item : Sigma Expr) (_ : PUnit) => do
      item.2.validate caps env
      pure (.yield .unit)) = .ok .unit) :
    ∀ item ∈ values, item.2.validate caps env = .ok () := by
  refine forIn_extract
    (fun (item : Sigma Expr) _ => do
      item.2.validate caps env
      pure (.yield .unit))
    (fun item => item.2.validate caps env = .ok ()) values ?_ ?_
  · intro item step checked
    cases valid : item.2.validate caps env with
    | error message =>
      simp [valid, Functor.map, Except.map] at checked
    | ok result =>
      cases result
      simp [valid, Functor.map, Except.map] at checked
      cases checked
      exact ⟨rfl, by simpa using valid⟩
  · exact success

end Noctium.Verification.GenericStateExpressionChildren
