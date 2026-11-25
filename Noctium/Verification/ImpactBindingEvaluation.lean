import Noctium.Verification.ImpactExpressionEvaluation
import Noctium.Verification.ImpactExpressionMatch

namespace Noctium.Verification.ImpactBindingEvaluation

open Lean
open Noctium
open Noctium.Verification.ImpactExpressionEvaluation
open Noctium.Verification.ImpactExpressionMatch

/-- The independent JSON runner agrees with the typed evaluator at one input
environment and one admitted expression. Errors reject on both sides. -/
def AgreesAt (ctx : EvalContext) (run : Runner) {ty : Ty}
    (expression : Expr ty) (raw : Json) (env : EvalEnv)
    (_matched : Matches expression raw) : Prop :=
  run env raw = (expression.eval ctx env).toOption.map (Value.pack ty)

/-- The next binding evaluates in the current environment, then shadows any
older entry by prepending its value. No distinct-name assumption is needed. -/
theorem evaluateBindings_cons (run : Runner) (env : EvalEnv) (name : String)
    (raw : Json) (tail : List (String × Json)) :
    evaluateBindings run env ((name, raw) :: tail) =
      (run env raw).bind fun value =>
        evaluateBindings run ((name, value) :: env) tail := by
  simp only [evaluateBindings, List.foldlM_cons]
  cases result : run env raw <;> rfl

/-- One flattened binding agrees with the corresponding typed `letE`. The
premise for the tail is needed only in the environment produced by a successful
right-hand side, so this lemma preserves both rejection and lexical shadowing. -/
theorem evaluate_bind_cons_agrees
    (ctx : EvalContext) (run : Runner) (env : EvalEnv)
    {source target : Ty} {name : String} {value : Expr source}
    {body : Expr target} {valueJson : Json}
    {tail : List (String × Json)} {bodyJson : Json}
    (valueMatches : Matches value valueJson)
    (valueAgrees : AgreesAt ctx run value valueJson env valueMatches)
    (tailAgrees : ∀ result,
      value.eval ctx env = .ok result →
        evaluateNode ctx run ((name, Value.pack source result) :: env)
            (.bind tail bodyJson) =
          (body.eval ctx ((name, Value.pack source result) :: env)).toOption.map
            (Value.pack target)) :
    evaluateNode ctx run env (.bind ((name, valueJson) :: tail) bodyJson) =
      ((Expr.letE name value body).eval ctx env).toOption.map (Value.pack target) := by
  simp only [evaluateNode, evaluateBindings_cons]
  rw [valueAgrees]
  cases evaluated : value.eval ctx env with
  | error error =>
      simp [evaluated, Except.toOption, Expr.eval, Bind.bind, Except.bind]
  | ok result =>
      simp only [Except.toOption, Option.map_some, Option.bind_some]
      have tailValue := tailAgrees result evaluated
      simp only [evaluateNode] at tailValue
      rw [tailValue]
      simp [Expr.eval, evaluated, Except.toOption, Bind.bind, Except.bind]

/-- The empty flattened sequence runs its terminal body in the original
environment. -/
theorem evaluate_bind_terminal_agrees
    (ctx : EvalContext) (run : Runner) (env : EvalEnv)
    {ty : Ty} {expression : Expr ty} {bodyJson : Json}
    (matched : Matches expression bodyJson)
    (bodyAgrees : AgreesAt ctx run expression bodyJson env matched) :
    evaluateNode ctx run env (.bind [] bodyJson) =
      (expression.eval ctx env).toOption.map (Value.pack ty) := by
  simpa [AgreesAt, evaluateNode, evaluateBindings] using bodyAgrees

end Noctium.Verification.ImpactBindingEvaluation
