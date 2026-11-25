import Noctium.Verification.ImpactDecimal
import Noctium.Verification.ImpactScalarPrimitives
import Noctium.Verification.ImpactScalarType
import Noctium.Verification.GenericStateEvaluationCanonical

namespace Noctium.Verification.ImpactExpressionEvaluation

open Lean ImpactExpressionNode
open ImpactDecimal ImpactScalarPrimitives ImpactScalarType

abbrev Runner := EvalEnv → Json → Option Value

/-- A lexical binding becomes the first match for its name. This models
Rust's insert into the local map after the right-hand side has run. -/
def evaluateBindings (run : Runner) (env : EvalEnv) :
    List (String × Json) → Option EvalEnv :=
  List.foldlM (fun current (name, raw) =>
    (run current raw).map (fun value => (name, value) :: current)) env

def evaluateReference (modulus : Nat) (env : EvalEnv) (name : String) : Option Value := do
  let value ← env.lookup name
  if canonical modulus value then some value else none

/-- Evaluate one decoded scalar expression layer using the supplied child
evaluator. The context supplies the field modulus and the Poseidon2 oracle. -/
def evaluateNode (ctx : EvalContext) (run : Runner) (env : EvalEnv) : Node → Option Value
  | .native decimal => parseCanonical decimal >>= nativeLiteral ctx.modulus
  | .bool value => some (.bool value)
  | .uint bound decimal => do
      let maximum ← parseCanonical bound
      let value ← parseCanonical decimal
      uintLiteral ctx.modulus maximum value
  | .reference name => evaluateReference ctx.modulus env name
  | .binary .eq left right => do
      let a ← run env left
      let b ← run env right
      equal ctx.modulus a b
  | .binary op left right => do
      let a ← run env left
      let b ← run env right
      nativeBinary ctx.modulus op a b
  | .unsigned op bound left right => do
      let a ← run env left
      let b ← run env right
      let maximum ← parseCanonical bound
      unsignedBinary ctx.modulus maximum op a b
  | .cast target child => do
      let value ← run env child
      let ty ← parseScalarTypeName target
      cast ctx.modulus ty value
  | .bind bindings body => do
      let current ← evaluateBindings run env bindings
      run current body
  | .assertThen condition body => do
      let guard ← run env condition
      let _ ← ImpactScalarPrimitives.assert guard
      run env body
  | .select condition yes no => do
      let some (.bool guard) := run env condition | none
      let a ← run env yes
      let b ← run env no
      select ctx.modulus (.bool guard) a b
  | .poseidon2 decimal left right => do
      let domain ← parseCanonical decimal
      let _ ← nativeLiteral ctx.modulus domain
      let a ← run env left
      let b ← run env right
      poseidon ctx domain a b

/-- Depth-bounded execution of scalar JSON for checking emitted artifacts.
Fuel exhaustion, decoder rejection, and evaluation rejection return none. -/
def evaluate : Nat → EvalContext → Runner
  | 0, _, _, _ => none
  | fuel + 1, ctx, env, raw => do
      let node ← (decode raw).toOption
      evaluateNode ctx (evaluate fuel ctx) env node

theorem evaluate_decoded (fuel : Nat) (ctx : EvalContext) (env : EvalEnv)
    {raw : Json} {node : Node} (decoded : decode raw = .ok node) :
    evaluate (fuel + 1) ctx env raw = evaluateNode ctx (evaluate fuel ctx) env node := by
  simp [evaluate, decoded]
  rfl

theorem nativeLiteral_agrees (ctx : EvalContext) (run : Runner) (env : EvalEnv) (value : Nat) :
    evaluateNode ctx run env (.native (toString value)) =
      ((Expr.native value).eval ctx env).toOption.map (Value.pack .native) := by
  simp only [evaluateNode, parseCanonical_toString, Bind.bind, Option.bind_some,
    nativeLiteral, Expr.eval]
  split <;> rfl

theorem boolLiteral_agrees (ctx : EvalContext) (run : Runner) (env : EvalEnv)
    (value : _root_.Bool) :
    evaluateNode ctx run env (.bool value) =
      ((Expr.bool value).eval ctx env).toOption.map (Value.pack .bool) := by
  simp [evaluateNode, Expr.eval, Value.pack, Except.toOption]

theorem uintLiteral_agrees (ctx : EvalContext) (run : Runner) (env : EvalEnv)
    (maximum value : Nat) :
    evaluateNode ctx run env (.uint (toString maximum) (toString value)) =
      ((Expr.uint maximum value).eval ctx env).toOption.map (Value.pack (.uint maximum)) := by
  simp only [evaluateNode, parseCanonical_toString, Bind.bind, Option.bind_some, uintLiteral,
    Expr.eval, canonical_eq]
  by_cases maximumFits : maximum ≤ ScalarPolicy.maxUint <;>
    by_cases valueFits : value ≤ maximum <;>
    by_cases fieldFits : value < ctx.modulus <;>
    simp [maximumFits, valueFits, fieldFits, Value.pack, Except.toOption, Pure.pure, Except.pure]

/-- Once the decoded operand agrees, the serialized scalar cast has the same
result or rejection as the typed source cast. -/
theorem cast_agrees (ctx : EvalContext) (modulus : ctx.modulus = Field.modulus)
    (run : Runner) (env : EvalEnv) {source target : Ty} (value : Expr source) (raw : Json)
    (sourceType : ScalarNormalization.ScalarType source)
    (targetType : ScalarNormalization.ScalarType target)
    (supported : ScalarNormalization.ScalarExpression value)
    (parsed : parseScalarTypeName (NativeExpression.typeName target) = some target)
    (agrees : run env raw = (value.eval ctx env).toOption.map (Value.pack source)) :
    evaluateNode ctx run env (.cast (NativeExpression.typeName target) raw) =
      ((Expr.cast target value).eval ctx env).toOption.map (Value.pack target) := by
  cases result : value.eval ctx env with
  | error reason =>
    cases sourceType <;> cases targetType <;>
      simp [evaluateNode, agrees, result, Expr.eval, Ty.isBytes, Ty.isJubjub, Ty.isForeign,
        Bind.bind, Except.bind, Except.toOption]
  | ok found =>
    have admitted := GenericStateEvaluationCanonical.expression_eval_canonical
      ctx env value supported found modulus result
    rw [ScalarNormalization.eval_cast_scalar ctx env value sourceType targetType found result]
    simpa [evaluateNode, agrees, result, parsed, Except.toOption] using
      ImpactScalarPrimitives.cast_eq_scalarCast ctx modulus sourceType targetType found admitted

end Noctium.Verification.ImpactExpressionEvaluation
