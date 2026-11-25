import Noctium.Verification.ImpactArithmeticAgreement
import Noctium.Verification.ImpactBindingEvaluation
import Noctium.Verification.ImpactControlAgreement
import Noctium.Verification.ImpactEvaluationValidation
import Noctium.Verification.ImpactExpressionSoundness
import Noctium.Verification.ImpactReferenceEvaluation

namespace Noctium.Verification.ImpactExpressionAgreement

open Lean ImpactExpressionNode ImpactExpressionMatch ImpactExpressionEvaluation
open ImpactEvaluationValidation ImpactReferenceEvaluation ScalarNormalization

private def outcome (ctx : EvalContext) (expression : Expr ty) (env : EvalEnv) : Option Value :=
  (expression.eval ctx env).toOption.map (Value.pack ty)

private def validIn (types : TypeEnv) (expression : Expr ty) : Prop :=
  expression.validate Capabilities.scalarFragment types = .ok ()

/-- The bound is uniform over environments, including those produced when a
binding shadows a previous name. The equality preserves both success and
rejection for every fuel amount above that bound. -/
private def Agreement (ctx : EvalContext) (expression : Expr ty)
    (run : Nat → EvalEnv → Option Value) : Prop :=
  ScalarExpression expression ∧
    ∃ minimum, ∀ fuel, minimum ≤ fuel → ∀ types env,
      validIn types expression → TypedScalarEnv types env →
      run fuel env = outcome ctx expression env

private theorem decodedAgreement {ctx : EvalContext} {expression : Expr ty}
    {raw : Json} {node : Node} (decoded : decode raw = .ok node)
    (agreement : Agreement ctx expression
      (fun fuel env => evaluateNode ctx (evaluate fuel ctx) env node)) :
    Agreement ctx expression (fun fuel env => evaluate fuel ctx env raw) := by
  obtain ⟨supported, minimum, agrees⟩ := agreement
  refine ⟨supported, minimum + 1, ?_⟩
  intro fuel enough types env valid typed
  cases fuel with
  | zero => omega
  | succ fuel =>
    change evaluate (fuel + 1) ctx env raw = _
    rw [evaluate_decoded fuel ctx env decoded]
    exact agrees fuel (by omega) types env valid typed

private theorem binaryAgreement
    {ctx : EvalContext} {left : Expr leftTy} {right : Expr rightTy} {expression : Expr ty}
    {leftJson rightJson raw : Json} {node : Node}
    (decoded : decode raw = .ok node) (supported : ScalarExpression expression)
    (leftAgreement : Agreement ctx left (fun fuel env => evaluate fuel ctx env leftJson))
    (rightAgreement : Agreement ctx right (fun fuel env => evaluate fuel ctx env rightJson))
    (children : ∀ types, validIn types expression → validIn types left ∧ validIn types right)
    (step : ∀ run env, run env leftJson = outcome ctx left env →
      run env rightJson = outcome ctx right env →
      evaluateNode ctx run env node = outcome ctx expression env) :
    Agreement ctx expression (fun fuel env => evaluate fuel ctx env raw) := by
  apply decodedAgreement decoded
  obtain ⟨_, leftFuel, leftAgrees⟩ := leftAgreement
  obtain ⟨_, rightFuel, rightAgrees⟩ := rightAgreement
  refine ⟨supported, max leftFuel rightFuel, ?_⟩
  intro fuel enough types env valid typed
  obtain ⟨leftValid, rightValid⟩ := children types valid
  exact step _ env
    (leftAgrees fuel (by omega) types env leftValid typed)
    (rightAgrees fuel (by omega) types env rightValid typed)

private theorem matchedAgreement (ctx : EvalContext) (modulus : ctx.modulus = Field.modulus)
    {expression : Expr ty} {raw : Json} (matched : Matches expression raw) :
    Agreement ctx expression (fun fuel env => evaluate fuel ctx env raw) := by
  refine Matches.rec
    (motive_1 := fun e json _ => Agreement ctx e (fun fuel env => evaluate fuel ctx env json))
    (motive_2 := fun e rows body _ => Agreement ctx e (fun fuel env =>
      evaluateNode ctx (evaluate fuel ctx) env (.bind rows body)))
    ?matchNative ?matchBool ?matchUInt ?matchRef ?matchAdd ?matchMul ?matchSub
    ?matchUadd ?matchUsub ?matchUmul ?matchCast ?matchLet ?matchAssert ?matchCopy
    ?matchDisclose ?matchEq ?matchSelect ?matchPoseidon
    ?bindingTerminal ?bindingCons ?bindingCopy ?bindingDisclose matched
  case matchNative =>
    intro value raw decoded
    exact decodedAgreement decoded ⟨.native value, 0, fun fuel _ _ env _ _ =>
      nativeLiteral_agrees ctx (evaluate fuel ctx) env value⟩
  case matchBool =>
    intro value raw decoded
    exact decodedAgreement decoded ⟨.bool value, 0, fun fuel _ _ env _ _ =>
      boolLiteral_agrees ctx (evaluate fuel ctx) env value⟩
  case matchUInt =>
    intro maximum value raw decoded
    exact decodedAgreement decoded ⟨.uint maximum value, 0, fun fuel _ _ env _ _ =>
      uintLiteral_agrees ctx (evaluate fuel ctx) env maximum value⟩
  case matchRef =>
    intro ty name raw decoded scalarType
    apply decodedAgreement decoded
    refine ⟨.ref name scalarType, 0, ?_⟩
    intro fuel _ types env valid typed
    exact evaluateReference_agrees ctx modulus types env typed name scalarType
      (ref_lookup _ _ _ scalarType valid)
  case matchAdd =>
    intro left right raw leftJson rightJson decoded _ _ ihLeft ihRight
    apply binaryAgreement decoded (.add left right ihLeft.1 ihRight.1) ihLeft ihRight
    · intro types valid
      simpa [validIn, Expr.validate, Bind.bind, validate_unit_bind, Capabilities.scalarFragment, Capabilities.crypto] using valid
    · intro run env leftAgrees rightAgrees
      exact ImpactArithmeticAgreement.add_agrees ctx modulus run env left right leftJson rightJson
        ihLeft.1 ihRight.1 leftAgrees rightAgrees
  case matchMul =>
    intro left right raw leftJson rightJson decoded _ _ ihLeft ihRight
    apply binaryAgreement decoded (.mul left right ihLeft.1 ihRight.1) ihLeft ihRight
    · intro types valid
      simpa [validIn, Expr.validate, Bind.bind, validate_unit_bind, Capabilities.scalarFragment, Capabilities.crypto] using valid
    · intro run env leftAgrees rightAgrees
      exact ImpactArithmeticAgreement.mul_agrees ctx modulus run env left right leftJson rightJson
        ihLeft.1 ihRight.1 leftAgrees rightAgrees
  case matchSub =>
    intro left right raw leftJson rightJson decoded _ _ ihLeft ihRight
    apply binaryAgreement decoded (.sub left right ihLeft.1 ihRight.1) ihLeft ihRight
    · intro types valid
      simpa [validIn, Expr.validate, Bind.bind, validate_unit_bind, Capabilities.scalarFragment, Capabilities.crypto] using valid
    · intro run env leftAgrees rightAgrees
      exact ImpactArithmeticAgreement.sub_agrees ctx modulus run env left right leftJson rightJson
        ihLeft.1 ihRight.1 leftAgrees rightAgrees
  case matchUadd =>
    intro m n left right raw leftJson rightJson decoded _ _ ihLeft ihRight
    apply binaryAgreement decoded (.uadd left right ihLeft.1 ihRight.1) ihLeft ihRight
    · intro types valid
      have checked : (Ty.uint (m + n)).validate Capabilities.scalarFragment = .ok () ∧
          validIn types left ∧ validIn types right := by
        simpa [validIn, Expr.validate, Bind.bind, validate_unit_bind, Capabilities.scalarFragment, Capabilities.crypto] using valid
      exact checked.2
    · intro run env leftAgrees rightAgrees
      exact ImpactArithmeticAgreement.uadd_agrees ctx modulus run env left right leftJson rightJson
        ihLeft.1 ihRight.1 leftAgrees rightAgrees
  case matchUsub =>
    intro m n left right raw leftJson rightJson decoded _ _ ihLeft ihRight
    apply binaryAgreement decoded (.usub left right ihLeft.1 ihRight.1) ihLeft ihRight
    · intro types valid
      have checked : (Ty.uint m).validate Capabilities.scalarFragment = .ok () ∧
          validIn types left ∧ validIn types right := by
        simpa [validIn, Expr.validate, Bind.bind, validate_unit_bind, Capabilities.scalarFragment, Capabilities.crypto] using valid
      exact checked.2
    · intro run env leftAgrees rightAgrees
      exact ImpactArithmeticAgreement.usub_agrees ctx modulus run env left right leftJson rightJson
        ihLeft.1 ihRight.1 leftAgrees rightAgrees
  case matchUmul =>
    intro m n left right raw leftJson rightJson decoded _ _ ihLeft ihRight
    apply binaryAgreement decoded (.umul left right ihLeft.1 ihRight.1) ihLeft ihRight
    · intro types valid
      have checked : (Ty.uint (m * n)).validate Capabilities.scalarFragment = .ok () ∧
          validIn types left ∧ validIn types right := by
        simpa [validIn, Expr.validate, Bind.bind, validate_unit_bind, Capabilities.scalarFragment, Capabilities.crypto] using valid
      exact checked.2
    · intro run env leftAgrees rightAgrees
      exact ImpactArithmeticAgreement.umul_agrees ctx modulus run env left right leftJson rightJson
        ihLeft.1 ihRight.1 leftAgrees rightAgrees
  case matchCast =>
    intro source target value raw valueJson decoded targetType _ ih
    obtain ⟨supported, minimum, agrees⟩ := ih
    obtain ⟨sourceType⟩ := GenericStateEvaluationCanonical.scalarExpression_type supported
    apply decodedAgreement decoded
    refine ⟨.cast value sourceType targetType supported, minimum, ?_⟩
    intro fuel enough types env valid typed
    obtain ⟨childValid, parsed⟩ := cast_valid_children
      Capabilities.scalarFragment types sourceType targetType value valid
    exact cast_agrees ctx modulus _ env value valueJson sourceType targetType supported parsed
      (agrees fuel enough types env childValid typed)
  case matchLet =>
    intro ty expression raw rows body decoded _ _ ih
    exact decodedAgreement decoded ih
  case matchAssert =>
    intro ty condition body raw conditionJson bodyJson decoded _ _ ihCondition ihBody
    apply binaryAgreement decoded (.assertE condition body ihCondition.1 ihBody.1) ihCondition ihBody
    · intro types valid
      simpa [validIn, Expr.validate, Bind.bind, validate_unit_bind] using valid
    · intro run env conditionAgrees bodyAgrees
      exact ImpactControlAgreement.assert_agrees ctx modulus run env condition body
        conditionJson bodyJson conditionAgrees bodyAgrees
  case matchCopy =>
    intro ty value raw _ ih
    obtain ⟨supported, minimum, agrees⟩ := ih
    refine ⟨.copyValue value supported, minimum, ?_⟩
    intro fuel enough types env valid typed
    simpa only [outcome, Expr.eval] using
      agrees fuel enough types env (by simpa [validIn, Expr.validate] using valid) typed
  case matchDisclose =>
    intro ty span value raw _ ih
    obtain ⟨supported, minimum, agrees⟩ := ih
    refine ⟨.disclose span value supported, minimum, ?_⟩
    intro fuel enough types env valid typed
    simpa only [outcome, Expr.eval] using
      agrees fuel enough types env (by simpa [validIn, Expr.validate] using valid) typed
  case matchEq =>
    intro ty left right raw leftJson rightJson decoded scalarType _ _ ihLeft ihRight
    apply binaryAgreement decoded (.eq left right scalarType ihLeft.1 ihRight.1) ihLeft ihRight
    · intro types valid
      cases scalarType <;>
        simpa [validIn, Expr.validate, Bind.bind, validate_unit_bind, Capabilities.scalarFragment, Capabilities.crypto,
          Ty.isBytes] using valid
    · intro run env leftAgrees rightAgrees
      exact ImpactControlAgreement.eq_agrees ctx modulus run env left right leftJson rightJson
        scalarType ihLeft.1 ihRight.1 leftAgrees rightAgrees
  case matchSelect =>
    intro ty condition yes no raw conditionJson yesJson noJson decoded scalarType _ _ _
      ihCondition ihYes ihNo
    obtain ⟨conditionSupported, conditionFuel, conditionAgrees⟩ := ihCondition
    obtain ⟨yesSupported, yesFuel, yesAgrees⟩ := ihYes
    obtain ⟨noSupported, noFuel, noAgrees⟩ := ihNo
    apply decodedAgreement decoded
    refine ⟨.select condition yes no scalarType conditionSupported yesSupported noSupported,
      max conditionFuel (max yesFuel noFuel), ?_⟩
    intro fuel enough types env valid typed
    have checked : validIn types condition ∧ validIn types yes ∧ validIn types no := by
      cases scalarType <;>
        simpa [validIn, Expr.validate, Bind.bind, validate_unit_bind, Capabilities.scalarFragment, Capabilities.crypto,
          Ty.isBytes, Ty.isJubjub, Ty.isForeign] using valid
    exact ImpactControlAgreement.select_agrees ctx modulus _ env condition yes no
      conditionJson yesJson noJson scalarType yesSupported noSupported
      (conditionAgrees fuel (by omega) types env checked.1 typed)
      (yesAgrees fuel (by omega) types env checked.2.1 typed)
      (noAgrees fuel (by omega) types env checked.2.2 typed)
  case matchPoseidon =>
    intro domain left right raw leftJson rightJson decoded _ _ ihLeft ihRight
    apply binaryAgreement decoded (.poseidon2 domain left right ihLeft.1 ihRight.1) ihLeft ihRight
    · intro types valid
      simp only [validIn, Expr.validate] at valid
      split at valid
      · change Except.error _ = Except.ok () at valid
        contradiction
      · change (left.validate Capabilities.scalarFragment types >>=
          fun _ => right.validate Capabilities.scalarFragment types) = .ok () at valid
        exact (validate_unit_bind _ _).1 valid
    · intro run env leftAgrees rightAgrees
      exact ImpactControlAgreement.poseidon_agrees ctx modulus run env domain left right
        leftJson rightJson ihLeft.1 ihRight.1 leftAgrees rightAgrees
  case bindingTerminal =>
    intro ty expression bodyJson matched ih
    obtain ⟨supported, minimum, agrees⟩ := ih
    exact ⟨supported, minimum, fun fuel enough types env valid typed =>
      ImpactBindingEvaluation.evaluate_bind_terminal_agrees ctx _ env matched
        (agrees fuel enough types env valid typed)⟩
  case bindingCons =>
    intro source target name value body valueJson tail bodyJson valueMatches _
      ihValue ihBody
    obtain ⟨valueSupported, valueFuel, valueAgrees⟩ := ihValue
    obtain ⟨bodySupported, bodyFuel, bodyAgrees⟩ := ihBody
    obtain ⟨sourceType⟩ := GenericStateEvaluationCanonical.scalarExpression_type valueSupported
    refine ⟨.letE name value body sourceType valueSupported bodySupported,
      max valueFuel bodyFuel, ?_⟩
    intro fuel enough types env valid typed
    have checked := let_valid Capabilities.scalarFragment types name value body valid
    apply ImpactBindingEvaluation.evaluate_bind_cons_agrees ctx _ env valueMatches
      (valueAgrees fuel (by omega) types env checked.1 typed)
    intro result evaluated
    have canonical := GenericStateEvaluationCanonical.expression_eval_canonical
      ctx env value valueSupported result modulus evaluated
    exact bodyAgrees fuel (by omega) ((name, source) :: types) _
      checked.2 (typed.extend name result canonical)
  case bindingCopy =>
    intro ty value rows body _ ih
    obtain ⟨supported, minimum, agrees⟩ := ih
    refine ⟨.copyValue value supported, minimum, ?_⟩
    intro fuel enough types env valid typed
    simpa only [outcome, Expr.eval] using
      agrees fuel enough types env (by simpa [validIn, Expr.validate] using valid) typed
  case bindingDisclose =>
    intro ty span value rows body _ ih
    obtain ⟨supported, minimum, agrees⟩ := ih
    refine ⟨.disclose span value supported, minimum, ?_⟩
    intro fuel enough types env valid typed
    simpa only [outcome, Expr.eval] using
      agrees fuel enough types env (by simpa [validIn, Expr.validate] using valid) typed

/-- Every matching scalar expression has a sufficient fuel bound for equality
between decoded execution and packed source evaluation. The bound depends on
the expression and its wire shape, so the same bound works across lexical
environments and for source failures. -/
theorem evaluate_matches (ctx : EvalContext) (modulus : ctx.modulus = Field.modulus)
    {expression : Expr ty} {raw : Json} (matched : Matches expression raw) :
    ∃ minimum, ∀ fuel, minimum ≤ fuel → ∀ types env,
      expression.validate Capabilities.scalarFragment types = .ok () →
      TypedScalarEnv types env →
      evaluate fuel ctx env raw =
        (expression.eval ctx env).toOption.map (Value.pack ty) :=
  (matchedAgreement ctx modulus matched).2

/-- Apply whole-expression agreement to the compiler's actual expression
serializer. This theorem interprets the independent Lean evaluator. -/
theorem evaluate_toJson (ctx : EvalContext) (modulus : ctx.modulus = Field.modulus)
    {expression : Expr ty} (supported : ScalarExpression expression) :
    ∃ minimum, ∀ fuel, minimum ≤ fuel → ∀ types env,
      expression.validate Capabilities.scalarFragment types = .ok () →
      TypedScalarEnv types env →
      evaluate fuel ctx env (NativeExpression.toJson expression) =
        (expression.eval ctx env).toOption.map (Value.pack ty) :=
  evaluate_matches ctx modulus (ImpactExpressionSoundness.matches_toJson supported)

end Noctium.Verification.ImpactExpressionAgreement
