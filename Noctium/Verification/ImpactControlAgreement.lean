import Noctium.Verification.ImpactExpressionEvaluation
import Noctium.Verification.GenericStateEvaluationCanonical

namespace Noctium.Verification.ImpactControlAgreement

open Lean Noctium
open ImpactExpressionEvaluation ImpactScalarPrimitives ImpactScalarType
open ScalarNormalization

private def scalarEq {ty : Ty} : ScalarType ty → ty.Denote → ty.Denote → Bool
  | .native, left, right => left == right
  | .bool, left, right => left == right
  | .uint _, left, right => left == right

private theorem equal_packed (ctx : EvalContext) {ty : Ty}
    (scalarType : ScalarType ty) (left right : ty.Denote)
    (modulus : ctx.modulus = Field.modulus)
    (leftCanonical : ScalarNormalization.Canonical ty left)
    (rightCanonical : ScalarNormalization.Canonical ty right) :
    equal ctx.modulus (Value.pack ty left) (Value.pack ty right) =
      some (.bool (scalarEq scalarType left right)) := by
  cases scalarType with
  | native =>
      have leftBound : left < ctx.modulus := by
        simpa [ScalarNormalization.Canonical, ScalarNormalization.sourceNumber?, modulus]
          using leftCanonical
      have rightBound : right < ctx.modulus := by
        simpa [ScalarNormalization.Canonical, ScalarNormalization.sourceNumber?, modulus]
          using rightCanonical
      simp [equal, guard, canonical, scalarType?, Value.pack, scalarEq, leftBound, rightBound,
        BEq.beq, Noctium.instBEqTy.beq]
  | bool =>
      simp [equal, guard, canonical, scalarType?, Value.pack, scalarEq,
        BEq.beq, Noctium.instBEqTy.beq]
  | uint maximum =>
      have leftCanonical' : left < Field.modulus ∧ maximum ≤ ScalarPolicy.maxUint ∧
          left ≤ maximum := by
        simpa [ScalarNormalization.Canonical, ScalarNormalization.sourceNumber?]
          using leftCanonical
      have rightCanonical' : right < Field.modulus ∧ maximum ≤ ScalarPolicy.maxUint ∧
          right ≤ maximum := by
        simpa [ScalarNormalization.Canonical, ScalarNormalization.sourceNumber?]
          using rightCanonical
      rcases leftCanonical' with ⟨leftFieldBound, leftMaxBound, leftValueBound⟩
      rcases rightCanonical' with ⟨rightFieldBound, rightMaxBound, rightValueBound⟩
      have leftBound : maximum ≤ ScalarPolicy.maxUint ∧ left ≤ maximum ∧
          left < ctx.modulus := ⟨leftMaxBound, leftValueBound, by simpa [modulus] using leftFieldBound⟩
      have rightBound : maximum ≤ ScalarPolicy.maxUint ∧ right ≤ maximum ∧
          right < ctx.modulus := ⟨rightMaxBound, rightValueBound, by simpa [modulus] using rightFieldBound⟩
      simp [equal, guard, canonical, scalarType?, Value.pack, scalarEq,
        leftBound, rightBound, BEq.beq, Noctium.instBEqTy.beq]

private theorem select_packed (ctx : EvalContext) {ty : Ty}
    (scalarType : ScalarType ty) (modulus : ctx.modulus = Field.modulus)
    (condition : Bool) (yes no : ty.Denote)
    (yesCanonical : ScalarNormalization.Canonical ty yes)
    (noCanonical : ScalarNormalization.Canonical ty no) :
    select ctx.modulus (.bool condition) (Value.pack ty yes) (Value.pack ty no) =
      some (Value.pack ty (if condition then yes else no)) := by
  cases scalarType with
  | native =>
      have yesBound : yes < ctx.modulus := by
        simpa [ScalarNormalization.Canonical, ScalarNormalization.sourceNumber?, modulus]
          using yesCanonical
      have noBound : no < ctx.modulus := by
        simpa [ScalarNormalization.Canonical, ScalarNormalization.sourceNumber?, modulus]
          using noCanonical
      cases condition <;>
        simp [select, guard, canonical, scalarType?, Value.pack, yesBound, noBound,
          BEq.beq, Noctium.instBEqTy.beq]
  | bool =>
      cases condition <;>
        simp [select, guard, canonical, scalarType?, Value.pack,
          BEq.beq, Noctium.instBEqTy.beq]
  | uint maximum =>
      have yesCanonical' : yes < Field.modulus ∧ maximum ≤ ScalarPolicy.maxUint ∧
          yes ≤ maximum := by
        simpa [ScalarNormalization.Canonical, ScalarNormalization.sourceNumber?]
          using yesCanonical
      have noCanonical' : no < Field.modulus ∧ maximum ≤ ScalarPolicy.maxUint ∧
          no ≤ maximum := by
        simpa [ScalarNormalization.Canonical, ScalarNormalization.sourceNumber?]
          using noCanonical
      rcases yesCanonical' with ⟨yesFieldBound, yesMaxBound, yesValueBound⟩
      rcases noCanonical' with ⟨noFieldBound, noMaxBound, noValueBound⟩
      have yesBound : maximum ≤ ScalarPolicy.maxUint ∧ yes ≤ maximum ∧
          yes < ctx.modulus := ⟨yesMaxBound, yesValueBound, by simpa [modulus] using yesFieldBound⟩
      have noBound : maximum ≤ ScalarPolicy.maxUint ∧ no ≤ maximum ∧
          no < ctx.modulus := ⟨noMaxBound, noValueBound, by simpa [modulus] using noFieldBound⟩
      cases condition <;>
        simp [select, guard, canonical, scalarType?, Value.pack, yesBound, noBound,
          BEq.beq, Noctium.instBEqTy.beq]

/-- Dynamic scalar equality agrees with the typed expression evaluator when
both serialized children agree at the current environment. -/
theorem eq_agrees (ctx : EvalContext) (modulus : ctx.modulus = Field.modulus)
    (run : Runner) (env : EvalEnv) {ty : Ty} (left right : Expr ty)
    (leftJson rightJson : Json) (scalarType : ScalarType ty)
    (leftSupported : ScalarExpression left) (rightSupported : ScalarExpression right)
    (leftAgrees : run env leftJson =
      (left.eval ctx env).toOption.map (Value.pack ty))
    (rightAgrees : run env rightJson =
      (right.eval ctx env).toOption.map (Value.pack ty)) :
    evaluateNode ctx run env (.binary .eq leftJson rightJson) =
      ((Expr.eq left right).eval ctx env).toOption.map (Value.pack .bool) := by
  simp only [evaluateNode]
  rw [leftAgrees, rightAgrees]
  cases leftEval : left.eval ctx env with
  | error error =>
      cases scalarType <;>
        simp [leftEval, Except.toOption, Expr.eval, Bind.bind, Except.bind]
  | ok leftValue =>
      cases rightEval : right.eval ctx env with
      | error error =>
          cases scalarType <;>
            simp [leftEval, rightEval, Except.toOption, Expr.eval,
              Bind.bind, Except.bind]
      | ok rightValue =>
          have leftSourceCanonical := GenericStateEvaluationCanonical.expression_eval_canonical
            ctx env left leftSupported leftValue modulus leftEval
          have rightSourceCanonical := GenericStateEvaluationCanonical.expression_eval_canonical
            ctx env right rightSupported rightValue modulus rightEval
          have dynamicEquality := equal_packed ctx scalarType leftValue rightValue modulus
            leftSourceCanonical rightSourceCanonical
          cases scalarType with
          | native =>
              simp only [leftEval, rightEval, Except.toOption, Option.map_some, Expr.eval]
              change equal ctx.modulus (.native leftValue) (.native rightValue) =
                some (.bool (leftValue == rightValue))
              exact dynamicEquality
          | bool =>
              simp only [leftEval, rightEval, Except.toOption, Option.map_some, Expr.eval]
              change equal ctx.modulus (.bool leftValue) (.bool rightValue) =
                some (.bool (leftValue == rightValue))
              exact dynamicEquality
          | uint maximum =>
              simp only [leftEval, rightEval, Except.toOption, Option.map_some, Expr.eval]
              change equal ctx.modulus (.uint maximum leftValue) (.uint maximum rightValue) =
                some (.bool (leftValue == rightValue))
              exact dynamicEquality

/-- Dynamic scalar selection agrees with the eager typed selector when both
arms have admitted scalar values. -/
theorem select_agrees (ctx : EvalContext) (modulus : ctx.modulus = Field.modulus)
    (run : Runner) (env : EvalEnv) {ty : Ty} (condition : Expr .bool)
    (yes no : Expr ty) (conditionJson yesJson noJson : Json)
    (scalarType : ScalarType ty) (yesSupported : ScalarExpression yes)
    (noSupported : ScalarExpression no)
    (conditionAgrees : run env conditionJson =
      (condition.eval ctx env).toOption.map (Value.pack .bool))
    (yesAgrees : run env yesJson = (yes.eval ctx env).toOption.map (Value.pack ty))
    (noAgrees : run env noJson = (no.eval ctx env).toOption.map (Value.pack ty)) :
    evaluateNode ctx run env (.select conditionJson yesJson noJson) =
      ((Expr.select condition yes no).eval ctx env).toOption.map (Value.pack ty) := by
  simp only [evaluateNode]
  rw [conditionAgrees, yesAgrees, noAgrees]
  cases conditionEval : condition.eval ctx env with
  | error error =>
      simp [conditionEval, Except.toOption, Expr.eval, Bind.bind, Except.bind,
        Option.map]
  | ok conditionValue =>
      cases yesEval : yes.eval ctx env with
      | error error =>
          simp [conditionEval, yesEval, Except.toOption, Expr.eval,
            Bind.bind, Except.bind, Option.bind, Option.map, Value.pack]
      | ok yesValue =>
          cases noEval : no.eval ctx env with
          | error error =>
              simp [conditionEval, yesEval, noEval, Except.toOption, Expr.eval,
                Bind.bind, Except.bind, Option.bind, Option.map, Value.pack]
          | ok noValue =>
              have yesSourceCanonical := GenericStateEvaluationCanonical.expression_eval_canonical
                ctx env yes yesSupported yesValue modulus yesEval
              have noSourceCanonical := GenericStateEvaluationCanonical.expression_eval_canonical
                ctx env no noSupported noValue modulus noEval
              have dynamicSelection := select_packed ctx scalarType modulus conditionValue
                yesValue noValue yesSourceCanonical noSourceCanonical
              simpa [conditionEval, yesEval, noEval, Except.toOption, Expr.eval,
                Bind.bind, Except.bind, Option.bind, Option.map, Value.pack, Pure.pure, Except.pure]
                using dynamicSelection

/-- A serialized assertion executes its body precisely when the typed Bool
condition succeeds as `true`. -/
theorem assert_agrees (ctx : EvalContext) (_modulus : ctx.modulus = Field.modulus)
    (run : Runner) (env : EvalEnv) {ty : Ty} (condition : Expr .bool)
    (body : Expr ty) (conditionJson bodyJson : Json)
    (conditionAgrees : run env conditionJson =
      (condition.eval ctx env).toOption.map (Value.pack .bool))
    (bodyAgrees : run env bodyJson = (body.eval ctx env).toOption.map (Value.pack ty)) :
    evaluateNode ctx run env (.assertThen conditionJson bodyJson) =
      ((Expr.assertE condition body).eval ctx env).toOption.map (Value.pack ty) := by
  simp only [evaluateNode]
  rw [conditionAgrees, bodyAgrees]
  cases conditionEval : condition.eval ctx env with
  | error error =>
      simp [conditionEval, Except.toOption, Expr.eval, Bind.bind, Except.bind,
        Option.bind, Option.map, Value.pack]
  | ok conditionValue =>
      cases conditionValue <;>
        simp [conditionEval, Except.toOption, Expr.eval, ImpactScalarPrimitives.assert,
          Bind.bind, Except.bind, Option.bind, Option.map, Value.pack,
          Option.bind, Option.map] <;> rfl

/-- The expression evaluator and JSON evaluator call the same context oracle
for Poseidon2. This theorem makes no claim about that oracle's Rust
implementation. -/
theorem poseidon_agrees (ctx : EvalContext) (modulus : ctx.modulus = Field.modulus)
    (run : Runner) (env : EvalEnv) (domain : Nat) (left right : Expr .native)
    (leftJson rightJson : Json) (leftSupported : ScalarExpression left)
    (rightSupported : ScalarExpression right)
    (leftAgrees : run env leftJson = (left.eval ctx env).toOption.map (Value.pack .native))
    (rightAgrees : run env rightJson = (right.eval ctx env).toOption.map (Value.pack .native)) :
    evaluateNode ctx run env (.poseidon2 (toString domain) leftJson rightJson) =
      ((Expr.poseidon2 domain left right).eval ctx env).toOption.map (Value.pack .native) := by
  simp only [evaluateNode]
  rw [ImpactDecimal.parseCanonical_toString, leftAgrees, rightAgrees]
  by_cases domainBound : domain < ctx.modulus
  · cases leftEval : left.eval ctx env with
    | error error =>
        have domainNotAbove : ¬ctx.modulus ≤ domain := Nat.not_le_of_gt domainBound
        simp [domainBound, leftEval, Except.toOption, Expr.eval,
          ImpactScalarPrimitives.nativeLiteral, domainNotAbove, Bind.bind, Except.bind,
          Option.bind, Option.map, Value.pack]
    | ok leftValue =>
        cases rightEval : right.eval ctx env with
        | error error =>
            have domainNotAbove : ¬ctx.modulus ≤ domain := Nat.not_le_of_gt domainBound
            simp [domainBound, leftEval, rightEval, Except.toOption, Expr.eval,
              ImpactScalarPrimitives.nativeLiteral, domainNotAbove, Bind.bind, Except.bind,
              Option.bind, Option.map, Value.pack]
        | ok rightValue =>
            have leftSourceCanonical := GenericStateEvaluationCanonical.expression_eval_canonical
              ctx env left leftSupported leftValue modulus leftEval
            have rightSourceCanonical := GenericStateEvaluationCanonical.expression_eval_canonical
              ctx env right rightSupported rightValue modulus rightEval
            have leftFieldBound : leftValue < Field.modulus := by
              simpa [ScalarNormalization.Canonical, ScalarNormalization.sourceNumber?]
                using leftSourceCanonical
            have rightFieldBound : rightValue < Field.modulus := by
              simpa [ScalarNormalization.Canonical, ScalarNormalization.sourceNumber?]
                using rightSourceCanonical
            have leftBound : leftValue < ctx.modulus := by simpa [modulus] using leftFieldBound
            have rightBound : rightValue < ctx.modulus := by simpa [modulus] using rightFieldBound
            have domainNotAbove : ¬ctx.modulus ≤ domain := Nat.not_le_of_gt domainBound
            have modulusCheck : (ctx.modulus == Field.modulus) = true := by simp [modulus]
            cases oracle : ctx.poseidon2 domain leftValue rightValue with
            | error error =>
                simp [domainBound, leftEval, rightEval, oracle,
                  Except.toOption, Expr.eval, ImpactScalarPrimitives.nativeLiteral,
                  ImpactScalarPrimitives.poseidon, ImpactScalarPrimitives.canonical,
                  leftBound, rightBound, domainNotAbove, modulusCheck, guard, Bind.bind, Except.bind,
                  Option.bind, Option.map, Value.pack, Pure.pure]
                  <;> rfl
            | ok result =>
                by_cases resultBound : result < ctx.modulus
                · have resultNotAbove : ¬ctx.modulus ≤ result := Nat.not_le_of_gt resultBound
                  simp [domainBound, leftEval, rightEval, oracle, resultBound,
                    Except.toOption, Expr.eval, ImpactScalarPrimitives.nativeLiteral,
                    ImpactScalarPrimitives.poseidon, ImpactScalarPrimitives.canonical,
                    leftBound, rightBound, domainNotAbove, resultNotAbove,
                    modulusCheck, guard, Bind.bind, Except.bind, Option.bind, Option.map, Value.pack,
                    Pure.pure, Except.pure] <;> rfl
                · have resultAbove : ctx.modulus ≤ result := Nat.le_of_not_gt resultBound
                  simp [domainBound, leftEval, rightEval, oracle, resultAbove,
                    Except.toOption, Expr.eval, ImpactScalarPrimitives.nativeLiteral,
                    ImpactScalarPrimitives.poseidon, ImpactScalarPrimitives.canonical,
                    leftBound, rightBound, domainNotAbove, resultBound,
                    modulusCheck, guard, Bind.bind, Except.bind, Option.bind, Option.map, Value.pack,
                    Pure.pure, Except.pure] <;> rfl
  · have domainOutOfRange : ctx.modulus ≤ domain := Nat.le_of_not_gt domainBound
    simp [domainBound, domainOutOfRange, ImpactScalarPrimitives.nativeLiteral,
      Except.toOption, Expr.eval, Bind.bind, Except.bind, Option.bind, Option.map,
      Value.pack, Pure.pure, Except.pure] <;> rfl

end Noctium.Verification.ImpactControlAgreement
