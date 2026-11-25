import Noctium.Verification.ScalarNormalization

namespace Noctium.Verification.GenericStateEvaluationCanonical

open ScalarNormalization

private theorem scalarCast_canonical (ctx : EvalContext)
    {target : Ty} (targetType : ScalarType target) (number : Nat)
    (value : target.Denote) (modulus : ctx.modulus = Field.modulus)
    (evaluated : scalarCast ctx target targetType number = .ok value) :
    Canonical target value := by
  cases targetType with
  | native =>
    change (if number < ctx.modulus then (Except.ok number : Except String Nat)
      else (Except.error "noncanonical scalar conversion" : Except String Nat)) =
        .ok value at evaluated
    have bound : number < ctx.modulus := by
      by_cases h : number < ctx.modulus
      · exact h
      · simp [h] at evaluated
    have equality : value = number := by
      simp [bound] at evaluated
      exact evaluated.symm
    subst value
    exact ⟨by simpa [ScalarNormalization.number, modulus] using bound, trivial⟩
  | bool =>
    cases value <;>
      simp [Canonical, ScalarNormalization.number, Field.modulus]
  | uint maximum =>
    change (if maximum ≤ ScalarPolicy.maxUint && number ≤ maximum && number < ctx.modulus
      then (Except.ok number : Except String Nat)
      else (Except.error "scalar conversion exceeds unsigned bound" : Except String Nat)) =
        .ok value at evaluated
    have maximumBound : maximum ≤ ScalarPolicy.maxUint := by
      by_cases h : maximum ≤ ScalarPolicy.maxUint
      · exact h
      · simp [h] at evaluated
    have valueBound : number ≤ maximum := by
      by_cases h : number ≤ maximum
      · exact h
      · simp [maximumBound, h] at evaluated
    have fieldBound : number < ctx.modulus := by
      by_cases h : number < ctx.modulus
      · exact h
      · simp [maximumBound, valueBound, h] at evaluated
    have equality : value = number := by
      simp [maximumBound, valueBound, fieldBound] at evaluated
      exact evaluated.symm
    subst value
    exact ⟨by simpa [ScalarNormalization.number, modulus] using fieldBound,
      maximumBound, valueBound⟩

private theorem scalarType_supported {ty : Ty} (scalarType : ScalarType ty) :
    ty.isBytes = false ∧ ty.isJubjub = false ∧ ty.isForeign = false := by
  cases scalarType <;> simp [Ty.isBytes, Ty.isJubjub, Ty.isForeign]

private theorem canonical_native_of_bound (value : Nat) (bound : value < Field.modulus) :
    Canonical .native value := by
  exact ⟨by simpa [ScalarNormalization.number] using bound, trivial⟩

/-- Successful evaluation returns a canonical value for expressions admitted
by the scalar fragment. The admission excludes opaque, byte, curve and foreign
results whose source values do not have scalar canonicality. -/
theorem expression_eval_canonical (ctx : EvalContext) (env : EvalEnv)
    (expression : Expr ty) (admission : ScalarExpression expression)
    (value : ty.Denote) (modulus : ctx.modulus = Field.modulus)
    (evaluated : expression.eval ctx env = .ok value) :
    Canonical ty value := by
  induction admission generalizing env with
  | native number =>
    simp only [Expr.eval] at evaluated
    change (if number < ctx.modulus then (Except.ok number : Except String Nat)
      else (Except.error "noncanonical native constant" : Except String Nat)) =
        .ok value at evaluated
    have bound : number < ctx.modulus := by
      by_cases h : number < ctx.modulus
      · exact h
      · simp [h] at evaluated
    have equality : value = number := by
      simp [bound] at evaluated
      exact evaluated.symm
    subst value
    exact canonical_native_of_bound number (by simpa [modulus] using bound)
  | bool boolean =>
    cases value <;> simp [Canonical, ScalarNormalization.number, Field.modulus]
  | uint maximum number =>
    simp only [Expr.eval, canonical_eq] at evaluated
    have maximumBound : maximum ≤ ScalarPolicy.maxUint := by
      by_cases bound : maximum ≤ ScalarPolicy.maxUint
      · exact bound
      · simp [bound] at evaluated
    have valueBound : number ≤ maximum := by
      by_cases bound : number ≤ maximum
      · exact bound
      · simp [bound] at evaluated
    have fieldBound : number < ctx.modulus := by
      by_cases bound : number < ctx.modulus
      · exact bound
      · simp [bound] at evaluated
    have equality : value = number := by
      simp [maximumBound, valueBound, fieldBound] at evaluated
      exact (Except.ok.inj evaluated).symm
    subst value
    exact ⟨by simpa [ScalarNormalization.number, modulus] using fieldBound,
      maximumBound, valueBound⟩
  | @ref refTy name scalarType =>
    cases scalarType with
    | native =>
      simp only [Expr.eval, canonical_eq] at evaluated
      cases lookup : env.lookup name with
      | none => simp [lookup] at evaluated
      | some raw =>
        cases typed : raw.as .native with
        | none => simp [lookup, typed] at evaluated
        | some found =>
          have bound : found < ctx.modulus := by
            by_cases bound : found < ctx.modulus
            · exact bound
            · simp [Expr.eval, lookup, typed, canonical_eq, bound, bind, Except.bind] at evaluated
          have equality : value = found := by
            simp [Expr.eval, lookup, typed, canonical_eq, bound, bind, Except.bind] at evaluated
            change (Except.ok found : Except String Nat) = .ok value at evaluated
            exact (Except.ok.inj evaluated).symm
          subst value
          exact ⟨by simpa [ScalarNormalization.number, modulus] using bound, trivial⟩
    | bool =>
      cases value <;> simp [Canonical, ScalarNormalization.number, Field.modulus]
    | uint maximum =>
      cases lookup : env.lookup name with
      | none => simp [Expr.eval, lookup] at evaluated
      | some raw =>
        cases typed : raw.as (.uint maximum) with
        | none => simp [Expr.eval, lookup, typed] at evaluated
        | some found =>
          have maximumBound : maximum ≤ ScalarPolicy.maxUint := by
            by_cases bound : maximum ≤ ScalarPolicy.maxUint
            · exact bound
            · simp [Expr.eval, lookup, typed, canonical_eq, bound,
                bind, Except.bind] at evaluated
          have valueBound : found ≤ maximum := by
            by_cases bound : found ≤ maximum
            · exact bound
            · simp [Expr.eval, lookup, typed, canonical_eq, bound,
                bind, Except.bind] at evaluated
          have fieldBound : found < ctx.modulus := by
            by_cases bound : found < ctx.modulus
            · exact bound
            · simp [Expr.eval, lookup, typed, canonical_eq, bound,
                bind, Except.bind] at evaluated
          have equality : value = found := by
            simp [Expr.eval, lookup, typed, canonical_eq, maximumBound, valueBound,
              fieldBound] at evaluated
            change (Except.ok found : Except String Nat) = .ok value at evaluated
            exact (Except.ok.inj evaluated).symm
          subst value
          exact ⟨by simpa [ScalarNormalization.number, modulus] using fieldBound,
            maximumBound, valueBound⟩
  | add left right leftSupported rightSupported ihLeft ihRight =>
    cases leftEval : left.eval ctx env with
    | error message =>
      simp [Expr.eval, leftEval, modulus, Field.modulus,
        bind, Bind.bind, Except.bind] at evaluated
    | ok leftValue =>
      cases rightEval : right.eval ctx env with
      | error message =>
        simp [Expr.eval, leftEval, rightEval, modulus, Field.modulus,
          bind, Bind.bind, Except.bind] at evaluated
      | ok rightValue =>
        simp [Expr.eval, leftEval, rightEval, modulus, Field.modulus,
          bind, Bind.bind, Except.bind] at evaluated
        change (Except.ok ((leftValue + rightValue) % Field.modulus) : Except String Nat) =
          .ok value at evaluated
        have resultEq : (leftValue + rightValue) % Field.modulus = value :=
          Except.ok.inj evaluated
        subst value
        exact canonical_native_of_bound _ (Nat.mod_lt _ (by decide))
  | mul left right leftSupported rightSupported ihLeft ihRight =>
    cases leftEval : left.eval ctx env with
    | error message =>
      simp [Expr.eval, leftEval, modulus, Field.modulus,
        bind, Bind.bind, Except.bind] at evaluated
    | ok leftValue =>
      cases rightEval : right.eval ctx env with
      | error message =>
        simp [Expr.eval, leftEval, rightEval, modulus, Field.modulus,
          bind, Bind.bind, Except.bind] at evaluated
      | ok rightValue =>
        simp [Expr.eval, leftEval, rightEval, modulus, Field.modulus,
          bind, Bind.bind, Except.bind] at evaluated
        change (Except.ok ((leftValue * rightValue) % Field.modulus) : Except String Nat) =
          .ok value at evaluated
        have resultEq : (leftValue * rightValue) % Field.modulus = value :=
          Except.ok.inj evaluated
        subst value
        exact canonical_native_of_bound _ (Nat.mod_lt _ (by decide))
  | sub left right leftSupported rightSupported ihLeft ihRight =>
    cases leftEval : left.eval ctx env with
    | error message =>
      simp [Expr.eval, leftEval, modulus, Field.modulus,
        bind, Bind.bind, Except.bind] at evaluated
    | ok leftValue =>
      cases rightEval : right.eval ctx env with
      | error message =>
        simp [Expr.eval, leftEval, rightEval, modulus, Field.modulus,
          bind, Bind.bind, Except.bind] at evaluated
      | ok rightValue =>
        simp [Expr.eval, leftEval, rightEval, modulus, Field.modulus,
          bind, Bind.bind, Except.bind] at evaluated
        change (Except.ok ((Field.modulus + leftValue - rightValue) % Field.modulus) :
          Except String Nat) = .ok value at evaluated
        have resultEq : (Field.modulus + leftValue - rightValue) % Field.modulus = value :=
          Except.ok.inj evaluated
        subst value
        exact canonical_native_of_bound _ (Nat.mod_lt _ (by decide))
  | @uadd leftMaximum rightMaximum left right leftSupported rightSupported ihLeft ihRight =>
    cases leftEval : left.eval ctx env with
    | error message =>
      simp [Expr.eval, leftEval, bind, Bind.bind, Except.bind] at evaluated
    | ok leftValue =>
      cases rightEval : right.eval ctx env with
      | error message =>
        simp [Expr.eval, leftEval, rightEval, bind, Bind.bind, Except.bind] at evaluated
      | ok rightValue =>
        simp only [Expr.eval, leftEval, rightEval, bind, Bind.bind, Except.bind] at evaluated
        change scalarCast ctx _ (.uint (leftMaximum + rightMaximum))
          (leftValue + rightValue) = .ok value at evaluated
        exact scalarCast_canonical ctx (.uint (leftMaximum + rightMaximum))
          (leftValue + rightValue) value modulus evaluated
  | @usub leftMaximum rightMaximum left right leftSupported rightSupported ihLeft ihRight =>
    cases leftEval : left.eval ctx env with
    | error message =>
      simp [Expr.eval, leftEval, bind, Bind.bind, Except.bind] at evaluated
    | ok leftValue =>
      cases rightEval : right.eval ctx env with
      | error message =>
        simp [Expr.eval, leftEval, rightEval, bind, Bind.bind, Except.bind] at evaluated
      | ok rightValue =>
        have noUnderflow : ¬ leftValue < rightValue := by
          by_cases underflow : leftValue < rightValue
          · simp [Expr.eval, leftEval, rightEval, underflow, bind, Bind.bind,
              Except.bind] at evaluated
          · exact underflow
        simp only [Expr.eval, leftEval, rightEval, noUnderflow, bind, Bind.bind,
          Except.bind] at evaluated
        change scalarCast ctx _ (.uint leftMaximum) (leftValue - rightValue) =
          .ok value at evaluated
        exact scalarCast_canonical ctx (.uint leftMaximum)
          (leftValue - rightValue) value modulus evaluated
  | @umul leftMaximum rightMaximum left right leftSupported rightSupported ihLeft ihRight =>
    cases leftEval : left.eval ctx env with
    | error message =>
      simp [Expr.eval, leftEval, bind, Bind.bind, Except.bind] at evaluated
    | ok leftValue =>
      cases rightEval : right.eval ctx env with
      | error message =>
        simp [Expr.eval, leftEval, rightEval, bind, Bind.bind, Except.bind] at evaluated
      | ok rightValue =>
        simp only [Expr.eval, leftEval, rightEval, bind, Bind.bind, Except.bind] at evaluated
        change scalarCast ctx _ (.uint (leftMaximum * rightMaximum))
          (leftValue * rightValue) = .ok value at evaluated
        exact scalarCast_canonical ctx (.uint (leftMaximum * rightMaximum))
          (leftValue * rightValue) value modulus evaluated
  | @cast sourceTy target source sourceType targetType sourceSupported ihSource =>
    cases sourceEval : source.eval ctx env with
    | error message =>
      have sourceKinds := scalarType_supported sourceType
      have targetKinds := scalarType_supported targetType
      simp [Expr.eval, sourceEval, sourceKinds.1, sourceKinds.2.1,
        sourceKinds.2.2, targetKinds.1, targetKinds.2.1, targetKinds.2.2,
        bind, Bind.bind, Except.bind] at evaluated
    | ok sourceValue =>
      have castEvaluation := ScalarNormalization.eval_cast_scalar ctx env source
        sourceType targetType sourceValue sourceEval
      rw [castEvaluation] at evaluated
      exact scalarCast_canonical ctx targetType
        (ScalarNormalization.number sourceType sourceValue) value modulus evaluated
  | @letE sourceTy resultTy name bound body sourceScalar boundSupported bodySupported
      ihBound ihBody =>
    cases boundEval : bound.eval ctx env with
    | error message =>
      simp [Expr.eval, boundEval, bind, Bind.bind, Except.bind] at evaluated
    | ok boundValue =>
      simp only [Expr.eval, boundEval, bind, Bind.bind, Except.bind] at evaluated
      exact ihBody ((name, Value.pack sourceTy boundValue) :: env) value evaluated
  | @assertE resultTy condition body conditionSupported bodySupported
      ihCondition ihBody =>
    cases conditionEval : condition.eval ctx env with
    | error message =>
      simp [Expr.eval, conditionEval, bind, Bind.bind, Except.bind] at evaluated
    | ok conditionValue =>
      cases conditionValue with
      | false =>
        simp [Expr.eval, conditionEval, bind, Bind.bind, Except.bind] at evaluated
      | true =>
        simp only [Expr.eval, conditionEval, bind, Bind.bind, Except.bind] at evaluated
        exact ihBody env value evaluated
  | copyValue source sourceSupported ihSource =>
    have sourceEval : source.eval ctx env = .ok value := by
      simpa [Expr.eval] using evaluated
    exact ihSource env value sourceEval
  | disclose span source sourceSupported ihSource =>
    apply ihSource env value
    simpa [Expr.eval] using evaluated
  | eq left right scalarType leftSupported rightSupported ihLeft ihRight =>
    cases value <;> simp [Canonical, ScalarNormalization.number, Field.modulus]
  | select condition yes no scalarType conditionSupported yesSupported noSupported
      ihCondition ihYes ihNo =>
    cases conditionEval : condition.eval ctx env with
    | error message =>
      simp [Expr.eval, conditionEval, bind, Bind.bind, Except.bind] at evaluated
    | ok conditionValue =>
      cases yesEval : yes.eval ctx env with
      | error message =>
        simp [Expr.eval, conditionEval, yesEval, bind, Bind.bind, Except.bind] at evaluated
      | ok yesValue =>
        cases noEval : no.eval ctx env with
        | error message =>
          simp [Expr.eval, conditionEval, yesEval, noEval, bind, Bind.bind,
            Except.bind] at evaluated
        | ok noValue =>
          simp [Expr.eval, conditionEval, yesEval, noEval, bind, Bind.bind,
            Except.bind] at evaluated
          change Except.ok (if conditionValue = true then yesValue else noValue) =
            Except.ok value at evaluated
          have selectedEq : (if conditionValue = true then yesValue else noValue) = value :=
            Except.ok.inj evaluated
          cases conditionValue with
          | false =>
            rw [← selectedEq]
            exact ihNo env noValue noEval
          | true =>
            rw [← selectedEq]
            exact ihYes env yesValue yesEval
  | poseidon2 domain left right leftSupported rightSupported ihLeft ihRight =>
    have domainNotGe : ¬ ctx.modulus ≤ domain := by
      by_cases invalid : ctx.modulus ≤ domain
      · simp [Expr.eval, invalid, bind, Bind.bind, Except.bind] at evaluated
      · exact invalid
    cases leftEval : left.eval ctx env with
    | error message =>
      simp [Expr.eval, domainNotGe, leftEval, bind, Bind.bind, Except.bind] at evaluated
    | ok leftValue =>
      cases rightEval : right.eval ctx env with
      | error message =>
        simp [Expr.eval, domainNotGe, leftEval, rightEval, bind, Bind.bind,
          Except.bind] at evaluated
      | ok rightValue =>
        cases oracleEval : ctx.poseidon2 domain leftValue rightValue with
        | error message =>
          simp [Expr.eval, domainNotGe, leftEval, rightEval, oracleEval, bind,
            Bind.bind, Except.bind] at evaluated
        | ok result =>
          have resultBound : result < ctx.modulus := by
            by_cases bound : result < ctx.modulus
            · exact bound
            · have invalid : ctx.modulus ≤ result := by omega
              simp [Expr.eval, domainNotGe, leftEval, rightEval,
                oracleEval, invalid, bind, Bind.bind, Except.bind] at evaluated
          have resultNotGe : ¬ ctx.modulus ≤ result := Nat.not_le_of_gt resultBound
          simp [Expr.eval, domainNotGe, leftEval, rightEval,
            oracleEval, resultNotGe, bind, Bind.bind, Except.bind] at evaluated
          change (Except.ok result : Except String Nat) = .ok value at evaluated
          have resultEq : result = value := Except.ok.inj evaluated
          subst value
          exact canonical_native_of_bound result (by simpa [modulus] using resultBound)

end Noctium.Verification.GenericStateEvaluationCanonical
