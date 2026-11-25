import Noctium.Verification.GenericStateSourceTrace

namespace Noctium.Verification.GenericStateWriteSourceTrace
open ScalarNormalization

private theorem scalarType_of_canonical {ty : Ty} {value : ty.Denote}
    (canonical : Canonical ty value) : Nonempty (ScalarType ty) := by
  cases ty with
  | native => exact ⟨.native⟩
  | bool => exact ⟨.bool⟩
  | uint maximum => exact ⟨.uint maximum⟩
  | _ => simp [Canonical, sourceNumber?] at canonical

/-- Original source cell-write success exposes both the prior typed cell and
the canonical evaluated value used in the exact source update. -/
theorem writeCell_step_value (ctx : EvalContext) (env : EvalEnv)
    (state : LedgerState) (name : String) (ty : Ty) (expression : Expr ty)
    (after : SourceEffects.Frame) (admission : ScalarExpression expression)
    (modulus : ctx.modulus = Field.modulus)
    (success : SourceEffects.step ctx (.writeCell name ty expression)
      (env, state) = .ok after) :
    ∃ oldValue value : ty.Denote,
      state.cells.lookup name = some (Value.pack ty oldValue) ∧
      expression.eval ctx env = .ok value ∧ Canonical ty value ∧
      after = (env, {state with cells := SourceEffects.updateEntry name (Value.pack ty value) state.cells}) := by
  cases found : state.cells.lookup name with
  | none =>
    simp [SourceEffects.step, runEffectWithEnv, found, throw, throwThe,
      Bind.bind, Except.bind, Pure.pure, Except.pure] at success
  | some raw =>
    cases typed : raw.as ty with
    | none =>
      simp [SourceEffects.step, runEffectWithEnv, found, typed, throw, throwThe,
        Bind.bind, Except.bind, Pure.pure, Except.pure] at success
    | some oldValue =>
      cases evaluated : expression.eval ctx env with
      | error message =>
        simp [SourceEffects.step, runEffectWithEnv, found, typed, evaluated,
          Bind.bind, Except.bind] at success
      | ok value =>
        have canonical := GenericStateEvaluationCanonical.expression_eval_canonical
          ctx env expression admission value modulus evaluated
        obtain ⟨scalarType⟩ := scalarType_of_canonical canonical
        have rawTyped := GenericStateSourceTrace.typed_value_eq_pack
          scalarType raw oldValue typed
        subst raw
        have exactStep : SourceEffects.step ctx (.writeCell name ty expression)
            (env, state) = .ok (env, {state with cells := SourceEffects.updateEntry name (Value.pack ty value) state.cells}) := by
          simp [SourceEffects.step, runEffectWithEnv, found, typed, evaluated,
            SourceEffects.updateEntry, updateAssoc, Bind.bind, Except.bind,
            Pure.pure, Except.pure]
        rw [exactStep] at success
        exact ⟨oldValue, value, rfl, rfl,
          canonical,
          (Except.ok.inj success).symm⟩

/-- Original source map-write success exposes its canonical key/value and
exact tentative map replacement. Existing-entry validation stays on the
original evaluator path rather than becoming a new assumed condition. -/
theorem writeMap_step_values (ctx : EvalContext) (env : EvalEnv)
    (state : LedgerState) (name : String) (keyTy valueTy : Ty)
    (keyExpr : Expr keyTy) (valueExpr : Expr valueTy)
    (after : SourceEffects.Frame) (keyAdmission : ScalarExpression keyExpr)
    (valueAdmission : ScalarExpression valueExpr)
    (modulus : ctx.modulus = Field.modulus)
    (success : SourceEffects.step ctx (.writeMap name keyTy valueTy keyExpr valueExpr)
      (env, state) = .ok after) :
    ∃ key : keyTy.Denote, ∃ value : valueTy.Denote, ∃ entries,
      keyExpr.eval ctx env = .ok key ∧ valueExpr.eval ctx env = .ok value ∧
      Canonical keyTy key ∧ Canonical valueTy value ∧
      state.maps.lookup name = some entries ∧
      after = (env, {state with maps := SourceEffects.updateEntry name (SourceEffects.updateEntry (Value.pack keyTy key) (Value.pack valueTy value) entries) state.maps}) := by
  cases keyEval : keyExpr.eval ctx env with
  | error message =>
    simp [SourceEffects.step, runEffectWithEnv, keyEval, Bind.bind, Except.bind] at success
  | ok key =>
    cases valueEval : valueExpr.eval ctx env with
    | error message =>
      simp [SourceEffects.step, runEffectWithEnv, keyEval, valueEval,
        Bind.bind, Except.bind] at success
    | ok value =>
      cases found : state.maps.lookup name with
      | none =>
        simp [SourceEffects.step, runEffectWithEnv, keyEval, valueEval, found,
          throw, throwThe, Bind.bind, Except.bind, Pure.pure, Except.pure] at success
      | some entries =>
        simp only [SourceEffects.step, runEffectWithEnv, keyEval, valueEval, found,
          bind, Except.bind] at success
        split at success
        · cases success
        ·
          change Except.ok _ = .ok after at success
          exact ⟨key, value, entries, rfl, rfl,
            GenericStateEvaluationCanonical.expression_eval_canonical ctx env keyExpr
              keyAdmission key modulus keyEval,
            GenericStateEvaluationCanonical.expression_eval_canonical ctx env valueExpr
              valueAdmission value modulus valueEval,
            rfl, (Except.ok.inj success).symm⟩

end Noctium.Verification.GenericStateWriteSourceTrace
