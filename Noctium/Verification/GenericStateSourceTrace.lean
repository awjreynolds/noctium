import Noctium.Verification.SourceEffects
import Noctium.Verification.GenericStateEncoding
import Noctium.Verification.GenericStateEvaluationCanonical

namespace Noctium.Verification.GenericStateSourceTrace

open ScalarNormalization

theorem canonicalValue_sound {ty : Ty} (scalarType : ScalarType ty)
    (ctx : EvalContext) (value : ty.Denote) (modulus : ctx.modulus = Field.modulus)
    (checked : SourceEffects.canonicalValue ctx ty value = true) :
    Canonical ty value := by
  cases scalarType with
  | native =>
    exact ⟨by simpa [SourceEffects.canonicalValue, modulus, number] using checked,
      trivial⟩
  | bool =>
    cases value <;> simp [Canonical, Field.modulus]
  | uint maximum =>
    simp only [SourceEffects.canonicalValue, Bool.and_eq_true,
      decide_eq_true_eq] at checked
    rcases checked with ⟨⟨maximumBound, valueBound⟩, fieldBound⟩
    exact ⟨by simpa [modulus, number] using fieldBound,
      maximumBound, valueBound⟩

/-- Recover the unique packed value for a scalar type from a successful `as`. -/
theorem typed_value_eq_pack {ty : Ty} (scalarType : ScalarType ty)
    (raw : Value) (value : ty.Denote) (typed : raw.as ty = some value) :
    raw = Value.pack ty value := by
  cases scalarType with
  | native => cases raw <;> simp_all [Value.as, Value.pack]
  | bool => cases raw <;> simp_all [Value.as, Value.pack]
  | uint maximum => cases raw <;> simp_all [Value.as, Value.pack]

/-- A successful scalar cell read exposes its typed value and exact source frame. -/
private theorem readCell_step_shape {ty : Ty} (scalarType : ScalarType ty)
    (ctx : EvalContext) (env : EvalEnv) (state : LedgerState)
    (name destination : String) (after : SourceEffects.Frame)
    (success : SourceEffects.step ctx (.readCell name destination ty)
      (env, state) = .ok after) :
    ∃ (raw : Value) (value : ty.Denote),
      state.cells.lookup name = some raw ∧
      raw.as ty = some value ∧
      SourceEffects.canonicalValue ctx ty value = true ∧
      after = ((destination, Value.pack ty value) :: env, state) := by
  cases found : state.cells.lookup name with
  | none =>
    simp [SourceEffects.step, runEffectWithEnv, found, bind, Except.bind,
      throw, pure, Except.pure] at success
  | some raw =>
    cases typed : raw.as ty with
    | none =>
      simp [SourceEffects.step, runEffectWithEnv, found, typed, bind,
        Except.bind, throw, pure, Except.pure] at success
    | some value =>
      have checkedStep : SourceEffects.step ctx (.readCell name destination ty) (env, state) =
          if !SourceEffects.canonicalValue ctx ty value then
            .error s!"noncanonical state cell '{name}'"
          else .ok ((destination, Value.pack ty value) :: env, state) := by
        cases scalarType <;>
          simp [SourceEffects.step, runEffectWithEnv, found, typed, canonical_eq,
            SourceEffects.canonicalValue, bind, Except.bind, throw, throwThe,
            pure, Except.pure] <;> rfl
      rw [checkedStep] at success
      cases canonical : SourceEffects.canonicalValue ctx ty value with
      | false => simp [canonical] at success
      | true =>
        simp only [canonical, Bool.not_true, Bool.false_eq_true, ite_false] at success
        exact ⟨raw, value, rfl, typed, canonical, (Except.ok.inj success).symm⟩

/-- Scalar cell reads add the canonicality needed for a native relation input. -/
theorem readCell_step_value {ty : Ty} (scalarType : ScalarType ty)
    (ctx : EvalContext) (env : EvalEnv) (state : LedgerState)
    (name destination : String) (after : SourceEffects.Frame)
    (modulus : ctx.modulus = Field.modulus)
    (success : SourceEffects.step ctx (.readCell name destination ty)
      (env, state) = .ok after) :
    ∃ value : ty.Denote,
      state.cells.lookup name = some (Value.pack ty value) ∧
      Canonical ty value ∧
      after = ((destination, Value.pack ty value) :: env, state) := by
  obtain ⟨raw, value, lookup, typed, checked, frame⟩ :=
    readCell_step_shape scalarType ctx env state name destination after success
  have packed := typed_value_eq_pack scalarType raw value typed
  have canonical := canonicalValue_sound scalarType ctx value modulus checked
  refine ⟨value, ?_, canonical, frame⟩
  rw [packed] at lookup
  exact lookup

/-- Carry the checked initial ledger's schema to an actual later scalar read,
including a read after tentative writes in the same entrypoint. -/
theorem readCell_step_value_of_admitted (ctx : EvalContext) (env : EvalEnv)
    (declarations : List StateDecl) (initial current : LedgerState) (slots : List NativeState.Slot)
    (admitted : GenericStateEncoding.AdmittedState declarations initial slots)
    (name destination : String) (ty : Ty) (declaration : StateDecl)
    (found : declarations.find? (·.name == name) = some declaration)
    (kind : declaration.kind = .cell ty) (after : SourceEffects.Frame)
    (modulus : ctx.modulus = Field.modulus)
    (success : SourceEffects.step ctx (.readCell name destination ty)
      (env, current) = .ok after) :
    ∃ value : ty.Denote,
      current.cells.lookup name = some (Value.pack ty value) ∧
      Canonical ty value ∧
      after = ((destination, Value.pack ty value) :: env, current) := by
  have supported := (admitted.cellType name declaration ty found kind).2
  cases support : GenericStateEncoding.scalarType? ty with
  | none =>
    rw [support] at supported
    cases supported
  | some scalarType =>
    exact readCell_step_value scalarType ctx env current name destination after modulus success

/-- An accepted source absence effect yields the key evaluation and the
current map's missing-key fact used to build its false native read. -/
theorem requireAbsent_step_key (ctx : EvalContext) (env : EvalEnv)
    (state : LedgerState) (name : String) (keyTy : Ty)
    (keyExpr : Expr keyTy) (admission : ScalarExpression keyExpr)
    (after : SourceEffects.Frame)
    (modulus : ctx.modulus = Field.modulus)
    (success : SourceEffects.step ctx (.requireAbsent name keyTy keyExpr)
      (env, state) = .ok after) :
    ∃ key : keyTy.Denote, ∃ entries,
      keyExpr.eval ctx env = .ok key ∧
      Canonical keyTy key ∧
      state.maps.lookup name = some entries ∧
      entries.lookup (Value.pack keyTy key) = none ∧
      after = (env, state) := by
  cases keyEval : keyExpr.eval ctx env with
  | error message =>
    simp [SourceEffects.step, runEffectWithEnv, keyEval, bind, Except.bind] at success
  | ok key =>
    cases mapLookup : state.maps.lookup name with
    | none =>
      simp [SourceEffects.step, runEffectWithEnv, keyEval, mapLookup, bind,
        Except.bind, throw, throwThe] at success
    | some entries =>
      cases found : entries.lookup (Value.pack keyTy key) with
      | some raw =>
        simp [SourceEffects.step, runEffectWithEnv, keyEval, mapLookup, found,
          bind, Except.bind, throw, throwThe] at success
      | none =>
        have stepShape : SourceEffects.step ctx (.requireAbsent name keyTy keyExpr)
            (env, state) = .ok (env, state) := by
          simp [SourceEffects.step, runEffectWithEnv, keyEval, mapLookup, found,
            bind, Except.bind, pure, Except.pure]
        rw [stepShape] at success
        cases success
        exact ⟨key, entries, rfl,
          GenericStateEvaluationCanonical.expression_eval_canonical ctx env
            keyExpr admission key modulus keyEval,
          rfl, found, rfl⟩

/-- The successful original source evaluator exposes an ordered frame after
each effect. This trace is derived from SourceEffects.step, including reads
and tentative ledger updates, with no independent transition semantics. -/
inductive SourceTrace (ctx : EvalContext) :
    List Effect → SourceEffects.Frame → SourceEffects.Frame → Prop where
  | nil (frame : SourceEffects.Frame) : SourceTrace ctx [] frame frame
  | cons (effect : Effect) (rest : List Effect)
      (before middle after : SourceEffects.Frame)
      (first : SourceEffects.step ctx effect before = .ok middle)
      (later : SourceTrace ctx rest middle after) :
      SourceTrace ctx (effect :: rest) before after

theorem fold_ok_iff_trace (ctx : EvalContext) (effects : List Effect)
    (before after : SourceEffects.Frame) :
    SourceEffects.fold ctx effects before = .ok after ↔
      SourceTrace ctx effects before after := by
  induction effects generalizing before with
  | nil =>
    constructor
    · intro success
      simp only [SourceEffects.fold_nil] at success
      cases success
      exact .nil _
    · intro trace
      cases trace
      rfl
  | cons effect rest ih =>
    rw [SourceEffects.fold_cons]
    constructor
    · intro success
      cases first : SourceEffects.step ctx effect before with
      | error message => simp [first, Except.bind] at success
      | ok middle =>
        simp only [first, Except.bind] at success
        exact SourceTrace.cons effect rest before middle after first
          ((ih middle).mp success)
    · intro trace
      cases trace with
      | cons =>
        rename_i middle first later
        rw [first]
        exact (ih middle).mpr later

/-- Source evaluator success gives a first source step and a successful tail
at the exact intermediate frame. -/
theorem source_cons (ctx : EvalContext) (effect : Effect)
    (rest : List Effect) (before after : SourceEffects.Frame)
    (success : SourceEffects.fold ctx (effect :: rest) before = .ok after) :
    ∃ middle,
      SourceEffects.step ctx effect before = .ok middle ∧
      SourceEffects.fold ctx rest middle = .ok after := by
  rw [SourceEffects.fold_cons] at success
  cases first : SourceEffects.step ctx effect before with
  | error message => simp [first, Except.bind] at success
  | ok middle =>
    simp only [first, Except.bind] at success
    exact ⟨middle, rfl, success⟩

end Noctium.Verification.GenericStateSourceTrace
