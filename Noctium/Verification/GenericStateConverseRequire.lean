import Noctium.Verification.GenericStateConverseWrite

namespace Noctium.Verification.GenericStateConverseRequire
open Backend NativeState

/-- Successful original require execution forces its validated Boolean guard
to hold. -/
theorem source_require_true (ctx : EvalContext) (env : EvalEnv)
    (state : LedgerState) (condition : Expr .bool)
    (after : SourceEffects.Frame)
    (success : SourceEffects.step ctx (.require condition) (env, state) =
      .ok after) :
    condition.eval ctx env = .ok true ∧ after = (env, state) := by
  cases evaluated : condition.eval ctx env with
  | error message =>
    simp [SourceEffects.step, runEffectWithEnv, evaluated, Bind.bind, Except.bind] at success
  | ok value =>
    cases value with
    | false =>
      simp [SourceEffects.step, runEffectWithEnv, evaluated, Bind.bind, Except.bind,
        throw, throwThe] at success
    | true =>
      have exactStep : SourceEffects.step ctx (.require condition)
          (env, state) = .ok (env, state) := by
        simp [SourceEffects.step, runEffectWithEnv, evaluated, Bind.bind, Except.bind,
          Pure.pure, Except.pure]
      rw [exactStep] at success
      exact ⟨rfl, (Except.ok.inj success).symm⟩

/-- Source guard success and scope agreement make the actual production
require segment empty and keep the native machine unchanged. -/
theorem source_require_native (ctx : EvalContext)
    (sourceEnv candidateEnv : EvalEnv) (state : List StateDecl)
    (current : LedgerState) (slots : List NativeState.Slot)
    (condition : Expr .bool) (sourceAfter : SourceEffects.Frame)
    (base : Impact.Plan) (reads : List NativeState.Cell)
    (sourceStep : SourceEffects.step ctx (.require condition)
      (sourceEnv, current) = .ok sourceAfter)
    (candidateAgreement : condition.eval ctx candidateEnv =
      condition.eval ctx sourceEnv)
    (compiled : Impact.appendEffect state (.require condition) {} = .ok base) :
    condition.eval ctx candidateEnv = .ok true ∧
    base.operations.mapM (GenericStateOps.evalOp ctx candidateEnv) = .ok [] ∧
    NativeState.run [] ⟨[.vector slots], reads⟩ =
      some ⟨[.vector slots], reads⟩ ∧
    sourceAfter = (sourceEnv, current) := by
  obtain ⟨sourceTrue, sourceShape⟩ :=
    source_require_true ctx sourceEnv current condition sourceAfter sourceStep
  have candidateTrue : condition.eval ctx candidateEnv = .ok true := by
    rw [candidateAgreement]
    exact sourceTrue
  have empty : base.operations = [] := by
    simp [Impact.appendEffect] at compiled
    cases compiled
    rfl
  refine ⟨candidateTrue, ?_, rfl, sourceShape⟩
  rw [empty]
  rfl

end Noctium.Verification.GenericStateConverseRequire
