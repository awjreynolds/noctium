import Noctium.Verification.GenericStateWriteEvaluation
import Noctium.Verification.GuardedScalarTotalization

namespace Noctium.Verification.GuardedWriteLowering
open Backend ScalarNormalization

/-- On an active guard, a guarded Cell write's emitted value evaluates like
the source value, and its actual appended operations match an unguarded append
of that emitted expression. -/
theorem active_writeCell_chunk (ctx : EvalContext) (env : EvalEnv)
    (state : List StateDecl) (name : String) (ty : Ty) (value : Expr ty)
    (admitted : ScalarExpression value) (guard : Expr .bool)
    (before after : Impact.Plan)
    (active : guard.eval ctx env = .ok true)
    (modulus : ctx.modulus = Field.modulus)
    (compiled : Impact.appendEffectWithActivity state (.writeCell name ty value)
      (some guard) before = .ok after) :
    ∃ emittedValue : Expr ty,
      emittedValue.eval ctx env = value.eval ctx env ∧ ∃ raw,
        Impact.appendEffect state (.writeCell name ty emittedValue) before = .ok raw ∧
        after.operations = raw.operations := by
  obtain ⟨binder, fresh, raw, appended, sameOperations⟩ :=
    Impact.appendEffectWithActivity_writeCell_value state name ty value guard
      before after compiled
  exact ⟨_, GuardedScalarTotalization.eval_active_value ctx env value admitted
      guard binder fresh active modulus, raw, appended, sameOperations⟩

/-- On an active guard, a guarded Map write's emitted key and value each
evaluate like their source expressions. The guarded operation suffix matches
the raw append using those emitted expressions. -/
theorem active_writeMap_chunk (ctx : EvalContext) (env : EvalEnv)
    (state : List StateDecl) (name : String) (keyTy valueTy : Ty)
    (key : Expr keyTy) (value : Expr valueTy)
    (keyAdmitted : ScalarExpression key) (valueAdmitted : ScalarExpression value)
    (guard : Expr .bool) (before after : Impact.Plan)
    (active : guard.eval ctx env = .ok true)
    (modulus : ctx.modulus = Field.modulus)
    (compiled : Impact.appendEffectWithActivity state
      (.writeMap name keyTy valueTy key value) (some guard) before = .ok after) :
    ∃ emittedKey : Expr keyTy, ∃ emittedValue : Expr valueTy,
      emittedKey.eval ctx env = key.eval ctx env ∧
      emittedValue.eval ctx env = value.eval ctx env ∧ ∃ raw,
        Impact.appendEffect state
          (.writeMap name keyTy valueTy emittedKey emittedValue) before = .ok raw ∧
        after.operations = raw.operations := by
  obtain ⟨keyType⟩ := GenericStateEvaluationCanonical.scalarExpression_type keyAdmitted
  have keyNonForeign : ∀ kind, keyTy ≠ .foreign kind := by
    cases keyType <;> simp
  obtain ⟨keyBinder, keyFresh, valueBinder, valueFresh, raw, appended,
      sameOperations⟩ := Impact.appendEffectWithActivity_writeMap_key_value state
    name keyTy valueTy key value guard before after keyNonForeign compiled
  exact ⟨_, _,
    GuardedScalarTotalization.eval_active_value ctx env key keyAdmitted guard
      keyBinder keyFresh active modulus,
    GuardedScalarTotalization.eval_active_value ctx env value valueAdmitted guard
      valueBinder valueFresh active modulus,
    raw, appended, sameOperations⟩

end Noctium.Verification.GuardedWriteLowering
