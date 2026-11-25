import Noctium.Verification.SourceEffects

namespace Noctium.Verification.GuardedWriteSourceStep

private theorem throw_error {α : Type} (message : String) :
    (throw message : Except String α) = .error message := rfl

/-- An active guarded Cell write follows the ordinary production source step,
including the same evaluation and state errors. -/
theorem run_active_writeCell (ctx : EvalContext) (env : EvalEnv)
    (state : LedgerState) (name : String) {ty : Ty} (value : Expr ty)
    (guard : Expr .bool) (active : guard.eval ctx env = .ok true) :
    runEffectsWithGuardsAndEnv ctx [.writeCell name ty value] [some guard] env state =
      SourceEffects.step ctx (.writeCell name ty value) (env, state) := by
  dsimp [runEffectsWithGuardsAndEnv, List.zipIdx, List.all,
    List.isEmpty, List.length, Option.isNone, Option.getD, Option.isSome,
    Bind.bind, Except.bind, Pure.pure, Except.pure]
  rw [List.forIn_cons]
  dsimp [List.getElem?_cons_zero, Option.getD, Option.isSome,
    Bind.bind, Except.bind, Pure.pure, Except.pure]
  rw [active, SourceEffects.step]
  dsimp [runEffectWithEnv, Bind.bind, Except.bind, Pure.pure, Except.pure]
  cases state.cells.lookup name with
  | none => rfl
  | some existing =>
    cases typeResult : existing.as ty with
    | none => simp [typeResult, Option.isNone, throw_error]
    | some oldValue =>
      cases value.eval ctx env <;> simp [typeResult, Option.isNone]

/-- An inactive guarded Cell write leaves the source frame untouched. The
write value is not evaluated, and the target cell need not exist. -/
theorem run_inactive_writeCell (ctx : EvalContext) (env : EvalEnv)
    (state : LedgerState) (name : String) {ty : Ty} (value : Expr ty)
    (guard : Expr .bool) (inactive : guard.eval ctx env = .ok false) :
    runEffectsWithGuardsAndEnv ctx [.writeCell name ty value] [some guard] env state =
      .ok (env, state) := by
  dsimp [runEffectsWithGuardsAndEnv, List.zipIdx, List.all,
    List.isEmpty, List.length, Option.isNone, Option.getD, Option.isSome,
    Bind.bind, Except.bind, Pure.pure, Except.pure]
  rw [List.forIn_cons]
  dsimp [List.getElem?_cons_zero, Option.getD, Option.isSome,
    Bind.bind, Except.bind, Pure.pure, Except.pure]
  rw [inactive]
  rfl

/-- An active guarded Map write follows the ordinary production source step,
including failures while evaluating either operand or accessing the map. -/
theorem run_active_writeMap (ctx : EvalContext) (env : EvalEnv)
    (state : LedgerState) (name : String) {keyTy valueTy : Ty}
    (key : Expr keyTy) (value : Expr valueTy) (guard : Expr .bool)
    (active : guard.eval ctx env = .ok true) :
    runEffectsWithGuardsAndEnv ctx
        [.writeMap name keyTy valueTy key value] [some guard] env state =
      SourceEffects.step ctx (.writeMap name keyTy valueTy key value) (env, state) := by
  dsimp [runEffectsWithGuardsAndEnv, List.zipIdx, List.all,
    List.isEmpty, List.length, Option.isNone, Option.getD, Option.isSome,
    Bind.bind, Except.bind, Pure.pure, Except.pure]
  rw [List.forIn_cons]
  dsimp [List.getElem?_cons_zero, Option.getD, Option.isSome,
    Bind.bind, Except.bind, Pure.pure, Except.pure]
  rw [active, SourceEffects.step]
  dsimp [runEffectWithEnv, Bind.bind, Except.bind, Pure.pure, Except.pure]
  cases keyResult : key.eval ctx env with
  | error message => rfl
  | ok keyValue =>
    cases valueResult : value.eval ctx env with
    | error message => rfl
    | ok valueValue =>
      cases mapResult : state.maps.lookup name with
      | none => rfl
      | some entries =>
        simp only [Option.isNone, Bool.or_eq_true, throw_error]
        cases validationEq : (forIn entries PUnit.unit fun (item : Value × Value) (_ : PUnit.{1}) =>
          if (item.1.as keyTy).isNone || (item.2.as valueTy).isNone then
            (Except.error s!"state map type mismatch '{name}'" : Except String (ForInStep PUnit.{1}))
          else Except.ok (ForInStep.yield PUnit.unit)) <;>
            simp only [Option.isNone, Bool.or_eq_true] at validationEq <;>
            rw [validationEq] <;> rfl

/-- An inactive guarded Map write leaves the source frame untouched. Neither
the key nor the value is evaluated, and the target map need not exist. -/
theorem run_inactive_writeMap (ctx : EvalContext) (env : EvalEnv)
    (state : LedgerState) (name : String) {keyTy valueTy : Ty}
    (key : Expr keyTy) (value : Expr valueTy) (guard : Expr .bool)
    (inactive : guard.eval ctx env = .ok false) :
    runEffectsWithGuardsAndEnv ctx
        [.writeMap name keyTy valueTy key value] [some guard] env state =
      .ok (env, state) := by
  dsimp [runEffectsWithGuardsAndEnv, List.zipIdx, List.all,
    List.isEmpty, List.length, Option.isNone, Option.getD, Option.isSome,
    Bind.bind, Except.bind, Pure.pure, Except.pure]
  rw [List.forIn_cons]
  dsimp [List.getElem?_cons_zero, Option.getD, Option.isSome,
    Bind.bind, Except.bind, Pure.pure, Except.pure]
  rw [inactive]
  rfl

end Noctium.Verification.GuardedWriteSourceStep
