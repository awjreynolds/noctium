import Noctium.Verification.SourceEffects
import Noctium.Verification.GenericStateCheckedReadTrace

namespace Noctium.Verification.GuardedSourceEffects

open Backend
open Noctium.Verification.GenericStateCheckedReadTrace
open Noctium.Verification.SourceEffects

abbrev Frame := SourceEffects.Frame

/-- One indexed guarded effect, evaluated by the production source runner. -/
def step (ctx : EvalContext) (guard : Option (Expr .bool)) (effect : Effect)
    (frame : Frame) : Except String Frame :=
  runEffectsWithGuardsAndEnv ctx [effect] [guard] frame.1 frame.2

/-- Evaluate indexed effects in order, selecting guards with the same
out-of-range-to-none rule as the entrypoint source runner. -/
def fold (ctx : EvalContext) (guards : List (Option (Expr .bool)))
    (items : List (Effect × Nat)) (frame : Frame) : Except String Frame :=
  items.foldlM (fun frame item =>
    step ctx (guards[item.2]?.getD none) item.1 frame) frame

@[simp] theorem fold_nil (ctx : EvalContext)
    (guards : List (Option (Expr .bool))) (frame : Frame) :
    fold ctx guards [] frame = .ok frame := rfl

theorem fold_cons (ctx : EvalContext) (guards : List (Option (Expr .bool)))
    (item : Effect × Nat) (items : List (Effect × Nat)) (frame : Frame) :
    fold ctx guards (item :: items) frame =
      (step ctx (guards[item.2]?.getD none) item.1 frame).bind
        (fold ctx guards items) := rfl

private theorem forIn_agree_on {α β ε : Type} (items : List α) (current : β)
    (left right : α → β → Except ε (ForInStep β))
    (same : ∀ item ∈ items, ∀ frame, left item frame = right item frame) :
    forIn items current left = forIn items current right := by
  induction items generalizing current with
  | nil => rfl
  | cons head tail ih =>
    simp only [List.forIn_cons, same head (by simp)]
    congr 1
    funext step
    cases step with
    | done frame => rfl
    | yield frame => exact ih frame (fun item member => same item (by simp [member]))

theorem step_unguarded (ctx : EvalContext) (effect : Effect) (frame : Frame) :
    step ctx none effect frame = SourceEffects.step ctx effect frame := by
  change runEffectsWithEnv ctx [effect] frame.1 frame.2 =
    runEffectWithEnv ctx effect frame.1 frame.2
  simp [runEffectsWithEnv]

theorem step_guard_error (ctx : EvalContext) (condition : Expr .bool) (effect : Effect)
    (frame : Frame) (message : String)
    (supported : GuardedScalarReadEffect (some condition) effect)
    (failed : condition.eval ctx frame.1 = .error message) :
    step ctx (some condition) effect frame = .error message := by
  dsimp [step, runEffectsWithGuardsAndEnv, List.zipIdx, List.all, List.isEmpty,
    List.length, Option.isNone, Option.getD, Option.isSome, Bind.bind, Except.bind,
    Pure.pure, Except.pure]
  rw [List.forIn_cons]
  dsimp [List.getElem?_cons_zero, Option.getD, Option.isSome, Bind.bind, Except.bind,
    Pure.pure, Except.pure]
  rw [failed]
  cases supported <;> rfl

private theorem all_none_guard_at (guards : List (Option (Expr .bool)))
    (allNone : guards.all Option.isNone = true) (index : Nat) :
    guards[index]?.getD none = none := by
  induction guards generalizing index with
  | nil => simp
  | cons guard rest ih =>
    simp only [List.all_cons, Bool.and_eq_true] at allNone
    cases index with
    | zero => cases guard <;> simp_all [Option.isNone]
    | succ index => simpa using ih allNone.2 index

private theorem fold_eq_sourceFold (ctx : EvalContext)
    (guards : List (Option (Expr .bool))) (items : List (Effect × Nat))
    (frame : Frame) (allNone : guards.all Option.isNone = true) :
    fold ctx guards items frame = SourceEffects.fold ctx (items.map Prod.fst) frame := by
  induction items generalizing frame with
  | nil => rfl
  | cons item rest ih =>
    have headGuard := all_none_guard_at guards allNone item.2
    rw [fold_cons, headGuard, step_unguarded]
    simp only [List.map_cons]
    rw [SourceEffects.fold_cons]
    have tailEq : fold ctx guards rest = SourceEffects.fold ctx (List.map Prod.fst rest) := by
      funext current
      exact ih current
    exact congrArg (fun tail => (SourceEffects.step ctx item.1 frame).bind tail) tailEq

set_option maxHeartbeats 1000000 in
theorem runEffectsWithGuardsAndEnv_eq_fold (ctx : EvalContext)
    (effects : List Effect) (guards : List (Option (Expr .bool)))
    (frame : Frame)
    (metadataValid : guards.isEmpty ∨ guards.length = effects.length)
    (scope : GuardedScalarReadEffects guards (effects.zipIdx)) :
    runEffectsWithGuardsAndEnv ctx effects guards frame.1 frame.2 =
      fold ctx guards (effects.zipIdx) frame := by
  rcases metadataValid with empty | lengths
  · have guardsNil : guards = [] := by
      cases guards with
      | nil => rfl
      | cons guard rest => simp at empty
    subst guards
    calc
      runEffectsWithGuardsAndEnv ctx effects [] frame.1 frame.2 =
          SourceEffects.fold ctx effects frame := by
        change runEffectsWithEnv ctx effects frame.1 frame.2 = _
        exact SourceEffects.runEffectsWithEnv_eq_fold ctx effects frame.1 frame.2
      _ = fold ctx [] (effects.zipIdx) frame := by
        rw [fold_eq_sourceFold ctx [] (effects.zipIdx) frame rfl]
        simp
  · have valid : (guards.isEmpty || guards.length == effects.length) = true := by
      simp [lengths]
    change (do
      unless guards.isEmpty || guards.length == effects.length do
        throw "effect guard metadata length mismatch"
      if guards.all Option.isNone then
        runEffectsWithEnv ctx effects frame.1 frame.2
      else
        (show Except String Frame from _)) =
      fold ctx guards (effects.zipIdx) frame
    rw [valid]
    cases allNone : guards.all Option.isNone with
    | true =>
      rw [ite_eq_left (by decide : true = true)]
      calc
        runEffectsWithEnv ctx effects frame.1 frame.2 = SourceEffects.fold ctx effects frame :=
          SourceEffects.runEffectsWithEnv_eq_fold ctx effects frame.1 frame.2
        _ = fold ctx guards (effects.zipIdx) frame := by
          rw [fold_eq_sourceFold ctx guards (effects.zipIdx) frame allNone]
          exact (congrArg (fun items => SourceEffects.fold ctx items frame)
            (List.zipIdx_map_fst 0 effects)).symm
    | false =>
      rw [ite_eq_right (by decide : ¬ (false = true))]
      change ((forIn (m := Except String) (effects.zipIdx) frame
        (_ : (Effect × Nat) → Frame → Except String (ForInStep Frame))) >>= fun
          (suffix : Frame) => (pure (suffix.1, suffix.2) : Except String Frame)) = _
      have project : (fun (suffix : Frame) =>
          (pure (suffix.1, suffix.2) : Except String Frame)) =
          (pure : Frame → Except String Frame) := by
        funext suffix
        cases suffix
        rfl
      rw [project, bind_pure]

      let desiredCallback : (Effect × Nat) → Frame →
          Except String (ForInStep Frame) := fun item current =>
        ForInStep.yield <$> step ctx (guards[item.2]?.getD none) item.1 current
      refine Eq.trans (b := forIn (effects.zipIdx) frame desiredCallback) ?_ ?_
      · apply forIn_agree_on
        intro item member current
        rcases item with ⟨effect, position⟩
        have admitted := scope (effect, position) member
        dsimp only [desiredCallback, Prod.fst, Prod.snd] at admitted ⊢
        generalize gateAt : guards[position]?.getD none = gate at admitted ⊢
        cases admitted with
        | unguarded scalar =>
          rw [step_unguarded]
          cases scalar with
          | readCell name destination ty =>
            dsimp [SourceEffects.step, runEffectWithEnv, Option.isSome,
              Bind.bind, Except.bind, Pure.pure, Except.pure, Except.map, Functor.map]
            cases found : current.2.cells.lookup name with
            | none => simp [throw, throwThe] <;> rfl
            | some raw =>
              cases typed : raw.as ty with
              | none => simp [typed, throw, throwThe] <;> rfl
              | some value =>
                simp [typed]
                split <;> simp_all [throw, throwThe] <;> rfl

          | readMap name destination keyTy valueTy key =>
            dsimp [SourceEffects.step, runEffectWithEnv, Option.isSome,
              Bind.bind, Except.bind, Pure.pure, Except.pure, Except.map, Functor.map]
            cases keyEval : key.eval ctx current.1 with
            | error message => simp <;> rfl
            | ok index =>
              cases found : current.2.maps.lookup name with
              | none => simp [throw, throwThe] <;> rfl
              | some entries =>
                cases atKey : entries.lookup (Value.pack keyTy index) with
                | none => simp [atKey, throw, throwThe] <;> rfl
                | some raw =>
                  cases typed : raw.as valueTy with
                  | none => simp [atKey, typed, throw, throwThe] <;> rfl
                  | some value =>
                    simp [atKey, typed]
                    split <;> simp_all [throw, throwThe] <;> rfl

          | require required =>
            dsimp [SourceEffects.step, runEffectWithEnv, Option.isSome,
              Bind.bind, Except.bind, Pure.pure, Except.pure, Except.map, Functor.map]
            cases result : required.eval ctx current.1 with
            | error message => simp <;> rfl
            | ok passes => cases passes <;> simp <;> rfl
          | requireAbsent name keyTy key =>
            dsimp [SourceEffects.step, runEffectWithEnv, Option.isSome,
              Bind.bind, Except.bind, Pure.pure, Except.pure, Except.map, Functor.map]
            cases keyEval : key.eval ctx current.1 with
            | error message => simp <;> rfl
            | ok index =>
              cases found : current.2.maps.lookup name with
              | none => simp <;> rfl
              | some entries =>
                cases atKey : entries.lookup (Value.pack keyTy index) <;>
                  simp [atKey] <;> rfl
          | writeCell name ty value =>
            dsimp [SourceEffects.step, runEffectWithEnv, Option.isSome,
              Bind.bind, Except.bind, Pure.pure, Except.pure, Except.map, Functor.map]
            cases found : current.2.cells.lookup name with
            | none => simp [throw, throwThe] <;> rfl
            | some existing =>
              cases typed : existing.as ty with
              | none => simp [typed, throw, throwThe] <;> rfl
              | some resolved =>
                cases result : value.eval ctx current.1 <;>
                  simp [typed] <;> rfl

          | writeMap name keyTy valueTy key value =>
            dsimp [SourceEffects.step, runEffectWithEnv, Option.isSome,
              Bind.bind, Except.bind, Pure.pure, Except.pure, Except.map, Functor.map]
            cases keyEval : key.eval ctx current.1 with
            | error message => simp <;> rfl
            | ok index =>
              cases valueEval : value.eval ctx current.1 with
              | error message => simp <;> rfl
              | ok result =>
                cases found : current.2.maps.lookup name with
                | none => simp [throw, throwThe] <;> rfl
                | some entries =>
                  simp [throw, throwThe]
                  split <;> simp_all [] <;> rfl

        | require condition required =>
          unfold step
          dsimp [runEffectsWithGuardsAndEnv, List.zipIdx, List.all, List.isEmpty, List.length,
            Option.isNone, Option.getD, Option.isSome, Bind.bind, Except.bind, Pure.pure, Except.pure]
          rw [List.forIn_cons]
          dsimp [List.getElem?_cons_zero, Option.getD, Option.isSome, Bind.bind,
            Except.bind, Pure.pure, Except.pure]
          cases guardEval : condition.eval ctx current.1 with
          | error message => simp [Except.map, Functor.map]
          | ok value =>
            cases value with
            | false => rfl
            | true =>
              cases result : required.eval ctx current.1 with
              | error message => simp [Except.map, Functor.map] <;> rfl
              | ok passes => cases passes <;> simp [Except.map, Functor.map] <;> rfl
        | readCell condition name destination ty =>
          unfold step
          dsimp [runEffectsWithGuardsAndEnv, List.zipIdx, List.all, List.isEmpty, List.length,
            Option.isNone, Option.getD, Option.isSome, Bind.bind, Except.bind, Pure.pure, Except.pure]
          rw [List.forIn_cons]
          dsimp [List.getElem?_cons_zero, Option.getD, Option.isSome, Bind.bind,
            Except.bind, Pure.pure, Except.pure]
          cases guardEval : condition.eval ctx current.1 with
          | error message => simp [Except.map, Functor.map] <;> rfl
          | ok enabled =>
            cases enabled with
            | false => simp [Except.map, Functor.map] <;> rfl
            | true =>
              simp only [Except.map, Functor.map, throw, throwThe]
              cases found : current.2.cells.lookup name with
              | none => simp <;> rfl
              | some raw =>
                cases typed : raw.as ty with
                | none => simp [typed] <;> rfl
                | some value =>
                  simp [typed]
                  split <;> simp_all [] <;> rfl
        | readMap condition name destination keyTy valueTy key =>
          unfold step
          dsimp [runEffectsWithGuardsAndEnv, List.zipIdx, List.all, List.isEmpty, List.length,
            Option.isNone, Option.getD, Option.isSome, Bind.bind, Except.bind, Pure.pure, Except.pure]
          rw [List.forIn_cons]
          dsimp [List.getElem?_cons_zero, Option.getD, Option.isSome, Bind.bind,
            Except.bind, Pure.pure, Except.pure]
          cases guardEval : condition.eval ctx current.1 with
          | error message => simp [Except.map, Functor.map] <;> rfl
          | ok enabled =>
            cases enabled with
            | false => simp [Except.map, Functor.map] <;> rfl
            | true =>
              simp only [Except.map, Functor.map, throw, throwThe]
              cases keyEval : key.eval ctx current.1 with
              | error message => simp <;> rfl
              | ok index =>
                cases found : current.2.maps.lookup name with
                | none => simp <;> rfl
                | some entries =>
                  cases atKey : entries.lookup (Value.pack keyTy index) with
                  | none => simp [atKey] <;> rfl
                  | some raw =>
                    cases typed : raw.as valueTy with
                    | none => simp [atKey, typed] <;> rfl
                    | some value =>
                      simp [atKey, typed]
                      split <;> simp_all [] <;> rfl
        | writeCell condition name ty value =>
          unfold step
          dsimp [runEffectsWithGuardsAndEnv, List.zipIdx, List.all, List.isEmpty, List.length,
            Option.isNone, Option.getD, Option.isSome, Bind.bind, Except.bind, Pure.pure, Except.pure]
          rw [List.forIn_cons]
          dsimp [List.getElem?_cons_zero, Option.getD, Option.isSome, Bind.bind,
            Except.bind, Pure.pure, Except.pure]
          cases guardEval : condition.eval ctx current.1 with
          | error message => rfl
          | ok enabled =>
            cases enabled with
            | false => rfl
            | true =>
              cases found : current.2.cells.lookup name with
              | none => simp [Except.map, Functor.map, throw, throwThe] <;> rfl
              | some existing =>
                cases typed : existing.as ty with
                | none => simp [typed, Except.map, Functor.map, throw, throwThe] <;> rfl
                | some resolved =>
                  cases result : value.eval ctx current.1 <;>
                    simp [typed, Except.map, Functor.map] <;> rfl
        | writeMap condition name keyTy valueTy key value =>
          unfold step
          dsimp [runEffectsWithGuardsAndEnv, List.zipIdx, List.all, List.isEmpty, List.length,
            Option.isNone, Option.getD, Option.isSome, Bind.bind, Except.bind, Pure.pure, Except.pure]
          rw [List.forIn_cons]
          dsimp [List.getElem?_cons_zero, Option.getD, Option.isSome, Bind.bind,
            Except.bind, Pure.pure, Except.pure]
          cases guardEval : condition.eval ctx current.1 with
          | error message => rfl
          | ok enabled =>
            cases enabled with
            | false => rfl
            | true =>
              cases keyEval : key.eval ctx current.1 with
              | error message => simp [Except.map, Functor.map] <;> rfl
              | ok index =>
                cases valueEval : value.eval ctx current.1 with
                | error message => simp [Except.map, Functor.map] <;> rfl
                | ok result =>
                  cases found : current.2.maps.lookup name with
                  | none => simp [Except.map, Functor.map, throw, throwThe] <;> rfl
                  | some entries =>
                    simp [Except.map, Functor.map, throw, throwThe]
                    split <;> simp_all [] <;> rfl
      · dsimp only [desiredCallback]
        rw [List.forIn_yield_eq_foldlM]
        simp [fold]

end Noctium.Verification.GuardedSourceEffects
