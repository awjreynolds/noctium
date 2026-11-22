import Noctium.Verification.SourceEffects

open Noctium

private def ctx : EvalContext := {
  modulus := Field.modulus,
  poseidon2 := fun _ _ _ => .error "hash unused by this fixture"
}

private def initialState : LedgerState := {
  cells := [("counter", .native 4)]
}

private def orderedEffects : List Effect := [
  .readCell "counter" "before" .native,
  .writeCell "counter" .native
    (.add (.ref "before" : Expr .native) (.native 3)),
  .readCell "counter" "after" .native,
  .require (.eq (.ref "after" : Expr .native) (.native 7))
]

private def orderedResult : EvalEnv × LedgerState := (
  [("after", .native 7), ("before", .native 4)],
  {cells := [("counter", .native 7)]})

#guard match runEffectsWithEnv ctx orderedEffects [] initialState with
  | .ok (env, state) => env == orderedResult.1 && state == orderedResult.2
  | .error _ => false
#guard match Noctium.Verification.SourceEffects.fold ctx orderedEffects ([], initialState) with
  | .ok (env, state) => env == orderedResult.1 && state == orderedResult.2
  | .error _ => false
#guard match runEffects ctx orderedEffects [] initialState with
  | .ok state => state == orderedResult.2
  | .error _ => false

private def rejectedEffects : List Effect := [
  .readCell "counter" "before" .native,
  .writeCell "counter" .native
    (.add (.ref "before" : Expr .native) (.native 3)),
  .require (.bool false),
  .writeCell "counter" .native (.native 99)
]

#guard match runEffectsWithEnv ctx rejectedEffects [] initialState with
  | .error message => message == "state transition guard failed"
  | .ok _ => false
#guard match Noctium.Verification.SourceEffects.fold ctx rejectedEffects ([], initialState) with
  | .error message => message == "state transition guard failed"
  | .ok _ => false
#guard match runEffects ctx rejectedEffects [] initialState with
  | .error message => message == "state transition guard failed"
  | .ok _ => false
