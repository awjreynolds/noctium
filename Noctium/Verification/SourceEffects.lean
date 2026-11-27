import Noctium.Semantics

namespace Noctium.Verification.SourceEffects

abbrev Frame := EvalEnv × LedgerState

def canonicalValue (ctx : EvalContext) (ty : Ty) (value : ty.Denote) : Bool :=
  match ty with
  | .native => value < ctx.modulus
  | .bool => true
  | .uint maximum => maximum ≤ ScalarPolicy.maxUint && value ≤ maximum && value < ctx.modulus
  | .bytes length => value.length == length && value.all (· ≤ 255)
  | .opaqueBytes => value.length ≤ maxByteOperationLength && value.all (· ≤ 255) &&
      (value.isEmpty || value.getLast! != 0)
  | .opaqueString => value.utf8ByteSize ≤ maxOpaqueStringBytes &&
      (value.toUTF8.data.isEmpty || value.toUTF8.data.back! != 0)
  | .jubjubScalar => value < Jubjub.scalarOrder
  | .jubjubPoint => value.1 < ctx.modulus && value.2 < ctx.modulus &&
      (ctx.jubjub.pointValid value).isOk
  | .foreign kind => kind.canonical value

def updateEntry [BEq α] (key : α) (value : β) (entries : List (α × β)) : List (α × β) :=
  (key, value) :: entries.filter (fun item => !(item.1 == key))

/-- Run one source effect through the production evaluator. This keeps every
effect's first-error and unsupported-case behavior aligned with Semantics. -/
def step (ctx : EvalContext) (effect : Effect) (frame : Frame) : Except String Frame :=
  runEffectWithEnv ctx effect frame.1 frame.2


def fold (ctx : EvalContext) (effects : List Effect) (frame : Frame) : Except String Frame :=
  effects.foldlM (fun frame effect => step ctx effect frame) frame

@[simp] theorem fold_nil (ctx : EvalContext) (frame : Frame) :
    fold ctx [] frame = .ok frame := rfl

theorem fold_cons (ctx : EvalContext) (effect : Effect) (rest : List Effect) (frame : Frame) :
    fold ctx (effect :: rest) frame = (step ctx effect frame).bind (fold ctx rest) := rfl

theorem fold_append (ctx : EvalContext) (before after : List Effect) (frame : Frame) :
    fold ctx (before ++ after) frame = (fold ctx before frame).bind (fold ctx after) := by
  exact List.foldlM_append

/-- Split the production loop after its first successful effect. -/
theorem runEffectsWithEnv_cons (ctx : EvalContext) (effect : Effect) (rest : List Effect)
    (env : EvalEnv) (state : LedgerState) :
    runEffectsWithEnv ctx (effect :: rest) env state = (do
      let frame ← runEffectsWithEnv ctx [effect] env state
      runEffectsWithEnv ctx rest frame.1 frame.2) := by
  simp [runEffectsWithEnv, List.foldlM_cons, List.foldlM_nil]

theorem runEffectsWithEnv_eq_fold (ctx : EvalContext) (effects : List Effect)
    (env : EvalEnv) (state : LedgerState) :
    runEffectsWithEnv ctx effects env state = fold ctx effects (env, state) := by
  rfl

/-- Exact equality with the unchanged evaluator, including every error branch. -/
theorem runEffects_eq_fold (ctx : EvalContext) (effects : List Effect)
    (env : EvalEnv) (state : LedgerState) :
    runEffects ctx effects env state = (fold ctx effects (env, state)).map Prod.snd := by
  rfl


theorem runEffects_ok_iff (ctx : EvalContext) (effects : List Effect)
    (env : EvalEnv) (state next : LedgerState) :
    runEffects ctx effects env state = .ok next ↔
      ∃ finalEnv, fold ctx effects (env, state) = .ok (finalEnv, next) := by
  rw [runEffects_eq_fold]
  cases result : fold ctx effects (env, state) with
  | error message => simp [Except.map]
  | ok frame => cases frame; simp [Except.map]

end Noctium.Verification.SourceEffects
