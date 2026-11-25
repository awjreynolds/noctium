import Noctium.Verification.SourceEffects

namespace Noctium.Verification.SourceReplayBoundary

open Noctium

private theorem bind_ok {α β : Type} (value : α)
    (next : α → Except String β) :
    ((Except.ok value : Except String α) >>= next) = next value := rfl

private theorem map_ok {α β : Type} (f : α → β) (value : α) :
    f <$> (Except.ok value : Except String α) = .ok (f value) := rfl

attribute [local simp] bind_ok map_ok

/-- Entrypoint execution always starts ledger effects after clearing the
transaction-local input, output, and spend-claim accumulators. -/
def resetTransactionLists (state : LedgerState) : LedgerState :=
  {state with
    unshieldedInputs := [],
    unshieldedOutputs := [],
    unshieldedSpendClaims := []}

@[simp] theorem resetTransactionLists_idempotent (state : LedgerState) :
    resetTransactionLists (resetTransactionLists state) = resetTransactionLists state := by
  cases state
  rfl

/-- Calls whose persistent state agrees have identical replay results, even
when their incoming transaction-local accumulators differ. -/
theorem entrypoint_run_reset_invariant (ctx : EvalContext) (entry : Entrypoint)
    (env : EvalEnv) (left right : LedgerState)
    (samePersistentState : resetTransactionLists left = resetTransactionLists right) :
    entry.run ctx env left = entry.run ctx env right := by
  simpa only [Entrypoint.run, resetTransactionLists] using
    congrArg (fun source : LedgerState => entry.run ctx env source) samePersistentState

/-- Once disclosure and circuit evaluation succeed, an entrypoint with no
explicit returns exposes exactly the circuit outputs. With valid all-none
guard metadata, its ordered effect result determines the successor state. -/
theorem run_no_returns_all_none (ctx : EvalContext) (entry : Entrypoint)
    (env outputs orderedEnv : EvalEnv) (state next : LedgerState)
    (disclosure : Disclosure.entrypoint entry = .ok ())
    (circuitRun : entry.circuit.run ctx env = .ok outputs)
    (noReturns : entry.returns = [])
    (validGuardMetadata : entry.effectGuards.isEmpty ∨
      entry.effectGuards.length = entry.effects.length)
    (allGuardsNone : entry.effectGuards.all Option.isNone = true)
    (orderedFold : Noctium.Verification.SourceEffects.fold ctx entry.effects
      (outputs ++ env,
        {state with
          unshieldedInputs := [],
          unshieldedOutputs := [],
          unshieldedSpendClaims := []}) = .ok (orderedEnv, next)) :
    entry.run ctx env state = .ok (outputs, next) := by
  have orderedEffects : runEffectsWithEnv ctx entry.effects (outputs ++ env)
      {state with
        unshieldedInputs := [],
        unshieldedOutputs := [],
        unshieldedSpendClaims := []} = .ok (orderedEnv, next) := by
    rw [Noctium.Verification.SourceEffects.runEffectsWithEnv_eq_fold]
    exact orderedFold
  have guardLength : entry.effectGuards.isEmpty ||
      entry.effectGuards.length == entry.effects.length := by
    rcases validGuardMetadata with empty | length
    · simp [empty]
    · simp [length]
  have guardsNone : entry.effectGuards.all Option.isNone := allGuardsNone
  have effectsResult : runEffectsWithGuardsAndEnv ctx entry.effects entry.effectGuards
      (outputs ++ env)
      {state with
        unshieldedInputs := [],
        unshieldedOutputs := [],
        unshieldedSpendClaims := []} = .ok (orderedEnv, next) := by
    simp [runEffectsWithGuardsAndEnv, guardLength, guardsNone, orderedEffects]
  simp [Entrypoint.run, Entrypoint.evalReturns, disclosure, circuitRun, noReturns,
    effectsResult, bind_ok]

end Noctium.Verification.SourceReplayBoundary
