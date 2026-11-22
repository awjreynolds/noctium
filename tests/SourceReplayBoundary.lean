import Noctium.Verification.SourceReplayBoundary

open Noctium
open Noctium.Verification.SourceReplayBoundary

private theorem bind_ok {α β : Type} (value : α)
    (next : α → Except String β) :
    ((Except.ok value : Except String α) >>= next) = next value := rfl

attribute [local simp] bind_ok

private def replayContext : EvalContext := {
  modulus := Field.modulus,
  poseidon2 := fun _ _ _ => .error "unused by replay boundary fixture"
}

private def replayCircuit : Circuit := {
  name := "SourceReplayBoundary",
  outputs := [{name := "answer", ty := .native, value := .native 7}]
}

private def replayEntry : Entrypoint := {
  name := "apply",
  circuit := replayCircuit,
  effects := [.require (.bool true)],
  returns := [],
  effectGuards := [none]
}

private def transactionKey : TokenEffectKey := {
  color := [1],
  isUnshielded := true
}

private def spendKey : SpendClaimKey := {
  color := [2],
  isUnshielded := true,
  isContract := false,
  recipient := [3]
}

private def replayBefore : LedgerState := {
  unshieldedInputs := [(transactionKey, 2)],
  unshieldedOutputs := [(transactionKey, 3)],
  unshieldedSpendClaims := [(spendKey, 4)]
}

private def replayBeforeOtherTransactions : LedgerState := {
  unshieldedInputs := [(transactionKey, 9)],
  unshieldedOutputs := [],
  unshieldedSpendClaims := [(spendKey, 11)]
}

#guard (Disclosure.entrypoint replayEntry).isOk
#guard replayEntry.effectGuards.all Option.isNone
#guard replayEntry.effectGuards.length == replayEntry.effects.length

#guard match replayEntry.run replayContext [] replayBefore with
  | .ok (outputs, next) =>
      outputs == [("answer", .native 7)] &&
      next == resetTransactionLists replayBefore
  | .error _ => false

#guard match Noctium.Verification.SourceEffects.fold replayContext replayEntry.effects
    ([("answer", .native 7)], resetTransactionLists replayBefore) with
  | .ok (orderedEnv, next) =>
      orderedEnv == [("answer", .native 7)] &&
      next == resetTransactionLists replayBefore
  | .error _ => false

private def falseGuardEntry : Entrypoint := {
  replayEntry with
  effects := [.require (.bool false)],
  effectGuards := [some (.bool false)]
}

#guard (Disclosure.entrypoint falseGuardEntry).isOk
#guard match falseGuardEntry.run replayContext [] replayBefore with
  | .ok (outputs, next) =>
      outputs == [("answer", .native 7)] &&
      next == resetTransactionLists replayBefore
  | .error _ => false

private def explicitReturnEntry : Entrypoint := {
  replayEntry with
  returns := [{name := "receipt", ty := .native, value := .native 9}]
}

#guard (Disclosure.entrypoint explicitReturnEntry).isOk
#guard match explicitReturnEntry.run replayContext [] replayBefore with
  | .ok (outputs, _) =>
      outputs == [("answer", .native 7), ("receipt", .native 9)]
  | .error _ => false

example : replayEntry.run replayContext [] replayBefore =
    replayEntry.run replayContext [] replayBeforeOtherTransactions := by
  apply Noctium.Verification.SourceReplayBoundary.entrypoint_run_reset_invariant
  rfl

#guard match replayEntry.run replayContext [] replayBefore,
    replayEntry.run replayContext [] replayBeforeOtherTransactions with
  | .ok (leftOutputs, leftState), .ok (rightOutputs, rightState) =>
      leftOutputs == rightOutputs && leftState == rightState
  | _, _ => false
