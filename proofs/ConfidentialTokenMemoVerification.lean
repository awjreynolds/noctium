import examples.openzeppelin.ConfidentialToken
import Noctium.Verification

namespace OpenZeppelinPort.ConfidentialTokenMemoVerification

open Noctium
open Noctium.Verification

def zero32 : List Nat := List.replicate 32 0
def one32 : List Nat := 1 :: List.replicate 31 0
def two32 : List Nat := 2 :: List.replicate 31 0

/-- The selected entry is the seventh declared entry of the source contract. -/
def clearMemosEntry : Entrypoint :=
  OpenZeppelinPort.ConfidentialToken.entrypoints[6]'(by decide)

theorem selected_entry_name : clearMemosEntry.name = "clearMemos" := by decide

theorem selected_entry_uses_clearMemoInput :
    clearMemosEntry.circuit.name = OpenZeppelinPort.clearMemoInput.name ∧
    clearMemosEntry.circuit.inputs.map (fun input => (input.name, input.ty, input.visibility)) =
      OpenZeppelinPort.clearMemoInput.inputs.map (fun input => (input.name, input.ty, input.visibility)) ∧
    clearMemosEntry.circuit.outputs.map (fun item => (item.name, item.ty)) =
      OpenZeppelinPort.clearMemoInput.outputs.map (fun item => (item.name, item.ty)) := by
  decide

/-- The source fixture proves the exact four input bindings, account-id guard,
and two disclosed Jubjub coordinates of the quoted checked circuit. -/
abbrev quoted_clear_memo_circuit :=
  OpenZeppelinPort.clearMemoInput_exposes_checked_circuit

def memoHashOracle (input : List Nat) : Except String (List Nat) :=
  if input.length == 32 then
    if input == zero32 || input == two32 then .ok zero32 else .ok one32
  else if input.length == 64 then
    if input.drop 32 == zero32 || input.drop 32 == two32 then .ok zero32 else .ok one32
  else .ok one32

/-- Explicit toy context for source-level credential equations. This does not
model production hashing or Jubjub arithmetic. -/
def memoContext : EvalContext := {
  modulus := Field.modulus
  poseidon2 := fun _ _ _ => .ok 0
  persistentHash32 := memoHashOracle
  jubjub := {
    pointValid := fun _ => .ok ()
    mulGenerator := fun scalar =>
      .ok (if scalar == 0 then 0 else 5, if scalar == 0 then 1 else 7)
  }
}

def inputs (expectedEpoch : Nat) (accountSecret encryptionSecret : List Nat) : EvalEnv := [
  ("accountId", .bytes 32 zero32),
  ("expectedEpoch", .uint (2 ^ 64 - 1) expectedEpoch),
  ("$helper2", .bytes 32 accountSecret),
  ("$helper4", .bytes 32 encryptionSecret)]

theorem memo_hash_zero_prefix (domain : List Nat) (hlen : domain.length = 32) :
    memoHashOracle (domain ++ zero32) = .ok zero32 := by
  have hdrop : (domain ++ zero32).drop 32 = zero32 := by simp [hlen]
  simp [memoHashOracle, hlen, hdrop, zero32, two32, one32]

theorem memo_hash_two_prefix (domain : List Nat) (hlen : domain.length = 32) :
    memoHashOracle (domain ++ two32) = .ok zero32 := by
  have hdrop : (domain ++ two32).drop 32 = two32 := by simp [hlen, two32]
  simp [memoHashOracle, hlen, hdrop, zero32, two32, one32]

theorem memo_hash_one_prefix (domain : List Nat) (hlen : domain.length = 32) :
    memoHashOracle (domain ++ one32) = .ok one32 := by
  have hdrop : (domain ++ one32).drop 32 = one32 := by simp [hlen, one32]
  simp [memoHashOracle, hlen, hdrop, zero32, two32, one32]

theorem credential_hash_equations :
    memoContext.persistentHash32 zero32 = .ok zero32 ∧
    memoContext.persistentHash32 two32 = .ok zero32 ∧
    memoContext.persistentHash32 one32 = .ok one32 ∧
    (∀ domain, domain.length = 32 →
      memoContext.persistentHash32 (domain ++ zero32) = .ok zero32 ∧
      memoContext.persistentHash32 (domain ++ two32) = .ok zero32 ∧
      memoContext.persistentHash32 (domain ++ one32) = .ok one32) := by
  constructor
  · change memoHashOracle zero32 = .ok zero32
    rfl
  constructor
  · change memoHashOracle two32 = .ok zero32
    rfl
  constructor
  · change memoHashOracle one32 = .ok one32
    rfl
  · intro domain hlen
    constructor
    · exact memo_hash_zero_prefix domain hlen
    constructor
    · exact memo_hash_two_prefix domain hlen
    · exact memo_hash_one_prefix domain hlen

theorem credential_generator_equations :
    memoContext.jubjub.mulGenerator 0 = .ok (0, 1) ∧
    memoContext.jubjub.mulGenerator 1 = .ok (5, 7) := by
  constructor <;> simp [memoContext]

def memoKey : Value := .bytes 32 zero32
def otherMemoKey : Value := .bytes 32 one32
def otherMemoPayload : List Value := [.native 21, .native 22, .native 23]

def keyRecord : LedgerValue :=
  .composite (.structure "OpenZeppelinPort.ConfidentialToken.JubjubKey")
    [.native 0, .native 1]

def memoTreeBefore : LedgerValue := .map [
  (memoKey, .list [[.native 11, .native 12, .native 13]]),
  (otherMemoKey, .list [otherMemoPayload])]

def memoTreeAfter : LedgerValue := .map [
  (memoKey, .list []),
  (otherMemoKey, .list [otherMemoPayload])]

/-- Exact state selected for the source transition. The target has one memo,
registered identity key, and credit epoch 5. -/
def canonicalAdmittedState : LedgerState := {
  cells := [
    ("initialized", .bool Bool.true),
    ("totalSupply", .uint (2 ^ 128 - 1) 0),
    ("name", .opaqueString "Memo proof token"),
    ("symbol", .opaqueString "MPT"),
    ("decimals", .uint 255 18)],
  trees := [
    ("memos", memoTreeBefore),
    ("encryptionKeys", .map [(memoKey, keyRecord)]),
    ("balances", .map []),
    ("pending", .map []),
    ("creditEpochs", .map [(memoKey, .scalar (.uint (2 ^ 64 - 1) 5))]),
    ("escrow", .map []),
    ("escrowSpendEpochs", .map [])]
}

def expectedClearedState : LedgerState := {
  canonicalAdmittedState with
  trees := [
    ("memos", memoTreeAfter),
    ("encryptionKeys", .map [(memoKey, keyRecord)]),
    ("balances", .map []),
    ("pending", .map []),
    ("creditEpochs", .map [(memoKey, .scalar (.uint (2 ^ 64 - 1) 5))]),
    ("escrow", .map []),
    ("escrowSpendEpochs", .map [])]
}

def expectedOutputs : EvalEnv := [
  ("result.keyX", .native 0),
  ("result.keyY", .native 1)]

def memoResetSourceSpan : SourceSpan := {
  file := "examples/openzeppelin/ConfidentialToken.lean"
  line := 764
  column := 17
}

def memoResetEffect : Effect :=
  .listReset "memos" [.mk (.bytes 32) (.disclose memoResetSourceSpan (.ref "accountId"))]

def effectInputEnv : EvalEnv := expectedOutputs ++ inputs 5 zero32 zero32

theorem selected_entry_has_memo_reset_last :
    clearMemosEntry.effects.getLast? = some memoResetEffect := by
  rfl

theorem canonical_admission_facts :
    canonicalAdmittedState.cells.lookup "initialized" = some (.bool Bool.true) ∧
    canonicalAdmittedState.trees.lookup "memos" = some memoTreeBefore ∧
    canonicalAdmittedState.trees.lookup "encryptionKeys" =
      some (.map [(memoKey, keyRecord)]) ∧
    canonicalAdmittedState.trees.lookup "creditEpochs" =
      some (.map [(memoKey, .scalar (.uint (2 ^ 64 - 1) 5))]) := by
  simp [canonicalAdmittedState, memoTreeBefore, keyRecord, memoKey, otherMemoKey,
    otherMemoPayload, List.lookup]

theorem expected_state_frame_facts :
    expectedClearedState.cells = canonicalAdmittedState.cells ∧
    expectedClearedState.maps = canonicalAdmittedState.maps ∧
    expectedClearedState.trees.lookup "memos" = some memoTreeAfter ∧
    expectedClearedState.trees.lookup "encryptionKeys" =
      canonicalAdmittedState.trees.lookup "encryptionKeys" ∧
    expectedClearedState.trees.lookup "creditEpochs" =
      canonicalAdmittedState.trees.lookup "creditEpochs" := by
  simp [expectedClearedState, canonicalAdmittedState, memoTreeBefore, memoTreeAfter,
    keyRecord, memoKey, otherMemoKey, otherMemoPayload, List.lookup]

/-- The concrete production reset step clears only the selected memo list and
preserves the sibling account's memo. -/
theorem selected_memo_reset_step :
    runEffectWithEnv memoContext memoResetEffect effectInputEnv canonicalAdmittedState =
      .ok (effectInputEnv, expectedClearedState) := by
  have memoRoot : canonicalAdmittedState.trees.lookup "memos" = some memoTreeBefore :=
    canonical_admission_facts.2.1
  have result := runEffectWithEnv_listReset_bytes32 memoContext effectInputEnv
    canonicalAdmittedState "memos" memoResetSourceSpan zero32
    [(memoKey, .list [[.native 11, .native 12, .native 13]]),
      (otherMemoKey, .list [otherMemoPayload])]
    (by
      change List.lookup "accountId" (expectedOutputs ++ inputs 5 zero32 zero32) =
        some (.bytes 32 zero32)
      simp [expectedOutputs, inputs, zero32, List.lookup_append, List.lookup_cons])
    (by simp [zero32])
    (by intro byte hmem; simp [zero32] at hmem; subst byte; decide)
    (by simpa [memoTreeBefore, keyRecord, memoKey, otherMemoKey,
      otherMemoPayload] using memoRoot)
  have memoMapAfter :
      updateAssoc memoKey (LedgerValue.list [])
        [(memoKey, LedgerValue.list [[.native 11, .native 12, .native 13]]),
          (otherMemoKey, LedgerValue.list [otherMemoPayload])] =
        [(memoKey, LedgerValue.list []),
          (otherMemoKey, LedgerValue.list [otherMemoPayload])] := by
    have sameKey : (memoKey == memoKey) = Bool.true := by decide
    have otherKey : (otherMemoKey == memoKey) = Bool.false := by decide
    unfold updateAssoc
    simp only [List.filter_cons, List.filter_nil]
    rw [sameKey, otherKey]
    rfl
  have memoMapAfterExact :
      updateAssoc (Value.bytes 32 zero32) (LedgerValue.list [])
        [(memoKey, LedgerValue.list [[.native 11, .native 12, .native 13]]),
          (otherMemoKey, LedgerValue.list [otherMemoPayload])] =
        [(memoKey, LedgerValue.list []), (otherMemoKey, LedgerValue.list [otherMemoPayload])] := by
    change updateAssoc memoKey (LedgerValue.list [])
      [(memoKey, LedgerValue.list [[.native 11, .native 12, .native 13]]),
        (otherMemoKey, LedgerValue.list [otherMemoPayload])] =
      [(memoKey, LedgerValue.list []), (otherMemoKey, LedgerValue.list [otherMemoPayload])]
    exact memoMapAfter
  rw [memoMapAfterExact] at result
  simpa [memoResetEffect, expectedClearedState, canonicalAdmittedState,
    memoTreeBefore, memoTreeAfter, keyRecord, memoKey, otherMemoKey,
    otherMemoPayload, updateAssoc] using result

theorem selected_memo_reset_projections :
    (runEffectWithEnv memoContext memoResetEffect effectInputEnv canonicalAdmittedState).map
      (fun frame => frame.1.lookup "result.keyX") = .ok (some (.native 0)) ∧
    (runEffectWithEnv memoContext memoResetEffect effectInputEnv canonicalAdmittedState).map
      (fun frame => frame.2.trees.lookup "memos") = .ok (some memoTreeAfter) := by
  rw [selected_memo_reset_step]
  constructor <;> rfl

theorem selected_entry_has_no_extra_returns : clearMemosEntry.returns = [] := by
  rfl

/-- Convert a successful `Except` status into its Unit success value without
requiring an equality decision procedure for the error type. -/
theorem except_unit_eq_ok_of_isOk {ε : Type} (value : Except ε Unit)
    (isOk : value.isOk = Bool.true) : value = .ok () := by
  cases value with
  | error message => cases isOk
  | ok unit => cases unit; rfl

/-- Conditional bridge for the evaluator's successful entrypoint run. It keeps
disclosure validation, circuit execution, effect execution, and return-list
facts as visible premises. -/
theorem entrypoint_success_from_checked_steps
    (selected : Entrypoint) (ctx : EvalContext) (env : EvalEnv) (state : LedgerState)
    (outputs finalEnv : EvalEnv) (next : LedgerState)
    (disclosureIsOk : (Disclosure.entrypoint selected).isOk = Bool.true)
    (circuitResult : selected.circuit.run ctx env = .ok outputs)
    (effectsResult : runEffectsWithGuardsAndEnv ctx selected.effects selected.effectGuards
      (outputs ++ env) ({state with
        unshieldedInputs := []
        unshieldedOutputs := []
        unshieldedSpendClaims := []}) = .ok (finalEnv, next))
    (noReturns : selected.returns = []) :
    selected.run ctx env state = .ok (outputs, next) := by
  have disclosed := except_unit_eq_ok_of_isOk (Disclosure.entrypoint selected) disclosureIsOk
  unfold Entrypoint.run
  rw [disclosed]
  simp only [Except.bind, Bind.bind, Except.map, Functor.map]
  rw [circuitResult]
  simp only [Except.bind, Bind.bind, Except.map, Functor.map]
  rw [effectsResult]
  simp only [Except.bind, Bind.bind, Except.map, Functor.map]
  rw [noReturns]
  simp only [List.mapM_nil]
  have hnil : (pure ([] : List (String × Value)) : Except String (List (String × Value))) = .ok [] := rfl
  rw [hnil]
  simp only [List.append_nil]
  have hout : (pure (outputs, next) : Except String (EvalEnv × LedgerState)) =
      .ok (outputs, next) := rfl
  rw [hout]

theorem clear_memos_transition_from_checked_steps
    (disclosureIsOk : (Disclosure.entrypoint clearMemosEntry).isOk = Bool.true)
    (circuitResult : clearMemosEntry.circuit.run memoContext
      (inputs 5 zero32 zero32) = .ok expectedOutputs)
    (effectsResult : ∃ finalEnv,
      runEffectsWithGuardsAndEnv memoContext clearMemosEntry.effects
        clearMemosEntry.effectGuards (expectedOutputs ++ inputs 5 zero32 zero32)
        ({canonicalAdmittedState with
          unshieldedInputs := []
          unshieldedOutputs := []
          unshieldedSpendClaims := []}) = .ok (finalEnv, expectedClearedState)) :
    clearMemosEntry.run memoContext (inputs 5 zero32 zero32) canonicalAdmittedState =
      .ok (expectedOutputs, expectedClearedState) := by
  rcases effectsResult with ⟨finalEnv, effectsRun⟩
  exact entrypoint_success_from_checked_steps clearMemosEntry memoContext
    (inputs 5 zero32 zero32) canonicalAdmittedState expectedOutputs finalEnv
    expectedClearedState disclosureIsOk circuitResult effectsRun selected_entry_has_no_extra_returns

/-- Successful result projection through the concrete checked-step bridge.
This proves the selected key coordinate and target memo lookup without an
equality decision procedure for all of LedgerState. -/
theorem successful_projection_from_checked_steps
    (disclosureIsOk : (Disclosure.entrypoint clearMemosEntry).isOk = Bool.true)
    (circuitResult : clearMemosEntry.circuit.run memoContext
      (inputs 5 zero32 zero32) = .ok expectedOutputs)
    (effectsResult : ∃ finalEnv,
      runEffectsWithGuardsAndEnv memoContext clearMemosEntry.effects
        clearMemosEntry.effectGuards (expectedOutputs ++ inputs 5 zero32 zero32)
        ({canonicalAdmittedState with
          unshieldedInputs := []
          unshieldedOutputs := []
          unshieldedSpendClaims := []}) = .ok (finalEnv, expectedClearedState)) :
    (clearMemosEntry.run memoContext (inputs 5 zero32 zero32) canonicalAdmittedState).map
      (fun result => result.1.lookup "result.keyX") = .ok (some (.native 0)) ∧
    (clearMemosEntry.run memoContext (inputs 5 zero32 zero32) canonicalAdmittedState).map
      (fun result => result.2.trees.lookup "memos") = .ok (some memoTreeAfter) := by
  have transition := clear_memos_transition_from_checked_steps disclosureIsOk circuitResult effectsResult
  constructor <;> rw [transition] <;> rfl

theorem effects_failure_propagates
    (selected : Entrypoint) (ctx : EvalContext) (env : EvalEnv) (state : LedgerState)
    (outputs : EvalEnv) (message : String)
    (disclosureIsOk : (Disclosure.entrypoint selected).isOk = Bool.true)
    (circuitResult : selected.circuit.run ctx env = .ok outputs)
    (effectsFailure : runEffectsWithGuardsAndEnv ctx selected.effects selected.effectGuards
      (outputs ++ env) ({state with
        unshieldedInputs := []
        unshieldedOutputs := []
        unshieldedSpendClaims := []}) = .error message) :
    selected.run ctx env state = .error message := by
  have disclosed := except_unit_eq_ok_of_isOk (Disclosure.entrypoint selected) disclosureIsOk
  unfold Entrypoint.run
  rw [disclosed]
  simp only [Except.bind, Bind.bind, Except.map, Functor.map]
  rw [circuitResult]
  simp only [Except.bind, Bind.bind, Except.map, Functor.map]
  rw [effectsFailure]

theorem circuit_failure_propagates
    (selected : Entrypoint) (ctx : EvalContext) (env : EvalEnv) (state : LedgerState)
    (message : String)
    (disclosureIsOk : (Disclosure.entrypoint selected).isOk = Bool.true)
    (circuitFailure : selected.circuit.run ctx env = .error message) :
    selected.run ctx env state = .error message := by
  have disclosed := except_unit_eq_ok_of_isOk (Disclosure.entrypoint selected) disclosureIsOk
  unfold Entrypoint.run
  rw [disclosed]
  simp only [Except.bind, Bind.bind, Except.map, Functor.map]
  rw [circuitFailure]

/-- Exact stale-epoch conclusion once the selected entry's effects establish
the epoch guard failure. -/
theorem stale_epoch_rejection_from_effects
    (disclosureIsOk : (Disclosure.entrypoint clearMemosEntry).isOk = Bool.true)
    (circuitResult : clearMemosEntry.circuit.run memoContext
      (inputs 4 zero32 zero32) = .ok expectedOutputs)
    (effectsFailure : runEffectsWithGuardsAndEnv memoContext clearMemosEntry.effects
      clearMemosEntry.effectGuards (expectedOutputs ++ inputs 4 zero32 zero32)
      ({canonicalAdmittedState with
        unshieldedInputs := []
        unshieldedOutputs := []
        unshieldedSpendClaims := []}) = .error "state transition guard failed") :
    clearMemosEntry.run memoContext (inputs 4 zero32 zero32) canonicalAdmittedState =
      .error "state transition guard failed" := by
  exact effects_failure_propagates clearMemosEntry memoContext
    (inputs 4 zero32 zero32) canonicalAdmittedState expectedOutputs
    "state transition guard failed" disclosureIsOk circuitResult effectsFailure

def publicBindings (environment : EvalEnv) : List (String × Option Value) :=
  (clearMemosEntry.circuit.inputs.filter (·.visibility == .«public»)).map fun input =>
    (input.name, environment.lookup input.name)

def succeeded {α : Type} : Except String α → _root_.Bool
  | .ok _ => _root_.Bool.true
  | .error _ => _root_.Bool.false

theorem pinned_pairs_have_same_public_bindings :
    publicBindings (inputs 5 zero32 zero32) = publicBindings (inputs 5 two32 two32) ∧
    publicBindings (inputs 5 zero32 zero32) = publicBindings (inputs 5 one32 zero32) := by
  constructor <;> decide

/-- Successful-only result equality, conditional on both exact source runs
being admitted. Failure status remains outside this theorem. -/
theorem successful_only_source_privacy_for_pinned_pair
    (firstRun : clearMemosEntry.run memoContext (inputs 5 zero32 zero32)
      canonicalAdmittedState = .ok (expectedOutputs, expectedClearedState))
    (secondRun : clearMemosEntry.run memoContext (inputs 5 two32 two32)
      canonicalAdmittedState = .ok (expectedOutputs, expectedClearedState)) :
    publicBindings (inputs 5 zero32 zero32) = publicBindings (inputs 5 two32 two32) ∧
    clearMemosEntry.run memoContext (inputs 5 zero32 zero32) canonicalAdmittedState =
      clearMemosEntry.run memoContext (inputs 5 two32 two32) canonicalAdmittedState := by
  constructor
  · exact pinned_pairs_have_same_public_bindings.1
  · rw [firstRun, secondRun]

/-- A wrong account secret rejects if the checked circuit returns the source
constraint failure. This names the bridge premise without asserting it. -/
theorem wrong_account_secret_rejection_from_circuit
    (disclosureIsOk : (Disclosure.entrypoint clearMemosEntry).isOk = Bool.true)
    (circuitFailure : clearMemosEntry.circuit.run memoContext
      (inputs 5 one32 zero32) = .error "circuit constraint failed") :
    clearMemosEntry.run memoContext (inputs 5 one32 zero32) canonicalAdmittedState =
      .error "circuit constraint failed" := by
  exact circuit_failure_propagates clearMemosEntry memoContext
    (inputs 5 one32 zero32) canonicalAdmittedState "circuit constraint failed"
    disclosureIsOk circuitFailure

/-- A wrong encryption secret rejects if the selected effects fail their key
coordinate guard after a successful circuit result. -/
theorem wrong_encryption_secret_rejection_from_effects
    (disclosureIsOk : (Disclosure.entrypoint clearMemosEntry).isOk = Bool.true)
    (circuitResult : clearMemosEntry.circuit.run memoContext
      (inputs 5 zero32 one32) = .ok expectedOutputs)
    (effectsFailure : runEffectsWithGuardsAndEnv memoContext clearMemosEntry.effects
      clearMemosEntry.effectGuards (expectedOutputs ++ inputs 5 zero32 one32)
      ({canonicalAdmittedState with
        unshieldedInputs := []
        unshieldedOutputs := []
        unshieldedSpendClaims := []}) = .error "state transition guard failed") :
    clearMemosEntry.run memoContext (inputs 5 zero32 one32) canonicalAdmittedState =
      .error "state transition guard failed" := by
  exact effects_failure_propagates clearMemosEntry memoContext
    (inputs 5 zero32 one32) canonicalAdmittedState expectedOutputs
    "state transition guard failed" disclosureIsOk circuitResult effectsFailure

/-- A failure-status observer separates the accepted account credential from
the wrong-account case when the named execution premises hold. -/
theorem failure_observer_distinguishes_wrong_account_secret
    (acceptedRun : clearMemosEntry.run memoContext (inputs 5 zero32 zero32)
      canonicalAdmittedState = .ok (expectedOutputs, expectedClearedState))
    (rejectedRun : clearMemosEntry.run memoContext (inputs 5 one32 zero32)
      canonicalAdmittedState = .error "circuit constraint failed") :
    publicBindings (inputs 5 zero32 zero32) = publicBindings (inputs 5 one32 zero32) ∧
    succeeded (clearMemosEntry.run memoContext
      (inputs 5 zero32 zero32) canonicalAdmittedState) = _root_.Bool.true ∧
    succeeded (clearMemosEntry.run memoContext
      (inputs 5 one32 zero32) canonicalAdmittedState) = _root_.Bool.false := by
  constructor
  · exact pinned_pairs_have_same_public_bindings.2
  constructor
  · rw [acceptedRun]
    rfl
  · rw [rejectedRun]
    rfl

#print axioms entrypoint_success_from_checked_steps
#print axioms clear_memos_transition_from_checked_steps
#print axioms successful_projection_from_checked_steps
#print axioms stale_epoch_rejection_from_effects
#print axioms successful_only_source_privacy_for_pinned_pair
#print axioms wrong_account_secret_rejection_from_circuit
#print axioms wrong_encryption_secret_rejection_from_effects
#print axioms failure_observer_distinguishes_wrong_account_secret

end OpenZeppelinPort.ConfidentialTokenMemoVerification
