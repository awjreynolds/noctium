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

/-- The admitted source state contains one memo for the selected account and a
separate memo for another account. -/
theorem canonical_selected_and_sibling_memos :
    memoTreeBefore = .map [
      (memoKey, .list [[.native 11, .native 12, .native 13]]),
      (otherMemoKey, .list [otherMemoPayload])] ∧
    memoTreeAfter = .map [
      (memoKey, .list []),
      (otherMemoKey, .list [otherMemoPayload])] := by
  simp [memoTreeBefore, memoTreeAfter, memoKey, otherMemoKey, otherMemoPayload]

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
  unfold Entrypoint.run Entrypoint.evalReturns
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

/-- The selected disclosure checks and the checked circuit both reduce for
the explicit toy context and admitted example below. -/
theorem clear_memos_disclosure_is_admitted :
    (Disclosure.entrypoint clearMemosEntry).isOk = Bool.true := by
  have valid : Disclosure.entrypoint clearMemosEntry = .ok () := by
    with_unfolding_all rfl
  rw [valid]
  rfl

theorem clear_memos_checked_circuit_accepts_example :
    clearMemosEntry.circuit.run memoContext (inputs 5 zero32 zero32) =
      .ok expectedOutputs := by
  with_unfolding_all rfl

/-- Full source execution on the declared state clears its nonempty memo list,
preserves the sibling list, and returns the checked identity-key coordinates.
All values reduce in the kernel under `memoContext`, the explicit toy oracle. -/
theorem clear_memos_actual_success_on_admitted_example :
    clearMemosEntry.run memoContext (inputs 5 zero32 zero32) canonicalAdmittedState =
      .ok (expectedOutputs, expectedClearedState) := by
  with_unfolding_all rfl

theorem clear_memos_actual_two_secret_success :
    clearMemosEntry.run memoContext (inputs 5 two32 two32) canonicalAdmittedState =
      .ok (expectedOutputs, expectedClearedState) := by
  with_unfolding_all rfl

/-- A stale epoch reaches the source effects and fails their guard. -/
theorem clear_memos_actual_stale_epoch_rejection :
    clearMemosEntry.run memoContext (inputs 4 zero32 zero32) canonicalAdmittedState =
      .error "state transition guard failed" := by
  with_unfolding_all rfl

/-- A wrong account secret fails the checked source constraint. -/
theorem clear_memos_actual_wrong_account_secret_rejection :
    clearMemosEntry.run memoContext (inputs 5 one32 zero32) canonicalAdmittedState =
      .error "circuit constraint failed" := by
  with_unfolding_all rfl

/-- A wrong encryption secret derives a nonmatching key and fails the source
key-coordinate guard after the circuit succeeds. -/
theorem clear_memos_actual_wrong_encryption_secret_rejection :
    clearMemosEntry.run memoContext (inputs 5 zero32 one32) canonicalAdmittedState =
      .error "state transition guard failed" := by
  with_unfolding_all rfl

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

/-- Exact finite invocation domain for this source-model audit. It includes two
credential pairs accepted by the toy equations, one wrong account secret, one
wrong encryption secret and a stale-epoch call. The first four calls expose
accountId zero32 and epoch 5. The domain does not claim coverage of arbitrary
wallet secrets. -/
def memoInvariant (state : LedgerState) : Prop :=
  state = canonicalAdmittedState ∨ state = expectedClearedState

def memoAdmittedInputs (env : EvalEnv) : Prop :=
  env = inputs 5 zero32 zero32 ∨ env = inputs 5 two32 two32 ∨
  env = inputs 5 one32 zero32 ∨ env = inputs 5 zero32 one32 ∨
  env = inputs 4 zero32 zero32

def memoSpecification : Specification := {
  initial := fun state => state = canonicalAdmittedState
  invariant := memoInvariant
  precondition := fun ctx env state =>
    ctx = memoContext ∧ memoInvariant state ∧ memoAdmittedInputs env
  enabled := fun ctx env state =>
    ctx = memoContext ∧ memoInvariant state ∧
      (env = inputs 5 zero32 zero32 ∨ env = inputs 5 two32 two32)
  postcondition := fun _ _ _ outputs after =>
    outputs = expectedOutputs ∧ after = expectedClearedState
}

/-- The registered subject names the selected source contract entry at index 6,
which is definitionally the checked `clearMemosEntry` used above. -/
def memoSubject : Subject := {
  contract := OpenZeppelinPort.ConfidentialToken
  entrypoint := ⟨6, by decide⟩
  specification := memoSpecification
}

theorem memoSubject_entry : memoSubject.entry = clearMemosEntry := by rfl

def memoPolicy : AuditPolicy := {
  subject := memoSubject
  privacy := { releases := .none, scope := .successfulOnly }
  functionalGuarantee := "On the explicit finite toy invocation domain, successful clearMemos calls return only the checked identity key coordinates, clear the selected nonempty memo list, preserve the sibling and all other state, and retain the memo invariant. Wrong-secret and stale-epoch inputs remain admitted and reject."
  privacyGuarantee := "For admitted invocations with equal public source bindings, identical toy context and ledger, successful outcomes agree. Failure channels, provider traffic, proof bytes, deployed behavior and production cryptography are outside this source-model theorem."
}

theorem admitted_good_run (state : LedgerState)
    (stateAdmitted : memoInvariant state) (env : EvalEnv)
    (inputAdmitted : env = inputs 5 zero32 zero32 ∨ env = inputs 5 two32 two32) :
    clearMemosEntry.run memoContext env state = .ok (expectedOutputs, expectedClearedState) := by
  rcases stateAdmitted with before | after
  · subst state
    rcases inputAdmitted with first | second <;> subst env <;> with_unfolding_all rfl
  · subst state
    rcases inputAdmitted with first | second <;> subst env <;> with_unfolding_all rfl

theorem admitted_wrong_account_fails (state : LedgerState)
    (stateAdmitted : memoInvariant state) :
    clearMemosEntry.run memoContext (inputs 5 one32 zero32) state =
      .error "circuit constraint failed" := by
  rcases stateAdmitted with before | after <;> subst state <;> with_unfolding_all rfl

theorem admitted_wrong_encryption_fails (state : LedgerState)
    (stateAdmitted : memoInvariant state) :
    clearMemosEntry.run memoContext (inputs 5 zero32 one32) state =
      .error "state transition guard failed" := by
  rcases stateAdmitted with before | after <;> subst state <;> with_unfolding_all rfl

theorem admitted_stale_epoch_fails (state : LedgerState)
    (stateAdmitted : memoInvariant state) :
    clearMemosEntry.run memoContext (inputs 4 zero32 zero32) state =
      .error "state transition guard failed" := by
  rcases stateAdmitted with before | after <;> subst state <;> with_unfolding_all rfl

/-- Full functional obligation for the admitted source model. Wrong-secret
attempts remain in the precondition, while `enabled` names the two successful
credential examples required by progress. -/
theorem memoFunctional : FunctionalObligation memoPolicy := by
  change Correctness memoSubject
  constructor
  · intro before initial
    left
    exact initial
  · intro ctx env before outputs after invariant admitted success
    change memoInvariant before at invariant
    change ctx = memoContext ∧ memoInvariant before ∧ memoAdmittedInputs env at admitted
    rcases admitted with ⟨rfl, stateAdmitted, inputAdmitted⟩
    change clearMemosEntry.run memoContext env before = .ok (outputs, after) at success
    have successfulInput :
        env = inputs 5 zero32 zero32 ∨ env = inputs 5 two32 two32 := by
      rcases inputAdmitted with first | second | wrongAccount | wrongEncryption | staleEpoch
      · exact Or.inl first
      · exact Or.inr second
      · subst env
        rw [admitted_wrong_account_fails before stateAdmitted] at success
        contradiction
      · subst env
        rw [admitted_wrong_encryption_fails before stateAdmitted] at success
        contradiction
      · subst env
        rw [admitted_stale_epoch_fails before stateAdmitted] at success
        contradiction
    have actual := admitted_good_run before stateAdmitted env successfulInput
    rw [actual] at success
    cases success
    constructor
    · exact ⟨rfl, rfl⟩
    · right
      rfl
  · intro ctx env before _invariant admitted enabled
    change ctx = memoContext ∧ memoInvariant before ∧ memoAdmittedInputs env at admitted
    rcases admitted with ⟨rfl, _, _⟩
    change memoContext = memoContext ∧ memoInvariant before ∧
      (env = inputs 5 zero32 zero32 ∨ env = inputs 5 two32 two32) at enabled
    rcases enabled with ⟨_, stateAdmitted, inputAdmitted⟩
    exact ⟨expectedOutputs, expectedClearedState,
      admitted_good_run before stateAdmitted env inputAdmitted⟩
  · refine ⟨memoContext, inputs 5 zero32 zero32, canonicalAdmittedState, rfl, ?_, ?_⟩
    · exact ⟨rfl, Or.inl rfl, Or.inl rfl⟩
    · exact ⟨rfl, Or.inl rfl, Or.inl rfl⟩

/-- The exact API-level successful-only privacy obligation quantifies over every
admitted invocation pair. The precondition fixes the explicit toy context and
canonical ledger invariant. Its finite private-input domain includes both
wrong-secret rejection cases. -/
theorem memoPrivacy : PrivacyObligation memoPolicy := by
  change PrivacyCorrect memoSubject memoPolicy.privacy
  unfold PrivacyCorrect
  intro left right leftAdmitted rightAdmitted equivalent _release covered
  rcases left with ⟨leftContext, leftInputs, leftState⟩
  rcases right with ⟨rightContext, rightInputs, rightState⟩
  change leftContext = rightContext ∧ leftState = rightState ∧
    publicBindings leftInputs = publicBindings rightInputs at equivalent
  obtain ⟨contextEq, stateEq, publicEq⟩ := equivalent
  subst rightContext rightState
  change memoInvariant leftState ∧
    (leftContext = memoContext ∧ memoInvariant leftState ∧ memoAdmittedInputs leftInputs) at leftAdmitted
  change memoInvariant leftState ∧
    (leftContext = memoContext ∧ memoInvariant leftState ∧ memoAdmittedInputs rightInputs) at rightAdmitted
  rcases leftAdmitted with ⟨leftInvariant, ⟨leftContextEq, _, leftInputDomain⟩⟩
  rcases rightAdmitted with ⟨rightInvariant, ⟨_, _, rightInputDomain⟩⟩
  subst leftContext
  change (∃ outputs state, clearMemosEntry.run memoContext leftInputs leftState = .ok (outputs, state)) ∧
    (∃ outputs state, clearMemosEntry.run memoContext rightInputs leftState = .ok (outputs, state)) at covered
  obtain ⟨leftOutputs, leftAfter, leftSuccess⟩ := covered.1
  obtain ⟨rightOutputs, rightAfter, rightSuccess⟩ := covered.2
  change clearMemosEntry.run memoContext leftInputs leftState = .ok (leftOutputs, leftAfter) at leftSuccess
  change clearMemosEntry.run memoContext rightInputs leftState = .ok (rightOutputs, rightAfter) at rightSuccess
  have leftSuccessfulInput :
      leftInputs = inputs 5 zero32 zero32 ∨ leftInputs = inputs 5 two32 two32 := by
    rcases leftInputDomain with first | second | wrongAccount | wrongEncryption | staleEpoch
    · exact Or.inl first
    · exact Or.inr second
    · subst leftInputs
      rw [admitted_wrong_account_fails leftState leftInvariant] at leftSuccess
      contradiction
    · subst leftInputs
      rw [admitted_wrong_encryption_fails leftState leftInvariant] at leftSuccess
      contradiction
    · subst leftInputs
      rw [admitted_stale_epoch_fails leftState leftInvariant] at leftSuccess
      contradiction
  have rightSuccessfulInput :
      rightInputs = inputs 5 zero32 zero32 ∨ rightInputs = inputs 5 two32 two32 := by
    rcases rightInputDomain with first | second | wrongAccount | wrongEncryption | staleEpoch
    · exact Or.inl first
    · exact Or.inr second
    · subst rightInputs
      rw [admitted_wrong_account_fails leftState rightInvariant] at rightSuccess
      contradiction
    · subst rightInputs
      rw [admitted_wrong_encryption_fails leftState rightInvariant] at rightSuccess
      contradiction
    · subst rightInputs
      rw [admitted_stale_epoch_fails leftState rightInvariant] at rightSuccess
      contradiction
  rw [admitted_good_run leftState leftInvariant leftInputs leftSuccessfulInput] at leftSuccess
  rw [admitted_good_run leftState rightInvariant rightInputs rightSuccessfulInput] at rightSuccess
  cases leftSuccess
  cases rightSuccess
  change clearMemosEntry.run memoContext leftInputs leftState =
    clearMemosEntry.run memoContext rightInputs leftState
  rw [admitted_good_run leftState leftInvariant leftInputs leftSuccessfulInput,
    admitted_good_run leftState rightInvariant rightInputs rightSuccessfulInput]

/-- With the same admitted source inputs and state, an all-outcomes policy
fails because status reveals a wrong private encryption secret. -/
theorem memoAllOutcomesPrivacyFails :
    ¬ PrivacyCorrect memoSubject { releases := .none, scope := .allOutcomes } := by
  intro privacy
  let accepted : Invocation := ⟨memoContext, inputs 5 zero32 zero32, canonicalAdmittedState⟩
  let wrongEncryption : Invocation := ⟨memoContext, inputs 5 zero32 one32, canonicalAdmittedState⟩
  have acceptedAdmitted : memoSubject.admissible accepted := by
    change memoInvariant canonicalAdmittedState ∧
      (memoContext = memoContext ∧ memoInvariant canonicalAdmittedState ∧
        memoAdmittedInputs (inputs 5 zero32 zero32))
    exact ⟨Or.inl rfl, ⟨rfl, Or.inl rfl, Or.inl rfl⟩⟩
  have wrongEncryptionAdmitted : memoSubject.admissible wrongEncryption := by
    change memoInvariant canonicalAdmittedState ∧
      (memoContext = memoContext ∧ memoInvariant canonicalAdmittedState ∧
        memoAdmittedInputs (inputs 5 zero32 one32))
    exact ⟨Or.inl rfl, ⟨rfl, Or.inl rfl, Or.inr (Or.inr (Or.inr (Or.inl rfl)))⟩⟩
  have publicEquivalent : memoSubject.publicEquivalent accepted wrongEncryption := by
    change memoContext = memoContext ∧ canonicalAdmittedState = canonicalAdmittedState ∧
      publicBindings (inputs 5 zero32 zero32) = publicBindings (inputs 5 zero32 one32)
    exact ⟨rfl, rfl, by decide⟩
  have outcomeEquality := privacy accepted wrongEncryption acceptedAdmitted
    wrongEncryptionAdmitted publicEquivalent trivial (by simp [ObservationScope.covers])
  change clearMemosEntry.run memoContext (inputs 5 zero32 zero32) canonicalAdmittedState =
    clearMemosEntry.run memoContext (inputs 5 zero32 one32) canonicalAdmittedState at outcomeEquality
  rw [clear_memos_actual_success_on_admitted_example,
    clear_memos_actual_wrong_encryption_secret_rejection] at outcomeEquality
  cases outcomeEquality

#noctium_register_functional memoFunctional for memoPolicy
#noctium_register_privacy memoPrivacy for memoPolicy

/-- Both toy credential pairs have the same exact source result on the admitted
example. This is successful-result equality, not a claim about real hashing. -/
theorem clear_memos_actual_successful_only_source_privacy :
    publicBindings (inputs 5 zero32 zero32) = publicBindings (inputs 5 two32 two32) ∧
    clearMemosEntry.run memoContext (inputs 5 zero32 zero32) canonicalAdmittedState =
      clearMemosEntry.run memoContext (inputs 5 two32 two32) canonicalAdmittedState := by
  constructor
  · exact pinned_pairs_have_same_public_bindings.1
  · rw [clear_memos_actual_success_on_admitted_example,
      clear_memos_actual_two_secret_success]

/-- The status observer separates the accepted example from a wrong account
secret even though their public source bindings match. -/
theorem clear_memos_actual_failure_observer_distinguishes_wrong_account :
    publicBindings (inputs 5 zero32 zero32) = publicBindings (inputs 5 one32 zero32) ∧
    succeeded (clearMemosEntry.run memoContext
      (inputs 5 zero32 zero32) canonicalAdmittedState) = _root_.Bool.true ∧
    succeeded (clearMemosEntry.run memoContext
      (inputs 5 one32 zero32) canonicalAdmittedState) = _root_.Bool.false := by
  constructor
  · exact pinned_pairs_have_same_public_bindings.2
  constructor
  · rw [clear_memos_actual_success_on_admitted_example]
    rfl
  · rw [clear_memos_actual_wrong_account_secret_rejection]
    rfl

/-- The all-outcomes status observer also distinguishes a wrong encryption
secret. Both invocations expose the same public source inputs. -/
theorem clear_memos_actual_failure_observer_distinguishes_wrong_encryption :
    publicBindings (inputs 5 zero32 zero32) = publicBindings (inputs 5 zero32 one32) ∧
    succeeded (clearMemosEntry.run memoContext
      (inputs 5 zero32 zero32) canonicalAdmittedState) = _root_.Bool.true ∧
    succeeded (clearMemosEntry.run memoContext
      (inputs 5 zero32 one32) canonicalAdmittedState) = _root_.Bool.false := by
  constructor
  · decide
  constructor
  · rw [clear_memos_actual_success_on_admitted_example]
    rfl
  · rw [clear_memos_actual_wrong_encryption_secret_rejection]
    rfl

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
#print axioms clear_memos_actual_success_on_admitted_example
#print axioms clear_memos_actual_two_secret_success
#print axioms clear_memos_actual_stale_epoch_rejection
#print axioms clear_memos_actual_wrong_account_secret_rejection
#print axioms clear_memos_actual_wrong_encryption_secret_rejection
#print axioms clear_memos_actual_successful_only_source_privacy
#print axioms clear_memos_actual_failure_observer_distinguishes_wrong_account
#print axioms clear_memos_actual_failure_observer_distinguishes_wrong_encryption
#print axioms memoFunctional
#print axioms memoPrivacy
#print axioms memoAllOutcomesPrivacyFails
#print axioms successful_projection_from_checked_steps
#print axioms stale_epoch_rejection_from_effects
#print axioms successful_only_source_privacy_for_pinned_pair
#print axioms wrong_account_secret_rejection_from_circuit
#print axioms wrong_encryption_secret_rejection_from_effects
#print axioms failure_observer_distinguishes_wrong_account_secret

end OpenZeppelinPort.ConfidentialTokenMemoVerification
