import proofs.PrivateClaim
import Noctium.Verification

namespace Noctium.PrivateClaimVerification
open PrivateClaimProofs Verification

private theorem entrypointSuccessHasCircuitSuccess (ctx : EvalContext) (target : Entrypoint)
    (env : EvalEnv) (state : LedgerState) (outputs : EvalEnv) (after : LedgerState)
    (valid : Disclosure.entrypoint target = .ok ())
    (success : target.run ctx env state = .ok (outputs, after)) :
    ∃ circuitOutputs, target.circuit.run ctx env = .ok circuitOutputs := by
  unfold Entrypoint.run at success
  rw [valid] at success
  dsimp only [Bind.bind, Except.bind, Except.pure] at success
  cases hCircuit : target.circuit.run ctx env with
  | error message => rw [hCircuit] at success; contradiction
  | ok circuitOutputs => exact ⟨circuitOutputs, rfl⟩

/-- Accepted executions establish authorization even when Pre does not assume it. -/
theorem accepted_circuit (ctx : EvalContext) (input : InputValues)
    (canonical : CanonicalInputs ctx input) (before after : LedgerState) (outputs : EvalEnv)
    (success : claimEntry.run ctx (inputEnvironment input) before = .ok (outputs, after)) :
    claimEntry.circuit.run ctx (inputEnvironment input) = .ok [("nullifier", .native input.nullifier)] := by
  obtain ⟨circuitOutputs, result⟩ := entrypointSuccessHasCircuitSuccess ctx claimEntry
    (inputEnvironment input) before outputs after entry_disclosure_valid success
  exact result.trans (congrArg Except.ok
    (successful_source_output ctx input canonical circuitOutputs result))

theorem effects_reject_existing (ctx : EvalContext) (input : InputValues)
    (values : List (Nat × _root_.Bool)) (canonical : CanonicalInputs ctx input)
    (value : Value) (present : (typedEntries values).lookup (.native input.nullifier) = some value) :
    runEffectsWithEnv ctx claimEntry.effects (("nullifier", .native input.nullifier) :: inputEnvironment input)
      (state input.root input.campaign values) = .error "state map key already present" := by
  have hr := Nat.not_le.mpr canonical.root
  have hc := Nat.not_le.mpr canonical.campaign
  have hn := Nat.not_le.mpr canonical.nullifier
  simp! [runEffectsWithEnv, runEffectWithEnv, claimEntry, PrivateClaim, state, Expr.eval, Value.as, Value.pack,
    inputEnvironment, canonical.root, canonical.campaign, canonical.nullifier,
    hr, hc, hn, present, Except.pure, Except.bind, Except.map]
  rfl

theorem accepted_authorized (ctx : EvalContext) (input : InputValues)
    (canonical : CanonicalInputs ctx input) (root campaign : Nat)
    (values : List (Nat × _root_.Bool)) (hr : root < ctx.modulus) (hc : campaign < ctx.modulus)
    (outputs : EvalEnv) (after : LedgerState)
    (success : claimEntry.run ctx (inputEnvironment input) (state root campaign values) = .ok (outputs, after)) :
    root = input.root ∧ campaign = input.campaign ∧
      (typedEntries values).lookup (.native input.nullifier) = none := by
  have circuit := accepted_circuit ctx input canonical _ _ _ success
  have rootEq : root = input.root := by
    by_cases equal : root = input.root
    · exact equal
    apply False.elim
    have different := equal
    have rejected := wrong_root_claim_rejected ctx (inputEnvironment input) root input.root campaign
      input.nullifier values circuit (by rfl) hr canonical.root different
    rw [success] at rejected
    contradiction
  subst root
  have campaignEq : campaign = input.campaign := by
    by_cases equal : campaign = input.campaign
    · exact equal
    apply False.elim
    have different := equal
    have rejected := wrong_campaign_claim_rejected ctx (inputEnvironment input) input.root campaign
      input.campaign input.nullifier values circuit (by rfl) (by rfl) canonical.root hc canonical.campaign different
    rw [success] at rejected
    contradiction
  subst campaign
  refine ⟨rfl, rfl, ?_⟩
  cases present : (typedEntries values).lookup (.native input.nullifier) with
  | none => rfl
  | some value =>
    have rejected : claimEntry.run ctx (inputEnvironment input) (state input.root input.campaign values) =
        .error "state map key already present" := by
      simp only [Entrypoint.run, entry_disclosure_valid, clear_settlement_state]
      dsimp only [Bind.bind, Except.bind, Except.pure]
      rw [circuit]
      dsimp only [Bind.bind, Except.bind]
      simp only [List.cons_append, List.nil_append]
      rw [claim_entry_run_effects]
      rw [effects_reject_existing ctx input values canonical value present]
    rw [success] at rejected
    contradiction

/-- Initialized canonical public state, independent of the witness/hash oracle. -/
def initial (before : LedgerState) : Prop :=
  ∃ root campaign, root < Field.modulus ∧ campaign < Field.modulus ∧ before = state root campaign []

def invariant (before : LedgerState) : Prop :=
  ∃ root campaign values, before = state root campaign values ∧ StateInvariant fixtureContext root campaign values

/-- Shape and canonical values only. No eligibility, configuration, absence or acceptance premise. -/
def precondition (ctx : EvalContext) (inputs : EvalEnv) (_before : LedgerState) : Prop :=
  ctx.modulus = Field.modulus ∧ ∃ input, inputs = inputEnvironment input ∧ CanonicalInputs ctx input

/-- Progress requires explicit path hashes, configured public inputs and an unused key. -/
def enabled (ctx : EvalContext) (inputs : EvalEnv) (before : LedgerState) : Prop :=
  ∃ input leaf node values, inputs = inputEnvironment input ∧ CanonicalInputs ctx input ∧
    before = state input.root input.campaign values ∧ HashTrace ctx input leaf node ∧
    (typedEntries values).lookup (.native input.nullifier) = none

def postcondition (ctx : EvalContext) (inputs : EvalEnv) (before : LedgerState)
    (outputs : EvalEnv) (after : LedgerState) : Prop :=
  ∃ input values, inputs = inputEnvironment input ∧
    before = state input.root input.campaign values ∧
    (typedEntries values).lookup (.native input.nullifier) = none ∧
    rootExpression.eval ctx inputs = .ok input.root ∧
    nullifierExpression.eval ctx inputs = .ok input.nullifier ∧
    outputs = [("nullifier", .native input.nullifier)] ∧
    after = state input.root input.campaign (recordValues input.nullifier values) ∧
    claimEntry.run ctx inputs after = .error "state map key already present"

def specification : Specification := { initial, invariant, precondition, enabled, postcondition }
def subject : Subject := { contract := PrivateClaim, entrypoint := ⟨0, by decide⟩, specification }
def policy : AuditPolicy := {
  subject
  privacy := { releases := .none, scope := .successfulOnly }
  functionalGuarantee := "Accepted canonical source claims satisfy root/nullifier checks, configured state and absence, record once, preserve invariant, and reject replay. Explicit hash-trace progress."
  privacyGuarantee := "Successful source outcomes agree for equal declared public inputs, identical public state and context. No additional release. Excludes failures, timing, proof bytes and native lowering."
}

theorem subject_entry : subject.entry = claimEntry := by rfl

private theorem transport_invariant (ctx : EvalContext) (hmod : ctx.modulus = Field.modulus)
    (root campaign : Nat) (values : List (Nat × _root_.Bool))
    (old : StateInvariant fixtureContext root campaign values) : StateInvariant ctx root campaign values := by
  refine ⟨?_, ?_, ?_⟩
  · simpa only [hmod, fixtureContext] using old.1
  · simpa only [hmod, fixtureContext] using old.2.1
  · constructor
    · exact old.2.2.uniqueKeys
    · intro item membership
      simpa only [hmod, fixtureContext] using old.2.2.canonicalKeys item membership
    · exact old.2.2.allMarked

private theorem restore_invariant (ctx : EvalContext) (hmod : ctx.modulus = Field.modulus)
    (root campaign : Nat) (values : List (Nat × _root_.Bool))
    (old : StateInvariant ctx root campaign values) : StateInvariant fixtureContext root campaign values := by
  refine ⟨?_, ?_, ?_⟩
  · simpa only [hmod, fixtureContext] using old.1
  · simpa only [hmod, fixtureContext] using old.2.1
  · constructor
    · exact old.2.2.uniqueKeys
    · intro item membership
      simpa only [hmod, fixtureContext] using old.2.2.canonicalKeys item membership
    · exact old.2.2.allMarked

theorem functional : FunctionalObligation policy := by
  constructor
  · intro before ⟨root, campaign, hr, hc, hb⟩
    exact ⟨root, campaign, [], hb, initial_state_invariant fixtureContext root campaign hr hc⟩
  · intro ctx inputs before outputs after inv pre success
    change claimEntry.run ctx inputs before = .ok (outputs, after) at success
    obtain ⟨root, campaign, values, hb, old⟩ := inv
    obtain ⟨hmod, input, hi, canonical⟩ := pre
    subst inputs before
    have current := transport_invariant ctx hmod root campaign values old
    obtain ⟨hr, hc, unspent⟩ := accepted_authorized ctx input canonical root campaign values
      current.1 current.2.1 outputs after success
    subst root campaign
    have exactState := successful_claim_exact_state ctx input values canonical unspent outputs after success
    have hashes := successful_contract_root_and_nullifier ctx input canonical _ _ _ success
    have circuit := accepted_circuit ctx input canonical _ _ _ success
    refine ⟨⟨input, values, rfl, rfl, unspent, hashes.1, hashes.2, exactState.1, exactState.2, ?_⟩, ?_⟩
    · rw [exactState.2, ← recorded_is_canonical_state]
      exact recorded_claim_rejects_replay ctx _ _ _ _ values circuit (by rfl) (by rfl)
        canonical.root canonical.campaign canonical.nullifier
    · exact ⟨input.root, input.campaign, recordValues input.nullifier values, exactState.2,
        restore_invariant ctx hmod _ _ _ (recorded_state_preserves_invariant ctx _ _ _ values canonical.nullifier current)⟩
  · intro ctx inputs before _inv _pre enable
    obtain ⟨input, leaf, node, values, hi, canonical, hb, trace, unspent⟩ := enable
    subst inputs before
    refine ⟨[("nullifier", .native input.nullifier)], recorded input.root input.campaign input.nullifier values, ?_⟩
    exact accepted_claim_transition ctx _ _ _ _ values
      (hash_trace_circuit_accepts ctx input leaf node canonical trace) (by rfl) (by rfl)
      canonical.root canonical.campaign canonical.nullifier unspent
  · refine ⟨fixtureContext, fixtureInputs, state 0 0 [], ?_, ?_, ?_⟩
    · exact ⟨0, 0, by decide, by decide, rfl⟩
    · exact ⟨rfl, fixtureValues, fixture_environment.symm, fixture_canonical⟩
    · exact ⟨fixtureValues, 0, 0, [], fixture_environment.symm, fixture_canonical,
        rfl, fixture_hash_trace, by rfl⟩

/-- The observer uses the public inputs declared by the actual source circuit. -/
theorem actual_public_inputs (input : InputValues) :
    subject.publicInputs (inputEnvironment input) =
      [("root", some (.native input.root)), ("campaign", some (.native input.campaign)),
       ("suppliedNullifier", some (.native input.nullifier))] := by rfl

theorem privacy : PrivacyObligation policy := by
  intro left right leftAdmissible rightAdmissible equivalent _release covered
  rcases left with ⟨ctx, leftInputs, before⟩
  rcases right with ⟨rightCtx, rightInputs, rightBefore⟩
  obtain ⟨contextEq, stateEq, publicEq⟩ := equivalent
  dsimp only at contextEq stateEq publicEq
  subst rightCtx rightBefore
  obtain ⟨leftInv, leftPre⟩ := leftAdmissible
  obtain ⟨_rightInv, rightPre⟩ := rightAdmissible
  obtain ⟨hmod, leftInput, hl, leftCanonical⟩ := leftPre
  obtain ⟨_rightMod, rightInput, hr, rightCanonical⟩ := rightPre
  dsimp only at hl hr
  subst leftInputs rightInputs
  change subject.publicInputs (inputEnvironment leftInput) = subject.publicInputs (inputEnvironment rightInput) at publicEq
  rw [actual_public_inputs, actual_public_inputs] at publicEq
  have rootEq : leftInput.root = rightInput.root := by
    have first := congrArg (fun xs => (xs.headD ("", none)).2) publicEq
    exact Value.native.inj (Option.some.inj first)
  have campaignEq : leftInput.campaign = rightInput.campaign := by
    have second := congrArg (fun xs => (xs.tail.headD ("", none)).2) publicEq
    exact Value.native.inj (Option.some.inj second)
  have nullifierEq : leftInput.nullifier = rightInput.nullifier := by
    have third := congrArg (fun xs => (xs.tail.tail.headD ("", none)).2) publicEq
    exact Value.native.inj (Option.some.inj third)
  obtain ⟨⟨leftOutputs, leftAfter, leftSuccess⟩, ⟨rightOutputs, rightAfter, rightSuccess⟩⟩ := covered
  change claimEntry.run ctx (inputEnvironment leftInput) before = .ok (leftOutputs, leftAfter) at leftSuccess
  change claimEntry.run ctx (inputEnvironment rightInput) before = .ok (rightOutputs, rightAfter) at rightSuccess
  obtain ⟨storedRoot, storedCampaign, values, beforeEq, inv⟩ := leftInv
  change before = state storedRoot storedCampaign values at beforeEq
  subst before
  have current := transport_invariant ctx hmod storedRoot storedCampaign values inv
  obtain ⟨storedRootEq, storedCampaignEq, unspent⟩ := accepted_authorized ctx leftInput leftCanonical
    storedRoot storedCampaign values current.1 current.2.1 leftOutputs leftAfter leftSuccess
  subst storedRoot storedCampaign
  have observations := successful_public_observations_equal ctx leftInput rightInput values
    leftCanonical rightCanonical rootEq campaignEq nullifierEq unspent
    leftOutputs rightOutputs leftAfter rightAfter leftSuccess rightSuccess
  have outputsEq : leftOutputs = rightOutputs := congrArg PublicObservation.outputs observations
  have afterEq : leftAfter = rightAfter := congrArg PublicObservation.state observations
  change claimEntry.run ctx (inputEnvironment leftInput) _ = claimEntry.run ctx (inputEnvironment rightInput) _
  rw [leftSuccess, rightSuccess, outputsEq, afterEq]

#noctium_register_functional functional for policy
#noctium_register_privacy privacy for policy
#print axioms functional
#print axioms privacy

end Noctium.PrivateClaimVerification
