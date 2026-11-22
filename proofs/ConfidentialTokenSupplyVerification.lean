import examples.openzeppelin.ConfidentialToken
import Noctium.Verification

open Noctium Noctium.Verification

namespace OpenZeppelinPort.ConfidentialTokenSupplyVerification

def supplyMaximum : Nat := 2 ^ 128 - 1

theorem supplyMaximum_within_scalar_policy : supplyMaximum ≤ ScalarPolicy.maxUint := by decide

def entrypointIndex : Fin ConfidentialToken.entrypoints.length := ⟨7, by decide⟩

def sourceEntry : Entrypoint := ConfidentialToken.entrypoints[entrypointIndex]

/-- "entrypoint":"totalSupply","index":7,"mismatchedPolicyPairs":[],"missingRoles":["functional","privacy"] -/
#guard_msgs (substring := true) in
#noctium_source_proof_coverage ConfidentialToken

theorem source_entrypoint_name : sourceEntry.name = "totalSupply" := by decide

theorem source_entrypoint_location :
    sourceEntry.span.file = "examples/openzeppelin/ConfidentialToken.lean" ∧
    sourceEntry.span.line = 767 := by decide

theorem source_entrypoint_has_no_inputs : sourceEntry.circuit.inputs = [] := by decide

theorem source_entrypoint_reads_only_supply :
    sourceEntry.effects = [.readCell "totalSupply" "currentSupply" (.uint supplyMaximum)] := by
  rfl

theorem source_entrypoint_effect_guards_default : sourceEntry.effectGuards = [none] := by
  rfl

theorem source_entrypoint_returns_supply_at_source :
    sourceEntry.returns.map (fun out => (out.name, out.ty, out.span.line)) =
      [("supply", .uint supplyMaximum, 769)] := by decide

theorem source_entrypoint_return_exact :
    sourceEntry.returns = [{
      name := "supply"
      ty := .uint supplyMaximum
      value := .ref "currentSupply"
      span := {file := "examples/openzeppelin/ConfidentialToken.lean", line := 769, column := 5}
    }] := by
  rfl

theorem source_supply_state_is_public_u128 :
    (ConfidentialToken.state.find? (·.name == "totalSupply")).map (·.kind) =
      some (.cell (.uint supplyMaximum)) := by decide

def sourceInitializesFlag : _root_.Bool :=
  match ConfidentialToken.constructor with
  | none => Bool.false
  | some ctor => ctor.initializers.any fun item =>
      item.state == "initialized" && item.type == .scalar .bool &&
        match item.value with
        | .scalar (.bool Bool.true) => Bool.true
        | _ => Bool.false

def sourceInitializesSupply : _root_.Bool :=
  match ConfidentialToken.constructor with
  | none => Bool.false
  | some ctor => ctor.initializers.any (·.state == "totalSupply")

theorem source_constructor_initializes_flag : sourceInitializesFlag = Bool.true := by decide

theorem source_constructor_leaves_supply_at_default : sourceInitializesSupply = Bool.false := by decide

def settlementEmpty (state : LedgerState) : Prop :=
  state.unshieldedInputs = [] ∧ state.unshieldedOutputs = [] ∧
    state.unshieldedSpendClaims = []

def supplyInvariant (state : LedgerState) : Prop :=
  ∃ supply, state.cells.lookup "totalSupply" = some (.uint supplyMaximum supply) ∧
    supply ≤ supplyMaximum ∧ state.cells.lookup "initialized" = some (.bool Bool.true) ∧
    settlementEmpty state

/-- A concrete initialized zero state in the source evaluator's ledger model.
This scoped model witness does not prove that the host constructor yields it. -/
def initializedZeroModelState : LedgerState := {
  cells := [
    ("name", .opaqueString "Noctium Token"),
    ("symbol", .opaqueString "NOC"),
    ("decimals", .uint 255 6),
    ("initialized", .bool Bool.true),
    ("totalSupply", .uint supplyMaximum 0)
  ]
  trees := [
    ("encryptionKeys", .map []),
    ("balances", .map []),
    ("pending", .map []),
    ("memos", .map []),
    ("creditEpochs", .map []),
    ("escrow", .map []),
    ("escrowSpendEpochs", .map [])
  ]
}

def specification : Specification := {
  initial := fun state => state = initializedZeroModelState
  invariant := supplyInvariant
  precondition := fun ctx inputs _ => ctx.modulus = Field.modulus ∧ inputs = []
  enabled := fun ctx inputs state =>
    ctx.modulus = Field.modulus ∧ inputs = [] ∧ supplyInvariant state
  postcondition := fun _ inputs before outputs after =>
    inputs = [] ∧ ∃ supply,
      before.cells.lookup "totalSupply" = some (.uint supplyMaximum supply) ∧
      outputs = [("supply", .uint supplyMaximum supply)] ∧ after = before
}

def subject : Subject := {
  contract := ConfidentialToken
  entrypoint := entrypointIndex
  specification
}

def policy : AuditPolicy := {
  subject
  privacy := { releases := .none, scope := .allOutcomes }
  functionalGuarantee :=
    "For initialized canonical source states at the pinned modulus with empty settlement buffers, the enabled getter returns the exact public UInt128 totalSupply cell and preserves the full source ledger state. A zero-valued source-model initial state demonstrates nonvacuity; host initialization is separate evidence."
  privacyGuarantee :=
    "For admitted source states, equal contexts and identical public ledger state with empty inputs yield equal full source outcomes, including returned environment and final ledger state or the error string. The returned value equals the public totalSupply cell, so it reveals no additional value. This source model does not establish native or deployed privacy."
}

theorem subject_entry_is_sourceEntry : subject.entry = sourceEntry := by rfl

theorem sourceEntry_disclosure_valid : Disclosure.entrypoint sourceEntry = .ok () := by
  with_unfolding_all rfl

theorem sourceEntry_circuit_empty (ctx : EvalContext) :
    sourceEntry.circuit.run ctx [] = .ok [] := by
  with_unfolding_all rfl

theorem read_supply_effect (ctx : EvalContext) (before : LedgerState) (supply : Nat)
    (hModulus : ctx.modulus = Field.modulus)
    (hCell : before.cells.lookup "totalSupply" = some (.uint supplyMaximum supply))
    (hBound : supply ≤ supplyMaximum) :
    runEffectsWithGuardsAndEnv ctx sourceEntry.effects sourceEntry.effectGuards [] before =
      .ok ([ ("currentSupply", .uint supplyMaximum supply) ], before) := by
  have hNoNativeOverflow : supplyMaximum ≤ ScalarPolicy.maxUint := by decide
  have hMaximumBelowField : supplyMaximum < Field.modulus := by decide
  have hCanonical : supply < ctx.modulus := by
    calc
      supply ≤ supplyMaximum := hBound
      _ < Field.modulus := hMaximumBelowField
      _ = ctx.modulus := hModulus.symm
  rw [source_entrypoint_reads_only_supply]
  simp only [source_entrypoint_effect_guards_default, runEffectsWithGuardsAndEnv,
    List.all_cons, Option.isNone_none, Bool.true_and, List.all_nil, ite_true]
  simp [runEffectsWithEnv, hCell, Value.as, supplyMaximum]
  split
  · rename_i hInvalid
    change (supplyMaximum ≤ ScalarPolicy.maxUint && supply ≤ supplyMaximum &&
      supply < ctx.modulus) = Bool.false at hInvalid
    simp [hNoNativeOverflow, hBound, hCanonical] at hInvalid
  · rfl

theorem sourceEntry_runs (ctx : EvalContext) (before : LedgerState) (supply : Nat)
    (context : ctx.modulus = Field.modulus)
    (hCell : before.cells.lookup "totalSupply" = some (.uint supplyMaximum supply))
    (bound : supply ≤ supplyMaximum) (settlement : settlementEmpty before) :
    sourceEntry.run ctx [] before =
      .ok ([("supply", .uint supplyMaximum supply)], before) := by
  have stateAfterClear :
      {before with unshieldedInputs := [], unshieldedOutputs := [], unshieldedSpendClaims := []} = before := by
    rcases settlement with ⟨hInputs, hOutputs, hClaims⟩
    cases before with
    | mk cells maps trees events shieldedMints unshieldedMints unshieldedInputs unshieldedOutputs unshieldedSpendClaims =>
      simp_all
  have maximumLtField : supplyMaximum < Field.modulus := by decide
  have supplyLt : supply < ctx.modulus := by
    rw [context]
    exact Nat.lt_of_le_of_lt bound maximumLtField
  have supplyCanonical :
      (supplyMaximum ≤ ScalarPolicy.maxUint && supply ≤ supplyMaximum &&
        supply < ctx.modulus) = Bool.true := by
    simp [supplyMaximum_within_scalar_policy, bound, supplyLt]
  have supplyRefEvaluates :
      (Expr.ref "currentSupply" : Expr (.uint supplyMaximum)).eval ctx
        [("currentSupply", .uint supplyMaximum supply)] = .ok supply := by
    simp [Expr.eval, List.lookup, Value.as, canonical_eq, supplyCanonical]
    rfl
  have effectsRun :
      runEffectsWithGuardsAndEnv ctx sourceEntry.effects sourceEntry.effectGuards [] before =
        .ok ([ ("currentSupply", .uint supplyMaximum supply) ], before) := by
    exact read_supply_effect ctx before supply context hCell bound
  unfold Entrypoint.run
  rw [sourceEntry_disclosure_valid]
  dsimp only [Bind.bind, Except.bind, Except.pure]
  rw [sourceEntry_circuit_empty]
  dsimp only [Bind.bind, Except.bind, Except.pure]
  simp only [List.nil_append]
  rw [stateAfterClear, effectsRun, source_entrypoint_return_exact]
  simp [supplyRefEvaluates, canonical_eq, supplyCanonical, Value.pack]
  rfl

theorem initialized_zero_model_invariant : supplyInvariant initializedZeroModelState := by
  refine ⟨0, ?_, Nat.zero_le _, ?_, ?_⟩
  · simp [initializedZeroModelState, supplyMaximum, List.lookup]
  · simp [initializedZeroModelState, List.lookup]
  · simp [settlementEmpty, initializedZeroModelState]

theorem initialized_zero_model_getter_accepts :
    sourceEntry.run
      {modulus := Field.modulus, poseidon2 := fun _ _ _ => .error "unused"}
      [] initializedZeroModelState =
      .ok ([ ("supply", .uint supplyMaximum 0) ], initializedZeroModelState) := by
  exact sourceEntry_runs _ initializedZeroModelState 0 rfl
    (by simp [initializedZeroModelState, supplyMaximum, List.lookup]) (by decide)
    (by simp [settlementEmpty, initializedZeroModelState])

def malformedMissingSupply : LedgerState := {initializedZeroModelState with
  cells := [("initialized", .bool Bool.true)]
}

theorem malformed_missing_supply_effect_rejected :
    runEffectsWithGuardsAndEnv
      {modulus := Field.modulus, poseidon2 := fun _ _ _ => .error "unused"}
      sourceEntry.effects sourceEntry.effectGuards [] malformedMissingSupply =
        .error "missing state cell 'totalSupply'" := by
  rw [source_entrypoint_reads_only_supply, source_entrypoint_effect_guards_default]
  rfl

theorem malformed_missing_supply_clear_is_identity :
    {malformedMissingSupply with
      unshieldedInputs := [], unshieldedOutputs := [], unshieldedSpendClaims := []} =
      malformedMissingSupply := by
  rfl

theorem missing_supply_cell_rejected :
    sourceEntry.run
      {modulus := Field.modulus, poseidon2 := fun _ _ _ => .error "unused"}
      [] malformedMissingSupply = .error "missing state cell 'totalSupply'" := by
  unfold Entrypoint.run
  rw [sourceEntry_disclosure_valid]
  dsimp only [Bind.bind, Except.bind, Except.pure]
  rw [sourceEntry_circuit_empty]
  dsimp only [Bind.bind, Except.bind, Except.pure]
  simp only [List.nil_append]
  rw [malformed_missing_supply_clear_is_identity]
  rw [malformed_missing_supply_effect_rejected]

def replaySupply (ctx : EvalContext) (state : LedgerState) :
    Except String (EvalEnv × LedgerState) := do
  let (_, afterFirst) ← sourceEntry.run ctx [] state
  sourceEntry.run ctx [] afterFirst

theorem source_getter_replay_accepts (ctx : EvalContext) (before : LedgerState)
    (supply : Nat) (context : ctx.modulus = Field.modulus)
    (hCell : before.cells.lookup "totalSupply" = some (.uint supplyMaximum supply))
    (bound : supply ≤ supplyMaximum) (settlement : settlementEmpty before) :
    replaySupply ctx before =
      .ok ([("supply", .uint supplyMaximum supply)], before) := by
  unfold replaySupply
  rw [sourceEntry_runs ctx before supply context hCell bound settlement]
  dsimp only [Bind.bind, Except.bind, Except.pure]
  rw [sourceEntry_runs ctx before supply context hCell bound settlement]

theorem functional : FunctionalObligation policy := by
  constructor
  · intro before initial
    subst before
    exact initialized_zero_model_invariant
  · intro ctx inputs before outputs after hInvariant pre success
    obtain ⟨supply, hCell, bound, hInitialized, settlement⟩ := hInvariant
    obtain ⟨context, inputsEmpty⟩ := pre
    subst inputs
    have accepted := sourceEntry_runs ctx before supply context hCell bound settlement
    change sourceEntry.run ctx [] before = .ok (outputs, after) at success
    rw [accepted] at success
    have invariantAfter : supplyInvariant before :=
      ⟨supply, hCell, bound, hInitialized, settlement⟩
    cases success
    exact ⟨⟨rfl, ⟨supply, hCell, rfl, rfl⟩⟩, invariantAfter⟩
  · intro ctx inputs before hInvariant pre enabled
    obtain ⟨supply, hCell, bound, hInitialized, settlement⟩ := hInvariant
    obtain ⟨context, inputsEmpty⟩ := pre
    subst inputs
    exact ⟨[("supply", .uint supplyMaximum supply)], before,
      sourceEntry_runs ctx before supply context hCell bound settlement⟩
  · exact ⟨
      {modulus := Field.modulus, poseidon2 := fun _ _ _ => .error "unused"},
      [], initializedZeroModelState, rfl, ⟨rfl, rfl⟩,
      ⟨rfl, rfl, initialized_zero_model_invariant⟩⟩

theorem privacy : PrivacyObligation policy := by
  intro left right leftAdmissible rightAdmissible equivalent _release _covered
  rcases left with ⟨leftContext, leftInputs, leftState⟩
  rcases right with ⟨rightContext, rightInputs, rightState⟩
  change supplyInvariant leftState ∧
      (leftContext.modulus = Field.modulus ∧ leftInputs = []) at leftAdmissible
  change supplyInvariant rightState ∧
      (rightContext.modulus = Field.modulus ∧ rightInputs = []) at rightAdmissible
  rcases leftAdmissible with ⟨leftInvariant, leftPre⟩
  rcases rightAdmissible with ⟨rightInvariant, rightPre⟩
  rcases equivalent with ⟨contextEq, stateEq, _publicInputsEq⟩
  obtain ⟨_leftModulus, leftInputsEmpty⟩ := leftPre
  obtain ⟨_rightModulus, rightInputsEmpty⟩ := rightPre
  rw [leftInputsEmpty, rightInputsEmpty]
  change leftContext = rightContext at contextEq
  change leftState = rightState at stateEq
  change sourceEntry.run leftContext [] leftState =
    sourceEntry.run rightContext [] rightState
  rw [contextEq, stateEq]

#noctium_register_functional functional for policy
#noctium_register_privacy privacy for policy

/-- "entrypoint":"totalSupply","index":7,"mismatchedPolicyPairs":[],"missingRoles":[],"policyPairing":"matched" -/
#guard_msgs (substring := true) in
#noctium_source_proof_coverage ConfidentialToken

run_cmd do
  let environment ← Lean.getEnv
  match Audit.check environment ``policy ``functional .privacy with
  | .error "wrong_obligation" => pure ()
  | _ => throwError "functional proof accepted for privacy role"
  match Audit.check environment ``policy ``functional .functional with
  | .ok _ => pure ()
  | _ => throwError "source functional proof rejected under its exact policy"

#print axioms functional
#print axioms privacy

end OpenZeppelinPort.ConfidentialTokenSupplyVerification
