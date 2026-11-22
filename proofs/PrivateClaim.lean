import examples.PrivateClaim
import Noctium.Claim

namespace Noctium.PrivateClaimProofs

def claimEntry : Entrypoint :=
  PrivateClaim.entrypoints.headD {name := "missing", circuit := {name := "missing"}}

theorem claim_entry_guards_all_none :
    claimEntry.effectGuards = List.replicate claimEntry.effects.length none := by
  with_unfolding_all rfl

theorem runEffectsWithGuardsAndEnv_all_none (ctx : EvalContext) (effects : List Effect)
    (guards : List (Option (Expr .bool))) (env : EvalEnv) (state : LedgerState)
    (hlen : guards.isEmpty || guards.length = effects.length)
    (hnone : guards.all Option.isNone) :
    runEffectsWithGuardsAndEnv ctx effects guards env state = runEffectsWithEnv ctx effects env state := by
  cases guards with
  | nil => simp [runEffectsWithGuardsAndEnv]
  | cons head tail =>
    have hlen' : (head :: tail).length = effects.length := by simpa using hlen
    have hnone' : (head :: tail).all Option.isNone = Bool.true := by simpa using hnone
    simp [runEffectsWithGuardsAndEnv, hlen', hnone']

theorem claim_entry_run_effects (ctx : EvalContext) (env : EvalEnv) (state : LedgerState) :
    runEffectsWithGuardsAndEnv ctx claimEntry.effects claimEntry.effectGuards env state =
      runEffectsWithEnv ctx claimEntry.effects env state := by
  apply runEffectsWithGuardsAndEnv_all_none
  · with_unfolding_all decide
  · with_unfolding_all decide

theorem entry_disclosure_valid : Disclosure.entrypoint claimEntry = .ok () := by
  with_unfolding_all rfl

def typedEntries (values : List (Nat × _root_.Bool)) : List (Value × Value) :=
  values.map fun (key, value) => (.native key, .bool value)

def state (root campaign : Nat) (values : List (Nat × _root_.Bool)) : LedgerState := {
  cells := [("acceptedRoot", .native root), ("campaignId", .native campaign)]
  maps := [("spent", typedEntries values)]
}

def recorded (root campaign nullifier : Nat) (values : List (Nat × _root_.Bool)) : LedgerState := {
  cells := (state root campaign values).cells
  maps := [("spent", Claim.markSpent nullifier (typedEntries values))]
}

def recordValues (nullifier : Nat) (values : List (Nat × _root_.Bool)) : List (Nat × _root_.Bool) :=
  (nullifier, Bool.true) :: values.filter (fun item => item.1 != nullifier)

@[simp] private theorem native_beq (a b : Nat) :
    (Value.native a == Value.native b) = (a == b) := by rfl

@[simp] private theorem native_bne (a b : Nat) :
    (Value.native a != Value.native b) = (!(a == b)) := by rfl

private theorem native_ref_eval (ctx : EvalContext) (env : EvalEnv) (name : String)
    (value : Nat) (h : env.lookup name = some (.native value)) (hc : value < ctx.modulus) :
    (Expr.ref name : Expr .native).eval ctx env = .ok value := by
  simp only [Expr.eval, h, Value.as]
  change (if !(decide (value < ctx.modulus)) then _ else _) = _
  simp [hc]
  rfl

private theorem typedEntries_forIn (values : List (Nat × _root_.Bool)) (message : String) :
    (forIn (typedEntries values) PUnit.unit fun (item : Value × Value) (_ : PUnit) =>
      if item.1.as .native = none ∨ item.2.as .bool = none then
        (fun (_ : PUnit) => ForInStep.yield PUnit.unit) <$>
          (throw message : Except String PUnit)
      else pure (ForInStep.yield PUnit.unit)) = .ok PUnit.unit := by
  induction values with
  | nil => rfl
  | cons item rest ih =>
    rcases item with ⟨key, value⟩
    simpa [typedEntries, Value.as, Except.pure, Except.bind] using ih

theorem effects_accept_unspent (ctx : EvalContext) (env : EvalEnv)
    (root campaign nullifier : Nat) (values : List (Nat × _root_.Bool))
    (hRoot : env.lookup "root" = some (.native root))
    (hCampaign : env.lookup "campaign" = some (.native campaign))
    (hcRoot : root < ctx.modulus) (hcCampaign : campaign < ctx.modulus)
    (hcNullifier : nullifier < ctx.modulus)
    (hAbsent : (typedEntries values).lookup (.native nullifier) = none) :
    runEffectsWithEnv ctx claimEntry.effects (("nullifier", .native nullifier) :: env)
      (state root campaign values) = .ok
        ([ ("storedCampaign", .native campaign), ("storedRoot", .native root),
           ("nullifier", .native nullifier) ] ++ env, recorded root campaign nullifier values) := by
  have hr : ¬ ctx.modulus ≤ root := Nat.not_le.mpr hcRoot
  have hc : ¬ ctx.modulus ≤ campaign := Nat.not_le.mpr hcCampaign
  have hn : ¬ ctx.modulus ≤ nullifier := Nat.not_le.mpr hcNullifier
  simp! [runEffectsWithEnv, runEffectWithEnv, claimEntry, PrivateClaim, state, recorded,
    Expr.eval, Value.as, Value.pack, hRoot, hCampaign, hcRoot, hcCampaign,
    hcNullifier, hr, hc, hn, hAbsent, Except.pure, Except.bind, Except.map]
  dsimp only [Bind.bind, Except.bind]
  rw [typedEntries_forIn]
  rfl

theorem recorded_lookup (root campaign nullifier : Nat) (values : List (Nat × _root_.Bool)) :
    ((recorded root campaign nullifier values).maps.lookup "spent").bind
      (fun entries => entries.lookup (.native nullifier)) = some (.bool Bool.true) := by
  have hSelf : (Value.native nullifier == Value.native nullifier) = Bool.true := by
    change (nullifier == nullifier) = Bool.true
    simp
  simp [recorded, Claim.markSpent, List.lookup, hSelf]

theorem recorded_preserves_cells (root campaign nullifier : Nat)
    (values : List (Nat × _root_.Bool)) :
    (recorded root campaign nullifier values).cells = (state root campaign values).cells := by rfl

theorem recorded_is_canonical_state (root campaign nullifier : Nat)
    (values : List (Nat × _root_.Bool)) :
    recorded root campaign nullifier values = state root campaign (recordValues nullifier values) := by
  simp only [recorded, state, recordValues, typedEntries, Claim.markSpent, List.map_cons]
  rw [List.filter_map]
  rfl

structure SpentInvariant (ctx : EvalContext) (values : List (Nat × _root_.Bool)) : Prop where
  uniqueKeys : (values.map Prod.fst).Nodup
  canonicalKeys : ∀ item ∈ values, item.1 < ctx.modulus
  allMarked : ∀ item ∈ values, item.2 = Bool.true

def StateInvariant (ctx : EvalContext) (root campaign : Nat)
    (values : List (Nat × _root_.Bool)) : Prop :=
  root < ctx.modulus ∧ campaign < ctx.modulus ∧ SpentInvariant ctx values

theorem initial_state_invariant (ctx : EvalContext) (root campaign : Nat)
    (hr : root < ctx.modulus) (hc : campaign < ctx.modulus) :
    StateInvariant ctx root campaign [] := by
  exact ⟨hr, hc, by constructor <;> simp⟩

theorem checked_initializer (root campaign : Nat) (hr : root < Field.modulus)
    (hc : campaign < Field.modulus) :
    Claim.initialState root campaign = .ok (state root campaign []) := by
  have hRoot : ¬ root >= Field.modulus := Nat.not_le.mpr hr
  have hCampaign : ¬ campaign >= Field.modulus := Nat.not_le.mpr hc
  simp only [Claim.initialState, Field.encode, ite_eq_right hRoot, ite_eq_right hCampaign]
  simp only [Std.Legacy.Range.forIn_eq_forIn_range']
  rfl

theorem record_values_preserves_invariant (ctx : EvalContext) (nullifier : Nat)
    (values : List (Nat × _root_.Bool)) (hn : nullifier < ctx.modulus)
    (before : SpentInvariant ctx values) : SpentInvariant ctx (recordValues nullifier values) := by
  have keyMap : (values.filter (fun item => item.1 != nullifier)).map Prod.fst =
      (values.map Prod.fst).filter (fun key => key != nullifier) := by
    rw [List.filter_map]
    rfl
  constructor
  · rw [recordValues, List.map_cons, keyMap]
    exact List.nodup_cons.mpr ⟨by simp, before.uniqueKeys.filter _⟩
  · intro item membership
    simp only [recordValues, List.mem_cons, List.mem_filter] at membership
    rcases membership with equal | ⟨old, _⟩
    · subst item
      exact hn
    · exact before.canonicalKeys item old
  · intro item membership
    simp only [recordValues, List.mem_cons, List.mem_filter] at membership
    rcases membership with equal | ⟨old, _⟩
    · subst item
      rfl
    · exact before.allMarked item old

theorem recorded_state_preserves_invariant (ctx : EvalContext) (root campaign nullifier : Nat)
    (values : List (Nat × _root_.Bool)) (hn : nullifier < ctx.modulus)
    (before : StateInvariant ctx root campaign values) :
    StateInvariant ctx root campaign (recordValues nullifier values) := by
  exact ⟨before.1, before.2.1, record_values_preserves_invariant ctx nullifier values hn before.2.2⟩

theorem recorded_preserves_other_nullifier (root campaign nullifier other : Nat)
    (values : List (Nat × _root_.Bool)) (hDifferent : other ≠ nullifier) :
    ((recorded root campaign nullifier values).maps.lookup "spent").bind
      (fun entries => entries.lookup (.native other)) = (typedEntries values).lookup (.native other) := by
  have hOther : (other == nullifier) = Bool.false := by simp [hDifferent]
  induction values with
  | nil => simp! [recorded, Claim.markSpent, typedEntries, List.lookup, hOther]
  | cons item rest ih =>
    rcases item with ⟨key, value⟩
    by_cases hk : key = nullifier
    · subst key
      simpa! [recorded, Claim.markSpent, typedEntries, List.lookup, hOther] using ih
    · by_cases ho : other = key
      · subst key
        simp! [recorded, Claim.markSpent, typedEntries, List.lookup, hOther, hDifferent]
      · have hkB : (key == nullifier) = Bool.false := by simp [hk]
        have hoB : (other == key) = Bool.false := by simp [ho]
        simpa! [recorded, Claim.markSpent, typedEntries, List.lookup, hOther, hkB, hoB] using ih

theorem effects_reject_recorded (ctx : EvalContext) (env : EvalEnv)
    (root campaign nullifier : Nat) (values : List (Nat × _root_.Bool))
    (hRoot : env.lookup "root" = some (.native root))
    (hCampaign : env.lookup "campaign" = some (.native campaign))
    (hcRoot : root < ctx.modulus) (hcCampaign : campaign < ctx.modulus)
    (hcNullifier : nullifier < ctx.modulus) :
    runEffectsWithEnv ctx claimEntry.effects (("nullifier", .native nullifier) :: env)
      (recorded root campaign nullifier values) = .error "state map key already present" := by
  have hr : ¬ ctx.modulus ≤ root := Nat.not_le.mpr hcRoot
  have hc : ¬ ctx.modulus ≤ campaign := Nat.not_le.mpr hcCampaign
  have hn : ¬ ctx.modulus ≤ nullifier := Nat.not_le.mpr hcNullifier
  have hSelf : (Value.native nullifier == Value.native nullifier) = Bool.true := by
    change (nullifier == nullifier) = Bool.true
    simp
  simp! [runEffectsWithEnv, runEffectWithEnv, claimEntry, PrivateClaim, state, recorded,
    Expr.eval, Value.as, Value.pack, hRoot, hCampaign, hcRoot, hcCampaign, hcNullifier,
    hr, hc, hn, Claim.markSpent, hSelf, Except.pure, Except.bind, Except.map]
  rfl

theorem clear_settlement_state (root campaign : Nat) (values : List (Nat × _root_.Bool)) :
    {state root campaign values with
      unshieldedInputs := [], unshieldedOutputs := [], unshieldedSpendClaims := []} =
      state root campaign values := rfl

private theorem clear_settlement_recorded (root campaign nullifier : Nat)
    (values : List (Nat × _root_.Bool)) :
    {recorded root campaign nullifier values with
      unshieldedInputs := [], unshieldedOutputs := [], unshieldedSpendClaims := []} =
      recorded root campaign nullifier values := rfl

/-- An accepted actual circuit, matching configured public parameters and an
unspent key produce exactly the stated successor. No hash assumption is hidden
here: circuit acceptance is an explicit premise. -/
theorem accepted_claim_transition (ctx : EvalContext) (env : EvalEnv)
    (root campaign nullifier : Nat) (values : List (Nat × _root_.Bool))
    (hCircuit : claimEntry.circuit.run ctx env = .ok [("nullifier", .native nullifier)])
    (hRoot : env.lookup "root" = some (.native root))
    (hCampaign : env.lookup "campaign" = some (.native campaign))
    (hcRoot : root < ctx.modulus) (hcCampaign : campaign < ctx.modulus)
    (hcNullifier : nullifier < ctx.modulus)
    (hAbsent : (typedEntries values).lookup (.native nullifier) = none) :
    claimEntry.run ctx env (state root campaign values) =
      .ok ([("nullifier", .native nullifier)], recorded root campaign nullifier values) := by
  simp only [Entrypoint.run, entry_disclosure_valid, clear_settlement_state]
  dsimp only [Bind.bind, Except.bind, Except.pure]
  rw [hCircuit]
  dsimp only [Bind.bind, Except.bind]
  simp only [List.cons_append, List.nil_append]
  rw [claim_entry_run_effects, effects_accept_unspent ctx env root campaign nullifier values hRoot hCampaign
    hcRoot hcCampaign hcNullifier hAbsent]
  rfl

/-- The same actual circuit inputs cannot execute a second claim after the
successful transition above, regardless of the hash oracle's implementation. -/
theorem recorded_claim_rejects_replay (ctx : EvalContext) (env : EvalEnv)
    (root campaign nullifier : Nat) (values : List (Nat × _root_.Bool))
    (hCircuit : claimEntry.circuit.run ctx env = .ok [("nullifier", .native nullifier)])
    (hRoot : env.lookup "root" = some (.native root))
    (hCampaign : env.lookup "campaign" = some (.native campaign))
    (hcRoot : root < ctx.modulus) (hcCampaign : campaign < ctx.modulus)
    (hcNullifier : nullifier < ctx.modulus) :
    claimEntry.run ctx env (recorded root campaign nullifier values) =
      .error "state map key already present" := by
  simp only [Entrypoint.run, entry_disclosure_valid, clear_settlement_recorded]
  dsimp only [Bind.bind, Except.bind, Except.pure]
  rw [hCircuit]
  dsimp only [Bind.bind, Except.bind]
  simp only [List.cons_append, List.nil_append]
  rw [claim_entry_run_effects, effects_reject_recorded ctx env root campaign nullifier values hRoot hCampaign
    hcRoot hcCampaign hcNullifier]

theorem wrong_root_effects_rejected (ctx : EvalContext) (env : EvalEnv)
    (storedRoot publicRoot campaign nullifier : Nat) (values : List (Nat × _root_.Bool))
    (hRoot : env.lookup "root" = some (.native publicRoot))
    (hcStored : storedRoot < ctx.modulus) (hcPublic : publicRoot < ctx.modulus)
    (hMismatch : storedRoot ≠ publicRoot) :
    runEffectsWithEnv ctx claimEntry.effects (("nullifier", .native nullifier) :: env)
      (state storedRoot campaign values) = .error "state transition guard failed" := by
  have hs : ¬ ctx.modulus ≤ storedRoot := Nat.not_le.mpr hcStored
  have hp : ¬ ctx.modulus ≤ publicRoot := Nat.not_le.mpr hcPublic
  simp! [runEffectsWithEnv, runEffectWithEnv, claimEntry, PrivateClaim, state, Expr.eval, Value.as, Value.pack,
    hRoot, hcStored, hcPublic, hs, hp, hMismatch, Except.pure, Except.bind, Except.map]
  rfl

theorem wrong_root_claim_rejected (ctx : EvalContext) (env : EvalEnv)
    (storedRoot publicRoot campaign nullifier : Nat) (values : List (Nat × _root_.Bool))
    (hCircuit : claimEntry.circuit.run ctx env = .ok [("nullifier", .native nullifier)])
    (hRoot : env.lookup "root" = some (.native publicRoot))
    (hcStored : storedRoot < ctx.modulus) (hcPublic : publicRoot < ctx.modulus)
    (hMismatch : storedRoot ≠ publicRoot) :
    claimEntry.run ctx env (state storedRoot campaign values) =
      .error "state transition guard failed" := by
  simp only [Entrypoint.run, entry_disclosure_valid, clear_settlement_state]
  dsimp only [Bind.bind, Except.bind, Except.pure]
  rw [hCircuit]
  dsimp only [Bind.bind, Except.bind]
  simp only [List.cons_append, List.nil_append]
  rw [claim_entry_run_effects, wrong_root_effects_rejected ctx env storedRoot publicRoot campaign nullifier values hRoot
    hcStored hcPublic hMismatch]

theorem wrong_campaign_effects_rejected (ctx : EvalContext) (env : EvalEnv)
    (root storedCampaign publicCampaign nullifier : Nat) (values : List (Nat × _root_.Bool))
    (hRoot : env.lookup "root" = some (.native root))
    (hCampaign : env.lookup "campaign" = some (.native publicCampaign))
    (hcRoot : root < ctx.modulus) (hcStored : storedCampaign < ctx.modulus)
    (hcPublic : publicCampaign < ctx.modulus) (hMismatch : storedCampaign ≠ publicCampaign) :
    runEffectsWithEnv ctx claimEntry.effects (("nullifier", .native nullifier) :: env)
      (state root storedCampaign values) = .error "state transition guard failed" := by
  have hr : ¬ ctx.modulus ≤ root := Nat.not_le.mpr hcRoot
  have hs : ¬ ctx.modulus ≤ storedCampaign := Nat.not_le.mpr hcStored
  have hp : ¬ ctx.modulus ≤ publicCampaign := Nat.not_le.mpr hcPublic
  simp! [runEffectsWithEnv, runEffectWithEnv, claimEntry, PrivateClaim, state, Expr.eval, Value.as, Value.pack,
    hRoot, hCampaign, hcRoot, hcStored, hcPublic, hr, hs, hp, hMismatch,
    Except.pure, Except.bind, Except.map]
  rfl

theorem wrong_campaign_claim_rejected (ctx : EvalContext) (env : EvalEnv)
    (root storedCampaign publicCampaign nullifier : Nat) (values : List (Nat × _root_.Bool))
    (hCircuit : claimEntry.circuit.run ctx env = .ok [("nullifier", .native nullifier)])
    (hRoot : env.lookup "root" = some (.native root))
    (hCampaign : env.lookup "campaign" = some (.native publicCampaign))
    (hcRoot : root < ctx.modulus) (hcStored : storedCampaign < ctx.modulus)
    (hcPublic : publicCampaign < ctx.modulus) (hMismatch : storedCampaign ≠ publicCampaign) :
    claimEntry.run ctx env (state root storedCampaign values) =
      .error "state transition guard failed" := by
  simp only [Entrypoint.run, entry_disclosure_valid, clear_settlement_state]
  dsimp only [Bind.bind, Except.bind, Except.pure]
  rw [hCircuit]
  dsimp only [Bind.bind, Except.bind]
  simp only [List.cons_append, List.nil_append]
  rw [claim_entry_run_effects, wrong_campaign_effects_rejected ctx env root storedCampaign publicCampaign nullifier values
    hRoot hCampaign hcRoot hcStored hcPublic hMismatch]

/-- State-transition specification. Circuit eligibility is an explicit premise;
it is not replaced by a claim about a particular cryptographic hash. -/
structure Preconditions (ctx : EvalContext) (env : EvalEnv)
    (root campaign nullifier : Nat) (values : List (Nat × _root_.Bool)) : Prop where
  circuit : claimEntry.circuit.run ctx env = .ok [("nullifier", .native nullifier)]
  publicRoot : env.lookup "root" = some (.native root)
  publicCampaign : env.lookup "campaign" = some (.native campaign)
  canonicalRoot : root < ctx.modulus
  canonicalCampaign : campaign < ctx.modulus
  canonicalNullifier : nullifier < ctx.modulus
  unspent : (typedEntries values).lookup (.native nullifier) = none

/-- Functional state correctness of the imported source entrypoint under the
stated preconditions, including an actual second execution attempt. -/
theorem state_functional_correctness (ctx : EvalContext) (env : EvalEnv)
    (root campaign nullifier : Nat) (values : List (Nat × _root_.Bool))
    (pre : Preconditions ctx env root campaign nullifier values) :
    ∃ after,
      claimEntry.run ctx env (state root campaign values) =
        .ok ([("nullifier", .native nullifier)], after) ∧
      after.cells = (state root campaign values).cells ∧
      (after.maps.lookup "spent").bind (fun entries => entries.lookup (.native nullifier)) =
        some (.bool Bool.true) ∧
      claimEntry.run ctx env after = .error "state map key already present" := by
  refine ⟨recorded root campaign nullifier values, ?_, ?_, ?_, ?_⟩
  · exact accepted_claim_transition ctx env root campaign nullifier values pre.circuit
      pre.publicRoot pre.publicCampaign pre.canonicalRoot pre.canonicalCampaign
      pre.canonicalNullifier pre.unspent
  · rfl
  · exact recorded_lookup root campaign nullifier values
  · exact recorded_claim_rejects_replay ctx env root campaign nullifier values pre.circuit
      pre.publicRoot pre.publicCampaign pre.canonicalRoot pre.canonicalCampaign pre.canonicalNullifier

structure InputValues where
  root : Nat
  campaign : Nat
  nullifier : Nat
  secret : Nat
  sibling0 : Nat
  sibling1 : Nat
  direction0 : _root_.Bool
  direction1 : _root_.Bool

def inputEnvironment (input : InputValues) : EvalEnv := [
  ("root", .native input.root), ("campaign", .native input.campaign),
  ("suppliedNullifier", .native input.nullifier), ("secret", .native input.secret),
  ("sibling0", .native input.sibling0), ("sibling1", .native input.sibling1),
  ("direction0", .bool input.direction0), ("direction1", .bool input.direction1)]

structure CanonicalInputs (ctx : EvalContext) (input : InputValues) : Prop where
  domains : 3 < ctx.modulus
  root : input.root < ctx.modulus
  campaign : input.campaign < ctx.modulus
  nullifier : input.nullifier < ctx.modulus
  secret : input.secret < ctx.modulus
  sibling0 : input.sibling0 < ctx.modulus
  sibling1 : input.sibling1 < ctx.modulus

def leafExpression : Expr .native := .poseidon2 1 (.ref "secret") (.ref "campaign")
def firstNodeExpression : Expr .native := .poseidon2 2
  (.select (.ref "direction0") (.ref "sibling0") leafExpression)
  (.select (.ref "direction0") leafExpression (.ref "sibling0"))
def rootExpression : Expr .native := .poseidon2 2
  (.select (.ref "direction1") (.ref "sibling1") firstNodeExpression)
  (.select (.ref "direction1") firstNodeExpression (.ref "sibling1"))
def nullifierExpression : Expr .native := .poseidon2 3 (.ref "secret") (.ref "campaign")

/-- This equality binds the mathematical expressions to the imported source;
editing the source constraints invalidates the proof. -/
theorem source_constraints : claimEntry.circuit.constraints = [
    .eq rootExpression (.ref "root"), .eq nullifierExpression (.ref "suppliedNullifier")] := by rfl

private theorem bool_ref_eval (ctx : EvalContext) (env : EvalEnv) (name : String)
    (value : _root_.Bool) (h : env.lookup name = some (.bool value)) :
    (Expr.ref name : Expr .bool).eval ctx env = .ok value := by
  simp only [Expr.eval, h, Value.as]
  rfl

private theorem select_eval (ctx : EvalContext) (env : EvalEnv)
    (condition : Expr .bool) (yes no : Expr .native) (bit : _root_.Bool) (a b : Nat)
    (hc : condition.eval ctx env = .ok bit)
    (ha : yes.eval ctx env = .ok a) (hb : no.eval ctx env = .ok b) :
    (Expr.select condition yes no).eval ctx env = .ok (if bit then a else b) := by
  simp only [Expr.eval, hc, ha, hb]
  rfl

private theorem hash_eval (ctx : EvalContext) (env : EvalEnv) (domain : Nat)
    (left right : Expr .native) (a b result : Nat)
    (hd : domain < ctx.modulus) (ha : left.eval ctx env = .ok a)
    (hb : right.eval ctx env = .ok b) (hh : ctx.poseidon2 domain a b = .ok result)
    (hc : result < ctx.modulus) :
    (Expr.poseidon2 domain left right).eval ctx env = .ok result := by
  simp only [Expr.eval]
  have hn : ¬ domain >= ctx.modulus := Nat.not_le.mpr hd
  have hr : ¬ result >= ctx.modulus := Nat.not_le.mpr hc
  rw [ite_eq_right hn, ha, hb]
  dsimp only [Bind.bind, Except.bind]
  rw [hh]
  dsimp only [Bind.bind, Except.bind]
  rw [ite_eq_right hr]
  rfl

private theorem equal_values_eval (ctx : EvalContext) (env : EvalEnv)
    (left right : Expr .native) (value : Nat)
    (hl : left.eval ctx env = .ok value) (hr : right.eval ctx env = .ok value) :
    (Expr.eq left right).eval ctx env = .ok Bool.true := by
  simp only [Expr.eval, hl, hr]
  change pure (value == value) = (Except.ok Bool.true : Except String _root_.Bool)
  simp
  rfl

theorem source_circuit_validate (ctx : EvalContext) (hDomain : 3 < ctx.modulus) :
    claimEntry.circuit.validate (evaluationCapabilities ctx) = .ok () := by
  have hd1 : ¬ ctx.modulus ≤ 1 := by omega
  have hd2 : ¬ ctx.modulus ≤ 2 := by omega
  have hd3 : ¬ ctx.modulus ≤ 3 := Nat.not_le.mpr hDomain
  have hNames : (["root", "campaign", "suppliedNullifier", "secret", "sibling0", "sibling1",
      "direction0", "direction1"] : List String).eraseDups.length = 8 := by decide
  have hOutputs : (["nullifier"] : List String).eraseDups.length = 1 := by decide
  simp! [claimEntry, PrivateClaim, claimRelation, Circuit.validate, evaluationCapabilities, Ty.validate,
    ScalarPolicy.validate, validateConstraints, Expr.validate, uniqueNames,
    hNames, hOutputs, hd1, hd2, hd3, Except.pure, Except.bind, Except.map]
  rfl

theorem source_circuit_execution (ctx : EvalContext) (input : InputValues)
    (canonical : CanonicalInputs ctx input) :
    claimEntry.circuit.run ctx (inputEnvironment input) =
      (do
        runConstraints ctx (inputEnvironment input) claimEntry.circuit.constraints
        pure [("nullifier", .native input.nullifier)]) := by
  unfold Circuit.run
  rw [source_circuit_validate ctx canonical.domains]
  generalize hChecks : runConstraints ctx (inputEnvironment input) claimEntry.circuit.constraints = checks
  have hNames : (["root", "campaign", "suppliedNullifier", "secret", "sibling0", "sibling1",
      "direction0", "direction1"] : List String).eraseDups.length = 8 := by decide
  have hr : ¬ ctx.modulus ≤ input.root := Nat.not_le.mpr canonical.root
  have hc : ¬ ctx.modulus ≤ input.campaign := Nat.not_le.mpr canonical.campaign
  have hn : ¬ ctx.modulus ≤ input.nullifier := Nat.not_le.mpr canonical.nullifier
  have hs : ¬ ctx.modulus ≤ input.secret := Nat.not_le.mpr canonical.secret
  have h0 : ¬ ctx.modulus ≤ input.sibling0 := Nat.not_le.mpr canonical.sibling0
  have h1 : ¬ ctx.modulus ≤ input.sibling1 := Nat.not_le.mpr canonical.sibling1
  cases checks with
  | error message =>
    simp! [claimEntry, PrivateClaim, claimRelation, inputEnvironment, uniqueNames, hNames,
      Expr.eval, Value.as, Value.pack, hr, hc, hn, hs, h0, h1,
      Except.pure, Except.bind, Except.map]
  | ok proofUnit =>
    cases proofUnit
    simp! [claimEntry, PrivateClaim, claimRelation, inputEnvironment, uniqueNames, hNames,
      Expr.eval, Value.as, Value.pack, hr, hc, hn, hs, h0, h1,
      Except.pure, Except.bind, Except.map]

theorem source_circuit_accepts_constraints (ctx : EvalContext) (input : InputValues)
    (canonical : CanonicalInputs ctx input)
    (checks : runConstraints ctx (inputEnvironment input) claimEntry.circuit.constraints = .ok ()) :
    claimEntry.circuit.run ctx (inputEnvironment input) =
      .ok [("nullifier", .native input.nullifier)] := by
  rw [source_circuit_execution ctx input canonical, checks]
  rfl

private theorem constraints_hold_of_success (ctx : EvalContext) (env : EvalEnv)
    (conditions : List (Expr .bool)) (success : runConstraints ctx env conditions = .ok ()) :
    ConstraintsHold ctx env conditions := by
  induction conditions with
  | nil => trivial
  | cons condition rest ih =>
    cases evaluated : condition.eval ctx env with
    | error message => simp [runConstraints, evaluated] at success
    | ok bit =>
      cases bit with
      | «false» => simp [runConstraints, evaluated] at success
      | «true» =>
        exact ⟨evaluated, ih (by simpa [runConstraints, evaluated] using success)⟩

theorem successful_source_constraints (ctx : EvalContext) (input : InputValues)
    (canonical : CanonicalInputs ctx input) (outputs : EvalEnv)
    (success : claimEntry.circuit.run ctx (inputEnvironment input) = .ok outputs) :
    ConstraintsHold ctx (inputEnvironment input) claimEntry.circuit.constraints := by
  rw [source_circuit_execution ctx input canonical] at success
  cases checked : runConstraints ctx (inputEnvironment input) claimEntry.circuit.constraints with
  | error message =>
    rw [checked] at success
    contradiction
  | ok proofUnit =>
    cases proofUnit
    exact constraints_hold_of_success ctx (inputEnvironment input) claimEntry.circuit.constraints checked

theorem successful_source_output (ctx : EvalContext) (input : InputValues)
    (canonical : CanonicalInputs ctx input) (outputs : EvalEnv)
    (success : claimEntry.circuit.run ctx (inputEnvironment input) = .ok outputs) :
    outputs = [("nullifier", .native input.nullifier)] := by
  rw [source_circuit_execution ctx input canonical] at success
  cases checked : runConstraints ctx (inputEnvironment input) claimEntry.circuit.constraints with
  | error message =>
    rw [checked] at success
    contradiction
  | ok proofUnit =>
    cases proofUnit
    rw [checked] at success
    change (Except.ok [("nullifier", .native input.nullifier)] : Except String EvalEnv) = .ok outputs at success
    exact (Except.ok.inj success).symm

theorem successful_claim_exact_state (ctx : EvalContext) (input : InputValues)
    (values : List (Nat × _root_.Bool)) (canonical : CanonicalInputs ctx input)
    (unspent : (typedEntries values).lookup (.native input.nullifier) = none)
    (outputs : EvalEnv) (after : LedgerState)
    (success : claimEntry.run ctx (inputEnvironment input) (state input.root input.campaign values) =
      .ok (outputs, after)) :
    outputs = [("nullifier", .native input.nullifier)] ∧
      after = state input.root input.campaign (recordValues input.nullifier values) := by
  have run := success
  simp only [Entrypoint.run, entry_disclosure_valid] at run
  dsimp only [Bind.bind, Except.bind, Except.pure] at run
  cases circuitResult : claimEntry.circuit.run ctx (inputEnvironment input) with
  | error message =>
    rw [circuitResult] at run
    contradiction
  | ok circuitOutputs =>
    have outputEquation := successful_source_output ctx input canonical circuitOutputs circuitResult
    rw [outputEquation] at circuitResult
    have exactRun := accepted_claim_transition ctx (inputEnvironment input) input.root input.campaign
      input.nullifier values circuitResult (by rfl) (by rfl)
      canonical.root canonical.campaign canonical.nullifier unspent
    have exactPair := Except.ok.inj (success.symm.trans exactRun)
    constructor
    · exact congrArg Prod.fst exactPair
    · simpa only [recorded_is_canonical_state] using congrArg Prod.snd exactPair

/-- The current source observer sees returned values and all public ledger state.
It contains no invented event, call, timing, log or proof-byte observation. -/
structure PublicObservation where
  outputs : EvalEnv
  state : LedgerState

def successfulObservation (result : Except String (EvalEnv × LedgerState)) : Option PublicObservation :=
  match result with
  | .error _ => none
  | .ok (outputs, next) => some {outputs, state := next}

/-- Successful executions with the same authorized public inputs and starting
public state expose identical current source observations, even with different
private secrets, siblings or directions. This is not cryptographic zero knowledge. -/
theorem successful_public_observations_equal (ctx : EvalContext)
    (left right : InputValues) (values : List (Nat × _root_.Bool))
    (leftCanonical : CanonicalInputs ctx left) (rightCanonical : CanonicalInputs ctx right)
    (sameRoot : left.root = right.root) (sameCampaign : left.campaign = right.campaign)
    (sameNullifier : left.nullifier = right.nullifier)
    (unspent : (typedEntries values).lookup (.native left.nullifier) = none)
    (leftOutputs rightOutputs : EvalEnv) (leftAfter rightAfter : LedgerState)
    (leftSuccess : claimEntry.run ctx (inputEnvironment left) (state left.root left.campaign values) =
      .ok (leftOutputs, leftAfter))
    (rightSuccess : claimEntry.run ctx (inputEnvironment right) (state left.root left.campaign values) =
      .ok (rightOutputs, rightAfter)) :
    ({outputs := leftOutputs, state := leftAfter} : PublicObservation) =
      {outputs := rightOutputs, state := rightAfter} := by
  have leftExact := successful_claim_exact_state ctx left values leftCanonical unspent
    leftOutputs leftAfter leftSuccess
  have rightUnspent : (typedEntries values).lookup (.native right.nullifier) = none := by
    simpa only [sameNullifier] using unspent
  have rightRun : claimEntry.run ctx (inputEnvironment right) (state right.root right.campaign values) =
      .ok (rightOutputs, rightAfter) := by
    simpa only [sameRoot, sameCampaign] using rightSuccess
  have rightExact := successful_claim_exact_state ctx right values rightCanonical rightUnspent
    rightOutputs rightAfter rightRun
  have sameOutputs : leftOutputs = rightOutputs := by
    rw [leftExact.1, rightExact.1, sameNullifier]
  have sameState : leftAfter = rightAfter := by
    rw [leftExact.2, rightExact.2, sameRoot, sameCampaign, sameNullifier]
  cases sameOutputs
  cases sameState
  rfl

private theorem equal_values_sound (ctx : EvalContext) (env : EvalEnv)
    (left right : Expr .native) (success : (Expr.eq left right).eval ctx env = .ok Bool.true) :
    ∃ value, left.eval ctx env = .ok value ∧ right.eval ctx env = .ok value := by
  simp only [Expr.eval] at success
  cases hl : left.eval ctx env with
  | error message =>
    rw [hl] at success
    contradiction
  | ok a =>
    rw [hl] at success
    dsimp only [Bind.bind, Except.bind] at success
    cases hr : right.eval ctx env with
    | error message =>
      rw [hr] at success
      contradiction
    | ok b =>
      rw [hr] at success
      change (Except.ok (a == b) : Except String _root_.Bool) = .ok Bool.true at success
      have equal : a = b := by simpa using Except.ok.inj success
      subst b
      exact ⟨a, rfl, rfl⟩

/-- Every successful actual source circuit execution reconstructs the declared
root and computes the declared domain-separated nullifier. -/
theorem successful_source_root_and_nullifier (ctx : EvalContext) (input : InputValues)
    (canonical : CanonicalInputs ctx input) (outputs : EvalEnv)
    (success : claimEntry.circuit.run ctx (inputEnvironment input) = .ok outputs) :
    rootExpression.eval ctx (inputEnvironment input) = .ok input.root ∧
      nullifierExpression.eval ctx (inputEnvironment input) = .ok input.nullifier := by
  have checks := successful_source_constraints ctx input canonical outputs success
  rw [source_constraints] at checks
  obtain ⟨rootCheck, nullifierCheck, _⟩ := checks
  obtain ⟨root, rootValue, rootRef⟩ := equal_values_sound ctx (inputEnvironment input)
    rootExpression (.ref "root") rootCheck
  obtain ⟨nullifier, nullifierValue, nullifierRef⟩ := equal_values_sound ctx (inputEnvironment input)
    nullifierExpression (.ref "suppliedNullifier") nullifierCheck
  have hr := native_ref_eval ctx (inputEnvironment input) "root" input.root (by rfl) canonical.root
  have hn := native_ref_eval ctx (inputEnvironment input) "suppliedNullifier" input.nullifier
    (by rfl) canonical.nullifier
  rw [hr] at rootRef
  rw [hn] at nullifierRef
  have er := Except.ok.inj rootRef
  have en := Except.ok.inj nullifierRef
  subst root nullifier
  exact ⟨rootValue, nullifierValue⟩

theorem successful_contract_root_and_nullifier (ctx : EvalContext) (input : InputValues)
    (canonical : CanonicalInputs ctx input) (before after : LedgerState) (outputs : EvalEnv)
    (success : claimEntry.run ctx (inputEnvironment input) before = .ok (outputs, after)) :
    rootExpression.eval ctx (inputEnvironment input) = .ok input.root ∧
      nullifierExpression.eval ctx (inputEnvironment input) = .ok input.nullifier := by
  simp only [Entrypoint.run, entry_disclosure_valid] at success
  dsimp only [Bind.bind, Except.bind, Except.pure] at success
  cases circuitResult : claimEntry.circuit.run ctx (inputEnvironment input) with
  | error message =>
    rw [circuitResult] at success
    contradiction
  | ok circuitOutputs =>
    exact successful_source_root_and_nullifier ctx input canonical circuitOutputs circuitResult

/-- The exact three path hashes and separate nullifier hash used by the source.
These are oracle equations, not cryptographic injectivity assumptions. -/
structure HashTrace (ctx : EvalContext) (input : InputValues) (leaf node0 : Nat) : Prop where
  canonicalLeaf : leaf < ctx.modulus
  canonicalNode : node0 < ctx.modulus
  leafHash : ctx.poseidon2 1 input.secret input.campaign = .ok leaf
  firstNode : ctx.poseidon2 2
    (if input.direction0 then input.sibling0 else leaf)
    (if input.direction0 then leaf else input.sibling0) = .ok node0
  secondNode : ctx.poseidon2 2
    (if input.direction1 then input.sibling1 else node0)
    (if input.direction1 then node0 else input.sibling1) = .ok input.root
  nullifierHash : ctx.poseidon2 3 input.secret input.campaign = .ok input.nullifier

theorem hash_trace_expressions (ctx : EvalContext) (input : InputValues)
    (leaf node0 : Nat) (canonical : CanonicalInputs ctx input)
    (trace : HashTrace ctx input leaf node0) :
    rootExpression.eval ctx (inputEnvironment input) = .ok input.root ∧
      nullifierExpression.eval ctx (inputEnvironment input) = .ok input.nullifier := by
  let env := inputEnvironment input
  have hSecret := native_ref_eval ctx env "secret" input.secret (by rfl) canonical.secret
  have hCampaign := native_ref_eval ctx env "campaign" input.campaign (by rfl) canonical.campaign
  have hSibling0 := native_ref_eval ctx env "sibling0" input.sibling0 (by rfl) canonical.sibling0
  have hSibling1 := native_ref_eval ctx env "sibling1" input.sibling1 (by rfl) canonical.sibling1
  have hDirection0 := bool_ref_eval ctx env "direction0" input.direction0 (by rfl)
  have hDirection1 := bool_ref_eval ctx env "direction1" input.direction1 (by rfl)
  have hd1 : 1 < ctx.modulus := by have := canonical.domains; omega
  have hd2 : 2 < ctx.modulus := by have := canonical.domains; omega
  have hLeaf : leafExpression.eval ctx env = .ok leaf :=
    hash_eval ctx env 1 (.ref "secret") (.ref "campaign") input.secret input.campaign leaf
      hd1 hSecret hCampaign trace.leafHash trace.canonicalLeaf
  have hFirst : firstNodeExpression.eval ctx env = .ok node0 :=
    hash_eval ctx env 2 _ _ _ _ node0 hd2
      (select_eval ctx env _ _ _ input.direction0 input.sibling0 leaf hDirection0 hSibling0 hLeaf)
      (select_eval ctx env _ _ _ input.direction0 leaf input.sibling0 hDirection0 hLeaf hSibling0)
      trace.firstNode trace.canonicalNode
  constructor
  · exact hash_eval ctx env 2 _ _ _ _ input.root hd2
      (select_eval ctx env _ _ _ input.direction1 input.sibling1 node0 hDirection1 hSibling1 hFirst)
      (select_eval ctx env _ _ _ input.direction1 node0 input.sibling1 hDirection1 hFirst hSibling1)
      trace.secondNode canonical.root
  · exact hash_eval ctx env 3 (.ref "secret") (.ref "campaign")
      input.secret input.campaign input.nullifier canonical.domains hSecret hCampaign
      trace.nullifierHash canonical.nullifier

/-- Canonical inputs plus explicit path reconstruction and domain-separated
nullifier equations establish actual circuit acceptance. -/
theorem hash_trace_circuit_accepts (ctx : EvalContext) (input : InputValues)
    (leaf node0 : Nat) (canonical : CanonicalInputs ctx input)
    (trace : HashTrace ctx input leaf node0) :
    claimEntry.circuit.run ctx (inputEnvironment input) =
      .ok [("nullifier", .native input.nullifier)] := by
  obtain ⟨hRoot, hNullifier⟩ := hash_trace_expressions ctx input leaf node0 canonical trace
  have hRootRef := native_ref_eval ctx (inputEnvironment input) "root" input.root (by rfl) canonical.root
  have hNullifierRef := native_ref_eval ctx (inputEnvironment input) "suppliedNullifier" input.nullifier
    (by rfl) canonical.nullifier
  have rootCheck := equal_values_eval ctx (inputEnvironment input) rootExpression (.ref "root")
    input.root hRoot hRootRef
  have nullifierCheck := equal_values_eval ctx (inputEnvironment input) nullifierExpression
    (.ref "suppliedNullifier") input.nullifier hNullifier hNullifierRef
  apply source_circuit_accepts_constraints ctx input canonical
  rw [source_constraints]
  simp only [runConstraints, rootCheck, nullifierCheck]

theorem hash_trace_preconditions (ctx : EvalContext) (input : InputValues)
    (leaf node0 : Nat) (values : List (Nat × _root_.Bool))
    (canonical : CanonicalInputs ctx input) (trace : HashTrace ctx input leaf node0)
    (unspent : (typedEntries values).lookup (.native input.nullifier) = none) :
    Preconditions ctx (inputEnvironment input) input.root input.campaign input.nullifier values := by
  exact {
    circuit := hash_trace_circuit_accepts ctx input leaf node0 canonical trace
    publicRoot := by rfl
    publicCampaign := by rfl
    canonicalRoot := canonical.root
    canonicalCampaign := canonical.campaign
    canonicalNullifier := canonical.nullifier
    unspent
  }

/-- A complete progress/state specification for the current source entrypoint,
under explicit canonical inputs and hash equations. This theorem neither assumes
entrypoint success nor a disconnected spent-set transition. -/
theorem eligible_claim_correct (ctx : EvalContext) (input : InputValues)
    (leaf node0 : Nat) (values : List (Nat × _root_.Bool))
    (canonical : CanonicalInputs ctx input) (trace : HashTrace ctx input leaf node0)
    (unspent : (typedEntries values).lookup (.native input.nullifier) = none)
    (spent : SpentInvariant ctx values) :
    let afterValues := recordValues input.nullifier values
    claimEntry.run ctx (inputEnvironment input) (state input.root input.campaign values) =
      .ok ([("nullifier", .native input.nullifier)], state input.root input.campaign afterValues) ∧
    StateInvariant ctx input.root input.campaign afterValues ∧
    ((state input.root input.campaign afterValues).maps.lookup "spent").bind
      (fun entries => entries.lookup (.native input.nullifier)) = some (.bool Bool.true) ∧
    (∀ other, other ≠ input.nullifier →
      ((state input.root input.campaign afterValues).maps.lookup "spent").bind
        (fun entries => entries.lookup (.native other)) =
          (typedEntries values).lookup (.native other)) ∧
    claimEntry.run ctx (inputEnvironment input) (state input.root input.campaign afterValues) =
      .error "state map key already present" := by
  have pre := hash_trace_preconditions ctx input leaf node0 values canonical trace unspent
  dsimp only
  constructor
  · have result := accepted_claim_transition ctx (inputEnvironment input) input.root input.campaign
      input.nullifier values pre.circuit pre.publicRoot pre.publicCampaign pre.canonicalRoot
      pre.canonicalCampaign pre.canonicalNullifier pre.unspent
    simpa only [recorded_is_canonical_state] using result
  constructor
  · exact recorded_state_preserves_invariant ctx input.root input.campaign input.nullifier values
      canonical.nullifier ⟨canonical.root, canonical.campaign, spent⟩
  constructor
  · have result := recorded_lookup input.root input.campaign input.nullifier values
    simpa only [recorded_is_canonical_state] using result
  constructor
  · intro other different
    have result := recorded_preserves_other_nullifier input.root input.campaign input.nullifier other
      values different
    simpa only [recorded_is_canonical_state] using result
  · have result := recorded_claim_rejects_replay ctx (inputEnvironment input) input.root input.campaign
      input.nullifier values pre.circuit pre.publicRoot pre.publicCampaign pre.canonicalRoot
      pre.canonicalCampaign pre.canonicalNullifier
    simpa only [recorded_is_canonical_state] using result


def fixtureContext : EvalContext := {
  modulus := Field.modulus
  poseidon2 := fun _ _ _ => .ok 0
}

def fixtureInputs : EvalEnv := [
  ("root", .native 0), ("campaign", .native 0), ("suppliedNullifier", .native 0),
  ("secret", .native 0), ("sibling0", .native 0), ("sibling1", .native 0),
  ("direction0", .bool Bool.false), ("direction1", .bool Bool.true)]

def fixtureValues : InputValues := {
  root := 0, campaign := 0, nullifier := 0, secret := 0, sibling0 := 0, sibling1 := 0
  direction0 := Bool.false, direction1 := Bool.true
}

theorem fixture_environment : inputEnvironment fixtureValues = fixtureInputs := by rfl

theorem fixture_canonical : CanonicalInputs fixtureContext fixtureValues := by
  constructor <;> decide

theorem fixture_hash_trace : HashTrace fixtureContext fixtureValues 0 0 := by
  constructor
  · decide
  · decide
  · rfl
  · rfl
  · rfl
  · rfl

/-- A kernel-computed non-vacuity witness for the abstract semantics. Its
constant-zero hash oracle is deliberately not a qualified cryptographic oracle. -/
theorem fixture_circuit_accepts :
    claimEntry.circuit.run fixtureContext fixtureInputs = .ok [("nullifier", .native 0)] := by
  with_unfolding_all rfl

theorem fixture_preconditions : Preconditions fixtureContext fixtureInputs 0 0 0 [] := by
  constructor
  · exact fixture_circuit_accepts
  · rfl
  · rfl
  · decide
  · decide
  · decide
  · rfl

theorem fixture_success :
    claimEntry.run fixtureContext fixtureInputs (state 0 0 []) =
      .ok ([("nullifier", .native 0)], recorded 0 0 0 []) :=
  accepted_claim_transition fixtureContext fixtureInputs 0 0 0 []
    fixture_preconditions.circuit fixture_preconditions.publicRoot fixture_preconditions.publicCampaign
    fixture_preconditions.canonicalRoot fixture_preconditions.canonicalCampaign
    fixture_preconditions.canonicalNullifier fixture_preconditions.unspent

theorem fixture_replay_rejected :
    claimEntry.run fixtureContext fixtureInputs (recorded 0 0 0 []) =
      .error "state map key already present" :=
  recorded_claim_rejects_replay fixtureContext fixtureInputs 0 0 0 []
    fixture_preconditions.circuit fixture_preconditions.publicRoot fixture_preconditions.publicCampaign
    fixture_preconditions.canonicalRoot fixture_preconditions.canonicalCampaign
    fixture_preconditions.canonicalNullifier

def secondFixtureValues : InputValues := {
  root := 0, campaign := 0, nullifier := 0, secret := 1, sibling0 := 2, sibling1 := 3
  direction0 := Bool.true, direction1 := Bool.false
}

theorem second_fixture_canonical : CanonicalInputs fixtureContext secondFixtureValues := by
  constructor <;> decide

theorem second_fixture_success :
    claimEntry.run fixtureContext (inputEnvironment secondFixtureValues) (state 0 0 []) =
      .ok ([("nullifier", .native 0)], recorded 0 0 0 []) := by
  with_unfolding_all rfl

theorem fixture_private_values_differ : fixtureValues.secret ≠ secondFixtureValues.secret := by decide

/-- A concrete pair of successful executions with different private data in the
explicit abstract oracle model. It does not establish native zero knowledge. -/
theorem fixture_observations_equal :
    successfulObservation (claimEntry.run fixtureContext (inputEnvironment fixtureValues) (state 0 0 [])) =
      successfulObservation (claimEntry.run fixtureContext (inputEnvironment secondFixtureValues) (state 0 0 [])) := by
  simp only [fixture_environment, fixture_success, second_fixture_success]

#print axioms state_functional_correctness
#print axioms eligible_claim_correct
#print axioms successful_source_root_and_nullifier
#print axioms successful_contract_root_and_nullifier
#print axioms hash_trace_circuit_accepts
#print axioms recorded_state_preserves_invariant
#print axioms successful_public_observations_equal
#print axioms checked_initializer
#print axioms wrong_root_claim_rejected
#print axioms wrong_campaign_claim_rejected
#print axioms fixture_circuit_accepts
#print axioms fixture_success
#print axioms fixture_replay_rejected
#print axioms fixture_observations_equal

end Noctium.PrivateClaimProofs
