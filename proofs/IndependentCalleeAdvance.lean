import tests.IndependentComposition
import Noctium.Verification.SourceEffects

namespace Noctium.Proofs.IndependentCalleeAdvance

open Noctium

private def advanceEntry : Entrypoint :=
  match IndependentCallee.entrypoints with
  | found :: _ => found
  | [] => {name := "", circuit := {name := ""}}

def callEnvironment (credential secret amount : Nat) : EvalEnv :=
  [("credential", .native credential), ("secret", .native secret),
   ("amount", .native amount)]

def advanceEffects (span : SourceSpan) : List Effect :=
  [.readCell "acceptedCredential" "expected" .native,
   .require (Expr.eq (Expr.ref (ty := .native) "expected")
     (Expr.ref (ty := .native) "credential")),
   .readCell "balance" "beforeBalance" .native,
   .writeCell "balance" .native
     (Expr.disclose span (Expr.add (Expr.ref (ty := .native) "beforeBalance")
       (Expr.ref (ty := .native) "amount"))),
   .counterAdjust "count" [] _root_.Bool.false (Expr.uint (2 ^ 32 - 1) 1)]

/-- The checked contract exposes `amount` as its only ledger call argument.
Its circuit has no public outputs, and the entry has no return values or
cross-contract claim effects. -/
theorem advance_abi_exact :
    advanceEntry.name = "advance" ∧
    advanceEntry.callInputs = ["amount"] ∧
    advanceEntry.callArguments.map (·.name) = ["amount"] ∧
    advanceEntry.callArguments.map (·.ty) = [.native] ∧
    advanceEntry.callArguments.map (·.visibility) = [.private] ∧
    advanceEntry.circuit.outputs = [] ∧
    advanceEntry.returns = [] ∧
    advanceEntry.returnViews = [] := by
  decide

theorem advance_effects_exact :
    ∃ span : SourceSpan, advanceEntry.effects = advanceEffects span := by
  refine ⟨{file := "tests/IndependentComposition.lean", line := 37, column := 22}, ?_⟩
  simp [advanceEntry, IndependentCallee, advanceEffects]

theorem evalTransientHash_single
    (ctx : EvalContext) (env : EvalEnv) (secret digest : Nat)
    (secretEval : (Expr.ref "secret" : Expr .native).eval ctx env = .ok secret)
    (secretCanonical : secret < ctx.modulus)
    (hashAgreement : ctx.transientHash [secret] = .ok digest)
    (digestCanonical : digest < ctx.modulus) :
    (Expr.transientHash [Expr.ref "secret"] : Expr .native).eval ctx env = .ok digest := by
  have secretInRange : ¬ ctx.modulus ≤ secret := Nat.not_le_of_gt secretCanonical
  have digestInRange : ¬ ctx.modulus ≤ digest := Nat.not_le_of_gt digestCanonical
  simp [Expr.eval, secretEval, secretInRange, digestInRange, hashAgreement,
    Types.defaultLimits, List.forIn_cons, Bind.bind, Except.bind,
    Pure.pure, Except.pure]

theorem independentCallee_hash_constraint_accepts
    (ctx : EvalContext) (credential secret amount : Nat)
    (credentialEval :
      (Expr.ref "credential" : Expr .native).eval ctx
        (callEnvironment credential secret amount) = .ok credential)
    (secretEval :
      (Expr.ref "secret" : Expr .native).eval ctx
        (callEnvironment credential secret amount) = .ok secret)
    (credentialCanonical : credential < ctx.modulus)
    (secretCanonical : secret < ctx.modulus)
    (hashAgreement : ctx.transientHash [secret] = .ok credential) :
    runConstraints ctx (callEnvironment credential secret amount)
      independentCalleeInputs.constraints = .ok () := by
  have hashEval := evalTransientHash_single ctx (callEnvironment credential secret amount)
    secret credential secretEval secretCanonical hashAgreement credentialCanonical
  have guardEval :
      (Expr.eq (Expr.transientHash [Expr.ref "secret"])
        (Expr.ref "credential")).eval ctx (callEnvironment credential secret amount) =
          .ok _root_.Bool.true := by
    simp [Expr.eval, credentialEval, hashEval]
    change (Except.ok (credential == credential) : Except String _root_.Bool) =
      Except.ok _root_.Bool.true
    simp
  change runConstraints ctx (callEnvironment credential secret amount)
    [Expr.eq (Expr.transientHash [Expr.ref "secret"]) (Expr.ref "credential")] = .ok ()
  simp [runConstraints, guardEval]

theorem disclosed_native_add_eval
    (ctx : EvalContext) (env : EvalEnv) (span : SourceSpan)
    (before amount : Nat)
    (beforeEval : (Expr.ref "beforeBalance" : Expr .native).eval ctx env = .ok before)
    (amountEval : (Expr.ref "amount" : Expr .native).eval ctx env = .ok amount)
    (nonzeroModulus : ctx.modulus ≠ 0) :
    (Expr.disclose span
      (Expr.add (Expr.ref "beforeBalance") (Expr.ref "amount"))).eval ctx env =
        .ok ((before + amount) % ctx.modulus) := by
  simp [Expr.eval, beforeEval, amountEval, nonzeroModulus,
    Bind.bind, Except.bind, Pure.pure, Except.pure]

theorem advance_effects_success
    (ctx : EvalContext) (credential secret amount balance count : Nat)
    (span : SourceSpan) (state : LedgerState)
    (storedCredential : state.cells.lookup "acceptedCredential" =
      some (.native credential))
    (storedBalance : state.cells.lookup "balance" = some (.native balance))
    (storedCounter : state.trees.lookup "count" =
      some (.scalar (.uint (2 ^ 64 - 1) count)))
    (credentialCanonical : credential < ctx.modulus)
    (amountCanonical : amount < ctx.modulus)
    (balanceCanonical : balance < ctx.modulus)
    (counterCanonical : count < ctx.modulus)
    (counterRoom : count < 2 ^ 64 - 1)
    (canonicalOne : 1 < ctx.modulus) :
    runEffectsWithEnv ctx (advanceEffects span)
      (callEnvironment credential secret amount) state =
    .ok (("beforeBalance", .native balance) ::
        ("expected", .native credential) :: callEnvironment credential secret amount,
      {state with
        cells := updateAssoc "balance" (.native ((balance + amount) % ctx.modulus)) state.cells
        trees := updateAssoc "count" (.scalar (.uint (2 ^ 64 - 1) (count + 1))) state.trees}) := by
  have nonzeroModulus : ctx.modulus ≠ 0 := by omega
  let expectedEnv := ("expected", .native credential) ::
    callEnvironment credential secret amount
  let beforeEnv := ("beforeBalance", .native balance) :: expectedEnv
  let afterWrite : LedgerState := {
    state with
    cells := updateAssoc "balance" (.native ((balance + amount) % ctx.modulus))
      state.cells
  }
  have readExpected :
      runEffectWithEnv ctx (.readCell "acceptedCredential" "expected" .native)
        (callEnvironment credential secret amount) state =
      .ok (expectedEnv, state) := by
    simp [runEffectWithEnv, expectedEnv, callEnvironment,
      canonical_eq, Value.as, Value.pack, storedCredential,
      Nat.not_le_of_gt credentialCanonical]
    rfl
  have requireEval :
      (Expr.eq (Expr.ref (ty := .native) "expected")
        (Expr.ref (ty := .native) "credential")).eval ctx expectedEnv = .ok _root_.Bool.true := by
    simp [Expr.eval, expectedEnv, callEnvironment, canonical_eq,
      Value.as, List.lookup, sameValue_native_eq,
      Nat.not_le_of_gt credentialCanonical]
    rfl
  have requireCredential :
      runEffectWithEnv ctx
        (.require (Expr.eq (Expr.ref (ty := .native) "expected")
          (Expr.ref (ty := .native) "credential")))
        expectedEnv state = .ok (expectedEnv, state) := by
    simp [runEffectWithEnv, requireEval]
    rfl
  have readBalance :
      runEffectWithEnv ctx (.readCell "balance" "beforeBalance" .native)
        expectedEnv state = .ok (beforeEnv, state) := by
    simp [runEffectWithEnv, expectedEnv, beforeEnv,
      callEnvironment, canonical_eq, Value.as, Value.pack, storedBalance,
      Nat.not_le_of_gt balanceCanonical]
    rfl
  have beforeEval :
      (Expr.ref (ty := .native) "beforeBalance").eval ctx beforeEnv = .ok balance := by
    simp [Expr.eval, beforeEnv, expectedEnv, callEnvironment, canonical_eq,
      Value.as, List.lookup, Nat.not_le_of_gt balanceCanonical]
    rfl
  have amountEval :
      (Expr.ref (ty := .native) "amount").eval ctx beforeEnv = .ok amount := by
    simp [Expr.eval, beforeEnv, expectedEnv, callEnvironment, canonical_eq,
      Value.as, List.lookup, Nat.not_le_of_gt amountCanonical]
    rfl
  have addEval := disclosed_native_add_eval ctx beforeEnv span balance amount
    beforeEval amountEval nonzeroModulus
  have writeBalance :
      runEffectWithEnv ctx
        (.writeCell "balance" .native
          (Expr.disclose span (Expr.add (Expr.ref (ty := .native) "beforeBalance")
            (Expr.ref (ty := .native) "amount"))))
        beforeEnv state = .ok (beforeEnv, afterWrite) := by
    simp [runEffectWithEnv, afterWrite, Value.as, storedBalance, addEval]
    rfl
  have counterLookup : afterWrite.trees.lookup "count" =
      some (.scalar (.uint (2 ^ 64 - 1) count)) := by
    simpa [afterWrite] using storedCounter
  have counterStep := runEffectWithEnv_counterAdjust_top_increment ctx beforeEnv afterWrite
    "count" count counterLookup counterCanonical counterRoom canonicalOne
  rw [Noctium.Verification.SourceEffects.runEffectsWithEnv_eq_fold]
  simp only [advanceEffects, Noctium.Verification.SourceEffects.fold_cons,
    Noctium.Verification.SourceEffects.fold_nil, Noctium.Verification.SourceEffects.step,
    readExpected, requireCredential, readBalance, writeBalance, counterStep,
    Except.bind]
  simp [afterWrite, beforeEnv, expectedEnv]

theorem advance_entry_effects_success
    (ctx : EvalContext) (credential secret amount balance count : Nat)
    (state : LedgerState)
    (storedCredential : state.cells.lookup "acceptedCredential" =
      some (.native credential))
    (storedBalance : state.cells.lookup "balance" = some (.native balance))
    (storedCounter : state.trees.lookup "count" =
      some (.scalar (.uint (2 ^ 64 - 1) count)))
    (credentialCanonical : credential < ctx.modulus)
    (amountCanonical : amount < ctx.modulus)
    (balanceCanonical : balance < ctx.modulus)
    (counterCanonical : count < ctx.modulus)
    (counterRoom : count < 2 ^ 64 - 1)
    (canonicalOne : 1 < ctx.modulus) :
    runEffectsWithEnv ctx advanceEntry.effects
      (callEnvironment credential secret amount) state =
    .ok (("beforeBalance", .native balance) ::
        ("expected", .native credential) :: callEnvironment credential secret amount,
      {state with
        cells := updateAssoc "balance" (.native ((balance + amount) % ctx.modulus)) state.cells
        trees := updateAssoc "count" (.scalar (.uint (2 ^ 64 - 1) (count + 1))) state.trees}) := by
  obtain ⟨span, effectsExact⟩ := advance_effects_exact
  rw [effectsExact]
  exact advance_effects_success ctx credential secret amount balance count span state
    storedCredential storedBalance storedCounter credentialCanonical amountCanonical
    balanceCanonical counterCanonical counterRoom canonicalOne

theorem independentCallee_advance_admissible_success
    (ctx : EvalContext) (credential secret amount balance count : Nat)
    (state : LedgerState)
    (storedCredential : state.cells.lookup "acceptedCredential" =
      some (.native credential))
    (storedBalance : state.cells.lookup "balance" = some (.native balance))
    (storedCounter : state.trees.lookup "count" =
      some (.scalar (.uint (2 ^ 64 - 1) count)))
    (credentialCanonical : credential < ctx.modulus)
    (secretCanonical : secret < ctx.modulus)
    (amountCanonical : amount < ctx.modulus)
    (balanceCanonical : balance < ctx.modulus)
    (counterCanonical : count < ctx.modulus)
    (counterRoom : count < 2 ^ 64 - 1)
    (canonicalOne : 1 < ctx.modulus)
    (hashAgreement : ctx.transientHash [secret] = .ok credential) :
    runConstraints ctx (callEnvironment credential secret amount)
        independentCalleeInputs.constraints = .ok () ∧
      runEffectsWithEnv ctx advanceEntry.effects
        (callEnvironment credential secret amount) state =
        .ok (("beforeBalance", .native balance) ::
            ("expected", .native credential) :: callEnvironment credential secret amount,
          {state with
            cells := updateAssoc "balance" (.native ((balance + amount) % ctx.modulus)) state.cells
            trees := updateAssoc "count" (.scalar (.uint (2 ^ 64 - 1) (count + 1))) state.trees}) := by
  have credentialEval :
      (Expr.ref (ty := .native) "credential").eval ctx
        (callEnvironment credential secret amount) = .ok credential := by
    simp [Expr.eval, callEnvironment, canonical_eq, Value.as, List.lookup,
      Nat.not_le_of_gt credentialCanonical]
    rfl
  have secretEval :
      (Expr.ref (ty := .native) "secret").eval ctx
        (callEnvironment credential secret amount) = .ok secret := by
    simp [Expr.eval, callEnvironment, canonical_eq, Value.as, List.lookup,
      Nat.not_le_of_gt secretCanonical]
    rfl
  constructor
  · exact independentCallee_hash_constraint_accepts ctx credential secret amount
      credentialEval secretEval credentialCanonical secretCanonical hashAgreement
  · exact advance_entry_effects_success ctx credential secret amount balance count state
      storedCredential storedBalance storedCounter credentialCanonical amountCanonical
      balanceCanonical counterCanonical counterRoom canonicalOne

private def concreteContext : EvalContext := {
  modulus := Field.modulus
  poseidon2 := fun _ _ _ => .error "unused Poseidon oracle"
  transientHash := fun inputs =>
    if inputs == [7] then .ok 29 else .error "unexpected transient-hash input"
}

private def concreteState (credential balance count : Nat) : LedgerState := {
  cells := [("acceptedCredential", .native credential), ("balance", .native balance)]
  trees := [("count", .scalar (.uint (2 ^ 64 - 1) count))]
}

example : Circuit.run concreteContext independentCalleeInputs (callEnvironment 29 7 3) = .ok [] := by
  with_unfolding_all rfl

example :
    runEffectsWithEnv concreteContext advanceEntry.effects (callEnvironment 29 7 3)
      (concreteState 29 10 5) =
    .ok (("beforeBalance", .native 10) :: ("expected", .native 29) ::
        callEnvironment 29 7 3,
      {cells := [("balance", .native 13), ("acceptedCredential", .native 29)],
       trees := [("count", .scalar (.uint (2 ^ 64 - 1) 6))]}) := by
  with_unfolding_all rfl

example :
    runEffectsWithEnv concreteContext advanceEntry.effects (callEnvironment 29 7 3)
      (concreteState 30 10 5) = .error "state transition guard failed" := by
  with_unfolding_all rfl

example :
    runEffectsWithEnv concreteContext advanceEntry.effects (callEnvironment 29 7 3)
      (concreteState 29 10 (2 ^ 64 - 1)) = .error "Counter addition overflow" := by
  with_unfolding_all rfl

end Noctium.Proofs.IndependentCalleeAdvance
