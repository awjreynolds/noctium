import Noctium.Verification

open Noctium Noctium.Verification

namespace VerificationFixture

private def withoutSettlementEffects (state : LedgerState) : LedgerState :=
  {state with unshieldedInputs := [], unshieldedOutputs := [], unshieldedSpendClaims := []}

def contract : Contract := {
  name := "ReviewedNoOp"
  entrypoints := [{name := "run", circuit := {name := "emptyRelation"}}]
}

def specification : Specification := {
  initial := fun state => state = {}
  invariant := fun _ => True
  precondition := fun _ inputs _ => inputs = []
  enabled := fun _ _ _ => True
  postcondition := fun _ _ before outputs after => outputs = [] ∧ after = withoutSettlementEffects before
}

def subject : Subject := {
  contract
  entrypoint := ⟨0, by decide⟩
  specification
}

def policy : AuditPolicy := {
  subject
  privacy := {scope := .allOutcomes}
  functionalGuarantee := "The no-op succeeds for empty inputs and preserves all public state."
  privacyGuarantee := "Under the reviewed precondition, equal public state has equal source results."
}

theorem entry_runs (ctx : EvalContext) (before : LedgerState) :
    subject.entry.run ctx [] before = .ok ([], withoutSettlementEffects before) := by rfl

theorem functional : FunctionalObligation policy := by
  constructor
  · intro before _
    trivial
  · intro ctx inputs before outputs after _ hpre hrun
    change inputs = [] at hpre
    subst inputs
    change subject.entry.run ctx [] before = .ok (outputs, after) at hrun
    rw [entry_runs] at hrun
    cases hrun
    exact ⟨⟨rfl, rfl⟩, True.intro⟩
  · intro ctx inputs before _ hpre _
    change inputs = [] at hpre
    subst inputs
    exact ⟨[], withoutSettlementEffects before, entry_runs ctx before⟩
  · exact ⟨{modulus := Field.modulus, poseidon2 := fun _ _ _ => .error "unused"}, [], {}, rfl, rfl, True.intro⟩

theorem privacy : PrivacyObligation policy := by
  intro left right hleft hright hpublic _ _
  have linputs : left.inputs = [] := hleft.2
  have rinputs : right.inputs = [] := hright.2
  have states : left.state = right.state := hpublic.2.1
  change subject.entry.run left.context left.inputs left.state =
    subject.entry.run right.context right.inputs right.state
  rw [linputs, rinputs, entry_runs, entry_runs, states]

def wrongContractPolicy : AuditPolicy :=
  {policy with subject := {subject with contract := {contract with name := "DifferentContract"}}}

def wrongSpecPolicy : AuditPolicy :=
  {policy with subject := {subject with specification := {specification with postcondition := fun _ _ _ _ _ => True}}}

theorem irrelevant : True := True.intro
theorem oneApprovedAxiom : True = True := propext Iff.rfl
axiom untrustedFalse : False
theorem fromUserAxiom : FunctionalObligation policy := False.elim untrustedFalse
theorem admitted : FunctionalObligation policy := by sorry
theorem alsoAdmitted : FunctionalObligation policy := by admit
theorem nativeTruth : 2 + 2 = 4 := by native_decide
theorem fromNativeComputation : FunctionalObligation policy :=
  (fun (_ : 2 + 2 = 4) => functional) nativeTruth

run_cmd do
  let env ← Lean.getEnv
  match Audit.axiomsIn env `VerificationFixture.oneApprovedAxiom with
  | .ok axioms =>
    unless axioms == #[`propext] do
      throwError "actual axiom closure must exclude unused approved axioms"
  | .error message => throwError "axiom closure inspection failed: {message}"
  for proof in [`VerificationFixture.functional, `VerificationFixture.privacy] do
    let role := if proof == `VerificationFixture.functional then Audit.Role.functional else .privacy
    unless (Audit.check env `VerificationFixture.policy proof role).isOk do
      throwError "legitimate proof rejected"
  for (p, proof) in [(`VerificationFixture.wrongContractPolicy, `VerificationFixture.functional),
      (`VerificationFixture.wrongSpecPolicy, `VerificationFixture.functional),
      (`VerificationFixture.policy, `VerificationFixture.irrelevant)] do
    match Audit.check env p proof .functional with
    | .error "wrong_obligation" => pure ()
    | _ => throwError "wrong subject/specification/proposition accepted"
  for proof in [`VerificationFixture.fromUserAxiom, `VerificationFixture.admitted,
      `VerificationFixture.alsoAdmitted, `VerificationFixture.fromNativeComputation] do
    match Audit.check env `VerificationFixture.policy proof .functional with
    | .error message => unless message.startsWith "forbidden_axiom:" do throwError "unexpected axiom failure: {message}"
    | .ok _ => throwError "untrusted axiom accepted"

#guard_msgs (drop info) in
#noctium_register_functional functional for policy

#guard_msgs (drop info) in
#noctium_register_privacy privacy for policy

#print axioms functional
#print axioms privacy

/- Functional correctness does not imply confidentiality. This source contract
intentionally authorizes its private Boolean at a public output. -/
def releasingContract : Contract := {
  name := "ReviewedRelease"
  entrypoints := [{name := "run", circuit := {
    name := "releaseRelation"
    inputs := [{name := "secret", ty := .bool, visibility := .«private»}]
    outputs := [⟨"released", .bool, .disclose {} (.ref "secret"), {}⟩]
  }}]
}

def releasingSpecification : Specification := {
  initial := fun state => state = {}
  invariant := fun _ => True
  precondition := fun _ inputs _ => ∃ bit, inputs = [("secret", .bool bit)]
  enabled := fun _ _ _ => True
  postcondition := fun _ inputs before outputs after =>
    (∃ bit, inputs = [("secret", .bool bit)] ∧ outputs = [("released", .bool bit)]) ∧ after = withoutSettlementEffects before
}

def releasingSubject : Subject := {
  contract := releasingContract
  entrypoint := ⟨0, by decide⟩
  specification := releasingSpecification
}

def releasingPolicy : AuditPolicy := {
  subject := releasingSubject
  privacy := {scope := .allOutcomes}
  functionalGuarantee := "Return the explicitly disclosed private Boolean."
  privacyGuarantee := "No-release privacy is false for this policy."
}

theorem release_runs (ctx : EvalContext) (before : LedgerState) (bit : Bool) :
    releasingSubject.entry.run ctx [("secret", .bool bit)] before =
      .ok ([("released", .bool bit)], withoutSettlementEffects before) := by cases bit <;> with_unfolding_all rfl

theorem releasingFunctional : FunctionalObligation releasingPolicy := by
  constructor
  · intro _ _
    trivial
  · intro ctx inputs before outputs after _ hpre hrun
    obtain ⟨bit, hinputs⟩ := hpre
    subst inputs
    change releasingSubject.entry.run ctx [("secret", .bool bit)] before = .ok (outputs, after) at hrun
    rw [release_runs] at hrun
    cases hrun
    exact ⟨⟨⟨bit, rfl, rfl⟩, rfl⟩, True.intro⟩
  · intro ctx inputs before _ hpre _
    obtain ⟨bit, hinputs⟩ := hpre
    subst inputs
    exact ⟨[("released", .bool bit)], withoutSettlementEffects before, release_runs ctx before bit⟩
  · exact ⟨{modulus := Field.modulus, poseidon2 := fun _ _ _ => .error "unused"},
      [("secret", .bool false)], {}, rfl, ⟨false, rfl⟩, True.intro⟩

theorem releasingNotPrivate : ¬ PrivacyObligation releasingPolicy := by
  intro h
  let ctx : EvalContext := {modulus := Field.modulus, poseidon2 := fun _ _ _ => .error "unused"}
  let left : Invocation := {context := ctx, inputs := [("secret", .bool false)], state := {}}
  let right : Invocation := {context := ctx, inputs := [("secret", .bool true)], state := {}}
  have hleft : releasingSubject.admissible left := ⟨True.intro, false, rfl⟩
  have hright : releasingSubject.admissible right := ⟨True.intro, true, rfl⟩
  have hpublic : releasingSubject.publicEquivalent left right := ⟨rfl, rfl, rfl⟩
  have impossible := h left right hleft hright hpublic True.intro True.intro
  change releasingSubject.entry.run ctx [("secret", .bool false)] {} =
    releasingSubject.entry.run ctx [("secret", .bool true)] {} at impossible
  rw [release_runs, release_runs] at impossible
  cases impossible

run_cmd do
  let env ← Lean.getEnv
  unless (Audit.check env `VerificationFixture.releasingPolicy `VerificationFixture.releasingFunctional .functional).isOk do
    throwError "legitimate release functional proof rejected"
  match Audit.check env `VerificationFixture.releasingPolicy `VerificationFixture.releasingFunctional .privacy with
  | .error "wrong_obligation" => pure ()
  | _ => throwError "functional correctness was mistaken for privacy"

/- Value-flow acceptance does not cover private-dependent failure observations.
The constraint retains unsigned subtraction, but releases no computed value. -/
def failureContract : Contract := {
  name := "ReviewedFailureChannel"
  entrypoints := [{name := "run", circuit := {
    name := "retainedUnsignedConstraint"
    inputs := [{name := "a", ty := .uint 1, visibility := .«private»},
      {name := "b", ty := .uint 1, visibility := .«private»}]
    constraints := [.eq (Expr.usub (m := 1) (n := 1) (.ref "a") (.ref "b"))
      (Expr.usub (m := 1) (n := 1) (.ref "a") (.ref "b"))]
    outputs := [⟨"accepted", .bool, .bool true, {}⟩]
  }}]
}

def failureInputs (a b : Nat) : EvalEnv := [("a", .uint 1 a), ("b", .uint 1 b)]

def failureSpecification : Specification := {
  initial := fun state => state = {}
  invariant := fun _ => True
  precondition := fun ctx inputs _ => ctx.modulus = Field.modulus ∧
    ∃ a b, a ≤ 1 ∧ b ≤ 1 ∧ inputs = failureInputs a b
  enabled := fun _ inputs _ => ∀ a b, inputs = failureInputs a b → b ≤ a
  postcondition := fun _ _ before outputs after => outputs = [("accepted", .bool true)] ∧ after = withoutSettlementEffects before
}

def failureSubject : Subject := {
  contract := failureContract
  entrypoint := ⟨0, by decide⟩
  specification := failureSpecification
}

def failurePolicy : AuditPolicy := {
  subject := failureSubject
  privacy := {scope := .successfulOnly}
  functionalGuarantee := "Canonical UInt inputs succeed when subtraction does not underflow; successes preserve state and return true."
  privacyGuarantee := "Equal public state gives equal successful source observations, excluding failure observations."
}

def failureAllOutcomesPolicy : AuditPolicy :=
  {failurePolicy with privacy := {scope := .allOutcomes}}

theorem failure_value_flow_accepts : Disclosure.contract failureContract = .ok () := by
  with_unfolding_all rfl

theorem failure_runs (ctx : EvalContext) (before : LedgerState) (a b : Nat)
    (hmod : ctx.modulus = Field.modulus) (ha : a ≤ 1) (hb : b ≤ 1) :
    failureSubject.entry.run ctx (failureInputs a b) before =
      if a < b then .error "unsigned subtraction underflow"
      else .ok ([("accepted", .bool true)], withoutSettlementEffects before) := by
  obtain ha : a = 0 ∨ a = 1 := by omega
  obtain hb : b = 0 ∨ b = 1 := by omega
  rcases ctx with ⟨modulus, oracle⟩
  change modulus = Field.modulus at hmod
  subst modulus
  rcases ha with rfl | rfl <;> rcases hb with rfl | rfl <;> with_unfolding_all rfl

theorem failureFunctional : FunctionalObligation failurePolicy := by
  constructor
  · intro _ _
    trivial
  · intro ctx inputs before outputs after _ hpre hrun
    obtain ⟨hmod, a, b, ha, hb, rfl⟩ := hpre
    change failureSubject.entry.run ctx (failureInputs a b) before = .ok (outputs, after) at hrun
    rw [failure_runs ctx before a b hmod ha hb] at hrun
    split at hrun
    · cases hrun
    · cases hrun
      exact ⟨⟨rfl, rfl⟩, True.intro⟩
  · intro ctx inputs before _ hpre henabled
    obtain ⟨hmod, a, b, ha, hb, rfl⟩ := hpre
    have hba : b ≤ a := henabled a b rfl
    refine ⟨[("accepted", .bool true)], withoutSettlementEffects before, ?_⟩
    change failureSubject.entry.run ctx (failureInputs a b) before = _
    rw [failure_runs ctx before a b hmod ha hb, ite_eq_right (by omega)]
  · refine ⟨{modulus := Field.modulus, poseidon2 := fun _ _ _ => .error "unused"},
      failureInputs 0 0, {}, rfl, ⟨rfl, 0, 0, by decide, by decide, rfl⟩, ?_⟩
    intro a b heq
    simp only [failureInputs, List.cons.injEq, Prod.mk.injEq, Value.uint.injEq] at heq
    omega

theorem failureSuccessfulPrivacy : PrivacyObligation failurePolicy := by
  intro left right hleft hright hpublic _ hscope
  obtain ⟨loutputs, lstate, hlrun⟩ := hscope.1
  obtain ⟨routputs, rstate, hrrun⟩ := hscope.2
  have hl := failureFunctional.preservation left.context left.inputs left.state loutputs lstate hleft.1 hleft.2 hlrun
  have hr := failureFunctional.preservation right.context right.inputs right.state routputs rstate hright.1 hright.2 hrrun
  rw [hlrun, hrrun, hl.1.1, hr.1.1, hl.1.2, hr.1.2, hpublic.2.1]

theorem failureNotAllOutcomesPrivate : ¬ PrivacyObligation failureAllOutcomesPolicy := by
  intro h
  let ctx : EvalContext := {modulus := Field.modulus, poseidon2 := fun _ _ _ => .error "unused"}
  let left : Invocation := {context := ctx, inputs := failureInputs 0 1, state := {}}
  let right : Invocation := {context := ctx, inputs := failureInputs 1 0, state := {}}
  have hleft : failureSubject.admissible left := ⟨True.intro, rfl, 0, 1, by decide, by decide, rfl⟩
  have hright : failureSubject.admissible right := ⟨True.intro, rfl, 1, 0, by decide, by decide, rfl⟩
  have hpublic : failureSubject.publicEquivalent left right := ⟨rfl, rfl, rfl⟩
  have impossible := h left right hleft hright hpublic True.intro True.intro
  change failureSubject.entry.run ctx (failureInputs 0 1) {} =
    failureSubject.entry.run ctx (failureInputs 1 0) {} at impossible
  rw [failure_runs ctx {} 0 1 rfl (by decide) (by decide),
    failure_runs ctx {} 1 0 rfl (by decide) (by decide)] at impossible
  cases impossible

run_cmd do
  let env ← Lean.getEnv
  unless (Audit.check env `VerificationFixture.failurePolicy `VerificationFixture.failureFunctional .functional).isOk do
    throwError "failure-channel functional proof rejected"
  unless (Audit.check env `VerificationFixture.failurePolicy `VerificationFixture.failureSuccessfulPrivacy .privacy).isOk do
    throwError "successful-only privacy proof rejected"
  match Audit.check env `VerificationFixture.failureAllOutcomesPolicy `VerificationFixture.failureSuccessfulPrivacy .privacy with
  | .error "wrong_obligation" => pure ()
  | _ => throwError "successful-only privacy was mistaken for all-outcomes privacy"

#print axioms failureFunctional
#print axioms failureSuccessfulPrivacy
#print axioms failureNotAllOutcomesPrivate

end VerificationFixture
