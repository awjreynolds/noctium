import Noctium.Verification

open Noctium Noctium.Verification

namespace ProofScaffoldFixture

private def withoutSettlementEffects (state : LedgerState) : LedgerState :=
  {state with unshieldedInputs := [], unshieldedOutputs := [], unshieldedSpendClaims := []}

def runEntry : Entrypoint := {name := "run", circuit := {name := "emptyRelation"}}
def otherEntry : Entrypoint := {name := "other", circuit := {name := "otherRelation"}}

def sourceContract : Contract := {
  name := "ScaffoldContract"
  entrypoints := [runEntry, otherEntry]
}

def specification : Specification := {
  initial := fun state => state = {}
  invariant := fun _ => True
  precondition := fun _ inputs _ => inputs = []
  enabled := fun _ _ _ => True
  postcondition := fun _ _ before outputs after =>
    outputs = [] ∧ after = withoutSettlementEffects before
}

def subject : Subject := {
  contract := sourceContract
  entrypoint := ⟨0, by decide⟩
  specification
}

def policy : AuditPolicy := {
  subject
  privacy := {scope := .allOutcomes}
  functionalGuarantee := "Run preserves the reviewed source state."
  privacyGuarantee := "Equal public views produce equal source outcomes."
}

def sameDisplayNameContract : Contract := {
  name := "ScaffoldContract"
  entrypoints := [{name := "run", circuit := {name := "differentRelation"}}, otherEntry]
}

def sameDisplayNamePolicy : AuditPolicy :=
  {policy with subject := {subject with contract := sameDisplayNameContract}}

def duplicateContract : Contract := {
  name := "DuplicateScaffoldContract"
  entrypoints := [runEntry, runEntry]
}

def duplicateSubject : Subject :=
  {subject with contract := duplicateContract}

def duplicatePolicy : AuditPolicy :=
  {policy with subject := duplicateSubject}

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
  · exact ⟨{modulus := Field.modulus, poseidon2 := fun _ _ _ => .error "unused"},
      [], {}, rfl, rfl, True.intro⟩

#guard_msgs (drop info) in
#noctium_register_functional functional for policy

/--
info: NOCTIUM_PROOF_SCAFFOLD
operation: ScaffoldContract.run (entrypoint index 0)
theorem ProofScaffoldFixture.policy.functionalScaffold : Noctium.Verification.FunctionalObligation
  ProofScaffoldFixture.policy := by
  constructor
  · intro before hInitial
    exact ?_
  · intro ctx inputs before outputs after hInvariant hPrecondition hRun
    exact ?_
  · intro ctx inputs before hInvariant hPrecondition hEnabled
    exact ?_
  · refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
-/
#guard_msgs in
#noctium_proof_scaffold functional for policy on sourceContract operation "run"

/--
info: NOCTIUM_PROOF_SCAFFOLD
operation: ScaffoldContract.run (entrypoint index 0)
theorem ProofScaffoldFixture.policy.privacyScaffold : Noctium.Verification.PrivacyObligation
  ProofScaffoldFixture.policy := by
  intro left right hLeftAdmissible hRightAdmissible hPublicEquivalent hReleaseAgreement hScope
  exact ?_
-/
#guard_msgs in
#noctium_proof_scaffold privacy for policy on sourceContract operation "run"

theorem policy.functionalScaffold : FunctionalObligation policy := functional

theorem policy.privacyScaffold : PrivacyObligation policy := by
  intro left right hleft hright hpublic _ _
  have leftInputs : left.inputs = [] := hleft.2
  have rightInputs : right.inputs = [] := hright.2
  have sameState : left.state = right.state := hpublic.2.1
  change subject.entry.run left.context left.inputs left.state =
    subject.entry.run right.context right.inputs right.state
  rw [leftInputs, rightInputs, entry_runs, entry_runs, sameState]

/--
error: proof_scaffold_contract_mismatch: selected contract is not kernel-equal to the policy contract
-/
#guard_msgs (substring := true) in
#noctium_proof_scaffold functional for policy on sameDisplayNameContract operation "run"

/--
error: proof_scaffold_policy_entrypoint_mismatch: policy selects index 0, named operation is at index 1
-/
#guard_msgs (substring := true) in
#noctium_proof_scaffold functional for policy on sourceContract operation "other"

/--
error: proof_scaffold_operation_missing
-/
#guard_msgs (substring := true) in
#noctium_proof_scaffold functional for policy on sourceContract operation "missing"

/--
error: proof_scaffold_operation_ambiguous
-/
#guard_msgs (substring := true) in
#noctium_proof_scaffold functional for duplicatePolicy on duplicateContract operation "run"

run_cmd do
  let registrations := proofRegistry.getState (← Lean.getEnv)
  unless registrations.size == 1 do
    throwError "proof scaffold changed the proof registry size"
  let some registration := registrations[0]? | throwError "proof registry entry is missing"
  unless registration.policy == ``ProofScaffoldFixture.policy &&
      registration.proof == ``ProofScaffoldFixture.functional &&
      registration.role == .functional do
    throwError "proof scaffold changed the existing proof registry entry"

end ProofScaffoldFixture
