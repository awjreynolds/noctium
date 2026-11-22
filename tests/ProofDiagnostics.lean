import Noctium.Verification

open Noctium Noctium.Verification

namespace ProofDiagnosticsFixture

private def withoutSettlementEffects (state : LedgerState) : LedgerState :=
  {state with unshieldedInputs := [], unshieldedOutputs := [], unshieldedSpendClaims := []}

def contract : Contract := {
  name := "DiagnosticContract"
  entrypoints := [{
    name := "run"
    circuit := {name := "emptyRelation"}
    span := {file := "tests/ProofDiagnostics.lean", line := 12, column := 3}
  }]
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
  contract
  entrypoint := ⟨0, by decide⟩
  specification
}

def policy : AuditPolicy := {
  subject
  privacy := {scope := .allOutcomes}
  functionalGuarantee := "Empty runs preserve the reviewed state."
  privacyGuarantee := "Equal public views produce equal source outcomes."
}

def differentPolicy : AuditPolicy :=
  {policy with subject := {subject with contract := {contract with name := "OtherDiagnosticContract"}}}

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

/--
error: wrong_obligation: submitted proof 'ProofDiagnosticsFixture.functional' has proposition:
  Noctium.Verification.FunctionalObligation ProofDiagnosticsFixture.policy
expected privacy proposition:
  Noctium.Verification.PrivacyObligation ProofDiagnosticsFixture.policy
contract/operation: DiagnosticContract.run
operation source location: tests/ProofDiagnostics.lean:12:3
-/
#guard_msgs (substring := true) in
#noctium_register_privacy functional for policy

/--
error: wrong_obligation: submitted proof 'ProofDiagnosticsFixture.functional' has proposition:
  Noctium.Verification.FunctionalObligation ProofDiagnosticsFixture.policy
expected functional proposition:
  Noctium.Verification.FunctionalObligation ProofDiagnosticsFixture.differentPolicy
contract/operation: OtherDiagnosticContract.run
operation source location: tests/ProofDiagnostics.lean:12:3
-/
#guard_msgs (substring := true) in
#noctium_register_functional functional for differentPolicy

run_cmd do
  let environment ← Lean.getEnv
  if (proofRegistry.getState environment).any
      (·.proof == ``ProofDiagnosticsFixture.functional) then
    throwError "a rejected proof entered the verification registry"

end ProofDiagnosticsFixture
