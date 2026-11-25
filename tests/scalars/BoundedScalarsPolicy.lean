import proofs.BoundedScalarsVerification

namespace Noctium.BoundedScalarsPolicyEvidence

open Noctium Noctium.Verification Noctium.BoundedScalarsVerification

private theorem subject_entry : subject.entry = applyEntry := by rfl

/-- The boundary vector uses both private operands at their maximum and matches
the public expected value exactly. -/
def acceptedBoundary : Inputs := ⟨510, 255, 255⟩

/-- This vector changes only the public expected value, so the source relation
rejects it before any ledger effect runs. -/
def rejectedExpected : Inputs := ⟨509, 255, 255⟩

theorem apply_declares_no_committed_returns : applyEntry.returns = [] := by
  with_unfolding_all rfl

theorem accepted_boundary_source_vector :
    applyEntry.run context (inputEnvironment acceptedBoundary) (state 0) =
      .ok ([("result", .uint 510 510)], state 510) := by
  exact apply_runs_when_enabled acceptedBoundary (by decide) (by decide) (by decide)

theorem rejected_expected_source_vector :
    applyEntry.run context (inputEnvironment rejectedExpected) (state 0) =
      .error "circuit constraint failed" := by
  with_unfolding_all rfl

theorem accepted_boundary_has_exact_postcondition :
    postcondition context (inputEnvironment acceptedBoundary) (state 0)
      [("result", .uint 510 510)] (state 510) := by
  exact ⟨acceptedBoundary, rfl, by decide, rfl, rfl, rfl⟩

/-- Both policies use this same initial, precondition, and enabled reachability
check. -/
def reachable (spec : Specification) : Prop :=
  ∃ ctx inputs before,
    spec.initial before ∧
    spec.precondition ctx inputs before ∧
    spec.enabled ctx inputs before

/-- Concrete nonvacuity witness for the unchanged registered production policy.
The source output is the internal result, and the contract declares no
committed returns. -/
theorem accepted_boundary_policy_witness :
    reachable policy.subject.specification ∧
    subject.entry.run context (inputEnvironment acceptedBoundary) (state 0) =
      .ok ([("result", .uint 510 510)], state 510) ∧
    postcondition context (inputEnvironment acceptedBoundary) (state 0)
      [("result", .uint 510 510)] (state 510) ∧
    subject.entry.returns = [] := by
  refine ⟨?_, ?_, accepted_boundary_has_exact_postcondition, ?_⟩
  · exact ⟨context, inputEnvironment acceptedBoundary, state 0,
      rfl, ⟨rfl, acceptedBoundary, rfl, by decide, by decide, by decide⟩,
      ⟨rfl, acceptedBoundary, rfl, by decide, by decide, by decide⟩⟩
  · rw [subject_entry]
    exact accepted_boundary_source_vector
  · change applyEntry.returns = []
    exact apply_declares_no_committed_returns

/-- Control policy changes only progress eligibility. It keeps the production
contract, entrypoint, and every other specification predicate. -/
def impossibleGuardSpecification : Specification :=
  { specification with enabled := fun _ _ _ => False }

def impossibleGuardSubject : Subject :=
  { subject with specification := impossibleGuardSpecification }

def impossibleGuardPolicy : AuditPolicy :=
  { policy with subject := impossibleGuardSubject }

theorem impossible_guard_changes_only_enabled :
    impossibleGuardSubject.contract = subject.contract ∧
    impossibleGuardSubject.entrypoint = subject.entrypoint ∧
    impossibleGuardSpecification.initial = specification.initial ∧
    impossibleGuardSpecification.invariant = specification.invariant ∧
    impossibleGuardSpecification.precondition = specification.precondition ∧
    impossibleGuardSpecification.postcondition = specification.postcondition ∧
    impossibleGuardSpecification.enabled = fun _ _ _ => False := by
  simp [impossibleGuardSubject, impossibleGuardSpecification, subject, specification]

/-- The control fails the same initial/precondition/enabled reachability check
used for the registered policy. -/
theorem impossible_guard_reachability_empty :
    ¬ reachable impossibleGuardPolicy.subject.specification := by
  rintro ⟨ctx, inputs, before, _initial, _precondition, enabled⟩
  exact enabled

end Noctium.BoundedScalarsPolicyEvidence
