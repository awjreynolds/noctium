import proofs.PrivateClaimVerification

namespace Noctium.PrivateClaimReachability

open Noctium Noctium.Verification Noctium.PrivateClaimProofs Noctium.PrivateClaimVerification

/-- Unregistered mutant of the actual claim policy. Only progress eligibility
changes, so the mutant retains the actual source contract and all other policy
predicates. -/
def disabledEnabledSpecification : Specification :=
  {specification with enabled := fun _ _ _ => False}

def disabledEnabledSubject : Subject :=
  {subject with specification := disabledEnabledSpecification}

def disabledEnabledPolicy : AuditPolicy :=
  {policy with subject := disabledEnabledSubject}

theorem mutant_changes_only_enabled :
    disabledEnabledSubject.contract = subject.contract ∧
    disabledEnabledSubject.entrypoint = subject.entrypoint ∧
    disabledEnabledSpecification.initial = specification.initial ∧
    disabledEnabledSpecification.invariant = specification.invariant ∧
    disabledEnabledSpecification.precondition = specification.precondition ∧
    disabledEnabledSpecification.postcondition = specification.postcondition ∧
    disabledEnabledSpecification.enabled = fun _ _ _ => False := by
  simp [disabledEnabledSubject, disabledEnabledSpecification, subject, specification]

/-- Every enabled-progress implication holds because the mutant has no enabled
invocations. This does not provide a reachable execution. -/
theorem disabled_progress_vacuous :
    ∀ ctx inputs before,
      disabledEnabledSpecification.invariant before →
      disabledEnabledSpecification.precondition ctx inputs before →
      disabledEnabledSpecification.enabled ctx inputs before →
      ∃ outputs after, disabledEnabledSubject.entry.run ctx inputs before =
        .ok (outputs, after) := by
  intro ctx inputs before _ _ enabled
  change False at enabled
  exact False.elim enabled

theorem disabled_reachability_empty :
    ¬ ∃ ctx inputs before,
      disabledEnabledSpecification.initial before ∧
      disabledEnabledSpecification.precondition ctx inputs before ∧
      disabledEnabledSpecification.enabled ctx inputs before := by
  rintro ⟨ctx, inputs, before, _initial, _precondition, enabled⟩
  change False at enabled
  exact enabled

/-- The full functional obligation includes nonvacuity, so the disabled mutant
cannot satisfy it even though its universal progress field is vacuous. -/
theorem disabled_policy_not_functional :
    ¬ FunctionalObligation disabledEnabledPolicy := by
  intro correctness
  rcases correctness.nonvacuity with ⟨ctx, inputs, before, _initial, _precondition, enabled⟩
  change False at enabled
  exact enabled

/-- The unmodified public policy still has an admitted witness, a successful
actual claim, and replay rejection from the resulting state. -/
theorem baseline_admitted_claim_and_replay :
    ∃ ctx inputs before outputs after,
      specification.initial before ∧
      specification.precondition ctx inputs before ∧
      specification.enabled ctx inputs before ∧
      claimEntry.run ctx inputs before = .ok (outputs, after) ∧
      claimEntry.run ctx inputs after = .error "state map key already present" := by
  have baseline : FunctionalObligation policy := functional
  obtain ⟨ctx, inputs, before, initial, precondition, enabled⟩ := baseline.nonvacuity
  have inv := baseline.initialization before initial
  obtain ⟨outputs, after, success⟩ := baseline.progress ctx inputs before inv precondition enabled
  obtain ⟨post, _afterInvariant⟩ := baseline.preservation ctx inputs before outputs after
    inv precondition success
  rcases post with ⟨_input, _values, _inputsExact, _beforeExact, _unspent, _rootEval,
    _nullifierEval, _outputsExact, _afterExact, replay⟩
  refine ⟨ctx, inputs, before, outputs, after, initial, precondition, enabled, ?_, ?_⟩
  · simpa [policy, subject_entry] using success
  · simpa [policy, subject_entry] using replay

end Noctium.PrivateClaimReachability
