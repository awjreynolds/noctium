import examples.openzeppelin.ConfidentialToken
import Noctium.Verification

namespace OpenZeppelinPort.ConfidentialTokenTotalSupply

open Noctium Verification

def supplyMaximum : Nat := 2 ^ 128 - 1

/-- Bind the subject to the getter at its actual index in the example contract. -/
def totalSupplyEntry : Entrypoint :=
  OpenZeppelinPort.ConfidentialToken.entrypoints[7]'(by decide)

theorem totalSupplyEntry_is_actual :
    totalSupplyEntry = OpenZeppelinPort.ConfidentialToken.entrypoints[7]'(by decide) ∧
      totalSupplyEntry.name = "totalSupply" := by
  constructor
  · rfl
  · decide

theorem noViewInputs_run (ctx : EvalContext) :
    noViewInputs.run ctx [] = .ok [] := by
  with_unfolding_all rfl

theorem totalSupply_entry_circuit : totalSupplyEntry.circuit = noViewInputs := by
  with_unfolding_all rfl

def totalSupplyRead : Effect :=
  .readCell "totalSupply" "currentSupply" (.uint supplyMaximum)

def totalSupplyReturn : Output := {
  name := "supply"
  ty := .uint supplyMaximum
  value := .ref "currentSupply"
  span := { file := "examples/openzeppelin/ConfidentialToken.lean", line := 769, column := 5 }
}

theorem totalSupply_entry_shape :
    totalSupplyEntry.effects = [totalSupplyRead] ∧
    totalSupplyEntry.effectGuards = [none] ∧
    totalSupplyEntry.returns = [totalSupplyReturn] := by
  constructor
  · with_unfolding_all rfl
  constructor
  · with_unfolding_all rfl
  · with_unfolding_all rfl

theorem totalSupply_disclosure_valid :
    Disclosure.entrypoint totalSupplyEntry = .ok () := by
  with_unfolding_all rfl

def sourceContext : EvalContext := {
  modulus := Field.modulus
  poseidon2 := fun _ _ _ => .error "unused"
}

def canonicalSupplyDomain (state : LedgerState) : Prop :=
  state.unshieldedInputs = [] ∧ state.unshieldedOutputs = [] ∧
  state.unshieldedSpendClaims = [] ∧
  state.cells.lookup "initialized" = some (.bool _root_.Bool.true) ∧
  ∃ supply, supply ≤ supplyMaximum ∧
    state.cells.lookup "totalSupply" = some (.uint supplyMaximum supply)

/-- The constructor explicitly sets initialized to true and leaves totalSupply
at its UInt128 default of zero. The proof assumes these source-derived values
and leaves other state free. -/
def sourceInitial (state : LedgerState) : Prop :=
  state.unshieldedInputs = [] ∧ state.unshieldedOutputs = [] ∧
  state.unshieldedSpendClaims = [] ∧
  state.cells.lookup "initialized" = some (.bool _root_.Bool.true) ∧
  state.cells.lookup "totalSupply" = some (.uint supplyMaximum 0)

def sourceState (supply : Nat) : LedgerState := {
  cells := [
    ("initialized", .bool _root_.Bool.true),
    ("totalSupply", .uint supplyMaximum supply)]
}

theorem source_initial_nonvacuous : sourceInitial (sourceState 0) := by
  unfold sourceInitial sourceState
  refine ⟨rfl, rfl, rfl, ?_, ?_⟩
  · simp only [List.lookup_cons]
    decide
  · simp only [List.lookup_cons]
    decide

theorem source_initial_in_domain (state : LedgerState)
    (initial : sourceInitial state) : canonicalSupplyDomain state := by
  rcases initial with ⟨inputs, outputs, claims, initialized, supply⟩
  exact ⟨inputs, outputs, claims, initialized, 0, by simp [supplyMaximum], supply⟩

theorem totalSupply_run (state : LedgerState) (supply : Nat)
    (supplyCell : state.cells.lookup "totalSupply" = some (.uint supplyMaximum supply))
    (supplyBound : supply ≤ supplyMaximum)
    (clean : state.unshieldedInputs = [] ∧ state.unshieldedOutputs = [] ∧
      state.unshieldedSpendClaims = []) :
    totalSupplyEntry.run sourceContext [] state =
      .ok ([ ("supply", .uint supplyMaximum supply) ], state) := by
  rcases clean with ⟨inputsEmpty, outputsEmpty, claimsEmpty⟩
  have maxLtModulus : supplyMaximum < Field.modulus := by decide
  have maxFitsPolicy : supplyMaximum ≤ ScalarPolicy.maxUint := by decide
  have supplyLtField : supply < Field.modulus :=
    Nat.lt_of_le_of_lt supplyBound maxLtModulus
  have maxNotLtSupply : ¬ supplyMaximum < supply := Nat.not_lt.mpr supplyBound
  have scalarNotLt : ¬ ScalarPolicy.maxUint < supplyMaximum :=
    Nat.not_lt_of_ge maxFitsPolicy
  have fieldNotLe : ¬ Field.modulus ≤ supply := Nat.not_le_of_gt supplyLtField
  have readNotCanonical :
      ¬ (ScalarPolicy.maxUint < supplyMaximum ∨ supplyMaximum < supply) := by
    exact not_or.mpr ⟨Nat.not_lt_of_ge maxFitsPolicy, Nat.not_lt.mpr supplyBound⟩
  have returnNotCanonical :
      ¬ (supplyMaximum ≤ ScalarPolicy.maxUint → supply ≤ supplyMaximum →
        Field.modulus ≤ supply) := by
    intro canonical
    exact fieldNotLe (canonical maxFitsPolicy supplyBound)
  simp only [Entrypoint.run, totalSupply_disclosure_valid, sourceContext]
  rw [totalSupply_entry_circuit, noViewInputs_run]
  rw [totalSupply_entry_shape.1, totalSupply_entry_shape.2.1, totalSupply_entry_shape.2.2]
  simp! [totalSupplyEntry, totalSupplyRead, totalSupplyReturn,
    OpenZeppelinPort.ConfidentialToken, supplyMaximum,
    runEffectsWithGuardsAndEnv, runEffectsWithEnv, runEffectWithEnv,
    supplyCell, supplyBound, maxLtModulus, maxFitsPolicy,
    scalarNotLt, fieldNotLe, inputsEmpty, outputsEmpty, claimsEmpty]
  simp_all [totalSupplyRead, totalSupplyReturn, Expr.eval, Value.as, Value.pack,
    ScalarPolicy.maxUint, ScalarPolicy.maxBits, readNotCanonical, returnNotCanonical,
    maxNotLtSupply, supplyCell, supplyBound, supplyMaximum, Field.modulus]
  split
  · exact False.elim (Nat.not_lt_of_ge supplyBound ‹_›)
  · have maxFitsPolicy : supplyMaximum ≤ ScalarPolicy.maxUint := by decide
    have outputNotCanonical :
        ¬ (supplyMaximum ≤ ScalarPolicy.maxUint → Field.modulus ≤ supply) := by
      intro canonical
      exact Nat.not_le_of_gt supplyLtField (canonical maxFitsPolicy)
    simp! [supplyBound, supplyLtField, outputNotCanonical, supplyMaximum, sourceContext]
    split
    · exact False.elim (outputNotCanonical ‹_›)
    · simp [Functor.map, Except.map, outputNotCanonical, supplyBound, supplyLtField,
        Nat.not_le_of_gt supplyLtField, supplyMaximum, sourceContext,
        inputsEmpty, outputsEmpty, claimsEmpty]
      cases state <;> simp_all [Except.pure]
      all_goals rfl

def specification : Specification := {
  initial := sourceInitial
  invariant := canonicalSupplyDomain
  precondition := fun ctx inputs _ => ctx = sourceContext ∧ inputs = []
  enabled := fun _ _ state => canonicalSupplyDomain state
  postcondition := fun _ _ before outputs after =>
    ∃ supply, supply ≤ supplyMaximum ∧
      before.cells.lookup "totalSupply" = some (.uint supplyMaximum supply) ∧
      outputs = [("supply", .uint supplyMaximum supply)] ∧ after = before
}

def subject : Subject := {
  contract := OpenZeppelinPort.ConfidentialToken
  entrypoint := ⟨7, by decide⟩
  specification
}

def policy : AuditPolicy := {
  subject
  privacy := { releases := .none, scope := .successfulOnly }
  functionalGuarantee := "On initialized canonical source states with no pending settlement data and no inputs, totalSupply returns the stored UInt128 supply and preserves the full ledger state."
  privacyGuarantee := "Successful executions with equal public inputs, context and ledger state return the same public supply and state. No extra release is declared."
}

theorem subject_entry : subject.entry = totalSupplyEntry := by rfl

theorem functional : FunctionalObligation policy := by
  constructor
  · intro before initial
    exact source_initial_in_domain before initial
  · intro ctx inputs before outputs after invariant pre success
    rcases invariant with ⟨inputsEmpty, outputsEmpty, claimsEmpty, initialized, supply⟩
    rcases supply with ⟨supply, supplyBound, supplyCell⟩
    rcases pre with ⟨contextEq, inputsEq⟩
    subst ctx
    subst inputs
    change totalSupplyEntry.run sourceContext [] before = .ok (outputs, after) at success
    have exactRun := totalSupply_run before supply supplyCell supplyBound
      ⟨inputsEmpty, outputsEmpty, claimsEmpty⟩
    rw [exactRun] at success
    injection success with pairEq
    cases pairEq
    exact ⟨⟨supply, supplyBound, supplyCell, rfl, rfl⟩,
      ⟨inputsEmpty, outputsEmpty, claimsEmpty, initialized,
        ⟨supply, supplyBound, supplyCell⟩⟩⟩
  · intro ctx inputs before invariant pre enabled
    rcases invariant with ⟨inputsEmpty, outputsEmpty, claimsEmpty, initialized, supply⟩
    rcases supply with ⟨supply, supplyBound, supplyCell⟩
    rcases pre with ⟨contextEq, inputsEq⟩
    subst ctx
    subst inputs
    exact ⟨[("supply", .uint supplyMaximum supply)], before,
      totalSupply_run before supply supplyCell supplyBound
        ⟨inputsEmpty, outputsEmpty, claimsEmpty⟩⟩
  · refine ⟨sourceContext, [], sourceState 0, ?_, ?_, ?_⟩
    · exact source_initial_nonvacuous
    · exact ⟨rfl, rfl⟩
    · exact source_initial_in_domain _ source_initial_nonvacuous

/-- The actual getter circuit declares no public source inputs. The return is
the only observed public value in this source policy. -/
theorem actual_public_observer : subject.publicInputs [] = [] := by
  change (subject.entry.circuit.inputs.filter (·.visibility == .«public»)).map
    (fun input => (input.name, (([] : EvalEnv).lookup input.name))) = []
  rw [subject_entry, totalSupply_entry_circuit]
  rfl

theorem privacy : PrivacyObligation policy := by
  intro left right leftAdmissible rightAdmissible equivalent _release _covered
  rcases left with ⟨leftContext, leftInputs, leftState⟩
  rcases right with ⟨rightContext, rightInputs, rightState⟩
  rcases equivalent with ⟨sameContext, sameState, _samePublicInputs⟩
  dsimp only at sameContext sameState
  subst rightContext
  subst rightState
  rcases leftAdmissible with ⟨leftInvariant, leftPrecondition⟩
  rcases rightAdmissible with ⟨_rightInvariant, rightPrecondition⟩
  rcases leftPrecondition with ⟨leftContextEq, leftInputsEq⟩
  rcases rightPrecondition with ⟨_rightContextEq, rightInputsEq⟩
  change leftContext = sourceContext at leftContextEq
  change leftInputs = [] at leftInputsEq
  change rightInputs = [] at rightInputsEq
  subst leftContext
  subst leftInputs
  subst rightInputs
  rcases leftInvariant with ⟨inputsEmpty, outputsEmpty, claimsEmpty, _initialized,
    ⟨supply, supplyBound, supplyCell⟩⟩
  change totalSupplyEntry.run sourceContext [] leftState =
    totalSupplyEntry.run sourceContext [] leftState
  rw [totalSupply_run leftState supply supplyCell supplyBound
    ⟨inputsEmpty, outputsEmpty, claimsEmpty⟩]

def malformedState : LedgerState := {
  cells := [("initialized", .bool _root_.Bool.true)]
}

theorem malformed_missing_supply_rejected :
    totalSupplyEntry.run sourceContext [] malformedState =
      .error "missing state cell 'totalSupply'" := by
  simp only [Entrypoint.run, totalSupply_disclosure_valid, sourceContext]
  rw [totalSupply_entry_circuit, noViewInputs_run]
  rw [totalSupply_entry_shape.1, totalSupply_entry_shape.2.1]
  simp! [runEffectsWithGuardsAndEnv, runEffectsWithEnv, runEffectWithEnv,
    totalSupplyRead, malformedState]
  have missingError :
      (throw (toString "missing state cell '" ++ toString "totalSupply" ++ toString "'") :
        Except String Unit) = .error "missing state cell 'totalSupply'" := by rfl
  rw [missingError]
  simp only [Bind.bind, Except.bind, Except.pure, instMonadExceptOfExcept]

theorem changed_output_rejected :
    totalSupplyEntry.run sourceContext [] (sourceState 0) ≠
      .ok ([ ("supply", .uint supplyMaximum 1) ], sourceState 0) := by
  rw [totalSupply_run (sourceState 0) 0 (by simp [sourceState, supplyMaximum, List.lookup_cons])
    (by simp [supplyMaximum]) ⟨rfl, rfl, rfl⟩]
  simp

def wrongSubjectPolicy : AuditPolicy := {
  policy with
  subject := { subject with entrypoint := ⟨6, by decide⟩ }
}

run_cmd do
  let env ← Lean.getEnv
  unless (Audit.check env ``policy ``functional .functional).isOk do
    throwError "totalSupply functional proof rejected"
  unless (Audit.check env ``policy ``privacy .privacy).isOk do
    throwError "totalSupply privacy proof rejected"
  for (badPolicy, proof, role) in [
      (``policy, ``privacy, Audit.Role.functional),
      (``wrongSubjectPolicy, ``functional, Audit.Role.functional)] do
    match Audit.check env badPolicy proof role with
    | .error "wrong_obligation" => pure ()
    | _ => throwError "wrong role or wrong source subject accepted"

#noctium_register_functional functional for policy
#noctium_register_privacy privacy for policy
#print axioms functional
#print axioms privacy

end OpenZeppelinPort.ConfidentialTokenTotalSupply
