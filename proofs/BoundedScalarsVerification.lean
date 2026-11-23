import examples.BoundedScalars
import Noctium.Verification

namespace Noctium.BoundedScalarsVerification
open Noctium Verification

structure InputValues where
  expected : Nat
  left : Nat
  right : Nat

def inputEnvironment (input : InputValues) : EvalEnv :=
  [("expected", .uint 510 input.expected), ("left", .uint 255 input.left),
    ("right", .uint 255 input.right)]

def ledgerState (total : Nat) : LedgerState :=
  { cells := [("total", .uint 510 total)] }

def boundedEntry : Entrypoint :=
  BoundedScalars.entrypoints.headD {name := "missing", circuit := {name := "missing"}}

def sumExpression : Expr (.uint 510) :=
  .uadd (m := 255) (n := 255) (.ref "left") (.ref "right")

/-- Values admitted by the actual source types: UIntRange 511 has maximum 510. -/
def CanonicalInputs (ctx : EvalContext) (input : InputValues) : Prop :=
  ctx.modulus = Field.modulus ∧ input.expected ≤ 510 ∧ input.left ≤ 255 ∧ input.right ≤ 255

def initial (before : LedgerState) : Prop := before = ledgerState 0

def invariant (before : LedgerState) : Prop :=
  ∃ total, total ≤ 510 ∧ before = ledgerState total

def precondition (ctx : EvalContext) (inputs : EvalEnv) (_before : LedgerState) : Prop :=
  ∃ input, inputs = inputEnvironment input ∧ CanonicalInputs ctx input

def enabled (ctx : EvalContext) (inputs : EvalEnv) (before : LedgerState) : Prop :=
  ∃ input, inputs = inputEnvironment input ∧ CanonicalInputs ctx input ∧
    before = ledgerState 0 ∧ input.left + input.right = input.expected

def postcondition (_ctx : EvalContext) (inputs : EvalEnv) (before : LedgerState)
    (outputs : EvalEnv) (after : LedgerState) : Prop :=
  ∃ input total, inputs = inputEnvironment input ∧ before = ledgerState total ∧ total = 0 ∧
    input.left + input.right = input.expected ∧
    outputs = [("result", .uint 510 input.expected)] ∧ after = ledgerState input.expected

def specification : Specification := { initial, invariant, precondition, enabled, postcondition }

def subject : Subject := { contract := BoundedScalars, entrypoint := ⟨0, by decide⟩, specification }

def policy : AuditPolicy := {
  subject
  privacy := { releases := .none, scope := .successfulOnly }
  functionalGuarantee := "Canonical bounded inputs with a zero total cell and a satisfying sum make progress; accepted calls return the exact public result, write it to total, and preserve the bounded state invariant."
  privacyGuarantee := "Successful calls with equal public inputs, public state, and context have equal outputs and final state. No extra release is declared."
}

def fixtureContext : EvalContext :=
  { modulus := Field.modulus, poseidon2 := fun _ _ _ => .error "unused" }

theorem source_circuit_constraints :
    boundedEntry.circuit.constraints =
      [Expr.eq sumExpression sumExpression, Expr.eq sumExpression (.ref "expected")] := by
  with_unfolding_all rfl

theorem source_entry_disclosure_valid : Disclosure.entrypoint boundedEntry = .ok () := by
  with_unfolding_all rfl

theorem source_circuit_validate (ctx : EvalContext) (hmod : ctx.modulus = Field.modulus) :
    boundedEntry.circuit.validate (evaluationCapabilities ctx) = .ok () := by
  have hprofile : evaluationCapabilities ctx = evaluationCapabilities fixtureContext := by
    simp [evaluationCapabilities, fixtureContext, hmod]
  rw [hprofile]
  with_unfolding_all rfl

private theorem expected_eval (ctx : EvalContext) (input : InputValues)
    (hinput : CanonicalInputs ctx input) :
    (Expr.ref "expected" : Expr (.uint 510)).eval ctx (inputEnvironment input) =
      .ok input.expected := by
  have hlt : input.expected < ctx.modulus := by
    rw [hinput.1]
    exact Nat.lt_of_le_of_lt hinput.2.1 (by decide)
  have hlookup : (inputEnvironment input).lookup "expected" =
      some (.uint 510 input.expected) := by simp [inputEnvironment, List.lookup]
  have hmax : 510 ≤ ScalarPolicy.maxUint := by decide
  simp only [Expr.eval, hlookup, Value.as]
  change (if !(510 ≤ ScalarPolicy.maxUint && input.expected ≤ 510 && input.expected < ctx.modulus)
    then (Except.error "noncanonical value 'expected'" : Except String Nat)
    else (Except.ok input.expected : Except String Nat)) = Except.ok input.expected
  simp [hmax, hinput.2.1, hlt] <;> rfl

private theorem left_eval (ctx : EvalContext) (input : InputValues)
    (hinput : CanonicalInputs ctx input) :
    (Expr.ref "left" : Expr (.uint 255)).eval ctx (inputEnvironment input) = .ok input.left := by
  have hlt : input.left < ctx.modulus := by
    rw [hinput.1]
    exact Nat.lt_of_le_of_lt hinput.2.2.1 (by decide)
  have hlookup : (inputEnvironment input).lookup "left" =
      some (.uint 255 input.left) := by simp [inputEnvironment, List.lookup]
  have hmax : 255 ≤ ScalarPolicy.maxUint := by decide
  simp only [Expr.eval, hlookup, Value.as]
  change (if !(255 ≤ ScalarPolicy.maxUint && input.left ≤ 255 && input.left < ctx.modulus)
    then (Except.error "noncanonical value 'left'" : Except String Nat)
    else (Except.ok input.left : Except String Nat)) = Except.ok input.left
  simp [hmax, hinput.2.2.1, hlt] <;> rfl

private theorem right_eval (ctx : EvalContext) (input : InputValues)
    (hinput : CanonicalInputs ctx input) :
    (Expr.ref "right" : Expr (.uint 255)).eval ctx (inputEnvironment input) = .ok input.right := by
  have hlt : input.right < ctx.modulus := by
    rw [hinput.1]
    exact Nat.lt_of_le_of_lt hinput.2.2.2 (by decide)
  have hlookup : (inputEnvironment input).lookup "right" =
      some (.uint 255 input.right) := by simp [inputEnvironment, List.lookup]
  have hmax : 255 ≤ ScalarPolicy.maxUint := by decide
  simp only [Expr.eval, hlookup, Value.as]
  change (if !(255 ≤ ScalarPolicy.maxUint && input.right ≤ 255 && input.right < ctx.modulus)
    then (Except.error "noncanonical value 'right'" : Except String Nat)
    else (Except.ok input.right : Except String Nat)) = Except.ok input.right
  simp [hmax, hinput.2.2.2, hlt] <;> rfl

private theorem sum_eval (ctx : EvalContext) (input : InputValues)
    (hinput : CanonicalInputs ctx input) :
    sumExpression.eval ctx (inputEnvironment input) = .ok (input.left + input.right) := by
  have hleft := left_eval ctx input hinput
  have hright := right_eval ctx input hinput
  have hbound : input.left + input.right ≤ 510 := by
    calc
      input.left + input.right ≤ 255 + 255 := Nat.add_le_add hinput.2.2.1 hinput.2.2.2
      _ = 510 := by decide
  have hmodulus : input.left + input.right < ctx.modulus := by
    rw [hinput.1]
    exact Nat.lt_of_le_of_lt hbound (by decide)
  simp only [sumExpression, Expr.eval, hleft, hright]
  change (if 510 ≤ ScalarPolicy.maxUint && input.left + input.right ≤ 510 &&
      input.left + input.right < ctx.modulus
    then Except.ok (input.left + input.right)
    else Except.error "scalar conversion exceeds unsigned bound") = Except.ok (input.left + input.right)
  have htype : 510 ≤ ScalarPolicy.maxUint := by decide
  simp [htype, hbound, hmodulus]

private theorem source_constraints_run (ctx : EvalContext) (input : InputValues)
    (hinput : CanonicalInputs ctx input) :
    runConstraints ctx (inputEnvironment input) boundedEntry.circuit.constraints =
      if input.left + input.right = input.expected then .ok ()
      else .error "circuit constraint failed" := by
  have hsum := sum_eval ctx input hinput
  have hexpected := expected_eval ctx input hinput
  have hself : (Expr.eq sumExpression sumExpression).eval ctx (inputEnvironment input) =
      Except.ok Bool.true := by
    simp only [Expr.eval, hsum]
    change Except.ok (input.left + input.right == input.left + input.right) = Except.ok Bool.true
    simp
  have heq : (Expr.eq sumExpression (.ref "expected")).eval ctx (inputEnvironment input) =
      Except.ok (input.left + input.right == input.expected) := by
    simp only [Expr.eval, hsum, hexpected]
    change Except.ok (input.left + input.right == input.expected) =
      Except.ok (input.left + input.right == input.expected)
    rfl
  rw [source_circuit_constraints]
  by_cases hsumValues : input.left + input.right = input.expected
  · simp [runConstraints, hself, heq, hsumValues]
  · have hbeq : (input.left + input.right == input.expected) = Bool.false := by
      apply Bool.eq_false_iff.mpr
      intro htrue
      exact hsumValues (eq_of_beq htrue)
    simp [runConstraints, hself, heq, hbeq, hsumValues]

theorem source_circuit_run (ctx : EvalContext) (input : InputValues)
    (hinput : CanonicalInputs ctx input) :
    boundedEntry.circuit.run ctx (inputEnvironment input) =
      if input.left + input.right = input.expected then
        .ok [("result", .uint 510 input.expected)]
      else .error "circuit constraint failed" := by
  have hvalidate := source_circuit_validate ctx hinput.1
  have hconstraints := source_constraints_run ctx input hinput
  have hexpectedlt : input.expected < ctx.modulus := by
    rw [hinput.1]
    exact Nat.lt_of_le_of_lt hinput.2.1 (by decide)
  have hleftlt : input.left < ctx.modulus := by
    rw [hinput.1]
    exact Nat.lt_of_le_of_lt hinput.2.2.1 (by decide)
  have hrightlt : input.right < ctx.modulus := by
    rw [hinput.1]
    exact Nat.lt_of_le_of_lt hinput.2.2.2 (by decide)
  have hexpectedField : input.expected < Field.modulus := by simpa [hinput.1] using hexpectedlt
  have hleftField : input.left < Field.modulus := by simpa [hinput.1] using hleftlt
  have hrightField : input.right < Field.modulus := by simpa [hinput.1] using hrightlt
  have hmax510 : 510 ≤ ScalarPolicy.maxUint := by decide
  have hmax255 : 255 ≤ ScalarPolicy.maxUint := by decide
  have huniq : ["expected", "left", "right"].eraseDups.length = 3 := by decide
  have hexpectedNotField : ¬ Field.modulus ≤ input.expected := by omega
  have hleftNotField : ¬ Field.modulus ≤ input.left := by omega
  have hrightNotField : ¬ Field.modulus ≤ input.right := by omega
  have hsource : boundedEntry.circuit = boundedRelation := by with_unfolding_all rfl
  rw [hsource] at hvalidate hconstraints
  have hconstraintsExact := hconstraints
  simp [boundedRelation, inputEnvironment] at hconstraintsExact
  have hresultEval : Expr.eval ctx
      [("expected", .uint 510 input.expected), ("left", .uint 255 input.left),
        ("right", .uint 255 input.right)] (Expr.ref "expected" : Expr (.uint 510)) =
      (Except.ok input.expected : Except String Nat) := by
    simpa [inputEnvironment] using expected_eval ctx input hinput
  unfold Circuit.run
  rw [hsource]
  rw [hvalidate]
  simp [inputEnvironment, uniqueNames, List.lookup, Value.as, ScalarPolicy.maxUint,
    ScalarPolicy.maxBits, canonical_eq, boundedRelation, hinput.1, hinput.2.1,
    hinput.2.2.1, hinput.2.2.2, hexpectedlt, hleftlt, hrightlt, hconstraintsExact,
    hmax510, hmax255, huniq, hexpectedNotField, hleftNotField, hrightNotField,
    Value.pack, sum_eval, expected_eval, Except.bind, Except.map]
  by_cases hsum : input.left + input.right = input.expected
  · simp only [if_pos hsum]
    rw [hresultEval]
    rfl
  · simp only [if_neg hsum]
    rfl

private theorem bind_ok {α β : Type} (value : α) (next : α → Except String β) :
    ((Except.ok value : Except String α) >>= next) = next value := rfl
private theorem bind_error {α β : Type} (message : String) (next : α → Except String β) :
    ((Except.error message : Except String α) >>= next) = .error message := rfl
private theorem map_ok {α β : Type} (f : α → β) (value : α) :
    f <$> (Except.ok value : Except String α) = Except.ok (f value) := rfl
private theorem map_error {α β : Type} (f : α → β) (message : String) :
    f <$> (Except.error message : Except String α) = Except.error message := rfl
private theorem throw_error {α : Type} (message : String) :
    (throw message : Except String α) = .error message := rfl
private theorem pure_ok {α : Type} (value : α) :
    (pure value : Except String α) = .ok value := rfl
attribute [local simp] bind_ok bind_error map_ok map_error throw_error pure_ok

private theorem source_entry_guards :
    boundedEntry.effectGuards = [none, none, none] := by with_unfolding_all rfl

private theorem source_entry_returns : boundedEntry.returns = [] := by with_unfolding_all rfl

private theorem source_entry_effect_count : boundedEntry.effects.length = 3 := by
  with_unfolding_all rfl

private theorem apply_effects_zero (ctx : EvalContext) (expected : Nat) (tail : EvalEnv)
    (hmod : ctx.modulus = Field.modulus) (hexpected : expected ≤ 510) :
    runEffectsWithEnv ctx boundedEntry.effects
      ([ ("result", .uint 510 expected) ] ++ tail) (ledgerState 0) =
      .ok (("old", .uint 510 0) :: ([ ("result", .uint 510 expected) ] ++ tail),
        ledgerState expected) := by
  have hmax : 510 ≤ ScalarPolicy.maxUint := by decide
  have hfield : 510 < Field.modulus := Nat.lt_of_le_of_lt hmax ScalarPolicy.maxUint_lt_native
  have heField : ¬ Field.modulus ≤ expected := by omega
  have hemax : ¬ 510 < expected := by omega
  have hmodPos : 0 < Field.modulus := by omega
  have hmodNe : Field.modulus ≠ 0 := Nat.ne_of_gt hmodPos
  simp! [runEffectsWithEnv, boundedEntry, BoundedScalars, ledgerState, Expr.eval, Value.as,
    Value.pack, List.forIn_cons, List.forIn_nil, List.lookup, hmod, hfield, hmax, heField,
    hemax, hmodPos, hmodNe, Except.pure, Except.bind, Except.map]
  simp [Except.bind, Except.pure, Except.map, List.lookup, updateAssoc]

private theorem apply_effects_nonzero (ctx : EvalContext) (expected total : Nat) (tail : EvalEnv)
    (hmod : ctx.modulus = Field.modulus) (hexpected : expected ≤ 510)
    (htotal : total ≤ 510) (hne : total ≠ 0) :
    runEffectsWithEnv ctx boundedEntry.effects
      ([ ("result", .uint 510 expected) ] ++ tail) (ledgerState total) =
      .error "state transition guard failed" := by
  have hmax : 510 ≤ ScalarPolicy.maxUint := by decide
  have hfield : 510 < Field.modulus := Nat.lt_of_le_of_lt hmax ScalarPolicy.maxUint_lt_native
  have heField : ¬ Field.modulus ≤ expected := by omega
  have hemax : ¬ 510 < expected := by omega
  have htField : ¬ Field.modulus ≤ total := by omega
  have htLtField : total < Field.modulus := by omega
  have hpos : 0 < total := Nat.pos_of_ne_zero hne
  have hn510 : ¬ 510 < total := by omega
  have hmodPos : 0 < Field.modulus := by omega
  have hmodNe : Field.modulus ≠ 0 := Nat.ne_of_gt hmodPos
  simp! [runEffectsWithEnv, boundedEntry, BoundedScalars, ledgerState, Expr.eval, Value.as,
    Value.pack, List.forIn_cons, List.forIn_nil, List.lookup, hmod, hfield, hmax, heField,
    hemax, hmodPos, hmodNe, htField, htLtField, hpos, hn510, Except.pure, Except.bind,
    Except.map]
  simp [Except.bind, Except.pure, Except.map, List.lookup, updateAssoc, hne]

theorem source_entry_run (ctx : EvalContext) (input : InputValues) (total : Nat)
    (hinput : CanonicalInputs ctx input) (htotal : total ≤ 510) :
    subject.entry.run ctx (inputEnvironment input) (ledgerState total) =
      if input.left + input.right = input.expected then
        if total = 0 then
          .ok ([ ("result", .uint 510 input.expected) ], ledgerState input.expected)
        else .error "state transition guard failed"
      else .error "circuit constraint failed" := by
  have hentry : subject.entry = boundedEntry := by rfl
  rw [hentry]
  simp only [Entrypoint.run, source_entry_disclosure_valid]
  rw [source_circuit_run ctx input hinput]
  by_cases hsum : input.left + input.right = input.expected
  · simp only [if_pos hsum]
    by_cases hzero : total = 0
    · simp only [if_pos hzero]
      have heffects := apply_effects_zero ctx input.expected (inputEnvironment input)
        hinput.1 hinput.2.1
      change runEffectsWithEnv ctx boundedEntry.effects
          (("result", .uint 510 input.expected) :: inputEnvironment input)
          ({cells := [("total", .uint 510 0)]} : LedgerState) =
        .ok (("old", .uint 510 0) :: (("result", .uint 510 input.expected) :: inputEnvironment input),
          ({cells := [("total", .uint 510 input.expected)]} : LedgerState)) at heffects
      simp [runEffectsWithGuardsAndEnv, source_entry_guards, source_entry_returns,
        source_entry_effect_count,
        ledgerState, hzero, heffects]
    · have heffects := apply_effects_nonzero ctx input.expected total (inputEnvironment input)
        hinput.1 hinput.2.1 htotal hzero
      change runEffectsWithEnv ctx boundedEntry.effects
          (("result", .uint 510 input.expected) :: inputEnvironment input)
          ({cells := [("total", .uint 510 total)]} : LedgerState) =
        .error "state transition guard failed" at heffects
      simp [runEffectsWithGuardsAndEnv, source_entry_guards, source_entry_returns,
        source_entry_effect_count,
        ledgerState, hzero, heffects]
  · simp [hsum]

theorem successful_transition (ctx : EvalContext) (input : InputValues) (total : Nat)
    (outputs : EvalEnv) (after : LedgerState)
    (hinput : CanonicalInputs ctx input) (htotal : total ≤ 510)
    (success : subject.entry.run ctx (inputEnvironment input) (ledgerState total) =
      .ok (outputs, after)) :
    input.left + input.right = input.expected ∧ total = 0 ∧
      outputs = [("result", .uint 510 input.expected)] ∧ after = ledgerState input.expected := by
  rw [source_entry_run ctx input total hinput htotal] at success
  by_cases hsum : input.left + input.right = input.expected
  · simp only [if_pos hsum] at success
    by_cases hzero : total = 0
    · simp only [if_pos hzero] at success
      injection success with result
      rcases result with ⟨rfl, rfl⟩
      exact ⟨hsum, hzero, rfl, rfl⟩
    · simp [hzero] at success
  · simp [hsum] at success

theorem enabled_success (ctx : EvalContext) (input : InputValues)
    (hinput : CanonicalInputs ctx input)
    (hsum : input.left + input.right = input.expected) :
    subject.entry.run ctx (inputEnvironment input) (ledgerState 0) =
      .ok ([("result", .uint 510 input.expected)], ledgerState input.expected) := by
  simpa [hsum] using source_entry_run ctx input 0 hinput (by decide)

theorem functional : FunctionalObligation policy := by
  constructor
  · intro before initState
    subst before
    exact ⟨0, by decide, rfl⟩
  · intro ctx inputs before outputs after inv pre success
    obtain ⟨total, htotal, hbefore⟩ := inv
    obtain ⟨input, hinputs, hinput⟩ := pre
    subst inputs before
    have facts := successful_transition ctx input total outputs after hinput htotal success
    rcases facts with ⟨hsum, hzero, houtputs, hafter⟩
    refine ⟨?_, ?_⟩
    · exact ⟨input, total, rfl, rfl, hzero, hsum, houtputs, hafter⟩
    · exact ⟨input.expected, hinput.2.1, hafter⟩
  · intro ctx inputs before _inv pre progress
    obtain ⟨input, hinputs, hinput, hbefore, hsum⟩ := progress
    subst inputs before
    refine ⟨[("result", .uint 510 input.expected)], ledgerState input.expected, ?_⟩
    exact enabled_success ctx input hinput hsum
  · refine ⟨{ modulus := Field.modulus, poseidon2 := fun _ _ _ => .error "unused" },
      inputEnvironment ⟨2, 1, 1⟩, ledgerState 0, ?_, ?_, ?_⟩
    · rfl
    · exact ⟨⟨2, 1, 1⟩, rfl, ⟨rfl, by decide, by decide, by decide⟩⟩
    · exact ⟨⟨2, 1, 1⟩, rfl, ⟨rfl, by decide, by decide, by decide⟩, rfl, by decide⟩

theorem actual_public_inputs (input : InputValues) :
    subject.publicInputs (inputEnvironment input) =
      [("expected", some (.uint 510 input.expected))] := by
  rfl

theorem privacy : PrivacyObligation policy := by
  intro left right leftAdmissible rightAdmissible equivalent _release covered
  rcases left with ⟨ctx, leftInputs, before⟩
  rcases right with ⟨rightCtx, rightInputs, rightBefore⟩
  rcases equivalent with ⟨contextEq, stateEq, publicEq⟩
  change ctx = rightCtx at contextEq
  change before = rightBefore at stateEq
  subst rightCtx rightBefore
  rcases leftAdmissible with ⟨leftInvariant, leftPrecondition⟩
  rcases rightAdmissible with ⟨_rightInvariant, rightPrecondition⟩
  change invariant before at leftInvariant
  change precondition ctx leftInputs before at leftPrecondition
  change precondition ctx rightInputs before at rightPrecondition
  rcases leftPrecondition with ⟨leftInput, leftInputsEq, leftCanonical⟩
  rcases rightPrecondition with ⟨rightInput, rightInputsEq, rightCanonical⟩
  change leftInputs = inputEnvironment leftInput at leftInputsEq
  change rightInputs = inputEnvironment rightInput at rightInputsEq
  change CanonicalInputs ctx leftInput at leftCanonical
  change CanonicalInputs ctx rightInput at rightCanonical
  change subject.publicInputs leftInputs = subject.publicInputs rightInputs at publicEq
  rw [leftInputsEq, rightInputsEq, actual_public_inputs, actual_public_inputs] at publicEq
  have expectedEq : leftInput.expected = rightInput.expected := by
    have mapped := congrArg (List.map fun row : String × Option Value => row.2) publicEq
    have optionEq : some (Value.uint 510 leftInput.expected) =
        some (Value.uint 510 rightInput.expected) := by
      injection mapped with optionEq
    have valueEq : Value.uint 510 leftInput.expected = Value.uint 510 rightInput.expected := by
      injection optionEq with valueEq
    injection valueEq
  obtain ⟨total, totalBound, beforeEq⟩ := leftInvariant
  change before = ledgerState total at beforeEq
  change (∃ outputs state, subject.execute ⟨ctx, leftInputs, before⟩ = .ok (outputs, state)) ∧
    (∃ outputs state, subject.execute ⟨ctx, rightInputs, before⟩ = .ok (outputs, state)) at covered
  rcases covered with ⟨⟨leftOutputs, leftAfter, leftSuccess⟩,
    ⟨rightOutputs, rightAfter, rightSuccess⟩⟩
  change subject.entry.run ctx leftInputs before = .ok (leftOutputs, leftAfter) at leftSuccess
  change subject.entry.run ctx rightInputs before = .ok (rightOutputs, rightAfter) at rightSuccess
  rw [leftInputsEq, beforeEq] at leftSuccess
  rw [rightInputsEq, beforeEq] at rightSuccess
  obtain ⟨_leftSum, leftZero, leftOutputEq, leftAfterEq⟩ :=
    successful_transition ctx leftInput total leftOutputs leftAfter leftCanonical totalBound leftSuccess
  obtain ⟨_rightSum, rightZero, rightOutputEq, rightAfterEq⟩ :=
    successful_transition ctx rightInput total rightOutputs rightAfter rightCanonical totalBound rightSuccess
  change subject.entry.run ctx leftInputs before = subject.entry.run ctx rightInputs before
  rw [leftInputsEq, rightInputsEq, beforeEq, leftSuccess, rightSuccess,
    leftOutputEq, rightOutputEq, leftAfterEq, rightAfterEq, expectedEq]

#noctium_register_functional functional for policy
#noctium_register_privacy privacy for policy
#noctium_source_proof_coverage BoundedScalars
#print axioms functional
#print axioms privacy

end Noctium.BoundedScalarsVerification
