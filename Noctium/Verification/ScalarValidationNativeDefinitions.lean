import Noctium.Verification.RangeDedupComparisonMeaning
import Noctium.Verification.ScalarValidationArithmeticLoop
import Noctium.Verification.ScalarValidationHashMeaning
import Noctium.Verification.ScalarValidationNativeLoop

namespace Noctium.Verification.ScalarValidationNativeDefinitions

open Lean Backend.Native NativeRelation NativeRelationJson
open Noctium.Verification.ScalarValidationArithmeticLoop
open Noctium.Verification.ScalarValidationHashMeaning
open Noctium.Verification.ScalarValidationNativeLoop

private theorem bind_ok {α β : Type} {value : Except String α} {next : α → Except String β}
    {result : β} : (value >>= next) = .ok result ↔
      ∃ found, value = .ok found ∧ next found = .ok result := by
  cases value <;> simp [Bind.bind, Except.bind]

theorem refine_nativeDefinitions {state next : State} {text : String} {maximum : Nat}
    (nativeDefinitions : NativeDefinitions state)
    (accepted : refine state text maximum = .ok next) :
    NativeDefinitions next := by
  unfold refine at accepted
  simp only [bind_ok] at accepted
  rcases accepted with ⟨fact, _, accepted⟩
  split at accepted
  next referenceText =>
    rcases accepted with ⟨_, _, result⟩
    have stateEq := Except.ok.inj result
    subst next
    intro name value member
    simp only [List.mem_map] at member
    rcases member with ⟨⟨oldName, oldValue⟩, member, equal⟩
    simp only [Prod.mk.injEq] at equal
    rcases equal with ⟨nameEq, valueEq⟩
    subst name
    subst value
    have oldNative := nativeDefinitions oldName oldValue member
    cases same : oldName == text <;> simp [oldNative]
  next =>
    rcases accepted with ⟨_, _, accepted⟩
    simp only [bind_ok] at accepted
    rcases accepted with ⟨_, _, result⟩
    have stateEq := Except.ok.inj result
    cases stateEq
    exact nativeDefinitions

theorem define_groupCount {state next : State} {name : String} {fact : Fact}
    (accepted : define state name fact = .ok next) :
    next.groupCount = state.groupCount := by
  unfold define at accepted
  simp only [bind_ok] at accepted
  rcases accepted with ⟨_, _, _, _, result⟩
  simp only [Pure.pure, Except.pure] at result
  cases result
  rfl

theorem defineResult_groupCount {state next : State} {raw : Json} {fact : Fact}
    (accepted : defineResult state raw fact = .ok next) :
    next.groupCount = state.groupCount := by
  unfold defineResult at accepted
  simp only [bind_ok] at accepted
  rcases accepted with ⟨_, _, defined⟩
  exact define_groupCount defined

private theorem define_inputCount {state next : State} {name : String} {fact : Fact}
    (accepted : define state name fact = .ok next) :
    next.inputCount = state.inputCount := by
  unfold define at accepted
  simp only [bind_ok] at accepted
  rcases accepted with ⟨_, _, _, _, result⟩
  simp only [Pure.pure, Except.pure] at result
  cases result
  rfl

private theorem define_assertionCount {state next : State} {name : String} {fact : Fact}
    (accepted : define state name fact = .ok next) :
    next.assertionCount = state.assertionCount := by
  unfold define at accepted
  simp only [bind_ok] at accepted
  rcases accepted with ⟨_, _, _, _, result⟩
  simp only [Pure.pure, Except.pure] at result
  cases result
  rfl

theorem defineResult_counters {state next : State} {raw : Json} {fact : Fact}
    (accepted : defineResult state raw fact = .ok next) :
    next.groupCount = state.groupCount ∧ next.inputCount = state.inputCount := by
  unfold defineResult at accepted
  simp only [bind_ok] at accepted
  rcases accepted with ⟨_, _, defined⟩
  exact ⟨define_groupCount defined, define_inputCount defined⟩

theorem defineResult_assertionCount {state next : State} {raw : Json} {fact : Fact}
    (accepted : defineResult state raw fact = .ok next) :
    next.assertionCount = state.assertionCount := by
  unfold defineResult at accepted
  simp only [bind_ok] at accepted
  rcases accepted with ⟨_, _, defined⟩
  exact define_assertionCount defined

theorem refine_groupCount {state next : State} {text : String} {maximum : Nat}
    (accepted : refine state text maximum = .ok next) :
    next.groupCount = state.groupCount := by
  unfold refine at accepted
  simp only [bind_ok] at accepted
  rcases accepted with ⟨_, _, accepted⟩
  split at accepted
  · rcases accepted with ⟨_, _, result⟩
    have stateEq := Except.ok.inj result
    subst next
    rfl
  · simp only [bind_ok] at accepted
    rcases accepted with ⟨_, _, accepted⟩
    rcases accepted with ⟨_, _, result⟩
    have stateEq := Except.ok.inj result
    subst next
    rfl

theorem refine_counters {state next : State} {text : String} {maximum : Nat}
    (accepted : refine state text maximum = .ok next) :
    next.groupCount = state.groupCount ∧ next.inputCount = state.inputCount := by
  unfold refine at accepted
  simp only [bind_ok] at accepted
  rcases accepted with ⟨_, _, accepted⟩
  split at accepted
  · rcases accepted with ⟨_, _, result⟩
    have stateEq := Except.ok.inj result
    subst next
    exact ⟨rfl, rfl⟩
  · simp only [bind_ok] at accepted
    rcases accepted with ⟨_, _, accepted⟩
    rcases accepted with ⟨_, _, result⟩
    have stateEq := Except.ok.inj result
    subst next
    exact ⟨rfl, rfl⟩

theorem refine_assertionCount {state next : State} {text : String} {maximum : Nat}
    (accepted : refine state text maximum = .ok next) :
    next.assertionCount = state.assertionCount := by
  unfold refine at accepted
  simp only [bind_ok] at accepted
  rcases accepted with ⟨_, _, accepted⟩
  split at accepted
  · rcases accepted with ⟨_, _, result⟩
    have stateEq := Except.ok.inj result
    subst next
    rfl
  · simp only [bind_ok] at accepted
    rcases accepted with ⟨_, _, accepted⟩
    rcases accepted with ⟨_, _, result⟩
    have stateEq := Except.ok.inj result
    subst next
    rfl

theorem accepted_copy_nativeDefinitions {expected : Expected} {state next : State} {raw : Json}
    (nativeDefinitions : NativeDefinitions state)
    (opcode : Backend.Native.stringField raw "op" = .ok "copy")
    (accepted : validateInstruction expected state raw = .ok next) :
    NativeDefinitions next := by
  obtain ⟨value, _, valueNative, defined⟩ :=
    accepted_copy_components nativeDefinitions opcode accepted
  exact defineResult_nativeDefinitions nativeDefinitions valueNative defined

theorem accepted_add_nativeDefinitions {expected : Expected} {state next : State} {raw : Json}
    (nativeDefinitions : NativeDefinitions state)
    (opcode : Backend.Native.stringField raw "op" = .ok "add")
    (accepted : validateInstruction expected state raw = .ok next) :
    NativeDefinitions next := by
  obtain ⟨_, _, _, _, _, _, _, combined, defined⟩ :=
    accepted_add_components nativeDefinitions opcode accepted
  exact defineResult_nativeDefinitions nativeDefinitions (combine_native combined) defined

theorem accepted_testEq_nativeDefinitions {expected : Expected} {state next : State} {raw : Json}
    (nativeDefinitions : NativeDefinitions state)
    (opcode : Backend.Native.stringField raw "op" = .ok "test_eq")
    (accepted : validateInstruction expected state raw = .ok next) :
    NativeDefinitions next := by
  obtain ⟨_, _, _, _, _, _, _, combined, defined⟩ :=
    accepted_testEq_components nativeDefinitions opcode accepted
  exact defineResult_nativeDefinitions nativeDefinitions (combine_native combined) defined

theorem accepted_constrainBits_nativeDefinitions {expected : Expected} {state next : State}
    {raw : Json}
    (nativeDefinitions : NativeDefinitions state)
    (opcode : Backend.Native.stringField raw "op" = .ok "constrain_bits")
    (accepted : validateInstruction expected state raw = .ok next) :
    NativeDefinitions next := by
  unfold validateInstruction at accepted
  simp only [bind_ok] at accepted
  rcases accepted with ⟨found, op, descriptor, registry, _, fields, accepted⟩
  have opcodeEq := Except.ok.inj (op.symm.trans opcode)
  subst found
  simp only [bind_ok] at accepted
  rcases accepted with ⟨valueText, valueTextParsed, accepted⟩
  rcases accepted with ⟨bits, bitsParsed, refined⟩
  exact refine_nativeDefinitions nativeDefinitions refined

theorem accepted_constrainBoolean_nativeDefinitions {expected : Expected} {state next : State}
    {raw : Json}
    (nativeDefinitions : NativeDefinitions state)
    (opcode : Backend.Native.stringField raw "op" = .ok "constrain_to_boolean")
    (accepted : validateInstruction expected state raw = .ok next) :
    NativeDefinitions next := by
  unfold validateInstruction at accepted
  simp only [bind_ok] at accepted
  rcases accepted with ⟨found, op, descriptor, registry, _, fields, accepted⟩
  have opcodeEq := Except.ok.inj (op.symm.trans opcode)
  subst found
  simp only [bind_ok] at accepted
  rcases accepted with ⟨valueText, valueParsed, refined⟩
  exact refine_nativeDefinitions nativeDefinitions refined

theorem accepted_assert_nativeDefinitions
    {expected : Backend.Native.Expected} {state next : Backend.Native.State}
    {raw : Json}
    (definitions : NativeDefinitions state)
    (opcode : Backend.Native.stringField raw "op" = .ok "assert")
    (accepted : Backend.Native.validateInstruction expected state raw = .ok next) :
    NativeDefinitions next := by
  unfold Backend.Native.validateInstruction at accepted
  simp only [ScalarValidationMeaning.bind_ok] at accepted
  rcases accepted with ⟨opcodeName, opcodeParsed, descriptor, descriptorParsed,
    registry, fieldsParsed, accepted⟩
  have opcodeEq : opcodeName = "assert" := Except.ok.inj (opcodeParsed.symm.trans opcode)
  subst opcodeName
  simp at accepted
  simp only [ScalarValidationMeaning.bind_ok] at accepted
  rcases accepted with ⟨value, valueParsed, _, booleanAccepted, accepted⟩
  let assertionCounted := if expected.assertions[state.assertionCount]? == some value.term then
    {state with assertionCount := state.assertionCount + 1} else state
  let assertionState : Backend.Native.State :=
    {assertionCounted with
      establishedAssertions := (value.term :: assertionCounted.establishedAssertions).eraseDups}
  have assertionDefinitions : NativeDefinitions assertionState := by
    intro name fact member
    cases matched : (expected.assertions[state.assertionCount]? == some value.term)
    · exact definitions name fact (by
        simpa [assertionState, assertionCounted, matched] using member)
    · exact definitions name fact (by
        simpa [assertionState, assertionCounted, matched] using member)
  split at accepted
  · simp only [ScalarValidationMeaning.bind_ok] at accepted
    rcases accepted with ⟨_, _, refined⟩
    exact refine_nativeDefinitions assertionDefinitions refined
  · cases accepted
    exact assertionDefinitions

theorem accepted_lessThan_nativeDefinitions
    {expected : Backend.Native.Expected} {state next : Backend.Native.State}
    {raw : Json}
    (definitions : NativeDefinitions state)
    (opcode : Backend.Native.stringField raw "op" = .ok "less_than")
    (accepted : Backend.Native.validateInstruction expected state raw = .ok next) :
    NativeDefinitions next := by
  obtain ⟨leftText, _, right, _, fact, _, _, _, _, _, _, combined, defined⟩ :=
    RangeDedupComparisonMeaning.acceptedLessThanDefinition opcode accepted
  have factNative : fact.valueType = NativeValueType.native := combine_native combined
  have definedFactNative :
      ({fact with assertedLessThan := match right.term with
        | .constant bound => if ['%'] <+: leftText.toList then some (leftText, bound) else none
        | _ => none}).valueType = NativeValueType.native := by
    simpa using factNative
  exact defineResult_nativeDefinitions definitions definedFactNative defined

theorem accepted_constrainEq_nativeDefinitions {expected : Expected} {state next : State} {raw : Json}
    (nativeDefinitions : NativeDefinitions state)
    (opcode : Backend.Native.stringField raw "op" = .ok "constrain_eq")
    (accepted : validateInstruction expected state raw = .ok next) :
    NativeDefinitions next := by
  unfold validateInstruction at accepted
  simp only [bind_ok] at accepted
  rcases accepted with ⟨found, op, descriptor, registry, _, fields, accepted⟩
  have opcodeEq := Except.ok.inj (op.symm.trans opcode)
  subst found
  simp only [bind_ok] at accepted
  rcases accepted with ⟨leftText, leftTextParsed, rightText, rightTextParsed,
    leftFact, leftParsed, rightFact, rightParsed, middle, leftRefined, rightRefined⟩
  have leftArgument : argument state raw "a" = .ok leftFact := by
    unfold argument
    rw [leftTextParsed]
    exact leftParsed
  have leftNative := argument_native_of_state nativeDefinitions leftArgument
  simp only [leftNative, Backend.Native.ensure] at rightRefined
  simp only [Bind.bind, Except.bind] at rightRefined
  rcases bind_ok.mp rightRefined with ⟨middleState, leftRefined, rest⟩
  rcases bind_ok.mp rest with ⟨nextState, rightRefine, final⟩
  have nextStateNative :=
    refine_nativeDefinitions (refine_nativeDefinitions nativeDefinitions leftRefined) rightRefine
  simp only [Pure.pure, Except.pure] at final
  have finalEq := Except.ok.inj final
  subst next
  intro name fact member
  change (name, fact) ∈ nextState.definitions at member
  exact nextStateNative name fact member

/-- A checked Impact group advances the transcript without changing any definitions. -/
theorem accepted_impact_state
    {expected : Expected} {state next : State} {raw : Json}
    (opcode : Backend.Native.stringField raw "op" = .ok "impact")
    (accepted : validateInstruction expected state raw = .ok next) :
    next = {state with groupCount := state.groupCount + 1} := by
  unfold validateInstruction at accepted
  simp only [bind_ok] at accepted
  rcases accepted with ⟨found, op, _, _, _, _, accepted⟩
  have opcodeEq := Except.ok.inj (op.symm.trans opcode)
  subst found
  simp only [bind_ok] at accepted
  rcases accepted with ⟨_, _, _, _, _, _, _, _, _, _, accepted⟩
  split at accepted
  · simp only [Pure.pure, Except.pure] at accepted
    cases empty : expected.groupGuards.isEmpty
    · cases guard : expected.groupGuards[state.groupCount]?
      · simp [empty, guard, Bind.bind, Except.bind, MonadExcept.throw] at accepted
      · simp [empty, guard, bind_ok] at accepted
        rcases accepted with ⟨_, _, _, _, rfl⟩
        rfl
    · simp [empty, bind_ok] at accepted
      rcases accepted with ⟨_, _, _, _, rfl⟩
      rfl
  · contradiction

private theorem accepted_output_nativeDefinitions
    {expected : Expected} {state next : State} {raw : Json}
    (definitions : NativeDefinitions state)
    (opcode : Backend.Native.stringField raw "op" = .ok "output")
    (accepted : validateInstruction expected state raw = .ok next) :
    NativeDefinitions next := by
  unfold validateInstruction at accepted
  simp only [bind_ok] at accepted
  rcases accepted with ⟨found, op, _, _, _, _, accepted⟩
  have opcodeEq := Except.ok.inj (op.symm.trans opcode)
  subst found
  simp only [bind_ok, Pure.pure, Except.pure, Except.ok.injEq] at accepted
  rcases accepted with ⟨_, _, _, _, _, _, result⟩
  subst next
  exact definitions

theorem accepted_copy_counters
    {expected : Expected} {state next : State} {raw : Json}
    (definitions : NativeDefinitions state)
    (opcode : Backend.Native.stringField raw "op" = .ok "copy")
    (accepted : validateInstruction expected state raw = .ok next) :
    next.groupCount = state.groupCount ∧ next.inputCount = state.inputCount := by
  obtain ⟨_, _, _, defined⟩ := accepted_copy_components definitions opcode accepted
  exact defineResult_counters defined

theorem accepted_add_counters
    {expected : Expected} {state next : State} {raw : Json}
    (definitions : NativeDefinitions state)
    (opcode : Backend.Native.stringField raw "op" = .ok "add")
    (accepted : validateInstruction expected state raw = .ok next) :
    next.groupCount = state.groupCount ∧ next.inputCount = state.inputCount := by
  obtain ⟨_, _, _, _, _, _, _, _, defined⟩ :=
    accepted_add_components definitions opcode accepted
  exact defineResult_counters defined

theorem accepted_mul_counters
    {expected : Expected} {state next : State} {raw : Json}
    (definitions : NativeDefinitions state)
    (opcode : Backend.Native.stringField raw "op" = .ok "mul")
    (accepted : validateInstruction expected state raw = .ok next) :
    next.groupCount = state.groupCount ∧ next.inputCount = state.inputCount := by
  obtain ⟨_, _, _, _, _, _, _, _, defined⟩ :=
    accepted_mul_components definitions opcode accepted
  exact defineResult_counters defined

theorem accepted_neg_counters
    {expected : Expected} {state next : State} {raw : Json}
    (definitions : NativeDefinitions state)
    (opcode : Backend.Native.stringField raw "op" = .ok "neg")
    (accepted : validateInstruction expected state raw = .ok next) :
    next.groupCount = state.groupCount ∧ next.inputCount = state.inputCount := by
  obtain ⟨_, _, _, _, _, defined⟩ :=
    accepted_neg_components definitions opcode accepted
  exact defineResult_counters defined

theorem accepted_testEq_counters
    {expected : Expected} {state next : State} {raw : Json}
    (definitions : NativeDefinitions state)
    (opcode : Backend.Native.stringField raw "op" = .ok "test_eq")
    (accepted : validateInstruction expected state raw = .ok next) :
    next.groupCount = state.groupCount ∧ next.inputCount = state.inputCount := by
  obtain ⟨_, _, _, _, _, _, _, _, defined⟩ :=
    accepted_testEq_components definitions opcode accepted
  exact defineResult_counters defined

theorem accepted_lessThan_counters
    {expected : Expected} {state next : State} {raw : Json}
    (opcode : Backend.Native.stringField raw "op" = .ok "less_than")
    (accepted : validateInstruction expected state raw = .ok next) :
    next.groupCount = state.groupCount ∧ next.inputCount = state.inputCount := by
  obtain ⟨_, _, _, _, _, _, _, _, _, _, _, _, defined⟩ :=
    RangeDedupComparisonMeaning.acceptedLessThanDefinition opcode accepted
  exact defineResult_counters defined

theorem accepted_constrainBits_counters
    {expected : Expected} {state next : State} {raw : Json}
    (opcode : Backend.Native.stringField raw "op" = .ok "constrain_bits")
    (accepted : validateInstruction expected state raw = .ok next) :
    next.groupCount = state.groupCount ∧ next.inputCount = state.inputCount := by
  unfold validateInstruction at accepted
  simp only [bind_ok] at accepted
  rcases accepted with ⟨found, op, descriptor, registry, _, fields, accepted⟩
  have opcodeEq := Except.ok.inj (op.symm.trans opcode)
  subst found
  simp only [bind_ok] at accepted
  rcases accepted with ⟨valueText, valueTextParsed, accepted⟩
  rcases accepted with ⟨bits, bitsParsed, refined⟩
  exact refine_counters refined

theorem accepted_constrainBoolean_counters
    {expected : Expected} {state next : State} {raw : Json}
    (opcode : Backend.Native.stringField raw "op" = .ok "constrain_to_boolean")
    (accepted : validateInstruction expected state raw = .ok next) :
    next.groupCount = state.groupCount ∧ next.inputCount = state.inputCount := by
  unfold validateInstruction at accepted
  simp only [bind_ok] at accepted
  rcases accepted with ⟨found, op, descriptor, registry, _, fields, accepted⟩
  have opcodeEq := Except.ok.inj (op.symm.trans opcode)
  subst found
  simp only [bind_ok] at accepted
  rcases accepted with ⟨valueText, valueParsed, refined⟩
  exact refine_counters refined

theorem accepted_assert_counters
    {expected : Expected} {state next : State} {raw : Json}
    (opcode : Backend.Native.stringField raw "op" = .ok "assert")
    (accepted : validateInstruction expected state raw = .ok next) :
    next.groupCount = state.groupCount ∧ next.inputCount = state.inputCount := by
  unfold Backend.Native.validateInstruction at accepted
  simp only [bind_ok] at accepted
  rcases accepted with ⟨opcodeName, opcodeParsed, descriptor, descriptorParsed,
    registry, fieldsParsed, accepted⟩
  have opcodeEq : opcodeName = "assert" := Except.ok.inj (opcodeParsed.symm.trans opcode)
  subst opcodeName
  simp at accepted
  simp only [bind_ok] at accepted
  rcases accepted with ⟨value, valueParsed, _, booleanAccepted, accepted⟩
  let assertionCounted := if expected.assertions[state.assertionCount]? == some value.term then
    {state with assertionCount := state.assertionCount + 1} else state
  let assertionState : Backend.Native.State :=
    {assertionCounted with
      establishedAssertions := (value.term :: assertionCounted.establishedAssertions).eraseDups}
  have assertionCounters :
      assertionState.groupCount = state.groupCount ∧
        assertionState.inputCount = state.inputCount := by
    by_cases matched : expected.assertions[state.assertionCount]? == some value.term <;>
      simp [assertionState, assertionCounted, matched]
  split at accepted
  · simp only [bind_ok] at accepted
    rcases accepted with ⟨_, _, refined⟩
    have counters := refine_counters refined
    exact ⟨counters.1.trans assertionCounters.1, counters.2.trans assertionCounters.2⟩
  · cases accepted
    exact assertionCounters

theorem accepted_output_counters
    {expected : Expected} {state next : State} {raw : Json}
    (opcode : Backend.Native.stringField raw "op" = .ok "output")
    (accepted : validateInstruction expected state raw = .ok next) :
    next.groupCount = state.groupCount ∧ next.inputCount = state.inputCount := by
  unfold validateInstruction at accepted
  simp only [bind_ok] at accepted
  rcases accepted with ⟨found, op, _, _, _, _, accepted⟩
  have opcodeEq := Except.ok.inj (op.symm.trans opcode)
  subst found
  simp only [bind_ok, Pure.pure, Except.pure, Except.ok.injEq] at accepted
  rcases accepted with ⟨_, _, _, _, _, _, result⟩
  subst next
  exact ⟨rfl, rfl⟩

theorem accepted_constrainEq_counters
    {expected : Expected} {state next : State} {raw : Json}
    (definitions : NativeDefinitions state)
    (opcode : Backend.Native.stringField raw "op" = .ok "constrain_eq")
    (accepted : validateInstruction expected state raw = .ok next) :
    next.groupCount = state.groupCount ∧ next.inputCount = state.inputCount := by
  unfold validateInstruction at accepted
  simp only [bind_ok] at accepted
  rcases accepted with ⟨found, op, descriptor, registry, _, fields, accepted⟩
  have opcodeEq := Except.ok.inj (op.symm.trans opcode)
  subst found
  simp only [bind_ok] at accepted
  rcases accepted with ⟨leftText, leftTextParsed, rightText, rightTextParsed,
    leftFact, leftParsed, rightFact, rightParsed, middle, leftRefined, rightRefined⟩
  have leftArgument : argument state raw "a" = .ok leftFact := by
    unfold argument
    rw [leftTextParsed]
    exact leftParsed
  have leftNative := argument_native_of_state definitions leftArgument
  simp only [leftNative, Backend.Native.ensure] at rightRefined
  simp only [Bind.bind, Except.bind] at rightRefined
  rcases bind_ok.mp rightRefined with ⟨middleState, leftRefined, rest⟩
  rcases bind_ok.mp rest with ⟨nextState, rightRefined, final⟩
  have counters :
      nextState.groupCount = state.groupCount ∧ nextState.inputCount = state.inputCount := by
    exact ⟨
      (refine_counters rightRefined).1.trans (refine_counters leftRefined).1,
      (refine_counters rightRefined).2.trans (refine_counters leftRefined).2⟩
  simp only [Pure.pure, Except.pure] at final
  have finalEq := Except.ok.inj final
  subst next
  exact ⟨by simp [counters.1], by simp [counters.2]⟩

theorem accepted_copy_groupCount
    {expected : Expected} {state next : State} {raw : Json}
    (definitions : NativeDefinitions state)
    (opcode : Backend.Native.stringField raw "op" = .ok "copy")
    (accepted : validateInstruction expected state raw = .ok next) :
    next.groupCount = state.groupCount :=
  (accepted_copy_counters definitions opcode accepted).1

theorem accepted_add_groupCount
    {expected : Expected} {state next : State} {raw : Json}
    (definitions : NativeDefinitions state)
    (opcode : Backend.Native.stringField raw "op" = .ok "add")
    (accepted : validateInstruction expected state raw = .ok next) :
    next.groupCount = state.groupCount :=
  (accepted_add_counters definitions opcode accepted).1

theorem accepted_mul_groupCount
    {expected : Expected} {state next : State} {raw : Json}
    (definitions : NativeDefinitions state)
    (opcode : Backend.Native.stringField raw "op" = .ok "mul")
    (accepted : validateInstruction expected state raw = .ok next) :
    next.groupCount = state.groupCount :=
  (accepted_mul_counters definitions opcode accepted).1

theorem accepted_neg_groupCount
    {expected : Expected} {state next : State} {raw : Json}
    (definitions : NativeDefinitions state)
    (opcode : Backend.Native.stringField raw "op" = .ok "neg")
    (accepted : validateInstruction expected state raw = .ok next) :
    next.groupCount = state.groupCount :=
  (accepted_neg_counters definitions opcode accepted).1

theorem accepted_testEq_groupCount
    {expected : Expected} {state next : State} {raw : Json}
    (definitions : NativeDefinitions state)
    (opcode : Backend.Native.stringField raw "op" = .ok "test_eq")
    (accepted : validateInstruction expected state raw = .ok next) :
    next.groupCount = state.groupCount :=
  (accepted_testEq_counters definitions opcode accepted).1

theorem accepted_lessThan_groupCount
    {expected : Expected} {state next : State} {raw : Json}
    (opcode : Backend.Native.stringField raw "op" = .ok "less_than")
    (accepted : validateInstruction expected state raw = .ok next) :
    next.groupCount = state.groupCount :=
  (accepted_lessThan_counters opcode accepted).1

theorem accepted_output_groupCount
    {expected : Expected} {state next : State} {raw : Json}
    (opcode : Backend.Native.stringField raw "op" = .ok "output")
    (accepted : validateInstruction expected state raw = .ok next) :
    next.groupCount = state.groupCount :=
  (accepted_output_counters opcode accepted).1

theorem accepted_constrainBits_groupCount
    {expected : Expected} {state next : State} {raw : Json}
    (opcode : Backend.Native.stringField raw "op" = .ok "constrain_bits")
    (accepted : validateInstruction expected state raw = .ok next) :
    next.groupCount = state.groupCount :=
  (accepted_constrainBits_counters opcode accepted).1

theorem accepted_constrainBoolean_groupCount
    {expected : Expected} {state next : State} {raw : Json}
    (opcode : Backend.Native.stringField raw "op" = .ok "constrain_to_boolean")
    (accepted : validateInstruction expected state raw = .ok next) :
    next.groupCount = state.groupCount :=
  (accepted_constrainBoolean_counters opcode accepted).1

theorem accepted_assert_groupCount
    {expected : Expected} {state next : State} {raw : Json}
    (opcode : Backend.Native.stringField raw "op" = .ok "assert")
    (accepted : validateInstruction expected state raw = .ok next) :
    next.groupCount = state.groupCount :=
  (accepted_assert_counters opcode accepted).1

theorem accepted_input_groupCount {expected : Expected} {state next : State}
    {raw : Json} {visibility : Visibility} {requirement : InputRequirement}
    (selected : expected.inputs[state.inputCount]? = some requirement)
    (nonforeignInput : requirement.ty.isForeign = false)
    (unguarded : requirement.activityGuard = none)
    (opcodeParsed : Backend.Native.stringField raw "op" = .ok (inputOpcode visibility))
    (accepted : validateInstruction expected state raw = .ok next) :
    next.groupCount = state.groupCount := by
  cases visibility <;> all_goals
    unfold validateInstruction at accepted
    simp only [bind_ok] at accepted
    rcases accepted with ⟨opcode, op, descriptor, registry, _, fields, accepted⟩
    have opcodeEq := Except.ok.inj (op.symm.trans opcodeParsed)
    simp only [opcodeEq, inputOpcode, selected] at accepted
    split at accepted
    · simp_all [Ty.isForeign]
    · simp only [unguarded] at accepted
      simp only [bind_ok] at accepted
      rcases accepted with ⟨typeJson, typeParsed, _, typeChecked, valueType, valueParsed,
        guardJson, guardParsed, _, guardChecked, output, outputParsed, _, schema,
        definedState, defined, result⟩
      have groupCountEq := define_groupCount defined
      have nextEq : ({definedState with inputCount := definedState.inputCount + 1}) = next :=
        Except.ok.inj result
      subst next
      simpa using groupCountEq

/-- A source-bound public input advances only the live input cursor. The
guard check and definition insertion leave the Impact group ordinal intact. -/
theorem accepted_guarded_public_input_groupCount {expected : Expected}
    {state next : State} {raw : Json} {requirement : InputRequirement}
    {guardTerm : Backend.Native.Term}
    (selected : expected.inputs[state.inputCount]? = some requirement)
    (nonforeignInput : requirement.ty.isForeign = false)
    (guarded : requirement.activityGuard = some guardTerm)
    (opcodeParsed : Backend.Native.stringField raw "op" = .ok "public_input")
    (accepted : validateInstruction expected state raw = .ok next) :
    next.groupCount = state.groupCount := by
  unfold validateInstruction at accepted
  simp only [bind_ok] at accepted
  rcases accepted with ⟨opcode, op, descriptor, registry, _, fields, accepted⟩
  have opcodeEq : opcode = "public_input" := Except.ok.inj (op.symm.trans opcodeParsed)
  simp only [opcodeEq, selected, guarded] at accepted
  cases ty : requirement.ty <;> try simp [Ty.isForeign, ty] at nonforeignInput
  all_goals
    simp only [ty] at accepted
    simp only [bind_ok] at accepted
    rcases accepted with ⟨typeJson, typeParsed, nativeTypeValue, nativeTypeParsed,
      valueType, valueParsed, guardModeUnit, guardModeChecked, guardText,
      guardTextParsed, guardFact, guardOperand, guardBoolean, guardBooleanChecked,
      guardMatchUnit, guardMatch, output, outputParsed, schemaUnit, schemaChecked,
      definedState, defined, result⟩
    have groupCountEq := define_groupCount defined
    have resultEq :
        {definedState with inputCount := definedState.inputCount + 1} = next :=
      Except.ok.inj result
    subst next
    simpa using groupCountEq

theorem accepted_constrainEq_groupCount {expected : Expected} {state next : State}
    {raw : Json}
    (definitions : NativeDefinitions state)
    (opcode : Backend.Native.stringField raw "op" = .ok "constrain_eq")
    (accepted : validateInstruction expected state raw = .ok next) :
    next.groupCount = state.groupCount :=
  (accepted_constrainEq_counters definitions opcode accepted).1

theorem accepted_impact_inputCount
    {expected : Expected} {state next : State} {raw : Json}
    (opcode : Backend.Native.stringField raw "op" = .ok "impact")
    (accepted : validateInstruction expected state raw = .ok next) :
    next.inputCount = state.inputCount := by
  rw [accepted_impact_state opcode accepted]

/-- The supported opcode profile for this trace fragment. Copy and constrain_eq
both decode to `.equal`, so the profile records which producer opcode was used. -/
inductive SupportedScalarOpcode (raw : Json) : Instruction → Prop where
  | publicInput (output : String)
      (opcode : Backend.Native.stringField raw "op" = .ok "public_input") :
      SupportedScalarOpcode raw (.input .public output)
  | privateInput (output : String)
      (opcode : Backend.Native.stringField raw "op" = .ok "private_input") :
      SupportedScalarOpcode raw (.input .private output)
  | add (a b : Operand) (output : String)
      (opcode : Backend.Native.stringField raw "op" = .ok "add") :
      SupportedScalarOpcode raw (.add a b output)
  | mul (a b : Operand) (output : String)
      (opcode : Backend.Native.stringField raw "op" = .ok "mul") :
      SupportedScalarOpcode raw (.mul a b output)
  | neg (a : Operand) (output : String)
      (opcode : Backend.Native.stringField raw "op" = .ok "neg") :
      SupportedScalarOpcode raw (.neg a output)
  | bits (value : Operand) (width : Nat)
      (opcode : Backend.Native.stringField raw "op" = .ok "constrain_bits") :
      SupportedScalarOpcode raw (.bits value width)
  | boolean (value : Operand)
      (opcode : Backend.Native.stringField raw "op" = .ok "constrain_to_boolean") :
      SupportedScalarOpcode raw (.boolean value)
  | lessThan (a b : Operand) (width : Nat) (output : String)
      (opcode : Backend.Native.stringField raw "op" = .ok "less_than") :
      SupportedScalarOpcode raw (.lessThan a b width output)
  | assertion (condition : Operand)
      (opcode : Backend.Native.stringField raw "op" = .ok "assert") :
      SupportedScalarOpcode raw (.assert condition)
  | testEq (a b : Operand) (output : String)
      (opcode : Backend.Native.stringField raw "op" = .ok "test_eq") :
      SupportedScalarOpcode raw (.testEq a b output)
  | copy (source destination : String)
      (opcode : Backend.Native.stringField raw "op" = .ok "copy") :
      SupportedScalarOpcode raw (.equal (.reference source) (.reference destination))
  | impact (guard : Operand) (inputs : List Operand)
      (opcode : Backend.Native.stringField raw "op" = .ok "impact") :
      SupportedScalarOpcode raw (.impact guard inputs)
  | output (values : List Operand)
      (opcode : Backend.Native.stringField raw "op" = .ok "output") :
      SupportedScalarOpcode raw (.output values)
  | hash (inputs : List Operand) (output : String)
      (opcode : Backend.Native.stringField raw "op" = .ok "transient_hash") :
      SupportedScalarOpcode raw (.hash inputs output)
  | constrainEq (a b : Operand)
      (opcode : Backend.Native.stringField raw "op" = .ok "constrain_eq") :
      SupportedScalarOpcode raw (.equal a b)

def impactGroupIncrement : Instruction → Nat
  | .impact _ _ => 1
  | _ => 0

/-- One accepted producer step advances the impact-group counter exactly when
the supported opcode is `impact`. Scalar inputs in this fragment are native
and unguarded. -/
theorem accepted_supportedScalarOpcode_groupCount_step
    {expected : Expected} {state next : State} {raw : Json} {instruction : Instruction}
    (definitions : NativeDefinitions state)
    (inputSchema : ∀ requirement ∈ expected.inputs, requirement.ty.isForeign = false)
    (inputGuards : ∀ requirement ∈ expected.inputs, requirement.activityGuard = none)
    (supported : SupportedScalarOpcode raw instruction)
    (accepted : validateInstruction expected state raw = .ok next) :
    next.groupCount = state.groupCount + impactGroupIncrement instruction := by
  cases supported with
  | publicInput output opcode =>
    obtain ⟨requirement, selected⟩ := accepted_input_requirement_selected
      (visibility := .«public») (by simpa [inputOpcode] using opcode) accepted
    have member : requirement ∈ expected.inputs := List.mem_of_getElem? selected
    have unchanged := accepted_input_groupCount (visibility := .«public») selected
      (inputSchema requirement member)
      (inputGuards requirement member) (by simpa [inputOpcode] using opcode) accepted
    rw [unchanged]
    simp [impactGroupIncrement]
  | privateInput output opcode =>
    obtain ⟨requirement, selected⟩ := accepted_input_requirement_selected
      (visibility := .«private») (by simpa [inputOpcode] using opcode) accepted
    have member : requirement ∈ expected.inputs := List.mem_of_getElem? selected
    have unchanged := accepted_input_groupCount (visibility := .«private») selected
      (inputSchema requirement member)
      (inputGuards requirement member) (by simpa [inputOpcode] using opcode) accepted
    rw [unchanged]
    simp [impactGroupIncrement]
  | add _ _ _ opcode =>
    rw [(accepted_add_counters definitions opcode accepted).1]
    simp [impactGroupIncrement]
  | mul _ _ _ opcode =>
    rw [(accepted_mul_counters definitions opcode accepted).1]
    simp [impactGroupIncrement]
  | neg _ _ opcode =>
    rw [(accepted_neg_counters definitions opcode accepted).1]
    simp [impactGroupIncrement]
  | bits _ _ opcode =>
    rw [(accepted_constrainBits_counters opcode accepted).1]
    simp [impactGroupIncrement]
  | boolean _ opcode =>
    rw [(accepted_constrainBoolean_counters opcode accepted).1]
    simp [impactGroupIncrement]
  | lessThan _ _ _ _ opcode =>
    rw [(accepted_lessThan_counters opcode accepted).1]
    simp [impactGroupIncrement]
  | assertion _ opcode =>
    rw [(accepted_assert_counters opcode accepted).1]
    simp [impactGroupIncrement]
  | testEq _ _ _ opcode =>
    rw [(accepted_testEq_counters definitions opcode accepted).1]
    simp [impactGroupIncrement]
  | copy _ _ opcode =>
    rw [(accepted_copy_counters definitions opcode accepted).1]
    simp [impactGroupIncrement]
  | impact _ _ opcode =>
    rw [accepted_impact_state opcode accepted]
    simp [impactGroupIncrement]
  | hash _ _ opcode =>
    obtain ⟨_, _, _, _, _, defined⟩ := accepted_hash_definition opcode accepted
    rw [(defineResult_counters defined).1]
    simp [impactGroupIncrement]
  | output _ opcode =>
    rw [(accepted_output_counters opcode accepted).1]
    simp [impactGroupIncrement]
  | constrainEq _ _ opcode =>
    rw [(accepted_constrainEq_counters definitions opcode accepted).1]
    simp [impactGroupIncrement]

/-- Accepted rows outside the input constructors leave the producer's live
input ordinal unchanged. Each branch follows the matching validator helper,
so unsupported opcodes and the older scalar validator never enter this proof. -/
theorem accepted_supportedScalarOpcode_noninput_inputCount_preserved
    {expected : Expected} {state next : State} {raw : Json} {instruction : Instruction}
    (definitions : NativeDefinitions state)
    (supported : SupportedScalarOpcode raw instruction)
    (noninput : ∀ visibility output, instruction ≠ .input visibility output)
    (accepted : validateInstruction expected state raw = .ok next) :
    next.inputCount = state.inputCount := by
  cases supported with
  | publicInput output _ => exact (noninput .«public» output rfl).elim
  | privateInput output _ => exact (noninput .«private» output rfl).elim
  | add _ _ _ opcode => exact (accepted_add_counters definitions opcode accepted).2
  | mul _ _ _ opcode => exact (accepted_mul_counters definitions opcode accepted).2
  | neg _ _ opcode => exact (accepted_neg_counters definitions opcode accepted).2
  | bits _ _ opcode => exact (accepted_constrainBits_counters opcode accepted).2
  | boolean _ opcode => exact (accepted_constrainBoolean_counters opcode accepted).2
  | lessThan _ _ _ _ opcode => exact (accepted_lessThan_counters opcode accepted).2
  | assertion _ opcode => exact (accepted_assert_counters opcode accepted).2
  | testEq _ _ _ opcode => exact (accepted_testEq_counters definitions opcode accepted).2
  | copy _ _ opcode => exact (accepted_copy_counters definitions opcode accepted).2
  | impact _ _ opcode => exact accepted_impact_inputCount opcode accepted
  | hash _ _ opcode =>
    obtain ⟨_, _, _, _, _, defined⟩ := accepted_hash_definition opcode accepted
    exact (defineResult_counters defined).2
  | output _ opcode => exact (accepted_output_counters opcode accepted).2
  | constrainEq _ _ opcode => exact (accepted_constrainEq_counters definitions opcode accepted).2

structure NativeDefinitionStep (raw : Json) (instruction : Instruction) : Prop where
  supported : SupportedScalarOpcode raw instruction
  decoded : NativeRelationJson.decodeInstruction raw = .ok instruction

inductive NativeDefinitionTrace : List (Json × Nat) → List Instruction → Prop where
  | nil : NativeDefinitionTrace [] []
  | cons {raw : Json} {index : Nat} {instruction : Instruction}
      {items : List (Json × Nat)} {instructions : List Instruction}
      (head : NativeDefinitionStep raw instruction)
      (tail : NativeDefinitionTrace items instructions) :
      NativeDefinitionTrace ((raw, index) :: items) (instruction :: instructions)

inductive SupportedScalarOpcodeTrace : List (Json × Nat) → List Instruction → Prop where
  | nil : SupportedScalarOpcodeTrace [] []
  | cons {raw : Json} {index : Nat} {instruction : Instruction}
      {items : List (Json × Nat)} {instructions : List Instruction}
      (head : SupportedScalarOpcode raw instruction)
      (tail : SupportedScalarOpcodeTrace items instructions) :
      SupportedScalarOpcodeTrace ((raw, index) :: items) (instruction :: instructions)

/-- Attach the exact per-instruction decoder proofs from a successful mapM to
an explicit supported-opcode trace. No other opcode is inferred or admitted. -/
theorem NativeDefinitionTrace.ofDecodedSupportedOpcodes
    {items : List (Json × Nat)} {instructions : List Instruction}
    (supported : SupportedScalarOpcodeTrace items instructions)
    (decoded : (items.map Prod.fst).mapM NativeRelationJson.decodeInstruction = .ok instructions) :
    NativeDefinitionTrace items instructions := by
  induction supported with
  | nil => exact .nil
  | @cons raw index instruction tailItems tailInstructions head tail ih =>
    simp only [List.map_cons, List.mapM_cons, bind_ok] at decoded
    rcases decoded with ⟨decodedInstruction, decodedHead, decodedTailInstructions,
      decodedTail, listEquality⟩
    simp only [Pure.pure, Except.pure] at listEquality
    rcases List.cons.inj (Except.ok.inj listEquality) with ⟨instructionEq, instructionsEq⟩
    cases instructionEq
    cases instructionsEq
    exact .cons ⟨head, decodedHead⟩ (ih decodedTail)

theorem NativeDefinitionTrace.decodes {items : List (Json × Nat)}
    {instructions : List Instruction} (trace : NativeDefinitionTrace items instructions) :
    (items.map Prod.fst).mapM NativeRelationJson.decodeInstruction = .ok instructions := by
  induction trace with
  | nil => simp [List.mapM_nil, Pure.pure, Except.pure]
  | @cons raw index instruction tailItems tailInstructions head tail ih =>
    simp [List.mapM_cons, head.decoded, ih, Bind.bind, Except.bind, Pure.pure, Except.pure]

theorem empty_nativeDefinitions : NativeDefinitions ({} : State) := by
  intro identifier fact found
  simp at found

theorem nativeDefinitions_step {expected : Expected} {state next : State}
    {raw : Json} {instruction : Instruction}
    (inputSchema : ∀ requirement ∈ expected.inputs, requirement.ty.isForeign = false)
    (nativeDefinitions : NativeDefinitions state)
    (step : NativeDefinitionStep raw instruction)
    (accepted : validateInstruction expected state raw = .ok next) :
    NativeDefinitions next := by
  cases step.supported with
  | publicInput output opcode =>
    have parsedOpcode : Backend.Native.stringField raw "op" =
        .ok (inputOpcode .public) := by simpa [inputOpcode] using opcode
    obtain ⟨requirement, selected⟩ := accepted_input_requirement_selected
      (visibility := .public) parsedOpcode accepted
    have member : requirement ∈ expected.inputs := List.mem_of_getElem? selected
    have nonforeignInput := inputSchema requirement member
    cases guarded : requirement.activityGuard with
    | none =>
      exact input_nativeDefinitions_step (visibility := .public) nativeDefinitions selected
        nonforeignInput guarded parsedOpcode accepted
    | some guardTerm =>
      exact guarded_public_input_nativeDefinitions_step nativeDefinitions selected
        nonforeignInput guarded parsedOpcode accepted
  | privateInput output opcode =>
    have parsedOpcode : Backend.Native.stringField raw "op" =
        .ok (inputOpcode .private) := by simpa [inputOpcode] using opcode
    obtain ⟨requirement, selected⟩ := accepted_input_requirement_selected
      (visibility := .private) parsedOpcode accepted
    have member : requirement ∈ expected.inputs := List.mem_of_getElem? selected
    have nonforeignInput := inputSchema requirement member
    have unguarded := accepted_private_input_unguarded selected parsedOpcode accepted
    exact input_nativeDefinitions_step (visibility := .private) nativeDefinitions selected
      nonforeignInput unguarded parsedOpcode accepted
  | add _ _ _ opcode => exact accepted_add_nativeDefinitions nativeDefinitions opcode accepted
  | hash _ _ opcode =>
      obtain ⟨_, fact, _, _, combined, defined⟩ :=
        accepted_hash_definition opcode accepted
      exact defineResult_nativeDefinitions nativeDefinitions (combine_native combined) defined
  | mul _ _ _ opcode =>
      obtain ⟨_, _, _, _, _, _, _, combined, defined⟩ :=
        accepted_mul_components nativeDefinitions opcode accepted
      exact defineResult_nativeDefinitions nativeDefinitions (combine_native combined) defined
  | neg _ _ opcode =>
      obtain ⟨_, _, _, _, combined, defined⟩ :=
        accepted_neg_components nativeDefinitions opcode accepted
      exact defineResult_nativeDefinitions nativeDefinitions (combine_native combined) defined
  | bits _ _ opcode =>
      exact accepted_constrainBits_nativeDefinitions nativeDefinitions opcode accepted
  | boolean _ opcode =>
      exact accepted_constrainBoolean_nativeDefinitions nativeDefinitions opcode accepted
  | lessThan _ _ _ _ opcode =>
      exact accepted_lessThan_nativeDefinitions nativeDefinitions opcode accepted
  | assertion _ opcode => exact accepted_assert_nativeDefinitions nativeDefinitions opcode accepted
  | testEq _ _ _ opcode => exact accepted_testEq_nativeDefinitions nativeDefinitions opcode accepted
  | copy _ _ opcode => exact accepted_copy_nativeDefinitions nativeDefinitions opcode accepted
  | impact _ _ opcode =>
      rw [accepted_impact_state opcode accepted]
      exact nativeDefinitions
  | output _ opcode => exact accepted_output_nativeDefinitions nativeDefinitions opcode accepted
  | constrainEq _ _ opcode =>
      exact accepted_constrainEq_nativeDefinitions nativeDefinitions opcode accepted

/-- Derive the final native-definition invariant from the actual decoded
instruction list and the producer's ordered validation fold. -/
theorem validateInstructionLoop_nativeDefinitions_of_trace
    {expected : Expected} {items : List (Json × Nat)} {instructions : List Instruction}
    {initial final : State}
    (inputSchema : ∀ requirement ∈ expected.inputs, requirement.ty.isForeign = false)
    (initialNativeDefinitions : NativeDefinitions initial)
    (trace : NativeDefinitionTrace items instructions)
    (accepted : validateInstructionLoop expected items initial = .ok final) :
    NativeDefinitions final := by
  induction trace generalizing initial final with
  | nil =>
    have initialEq : initial = final := by injection accepted
    subst final
    exact initialNativeDefinitions
  | @cons raw index instruction tailItems tailInstructions head tail ih =>
    rw [validateInstructionLoop, List.forIn_cons] at accepted
    cases checked : validateInstruction expected initial raw with
    | error message => simp [checked, Bind.bind, Except.bind] at accepted
    | ok next =>
      simp only [checked, bind_pure_comp] at accepted
      have nextNativeDefinitions := nativeDefinitions_step inputSchema
        initialNativeDefinitions head checked
      exact ih nextNativeDefinitions accepted

theorem validateInstructionLoop_supportedScalar_nativeDefinitions
    {expected : Expected} {items : List (Json × Nat)} {instructions : List Instruction}
    {final : State}
    (inputSchema : ∀ requirement ∈ expected.inputs, requirement.ty.isForeign = false)
    (supported : SupportedScalarOpcodeTrace items instructions)
    (decoded : (items.map Prod.fst).mapM NativeRelationJson.decodeInstruction = .ok instructions)
    (accepted : validateInstructionLoop expected items ({} : State) = .ok final) :
    NativeDefinitions final :=
  validateInstructionLoop_nativeDefinitions_of_trace inputSchema empty_nativeDefinitions
    (NativeDefinitionTrace.ofDecodedSupportedOpcodes supported decoded) accepted

end Noctium.Verification.ScalarValidationNativeDefinitions
