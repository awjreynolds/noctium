import Noctium.Verification.ScalarValidationNativeLoop
import Noctium.Verification.GenericStateCircuitParts

namespace Noctium.Verification.NativeInputOrdinal

open Lean Backend.Native NativeRelation NativeRelationJson
open Noctium.Verification.ScalarValidationMeaning
open Noctium.Verification.ScalarValidationNativeLoop

private theorem define_inputCount {state next : State} {name : String} {fact : Fact}
    (accepted : define state name fact = .ok next) :
    next.inputCount = state.inputCount := by
  unfold define at accepted
  rcases bind_ok.mp accepted with ⟨_, _, accepted⟩
  rcases bind_ok.mp accepted with ⟨_, _, result⟩
  cases result
  rfl

private theorem define_assertionCount {state next : State} {name : String} {fact : Fact}
    (accepted : define state name fact = .ok next) :
    next.assertionCount = state.assertionCount := by
  unfold define at accepted
  rcases bind_ok.mp accepted with ⟨_, _, accepted⟩
  rcases bind_ok.mp accepted with ⟨_, _, result⟩
  cases result
  rfl

/-- The unguarded public and private branches expose both input and assertion
counters from one producer inversion. -/
private theorem accepted_unguarded_input_count_frame {expected : Expected}
    {state next : State} {raw : Json} {requirement : InputRequirement}
    (visibility : Visibility)
    (selected : expected.inputs[state.inputCount]? = some requirement)
    (_nonforeignInput : requirement.ty.isForeign = false)
    (unguarded : requirement.activityGuard = none)
    (opcodeParsed : Backend.Native.stringField raw "op" =
      .ok (inputOpcode visibility))
    (accepted : validateInstruction expected state raw = .ok next) :
    next.inputCount = state.inputCount + 1 ∧
      next.assertionCount = state.assertionCount := by
  unfold validateInstruction at accepted
  simp only [bind_ok] at accepted
  rcases accepted with ⟨opcode, op, descriptor, registry, _, fields, accepted⟩
  have opcodeEq := Except.ok.inj (op.symm.trans opcodeParsed)
  cases visibility with
  | «public» =>
    have opcodeEq : opcode = "public_input" := by simpa [inputOpcode] using opcodeEq
    subst opcode
    simp only [opcodeEq, selected, unguarded] at accepted
    cases ty : requirement.ty <;> try simp [Ty.isForeign, ty] at _nonforeignInput
    all_goals
      simp only [ty] at accepted
      simp only [bind_ok] at accepted
      rcases accepted with ⟨typeJson, typeParsed, nativeTypeValue, nativeTypeParsed,
        valueType, valueParsed, guardJson, guardParsed, guardUnit, guardChecked,
        output, outputParsed, schemaUnit, schemaChecked, definedState, defined, result⟩
      have definedCount := define_inputCount defined
      have definedAssertions := define_assertionCount defined
      have resultEq :
          {definedState with inputCount := definedState.inputCount + 1} = next := by
        change Except.ok {definedState with inputCount := definedState.inputCount + 1} =
          Except.ok next at result
        exact Except.ok.inj result
      have countEq : next.inputCount = definedState.inputCount + 1 := by
        simpa only [State.inputCount] using
          (congrArg State.inputCount resultEq).symm
      rw [definedCount] at countEq
      have assertionEq : next.assertionCount = definedState.assertionCount := by
        simpa only [State.assertionCount] using
          (congrArg State.assertionCount resultEq).symm
      rw [definedAssertions] at assertionEq
      exact ⟨countEq, assertionEq⟩
  | «private» =>
    have opcodeEq : opcode = "private_input" := by simpa [inputOpcode] using opcodeEq
    subst opcode
    simp only [opcodeEq, selected, unguarded] at accepted
    cases ty : requirement.ty <;> try simp [Ty.isForeign, ty] at _nonforeignInput
    all_goals
      simp only [ty] at accepted
      simp only [bind_ok] at accepted
      rcases accepted with ⟨typeJson, typeParsed, nativeTypeValue, nativeTypeParsed,
        valueType, valueParsed, guardJson, guardParsed, guardUnit, guardChecked,
        output, outputParsed, schemaUnit, schemaChecked, definedState, defined, result⟩
      have definedCount := define_inputCount defined
      have definedAssertions := define_assertionCount defined
      have resultEq :
          {definedState with inputCount := definedState.inputCount + 1} = next := by
        change Except.ok {definedState with inputCount := definedState.inputCount + 1} =
          Except.ok next at result
        exact Except.ok.inj result
      have countEq : next.inputCount = definedState.inputCount + 1 := by
        simpa only [State.inputCount] using
          (congrArg State.inputCount resultEq).symm
      rw [definedCount] at countEq
      have assertionEq : next.assertionCount = definedState.assertionCount := by
        simpa only [State.assertionCount] using
          (congrArg State.assertionCount resultEq).symm
      rw [definedAssertions] at assertionEq
      exact ⟨countEq, assertionEq⟩

/-- Every accepted unguarded native input consumes exactly the live expected
input ordinal. The selected row and visibility checks are shared with the
active producer input bridge. -/
theorem accepted_unguarded_input_count_increment {expected : Expected}
    {state next : State} {raw : Json} {requirement : InputRequirement}
    (visibility : Visibility)
    (selected : expected.inputs[state.inputCount]? = some requirement)
    (nonforeignInput : requirement.ty.isForeign = false)
    (unguarded : requirement.activityGuard = none)
    (opcodeParsed : Backend.Native.stringField raw "op" =
      .ok (inputOpcode visibility))
    (accepted : validateInstruction expected state raw = .ok next) :
    next.inputCount = state.inputCount + 1 := by
  exact (accepted_unguarded_input_count_frame visibility selected nonforeignInput
    unguarded opcodeParsed accepted).1

/-- A guarded public ledger read consumes one input ordinal after the pinned
producer validates its source-bound guard and schema. -/
private theorem accepted_guarded_public_input_count_frame {expected : Expected}
    {state next : State} {raw : Json} {requirement : InputRequirement}
    {guardTerm : Backend.Native.Term}
    (selected : expected.inputs[state.inputCount]? = some requirement)
    (_nonforeignInput : requirement.ty.isForeign = false)
    (guarded : requirement.activityGuard = some guardTerm)
    (opcodeParsed : Backend.Native.stringField raw "op" = .ok "public_input")
    (accepted : validateInstruction expected state raw = .ok next) :
    next.inputCount = state.inputCount + 1 ∧
      next.assertionCount = state.assertionCount := by
  unfold validateInstruction at accepted
  simp only [bind_ok] at accepted
  rcases accepted with ⟨opcode, op, descriptor, registry, _, fields, accepted⟩
  have opcodeEq : opcode = "public_input" :=
    Except.ok.inj (op.symm.trans opcodeParsed)
  simp only [opcodeEq, selected, guarded] at accepted
  cases ty : requirement.ty <;> try simp [Ty.isForeign, ty] at _nonforeignInput
  all_goals
    simp only [ty] at accepted
    simp only [bind_ok] at accepted
    rcases accepted with ⟨typeJson, typeParsed, nativeTypeValue, nativeTypeParsed,
      valueType, valueParsed, guardModeUnit, guardModeChecked, guardText,
      guardTextParsed, guardFact, guardOperand, guardBoolean, guardBooleanChecked,
      guardMatchUnit, guardMatch, output, outputParsed, schemaUnit, schemaChecked,
      definedState, defined, result⟩
    have definedCount := define_inputCount defined
    have definedAssertions := define_assertionCount defined
    have resultEq :
        {definedState with inputCount := definedState.inputCount + 1} = next := by
      change Except.ok {definedState with inputCount := definedState.inputCount + 1} =
        Except.ok next at result
      exact Except.ok.inj result
    have countEq : next.inputCount = definedState.inputCount + 1 := by
      simpa only [State.inputCount] using
        (congrArg State.inputCount resultEq).symm
    rw [definedCount] at countEq
    have assertionEq : next.assertionCount = definedState.assertionCount := by
      simpa only [State.assertionCount] using
        (congrArg State.assertionCount resultEq).symm
    rw [definedAssertions] at assertionEq
    exact ⟨countEq, assertionEq⟩

/-- A guarded public ledger read consumes one input ordinal after the pinned
producer validates its source-bound guard and schema. -/
theorem accepted_guarded_public_input_count_increment {expected : Expected}
    {state next : State} {raw : Json} {requirement : InputRequirement}
    {guardTerm : Backend.Native.Term}
    (selected : expected.inputs[state.inputCount]? = some requirement)
    (nonforeignInput : requirement.ty.isForeign = false)
    (guarded : requirement.activityGuard = some guardTerm)
    (opcodeParsed : Backend.Native.stringField raw "op" = .ok "public_input")
    (accepted : validateInstruction expected state raw = .ok next) :
    next.inputCount = state.inputCount + 1 := by
  exact (accepted_guarded_public_input_count_frame selected nonforeignInput
    guarded opcodeParsed accepted).1

/-- Every accepted input row selects the next expected producer requirement
and advances the native input cursor exactly once. -/
theorem accepted_input_row_step {expected : Expected}
    {state next : State} {raw : Json} {visibility : Visibility}
    (inputSchema : ∀ requirement ∈ expected.inputs,
      requirement.ty.isForeign = false)
    (opcodeParsed : Backend.Native.stringField raw "op" =
      .ok (inputOpcode visibility))
    (accepted : validateInstruction expected state raw = .ok next) :
    ∃ requirement,
      expected.inputs[state.inputCount]? = some requirement ∧
      next.inputCount = state.inputCount + 1 := by
  obtain ⟨requirement, selected⟩ :=
    accepted_input_requirement_selected opcodeParsed accepted
  have member : requirement ∈ expected.inputs := List.mem_of_getElem? selected
  have count := by
    cases guard : requirement.activityGuard with
    | none =>
      exact accepted_unguarded_input_count_increment
        (visibility := visibility) selected (inputSchema requirement member)
        guard opcodeParsed accepted
    | some guardTerm =>
      cases visibility with
      | «public» =>
        exact accepted_guarded_public_input_count_increment selected
          (inputSchema requirement member) guard
          (by simpa [inputOpcode] using opcodeParsed) accepted
      | «private» =>
        have unguarded := accepted_private_input_unguarded selected
          (by simpa [inputOpcode] using opcodeParsed) accepted
        rw [guard] at unguarded
        cases unguarded
  exact ⟨requirement, selected, count⟩

/-- An accepted public or private input row preserves the checked assertion
ordinal. The selected and nonforeign row evidence matches the input-count
step lemmas above, including the guarded public-read case. -/
theorem accepted_input_row_assertion_count_unchanged {expected : Expected}
    {state next : State} {raw : Json} {visibility : Visibility}
    {requirement : InputRequirement}
    (selected : expected.inputs[state.inputCount]? = some requirement)
    (nonforeignInput : requirement.ty.isForeign = false)
    (opcodeParsed : Backend.Native.stringField raw "op" =
      .ok (inputOpcode visibility))
    (accepted : validateInstruction expected state raw = .ok next) :
    next.assertionCount = state.assertionCount := by
  cases guarded : requirement.activityGuard with
  | none =>
    exact (accepted_unguarded_input_count_frame visibility selected nonforeignInput
      guarded opcodeParsed accepted).2
  | some guardTerm =>
    cases visibility with
    | «public» =>
      exact (accepted_guarded_public_input_count_frame selected nonforeignInput guarded
        (by simpa [inputOpcode] using opcodeParsed) accepted).2
    | «private» =>
      have unguarded := accepted_private_input_unguarded selected
        (by simpa [inputOpcode] using opcodeParsed) accepted
      rw [guarded] at unguarded
      cases unguarded

/-- For the production ledger-call constructor, each accepted producer row is
the next element of the same ordered input list built from source inputs and
the checked Impact read fold. -/
theorem accepted_generic_state_input_row_step (state : List StateDecl)
    (entry : Entrypoint) {expected : Expected} {producerState next : State}
    {raw : Json} {visibility : Visibility}
    (expectedAccepted : Backend.Native.expectedEntrypoint state entry = .ok expected)
    (inputSchema : ∀ requirement ∈ expected.inputs,
      requirement.ty.isForeign = false)
    (opcodeParsed : Backend.Native.stringField raw "op" =
      .ok (inputOpcode visibility))
    (accepted : validateInstruction expected producerState raw = .ok next) :
    ∃ (plan : Backend.Impact.Plan)
      (inputState : List InputRequirement × List Backend.Native.Term ×
        List (Backend.Native.Term × Nat) × Nat)
      (requirement : InputRequirement),
      Backend.Impact.lower state entry = .ok plan ∧
      expected.inputs = inputState.1 ∧
      expected.inputs[producerState.inputCount]? = some requirement ∧
      next.inputCount = producerState.inputCount + 1 := by
  obtain ⟨plan, outputFrame, aliases, inputState, conditions, guards,
    constraintCollection, guardCollection, operationFrame, returns, activity,
    lowered, _, _, _, _, _, _, _, _, _, _, inputsExact, _, _, _, _, _, _⟩ :=
      GenericStateCircuitParts.expectedEntrypoint_parts state entry expected
        expectedAccepted
  obtain ⟨requirement, selected, increment⟩ :=
    accepted_input_row_step inputSchema opcodeParsed accepted
  exact ⟨plan, inputState, requirement, lowered, inputsExact, selected, increment⟩

private theorem input_schema_output_facts {raw : Json} {output identifier : String}
    {schemaUnit : Unit} {otherCheck : Bool}
    (outputParsed : Backend.Native.stringField raw "output" = .ok output)
    (schemaChecked : Backend.Native.ensure (output == identifier && otherCheck)
      "native transcript input schema/order mismatch" = .ok schemaUnit) :
    Backend.Native.stringField raw "output" = .ok identifier ∧ otherCheck = true := by
  cases schemaUnit
  have checked := ScalarValidationMeaning.ensure_ok.mp schemaChecked
  simp only [Bool.and_eq_true] at checked
  have outputEq : output = identifier := eq_of_beq checked.1
  rw [outputEq] at outputParsed
  exact ⟨outputParsed, checked.2⟩

private instance : LawfulBEq Visibility where
  rfl := by
    intro visibility
    cases visibility <;> rfl
  eq_of_beq := by
    intro left right matched
    cases left <;> cases right
    · rfl
    · have different : (Visibility.public == Visibility.private) = false := by decide
      rw [different] at matched
      cases matched
    · have different : (Visibility.private == Visibility.public) = false := by decide
      rw [different] at matched
      cases matched
    · rfl

private theorem input_descriptor_visibility_matches (visibility : Visibility)
    {descriptor : Backend.Native.Descriptor}
    (parsed : Backend.Native.requireInstruction (inputOpcode visibility) = .ok descriptor) :
    descriptor.privacy.inputVisibility = some visibility := by
  have registered :
      (Backend.Native.requireInstruction (inputOpcode visibility)).map
        (fun item => item.privacy.inputVisibility) = .ok (some visibility) := by
    cases visibility <;> rfl
  have parsedMapped := congrArg (fun result : Except String Backend.Native.Descriptor =>
    result.map (fun item => item.privacy.inputVisibility)) parsed
  have mappedDescriptor :
      (Except.ok descriptor : Except String Backend.Native.Descriptor).map
        (fun item => item.privacy.inputVisibility) =
      .ok descriptor.privacy.inputVisibility := rfl
  have mappedVisibility := mappedDescriptor.symm.trans parsedMapped.symm
  have checked := mappedVisibility.trans registered
  exact Except.ok.inj checked

/-- The producer's input schema check ties the raw output field and visibility
to the exact requirement selected by the live input ordinal. -/
theorem accepted_input_output_descriptor {expected : Expected}
    {state next : State} {raw : Json} {visibility : Visibility}
    {requirement : InputRequirement}
    (selected : expected.inputs[state.inputCount]? = some requirement)
    (nonforeignInput : requirement.ty.isForeign = false)
    (opcodeParsed : Backend.Native.stringField raw "op" =
      .ok (inputOpcode visibility))
    (accepted : validateInstruction expected state raw = .ok next) :
    Backend.Native.stringField raw "output" = .ok requirement.identifier ∧
      requirement.visibility = visibility := by
  cases guarded : requirement.activityGuard with
  | none =>
    unfold validateInstruction at accepted
    simp only [bind_ok] at accepted
    rcases accepted with ⟨opcode, op, descriptor, registry, _, fields, accepted⟩
    have opcodeEq := Except.ok.inj (op.symm.trans opcodeParsed)
    cases visibility with
    | «public» =>
      have opcodeEq : opcode = "public_input" := by simpa [inputOpcode] using opcodeEq
      subst opcode
      have descriptorVisibility := input_descriptor_visibility_matches .public
        (by simpa [inputOpcode] using registry)
      simp only [opcodeEq, selected, guarded] at accepted
      cases ty : requirement.ty <;> try simp [Ty.isForeign, ty] at nonforeignInput
      all_goals
        simp only [ty] at accepted
        simp only [bind_ok] at accepted
        rcases accepted with ⟨typeJson, typeParsed, nativeTypeValue, nativeTypeParsed,
          valueType, valueParsed, guardJson, guardParsed, guardUnit, guardChecked,
          output, outputParsed, schemaUnit, schemaChecked, definedState, defined, result⟩
        have schema := input_schema_output_facts outputParsed schemaChecked
        have checkedVisibility : descriptor.privacy.inputVisibility = some requirement.visibility :=
          eq_of_beq schema.2
        rw [descriptorVisibility] at checkedVisibility
        exact ⟨schema.1, (Option.some.inj checkedVisibility).symm⟩
    | «private» =>
      have opcodeEq : opcode = "private_input" := by simpa [inputOpcode] using opcodeEq
      subst opcode
      have descriptorVisibility := input_descriptor_visibility_matches .private
        (by simpa [inputOpcode] using registry)
      simp only [opcodeEq, selected, guarded] at accepted
      cases ty : requirement.ty <;> try simp [Ty.isForeign, ty] at nonforeignInput
      all_goals
        simp only [ty] at accepted
        simp only [bind_ok] at accepted
        rcases accepted with ⟨typeJson, typeParsed, nativeTypeValue, nativeTypeParsed,
          valueType, valueParsed, guardJson, guardParsed, guardUnit, guardChecked,
          output, outputParsed, schemaUnit, schemaChecked, definedState, defined, result⟩
        have schema := input_schema_output_facts outputParsed schemaChecked
        have checkedVisibility : descriptor.privacy.inputVisibility = some requirement.visibility :=
          eq_of_beq schema.2
        rw [descriptorVisibility] at checkedVisibility
        exact ⟨schema.1, (Option.some.inj checkedVisibility).symm⟩
  | some guardTerm =>
    cases visibility with
    | «public» =>
      unfold validateInstruction at accepted
      simp only [bind_ok] at accepted
      rcases accepted with ⟨opcode, op, descriptor, registry, _, fields, accepted⟩
      have opcodeEq : opcode = "public_input" :=
        Except.ok.inj (op.symm.trans opcodeParsed)
      subst opcode
      have descriptorVisibility := input_descriptor_visibility_matches .public
        (by simpa [inputOpcode] using registry)
      simp only [selected, guarded] at accepted
      cases ty : requirement.ty <;> try simp [Ty.isForeign, ty] at nonforeignInput
      all_goals
        simp only [ty] at accepted
        simp only [bind_ok] at accepted
        rcases accepted with ⟨typeJson, typeParsed, nativeTypeValue, nativeTypeParsed,
          valueType, valueParsed, guardModeUnit, guardModeChecked, guardText,
          guardTextParsed, guardFact, guardOperand, guardBoolean, guardBooleanChecked,
          guardMatchUnit, guardMatch, output, outputParsed, schemaUnit, schemaChecked,
          definedState, defined, result⟩
        have schema := input_schema_output_facts outputParsed schemaChecked
        have checkedVisibility : descriptor.privacy.inputVisibility = some requirement.visibility :=
          eq_of_beq schema.2
        rw [descriptorVisibility] at checkedVisibility
        exact ⟨schema.1, (Option.some.inj checkedVisibility).symm⟩
    | «private» =>
      have unguarded := accepted_private_input_unguarded selected
        (by simpa [inputOpcode] using opcodeParsed) accepted
      rw [guarded] at unguarded
      cases unguarded


/-- Project the exact raw guard and the native fact checked by the producer for
an accepted guarded public ledger read. -/
theorem accepted_guarded_public_input_guard_fact {expected : Expected}
    {state next : State} {raw : Json} {requirement : InputRequirement}
    {guardTerm : Backend.Native.Term}
    (selected : expected.inputs[state.inputCount]? = some requirement)
    (nonforeignInput : requirement.ty.isForeign = false)
    (guarded : requirement.activityGuard = some guardTerm)
    (opcodeParsed : Backend.Native.stringField raw "op" = .ok "public_input")
    (accepted : validateInstruction expected state raw = .ok next) :
    ∃ guardText fact, Backend.Native.stringField raw "guard" = .ok guardText ∧
      operand state guardText = .ok fact ∧ (fact.valueType == NativeValueType.native) = true ∧
      fact.maximum ≤ 1 ∧ fact.term = guardTerm := by
  unfold validateInstruction at accepted
  simp only [bind_ok] at accepted
  rcases accepted with ⟨opcode, op, descriptor, registry, _, fields, accepted⟩
  have opcodeEq : opcode = "public_input" :=
    Except.ok.inj (op.symm.trans opcodeParsed)
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
    change (do
      let value ← operand state guardText
      Backend.Native.ensure (value.valueType == NativeValueType.native)
        "native instruction operand must have Native type"
      pure value) = .ok guardFact at guardOperand
    rcases bind_ok.mp guardOperand with ⟨fact, operandParsed, typed⟩
    rcases bind_ok.mp typed with ⟨_, native, same⟩
    change Except.ok fact = Except.ok guardFact at same
    have factEq := Except.ok.inj same
    subst guardFact
    exact ⟨guardText, fact, guardTextParsed, operandParsed, ensure_ok.mp native,
      of_decide_eq_true (ensure_ok.mp guardBooleanChecked),
      eq_of_beq (ensure_ok.mp guardMatch)⟩

/-- The guarded row supplies its guard through the producer's string parser. -/
theorem accepted_guarded_public_input_guard_string {expected : Expected}
    {state next : State} {raw : Json} {requirement : InputRequirement}
    {guardTerm : Backend.Native.Term}
    (selected : expected.inputs[state.inputCount]? = some requirement)
    (nonforeignInput : requirement.ty.isForeign = false)
    (guarded : requirement.activityGuard = some guardTerm)
    (opcodeParsed : Backend.Native.stringField raw "op" = .ok "public_input")
    (accepted : validateInstruction expected state raw = .ok next) :
    ∃ guardText, Backend.Native.stringField raw "guard" = .ok guardText := by
  obtain ⟨guardText, _, parsed, _, _, _, _⟩ :=
    accepted_guarded_public_input_guard_fact selected nonforeignInput guarded opcodeParsed accepted
  exact ⟨guardText, parsed⟩

/-- An independently decoded guard of an accepted Native public read denotes
the source-selected guard term and has a Boolean field value. The caller
supplies the meaning invariant at the actual row pre-state. -/
theorem accepted_guarded_public_input_guard_meaning
    {hash : Hash} {inputs witness : Assignment} {expected : Expected}
    {state next : State} {raw : Json} {requirement : InputRequirement}
    {guardTerm : Backend.Native.Term} {guard : Operand}
    (invariant : StateMeaning hash inputs witness state)
    (selected : expected.inputs[state.inputCount]? = some requirement)
    (nonforeignInput : requirement.ty.isForeign = false)
    (guarded : requirement.activityGuard = some guardTerm)
    (opcodeParsed : Backend.Native.stringField raw "op" = .ok "public_input")
    (accepted : validateInstruction expected state raw = .ok next)
    (decoded : NativeRelationJson.decodeOperandField raw "guard" = .ok guard) :
    ScalarNormalization.interpret hash inputs guardTerm = some (guard.read witness) ∧
      (guard.read witness = zero ∨ guard.read witness = one) := by
  obtain ⟨guardText, fact, stringParsed, parsed, _, maximum, termEq⟩ :=
    accepted_guarded_public_input_guard_fact selected nonforeignInput guarded opcodeParsed accepted
  unfold Backend.Native.stringField at stringParsed
  unfold NativeRelationJson.decodeOperandField at decoded
  obtain ⟨guardJson, jsonParsed, textParsed⟩ := bind_ok.mp stringParsed
  rw [jsonParsed] at decoded
  change NativeRelationJson.decodeOperand guardJson = .ok guard at decoded
  have meaning := operand_decoded_meaning invariant textParsed parsed decoded
  have bound := Nat.le_trans meaning.bound maximum
  refine ⟨termEq ▸ meaning.term, ?_⟩
  have values : (guard.read witness).val = 0 ∨ (guard.read witness).val = 1 := by omega
  rcases values with inactive | active
  · left
    exact Fin.ext inactive
  · right
    exact Fin.ext active

private theorem checked_native_type_string {raw typeJson : Json} {unitValue : Unit}
    (typeParsed : raw.getObjVal? "type" = .ok typeJson)
    (typeChecked : NativeRelationJson.checkNativeType typeJson = .ok unitValue) :
    Backend.Native.stringField raw "type" = .ok "Scalar<BLS12-381>" := by
  unfold NativeRelationJson.checkNativeType at typeChecked
  simp only [ScalarValidationMeaning.bind_ok] at typeChecked
  rcases typeChecked with ⟨typeText, typeTextParsed, typeTextChecked⟩
  have textEq : typeText = "Scalar<BLS12-381>" :=
    eq_of_beq (ScalarValidationMeaning.ensure_ok.mp typeTextChecked)
  unfold Backend.Native.stringField
  change ((raw.getObjVal? "type") >>= fun value => value.getStr?) =
    .ok "Scalar<BLS12-381>"
  simp [typeParsed, typeTextParsed, textEq, Bind.bind, Except.bind]

/-- The strict input decoder preserves its output string, admits only a null
guard, and checks the native scalar wire type. -/
private theorem strict_decoded_input_fields {raw : Json} {visibility : Visibility}
    {output : String}
    (opcodeParsed : Backend.Native.stringField raw "op" =
      .ok (inputOpcode visibility))
    (decoded : NativeRelationJson.decodeInstruction raw =
      .ok (.input visibility output)) :
    Backend.Native.stringField raw "output" = .ok output ∧
      raw.getObjVal? "guard" = .ok Json.null ∧
      NativeRelationJson.validIdentifier output = true ∧
      Backend.Native.stringField raw "type" = .ok "Scalar<BLS12-381>" := by
  have nativeJson_stringField_eq (value : Json) (name : String) :
      NativeRelationJson.stringField value name = Backend.Native.stringField value name := rfl
  cases visibility with
  | «public» =>
    have decoderOpcode : NativeRelationJson.stringField raw "op" = .ok "public_input" := by
      rw [nativeJson_stringField_eq]
      simpa [inputOpcode] using opcodeParsed
    unfold NativeRelationJson.decodeInstruction at decoded
    simp only [ScalarValidationMeaning.bind_ok] at decoded
    rcases decoded with ⟨opcode, op, decoded⟩
    have opcodeEq : opcode = "public_input" :=
      Except.ok.inj (op.symm.trans decoderOpcode)
    subst opcode
    simp only [ScalarValidationMeaning.bind_ok] at decoded
    rcases decoded with ⟨fieldsUnit, fieldsChecked, guardJson, guardParsed,
      guardUnit, guardChecked, typeJson, typeParsed, typeUnit, typeChecked,
      decodedOutput, outputParsed, validUnit, validChecked, result⟩
    cases result
    refine ⟨(nativeJson_stringField_eq raw "output").symm.trans outputParsed, ?_, ?_, ?_⟩
    · have guardNull : guardJson.isNull = true := by
        cases guardUnit
        cases isNull : guardJson.isNull with
        | false => simp [NativeRelationJson.ensure, isNull] at guardChecked
        | true => rfl
      cases guardJson <;> simp_all [Json.isNull]
    · exact ScalarValidationMeaning.ensure_ok.mp validChecked
    · exact checked_native_type_string typeParsed typeChecked

  | «private» =>
    have decoderOpcode : NativeRelationJson.stringField raw "op" = .ok "private_input" := by
      rw [nativeJson_stringField_eq]
      simpa [inputOpcode] using opcodeParsed
    unfold NativeRelationJson.decodeInstruction at decoded
    simp only [ScalarValidationMeaning.bind_ok] at decoded
    rcases decoded with ⟨opcode, op, decoded⟩
    have opcodeEq : opcode = "private_input" :=
      Except.ok.inj (op.symm.trans decoderOpcode)
    subst opcode
    simp only [ScalarValidationMeaning.bind_ok] at decoded
    rcases decoded with ⟨fieldsUnit, fieldsChecked, guardJson, guardParsed,
      guardUnit, guardChecked, typeJson, typeParsed, typeUnit, typeChecked,
      decodedOutput, outputParsed, validUnit, validChecked, result⟩
    cases result
    refine ⟨(nativeJson_stringField_eq raw "output").symm.trans outputParsed, ?_, ?_, ?_⟩
    · have guardNull : guardJson.isNull = true := by
        cases guardUnit
        cases isNull : guardJson.isNull with
        | false => simp [NativeRelationJson.ensure, isNull] at guardChecked
        | true => rfl
      cases guardJson <;> simp_all [Json.isNull]
    · exact ScalarValidationMeaning.ensure_ok.mp validChecked
    · exact checked_native_type_string typeParsed typeChecked

/-- A strictly decoded input exposes the same output string stored in its
`Instruction.input` constructor. -/
theorem strict_decoded_input_output_identifier {raw : Json} {visibility : Visibility}
    {output : String}
    (opcodeParsed : Backend.Native.stringField raw "op" =
      .ok (inputOpcode visibility))
    (decoded : NativeRelationJson.decodeInstruction raw =
      .ok (.input visibility output)) :
    Backend.Native.stringField raw "output" = .ok output :=
  (strict_decoded_input_fields opcodeParsed decoded).1

/-- Strict input admission rejects preprocessing guards. -/
theorem strict_decoded_input_guard_is_null {raw : Json} {visibility : Visibility}
    {output : String}
    (opcodeParsed : Backend.Native.stringField raw "op" =
      .ok (inputOpcode visibility))
    (decoded : NativeRelationJson.decodeInstruction raw =
      .ok (.input visibility output)) :
    raw.getObjVal? "guard" = .ok Json.null :=
  (strict_decoded_input_fields opcodeParsed decoded).2.1

/-- Strictly decoded input rows have an identifier accepted by the decoder's
SSA-name check. -/
theorem strict_decoded_input_identifier_valid {raw : Json} {visibility : Visibility}
    {output : String}
    (opcodeParsed : Backend.Native.stringField raw "op" =
      .ok (inputOpcode visibility))
    (decoded : NativeRelationJson.decodeInstruction raw =
      .ok (.input visibility output)) :
    NativeRelationJson.validIdentifier output = true :=
  (strict_decoded_input_fields opcodeParsed decoded).2.2.1

private theorem accepted_foreign_input_type_name {expected : Expected}
    {state next : State} {raw : Json} {requirement : InputRequirement}
    {kind : Foreign.Kind} {visibility : Visibility}
    (selected : expected.inputs[state.inputCount]? = some requirement)
    (typed : requirement.ty = .foreign kind)
    (opcodeParsed : Backend.Native.stringField raw "op" =
      .ok (inputOpcode visibility))
    (accepted : validateInstruction expected state raw = .ok next) :
    Backend.Native.stringField raw "type" = .ok kind.nativeName := by
  unfold validateInstruction at accepted
  simp only [ScalarValidationMeaning.bind_ok] at accepted
  rcases accepted with ⟨opcode, op, descriptor, registry, _, fields, accepted⟩
  have opcodeEq := Except.ok.inj (op.symm.trans opcodeParsed)
  cases visibility with
  | «public» =>
    have opcodeEq : opcode = "public_input" := by simpa [inputOpcode] using opcodeEq
    subst opcode
    simp only [opcodeEq, selected, typed] at accepted
    simp only [ScalarValidationMeaning.bind_ok] at accepted
    rcases accepted with ⟨typeName, typeParsed, typeChecked, rest⟩
    have check : Backend.Native.ensure (typeName == kind.nativeName)
        "foreign input type differs from source" = .ok typeChecked := rest.1
    have textEq : typeName = kind.nativeName :=
      eq_of_beq (ScalarValidationMeaning.ensure_ok.mp check)
    rw [typeParsed, textEq]
  | «private» =>
    have opcodeEq : opcode = "private_input" := by simpa [inputOpcode] using opcodeEq
    subst opcode
    simp only [opcodeEq, selected, typed] at accepted
    simp only [ScalarValidationMeaning.bind_ok] at accepted
    rcases accepted with ⟨typeName, typeParsed, typeChecked, rest⟩
    have check : Backend.Native.ensure (typeName == kind.nativeName)
        "foreign input type differs from source" = .ok typeChecked := rest.1
    have textEq : typeName = kind.nativeName :=
      eq_of_beq (ScalarValidationMeaning.ensure_ok.mp check)
    rw [typeParsed, textEq]

private theorem foreign_native_name_ne_relation_native_type (kind : Foreign.Kind) :
    kind.nativeName ≠ "Scalar<BLS12-381>" := by
  cases kind <;> rename_i curve <;> cases curve <;> decide

/-- Producer admission and the strict decoder agree on a nonforeign selected
input type, since strict input rows carry the native scalar wire type. -/
theorem accepted_strict_input_requirement_not_foreign {expected : Expected}
    {state next : State} {raw : Json} {visibility : Visibility}
    {decodedOutput : String} {requirement : InputRequirement}
    (selected : expected.inputs[state.inputCount]? = some requirement)
    (opcodeParsed : Backend.Native.stringField raw "op" =
      .ok (inputOpcode visibility))
    (accepted : validateInstruction expected state raw = .ok next)
    (decoded : NativeRelationJson.decodeInstruction raw =
      .ok (.input visibility decodedOutput)) :
    requirement.ty.isForeign = false := by
  cases ty : requirement.ty with
  | native => simp [Ty.isForeign]
  | bool => simp [Ty.isForeign]
  | uint maximum => simp [Ty.isForeign]
  | bytes length => simp [Ty.isForeign]
  | opaqueBytes => simp [Ty.isForeign]
  | opaqueString => simp [Ty.isForeign]
  | jubjubScalar => simp [Ty.isForeign]
  | jubjubPoint => simp [Ty.isForeign]
  | foreign kind =>
    have producerType := accepted_foreign_input_type_name selected ty opcodeParsed accepted
    have decodedType := (strict_decoded_input_fields opcodeParsed decoded).2.2.2
    have typeEq : kind.nativeName = "Scalar<BLS12-381>" :=
      Except.ok.inj (producerType.symm.trans decodedType)
    exact False.elim ((foreign_native_name_ne_relation_native_type kind) typeEq)

/-- Producer-accepted guarded public reads cannot satisfy the strict decoder's
input shape: the producer parses a string guard and the decoder requires null. -/
theorem accepted_guarded_public_input_rejected_by_strict_decoder
    {expected : Expected} {state next : State} {raw : Json}
    {requirement : InputRequirement} {guardTerm : Backend.Native.Term}
    (selected : expected.inputs[state.inputCount]? = some requirement)
    (nonforeignInput : requirement.ty.isForeign = false)
    (guarded : requirement.activityGuard = some guardTerm)
    (opcodeParsed : Backend.Native.stringField raw "op" = .ok "public_input")
    (accepted : validateInstruction expected state raw = .ok next) :
    ¬ ∃ output,
      NativeRelationJson.decodeInstruction raw = .ok (.input .«public» output) := by
  obtain ⟨guardText, producerGuard⟩ := accepted_guarded_public_input_guard_string
    selected nonforeignInput guarded opcodeParsed accepted
  intro decodedInput
  obtain ⟨output, decoded⟩ := decodedInput
  have decoderGuard := strict_decoded_input_guard_is_null
    (by simpa [inputOpcode] using opcodeParsed) decoded
  unfold Backend.Native.stringField at producerGuard
  simp only [ScalarValidationMeaning.bind_ok] at producerGuard
  rcases producerGuard with ⟨found, fieldParsed, stringParsed⟩
  have foundNull : found = Json.null :=
    Except.ok.inj (fieldParsed.symm.trans decoderGuard)
  rw [foundNull] at stringParsed
  unfold Json.getStr? at stringParsed
  cases stringParsed

/-- When a producer input row also passes the strict decoder's input shape,
both boundaries expose the same ordered visibility and name. Guarded producer
rows remain outside this bridge because the strict decoder requires a null guard. -/
theorem accepted_input_row_descriptor_agrees {expected : Expected}
    {state next : State} {raw : Json} {visibility : Visibility}
    {requirement : InputRequirement} {decodedOutput : String}
    (selected : expected.inputs[state.inputCount]? = some requirement)
    (nonforeignInput : requirement.ty.isForeign = false)
    (opcodeParsed : Backend.Native.stringField raw "op" =
      .ok (inputOpcode visibility))
    (accepted : validateInstruction expected state raw = .ok next)
    (decoded : NativeRelationJson.decodeInstruction raw =
      .ok (.input visibility decodedOutput)) :
    Backend.Native.stringField raw "output" = .ok requirement.identifier ∧
      (visibility, decodedOutput) = (requirement.visibility, requirement.identifier) := by
  obtain ⟨producerName, requirementVisibility⟩ := accepted_input_output_descriptor selected
    nonforeignInput opcodeParsed accepted
  have decoderName := strict_decoded_input_output_identifier opcodeParsed decoded
  have outputEq := Except.ok.inj (decoderName.symm.trans producerName)
  exact ⟨producerName, Prod.ext requirementVisibility.symm outputEq⟩


/-- The ordered production read row agrees with the strict decoded input
descriptor and advances the producer cursor once. -/
theorem accepted_generic_state_input_row_descriptor_agrees (state : List StateDecl)
    (entry : Entrypoint) {expected : Expected} {producerState next : State}
    {raw : Json} {visibility : Visibility} {decodedOutput : String}
    (expectedAccepted : Backend.Native.expectedEntrypoint state entry = .ok expected)
    (inputSchema : ∀ requirement ∈ expected.inputs,
      requirement.ty.isForeign = false)
    (opcodeParsed : Backend.Native.stringField raw "op" =
      .ok (inputOpcode visibility))
    (accepted : validateInstruction expected producerState raw = .ok next)
    (decoded : NativeRelationJson.decodeInstruction raw =
      .ok (.input visibility decodedOutput)) :
    ∃ (plan : Backend.Impact.Plan)
      (inputState : List InputRequirement × List Backend.Native.Term ×
        List (Backend.Native.Term × Nat) × Nat)
      (requirement : InputRequirement),
      Backend.Impact.lower state entry = .ok plan ∧
      expected.inputs = inputState.1 ∧
      expected.inputs[producerState.inputCount]? = some requirement ∧
      next.inputCount = producerState.inputCount + 1 ∧
      Backend.Native.stringField raw "output" = .ok requirement.identifier ∧
      (visibility, decodedOutput) = (requirement.visibility, requirement.identifier) := by
  obtain ⟨plan, inputState, requirement, lowered, inputsExact, selected, increment⟩ :=
    accepted_generic_state_input_row_step state entry expectedAccepted inputSchema
      opcodeParsed accepted
  have member : requirement ∈ expected.inputs := List.mem_of_getElem? selected
  obtain ⟨producerName, decodedDescriptor⟩ := accepted_input_row_descriptor_agrees selected
    (inputSchema requirement member) opcodeParsed accepted decoded
  exact ⟨plan, inputState, requirement, lowered, inputsExact, selected,
    increment, producerName, decodedDescriptor⟩

end Noctium.Verification.NativeInputOrdinal
