import Noctium.Verification.ScalarValidationNativeLoop
import Noctium.Verification.GenericStateCircuitParts

namespace Noctium.Verification.NativeInputOrdinal

open Lean Backend.Native NativeRelationJson
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

/-- Every accepted unguarded native input consumes exactly the live expected
input ordinal. The selected row and visibility checks are shared with the
active producer input bridge. -/
theorem accepted_unguarded_input_count_increment {expected : Expected}
    {state next : State} {raw : Json} {requirement : InputRequirement}
    (visibility : Visibility)
    (selected : expected.inputs[state.inputCount]? = some requirement)
    (_nonforeignInput : requirement.ty.isForeign = false)
    (unguarded : requirement.activityGuard = none)
    (opcodeParsed : Backend.Native.stringField raw "op" =
      .ok (inputOpcode visibility))
    (accepted : validateInstruction expected state raw = .ok next) :
    next.inputCount = state.inputCount + 1 := by
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
      have resultEq :
          {definedState with inputCount := definedState.inputCount + 1} = next := by
        change Except.ok {definedState with inputCount := definedState.inputCount + 1} =
          Except.ok next at result
        exact Except.ok.inj result
      have countEq : next.inputCount = definedState.inputCount + 1 := by
        simpa only [State.inputCount] using
          (congrArg State.inputCount resultEq).symm
      rw [definedCount] at countEq
      exact countEq
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
      have resultEq :
          {definedState with inputCount := definedState.inputCount + 1} = next := by
        change Except.ok {definedState with inputCount := definedState.inputCount + 1} =
          Except.ok next at result
        exact Except.ok.inj result
      have countEq : next.inputCount = definedState.inputCount + 1 := by
        simpa only [State.inputCount] using
          (congrArg State.inputCount resultEq).symm
      rw [definedCount] at countEq
      exact countEq

/-- A guarded public ledger read consumes one input ordinal after the pinned
producer validates its source-bound guard and schema. -/
theorem accepted_guarded_public_input_count_increment {expected : Expected}
    {state next : State} {raw : Json} {requirement : InputRequirement}
    {guardTerm : Backend.Native.Term}
    (selected : expected.inputs[state.inputCount]? = some requirement)
    (_nonforeignInput : requirement.ty.isForeign = false)
    (guarded : requirement.activityGuard = some guardTerm)
    (opcodeParsed : Backend.Native.stringField raw "op" = .ok "public_input")
    (accepted : validateInstruction expected state raw = .ok next) :
    next.inputCount = state.inputCount + 1 := by
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
    have resultEq :
        {definedState with inputCount := definedState.inputCount + 1} = next := by
      change Except.ok {definedState with inputCount := definedState.inputCount + 1} =
        Except.ok next at result
      exact Except.ok.inj result
    have countEq : next.inputCount = definedState.inputCount + 1 := by
      simpa only [State.inputCount] using
        (congrArg State.inputCount resultEq).symm
    rw [definedCount] at countEq
    exact countEq

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

end Noctium.Verification.NativeInputOrdinal
