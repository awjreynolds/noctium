import Noctium.Backend.NativeProducer
import Noctium.Verification.NativeRelationJson
import Noctium.Verification.ScalarValidationMeaning
import Noctium.Verification.ScalarValidationArithmeticLoop

namespace Noctium.Verification.ScalarValidationNativeLoop

open Lean Backend.Native NativeRelation NativeRelationJson
open Noctium.Verification.ScalarValidationMeaning
open Noctium.Verification.ScalarValidationArithmeticLoop

def inputOpcode : Visibility → String
  | .«public» => "public_input"
  | .«private» => "private_input"

theorem define_nativeDefinitions {state next : State} {identifier : String} {fact : Fact}
    (nativeDefinitions : NativeDefinitions state)
    (factNative : fact.valueType = .native)
    (accepted : define state identifier fact = .ok next) :
    NativeDefinitions next := by
  unfold define at accepted
  simp only [bind_ok] at accepted
  rcases accepted with ⟨_, _, _, _, result⟩
  cases result
  intro name found member
  simp only [List.mem_append, List.mem_singleton, Prod.mk.injEq] at member
  rcases member with member | ⟨sameName, sameFact⟩
  · exact nativeDefinitions name found member
  · subst name
    subst found
    exact factNative

theorem input_nativeDefinitions_step {expected : Expected} {state next : State}
    {raw : Json} {visibility : Visibility} {requirement : InputRequirement}
    (nativeDefinitions : NativeDefinitions state)
    (selected : expected.inputs[state.inputCount]? = some requirement)
    (nonforeignInput : requirement.ty.isForeign = false)
    (unguarded : requirement.activityGuard = none)
    (opcodeParsed : Backend.Native.stringField raw "op" = .ok (inputOpcode visibility))
    (accepted : validateInstruction expected state raw = .ok next) :
    NativeDefinitions next := by
  cases visibility <;> all_goals
    unfold validateInstruction at accepted
    simp only [bind_ok] at accepted
    rcases accepted with ⟨opcode, op, descriptor, registry, _, fields, accepted⟩
    have opcodeEq := Except.ok.inj (op.symm.trans opcodeParsed)
    simp only [opcodeEq, inputOpcode, selected] at accepted
    split at accepted
    · simp_all [Ty.isForeign]
    ·
      simp only [unguarded] at accepted
      simp only [bind_ok] at accepted
      rcases accepted with ⟨typeJson, typeParsed, _, typeChecked, valueType, valueParsed,
        guardJson, guardParsed, _, guardChecked, output, outputParsed, _, schema,
        definedState, defined, result⟩
      cases valueParsed
      have definedInput : define state output
          ({term := .input output, maximum := Field.modulus - 1} : Fact) = .ok definedState := by
        change define state output
          ({term := .input output, maximum := Field.modulus - 1} : Fact) = .ok definedState at defined
        exact defined
      have typedState : NativeDefinitions definedState := by
        exact define_nativeDefinitions nativeDefinitions rfl definedInput
      let nextState : State := { definedState with inputCount := definedState.inputCount + 1 }
      have nextEq : nextState = next := by
        change Except.ok nextState = .ok next at result
        exact Except.ok.inj result
      subst next
      change NativeDefinitions {definedState with inputCount := definedState.inputCount + 1}
      exact typedState

/-- A source-bound guarded public read adds the same native input definition as
an unguarded input after its guard passes the producer's Boolean and identity
checks. -/
theorem guarded_public_input_nativeDefinitions_step {expected : Expected}
    {state next : State} {raw : Json} {requirement : InputRequirement}
    {guardTerm : Backend.Native.Term}
    (nativeDefinitions : NativeDefinitions state)
    (selected : expected.inputs[state.inputCount]? = some requirement)
    (nonforeignInput : requirement.ty.isForeign = false)
    (guarded : requirement.activityGuard = some guardTerm)
    (opcodeParsed : Backend.Native.stringField raw "op" = .ok "public_input")
    (accepted : validateInstruction expected state raw = .ok next) :
    NativeDefinitions next := by
  unfold validateInstruction at accepted
  simp only [bind_ok] at accepted
  rcases accepted with ⟨opcode, op, descriptor, registry, _, fields, accepted⟩
  have opcodeEq : opcode = "public_input" := Except.ok.inj (op.symm.trans opcodeParsed)
  simp only [opcodeEq, selected] at accepted
  split at accepted
  · simp_all [Ty.isForeign]
  · simp only [guarded] at accepted
    simp only [bind_ok] at accepted
    rcases accepted with ⟨typeJson, typeParsed, _, typeChecked, valueType, valueParsed,
      _, _, guardJson, guardParsed, _, guardChecked, _, _, _, _, output, outputParsed,
      _, schema, definedState, defined, result⟩
    cases valueParsed
    have typedState : NativeDefinitions definedState := by
      exact define_nativeDefinitions nativeDefinitions rfl defined
    let nextState : State := { definedState with inputCount := definedState.inputCount + 1 }
    have nextEq : nextState = next := by
      change Except.ok nextState = .ok next at result
      exact Except.ok.inj result
    subst next
    change NativeDefinitions {definedState with inputCount := definedState.inputCount + 1}
    exact typedState

theorem accepted_input_requirement_selected {expected : Expected} {state next : State}
    {raw : Json} {visibility : Visibility}
    (opcodeParsed : Backend.Native.stringField raw "op" = .ok (inputOpcode visibility))
    (accepted : validateInstruction expected state raw = .ok next) :
    ∃ requirement, expected.inputs[state.inputCount]? = some requirement := by
  cases visibility <;> all_goals
    unfold validateInstruction at accepted
    simp only [bind_ok] at accepted
    rcases accepted with ⟨opcode, op, descriptor, registry, _, fields, accepted⟩
    have opcodeEq := Except.ok.inj (op.symm.trans opcodeParsed)
    simp only [opcodeEq, inputOpcode] at accepted
    cases selected : expected.inputs[state.inputCount]? with
    | none => simp [selected] at accepted
    | some requirement => exact ⟨requirement, rfl⟩

inductive NativeStepHolds (hash : Hash) (witness : Assignment) (raw : Json) : Prop where
  | publicInput
      (opcode : Backend.Native.stringField raw "op" = .ok "public_input")
      : NativeStepHolds hash witness raw
  | privateInput
      (opcode : Backend.Native.stringField raw "op" = .ok "private_input")
      : NativeStepHolds hash witness raw
  | arithmetic (steps : NativeArithmeticHolds hash witness raw) :
      NativeStepHolds hash witness raw

/-- Accepted Native input and arithmetic instructions preserve meaning in
order. The actual producer state selects each input by its live input count.
Input steps use the producer's checked output and type schema, plus agreement
for the selected expected input. -/
theorem accepted_native_loop_meaning
    {hash : Hash} {inputs witness : Assignment} {expected : Expected}
    {items : List (Json × Nat)} {initial final : State}
    (invariant : StateMeaning hash inputs witness initial)
    (nativeDefinitions : NativeDefinitions initial)
    (inputSchema : ∀ requirement ∈ expected.inputs,
      requirement.ty.isForeign = false ∧ requirement.activityGuard = none)
    (inputAgreement : ∀ requirement ∈ expected.inputs,
      witness requirement.identifier = inputs requirement.identifier)
    (steps : ∀ item ∈ items, NativeStepHolds hash witness item.1)
    (accepted : validateInstructionLoop expected items initial = .ok final) :
    StateMeaning hash inputs witness final ∧ NativeDefinitions final := by
  induction items generalizing initial final with
  | nil =>
    have initialEq : initial = final := by injection accepted
    subst final
    exact ⟨invariant, nativeDefinitions⟩
  | cons head tail ih =>
    rw [validateInstructionLoop, List.forIn_cons] at accepted
    cases checked : validateInstruction expected initial head.1 with
    | error message => simp [checked, Bind.bind, Except.bind] at accepted
    | ok next =>
      simp only [checked, bind_pure_comp] at accepted
      have nextInvariant : StateMeaning hash inputs witness next ∧ NativeDefinitions next := by
        cases steps head (by simp) with
        | publicInput opcode =>
          obtain ⟨requirement, selected⟩ := accepted_input_requirement_selected
            (visibility := .«public») (by simpa [inputOpcode] using opcode) checked
          have member : requirement ∈ expected.inputs := List.mem_of_getElem? selected
          obtain ⟨nonforeignInput, unguarded⟩ := inputSchema requirement member
          have agreement := inputAgreement requirement member
          exact ⟨public_input_step_meaning invariant selected nonforeignInput unguarded agreement
              opcode checked,
            input_nativeDefinitions_step (visibility := .«public») nativeDefinitions selected
              nonforeignInput unguarded (by simpa [inputOpcode] using opcode) checked⟩
        | privateInput opcode =>
          obtain ⟨requirement, selected⟩ := accepted_input_requirement_selected
            (visibility := .«private») (by simpa [inputOpcode] using opcode) checked
          have member : requirement ∈ expected.inputs := List.mem_of_getElem? selected
          obtain ⟨nonforeignInput, unguarded⟩ := inputSchema requirement member
          have agreement := inputAgreement requirement member
          exact ⟨private_input_step_meaning invariant selected nonforeignInput unguarded agreement
              opcode checked,
            input_nativeDefinitions_step (visibility := .«private») nativeDefinitions selected
              nonforeignInput unguarded (by simpa [inputOpcode] using opcode) checked⟩
        | arithmetic arithmeticStep =>
          cases arithmeticStep with
          | add _ _ _ opcode decoded holds =>
            exact accepted_native_add_step_meaning invariant nativeDefinitions opcode checked
              decoded holds
          | mul _ _ _ opcode decoded holds =>
            exact accepted_native_mul_step_meaning invariant nativeDefinitions opcode checked
              decoded holds
          | neg _ _ opcode decoded holds =>
            exact accepted_native_neg_step_meaning invariant nativeDefinitions opcode checked
              decoded holds
      exact ih nextInvariant.1 nextInvariant.2
        (fun item member => steps item (List.mem_cons_of_mem _ member)) accepted

end Noctium.Verification.ScalarValidationNativeLoop
