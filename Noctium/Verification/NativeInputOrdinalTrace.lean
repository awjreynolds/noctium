import Noctium.Verification.NativeInputOrdinal
import Noctium.Verification.ScalarValidationNativeDefinitions

namespace Noctium.Verification.NativeInputOrdinalTrace

open Lean Backend.Native NativeRelation NativeRelationJson
open Noctium.Verification.NativeInputOrdinal
open Noctium.Verification.ScalarValidationArithmeticLoop
open Noctium.Verification.ScalarValidationNativeDefinitions
open Noctium.Verification.ScalarValidationNativeLoop

def expectedInputName (requirement : InputRequirement) : String := requirement.identifier

def strictInstructionInputNames : Instruction → List String
  | .input _ output => [output]
  | _ => []

/-- A decoded strict-profile row either consumes one expected input with the
same name, or preserves the producer input cursor and contributes no name. -/
theorem accepted_supportedScalarOpcode_input_names_step {expected : Expected}
    {state next : State} {raw : Json} {instruction : Instruction}
    (definitions : NativeDefinitions state)
    (inputSchema : ∀ requirement ∈ expected.inputs,
      requirement.ty.isForeign = false)
    (step : NativeDefinitionStep raw instruction)
    (accepted : validateInstruction expected state raw = .ok next) :
    (expected.inputs.take next.inputCount).map expectedInputName =
      (expected.inputs.take state.inputCount).map expectedInputName ++
        strictInstructionInputNames instruction := by
  cases step with
  | mk supported decoded =>
    cases supported with
    | publicInput output opcode =>
      have opcodeParsed : Backend.Native.stringField raw "op" =
          .ok (inputOpcode .public) := by
        simpa [inputOpcode] using opcode
      obtain ⟨requirement, selected, increment⟩ :=
        accepted_input_row_step inputSchema opcodeParsed accepted
      have member : requirement ∈ expected.inputs := List.mem_of_getElem? selected
      obtain ⟨_, decodedName⟩ := accepted_input_row_names_agree selected
        (inputSchema requirement member) opcodeParsed accepted decoded
      rw [increment, List.take_add_one, selected]
      simp [expectedInputName, strictInstructionInputNames, decodedName]
    | privateInput output opcode =>
      have opcodeParsed : Backend.Native.stringField raw "op" =
          .ok (inputOpcode .private) := by
        simpa [inputOpcode] using opcode
      obtain ⟨requirement, selected, increment⟩ :=
        accepted_input_row_step inputSchema opcodeParsed accepted
      have member : requirement ∈ expected.inputs := List.mem_of_getElem? selected
      obtain ⟨_, decodedName⟩ := accepted_input_row_names_agree selected
        (inputSchema requirement member) opcodeParsed accepted decoded
      rw [increment, List.take_add_one, selected]
      simp [expectedInputName, strictInstructionInputNames, decodedName]
    | add _ _ _ opcode =>
      have unchanged := (accepted_add_counters definitions opcode accepted).2
      rw [unchanged]
      simp [strictInstructionInputNames]
    | mul _ _ _ opcode =>
      have unchanged := (accepted_mul_counters definitions opcode accepted).2
      rw [unchanged]
      simp [strictInstructionInputNames]
    | neg _ _ opcode =>
      have unchanged := (accepted_neg_counters definitions opcode accepted).2
      rw [unchanged]
      simp [strictInstructionInputNames]
    | bits _ _ opcode =>
      have unchanged := (accepted_constrainBits_counters opcode accepted).2
      rw [unchanged]
      simp [strictInstructionInputNames]
    | boolean _ opcode =>
      have unchanged := (accepted_constrainBoolean_counters opcode accepted).2
      rw [unchanged]
      simp [strictInstructionInputNames]
    | lessThan _ _ _ _ opcode =>
      have unchanged := (accepted_lessThan_counters opcode accepted).2
      rw [unchanged]
      simp [strictInstructionInputNames]
    | assertion _ opcode =>
      have unchanged := (accepted_assert_counters opcode accepted).2
      rw [unchanged]
      simp [strictInstructionInputNames]
    | testEq _ _ _ opcode =>
      have unchanged := (accepted_testEq_counters definitions opcode accepted).2
      rw [unchanged]
      simp [strictInstructionInputNames]
    | copy _ _ opcode =>
      have unchanged := (accepted_copy_counters definitions opcode accepted).2
      rw [unchanged]
      simp [strictInstructionInputNames]
    | impact _ _ opcode =>
      have unchanged := accepted_impact_inputCount opcode accepted
      rw [unchanged]
      simp [strictInstructionInputNames]
    | output _ opcode =>
      have unchanged := (accepted_output_counters opcode accepted).2
      rw [unchanged]
      simp [strictInstructionInputNames]
    | constrainEq _ _ opcode =>
      have unchanged := (accepted_constrainEq_counters definitions opcode accepted).2
      rw [unchanged]
      simp [strictInstructionInputNames]

/-- Checked input names compose over the full accepted strict-profile trace.
Non-input rows preserve the live cursor through producer-specific counter
lemmas, while input rows advance once and match their decoded name. -/
theorem validateInstructionLoop_input_names_of_trace {expected : Expected}
    {items : List (Json × Nat)} {instructions : List Instruction}
    {initial final : State}
    (inputSchema : ∀ requirement ∈ expected.inputs,
      requirement.ty.isForeign = false)
    (initialDefinitions : NativeDefinitions initial)
    (trace : NativeDefinitionTrace items instructions)
    (accepted : validateInstructionLoop expected items initial = .ok final) :
    (expected.inputs.take final.inputCount).map expectedInputName =
      (expected.inputs.take initial.inputCount).map expectedInputName ++
        instructions.flatMap strictInstructionInputNames := by
  induction trace generalizing initial final with
  | nil =>
    have stateEq : initial = final := by injection accepted
    subst final
    simp
  | @cons raw index instruction tailItems tailInstructions head tail ih =>
    rw [validateInstructionLoop, List.forIn_cons] at accepted
    cases checked : validateInstruction expected initial raw with
    | error message => simp [checked, Bind.bind, Except.bind] at accepted
    | ok next =>
      simp only [checked, bind_pure_comp] at accepted
      have nextDefinitions := nativeDefinitions_step inputSchema initialDefinitions
        head checked
      have headNames := accepted_supportedScalarOpcode_input_names_step
        initialDefinitions inputSchema head checked
      have restNames := ih nextDefinitions accepted
      rw [restNames, headNames]
      simp [strictInstructionInputNames, List.append_assoc]

end Noctium.Verification.NativeInputOrdinalTrace
