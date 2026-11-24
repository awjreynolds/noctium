import Noctium.Verification.NativeInputOrdinal
import Noctium.Verification.NativeRelationInstructionProjection
import Noctium.Verification.ScalarValidationOpcodeProfile
import Noctium.Verification.ScalarValidationProjection
import Noctium.Verification.ScalarValidationNativeDefinitions

namespace Noctium.Verification.NativeInputOrdinalTrace

open Lean Backend.Native NativeRelation NativeRelationJson
open Noctium.Verification.NativeInputOrdinal
open Noctium.Verification.ScalarValidationArithmeticLoop
open Noctium.Verification.ScalarValidationNativeDefinitions
open Noctium.Verification.ScalarValidationNativeLoop
open Noctium.Verification.ScalarValidationOpcodeProfile
open Noctium.Verification.ScalarValidationProjection

def expectedInputDescriptor (requirement : InputRequirement) : Visibility × String :=
  (requirement.visibility, requirement.identifier)

def strictInstructionInputDescriptors : Instruction → List (Visibility × String)
  | .input visibility output => [(visibility, output)]
  | _ => []


/-- A decoded strict-profile row either consumes the next expected input with
the same visibility and name, or preserves the producer input cursor. -/
theorem accepted_supportedScalarOpcode_input_descriptors_step {expected : Expected}
    {state next : State} {raw : Json} {instruction : Instruction}
    (definitions : NativeDefinitions state)
    (inputSchema : ∀ requirement ∈ expected.inputs,
      requirement.ty.isForeign = false)
    (step : NativeDefinitionStep raw instruction)
    (accepted : validateInstruction expected state raw = .ok next) :
    (expected.inputs.take next.inputCount).map expectedInputDescriptor =
      (expected.inputs.take state.inputCount).map expectedInputDescriptor ++
        strictInstructionInputDescriptors instruction := by
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
      obtain ⟨_, decodedDescriptor⟩ := accepted_input_row_descriptor_agrees selected
        (inputSchema requirement member) opcodeParsed accepted decoded
      rw [increment, List.take_add_one, selected]
      simp [expectedInputDescriptor, strictInstructionInputDescriptors, decodedDescriptor]
    | privateInput output opcode =>
      have opcodeParsed : Backend.Native.stringField raw "op" =
          .ok (inputOpcode .private) := by
        simpa [inputOpcode] using opcode
      obtain ⟨requirement, selected, increment⟩ :=
        accepted_input_row_step inputSchema opcodeParsed accepted
      have member : requirement ∈ expected.inputs := List.mem_of_getElem? selected
      obtain ⟨_, decodedDescriptor⟩ := accepted_input_row_descriptor_agrees selected
        (inputSchema requirement member) opcodeParsed accepted decoded
      rw [increment, List.take_add_one, selected]
      simp [expectedInputDescriptor, strictInstructionInputDescriptors, decodedDescriptor]
    | add _ _ _ opcode =>
      have unchanged := (accepted_add_counters definitions opcode accepted).2
      rw [unchanged]
      simp [strictInstructionInputDescriptors]
    | mul _ _ _ opcode =>
      have unchanged := (accepted_mul_counters definitions opcode accepted).2
      rw [unchanged]
      simp [strictInstructionInputDescriptors]
    | neg _ _ opcode =>
      have unchanged := (accepted_neg_counters definitions opcode accepted).2
      rw [unchanged]
      simp [strictInstructionInputDescriptors]
    | bits _ _ opcode =>
      have unchanged := (accepted_constrainBits_counters opcode accepted).2
      rw [unchanged]
      simp [strictInstructionInputDescriptors]
    | boolean _ opcode =>
      have unchanged := (accepted_constrainBoolean_counters opcode accepted).2
      rw [unchanged]
      simp [strictInstructionInputDescriptors]
    | lessThan _ _ _ _ opcode =>
      have unchanged := (accepted_lessThan_counters opcode accepted).2
      rw [unchanged]
      simp [strictInstructionInputDescriptors]
    | assertion _ opcode =>
      have unchanged := (accepted_assert_counters opcode accepted).2
      rw [unchanged]
      simp [strictInstructionInputDescriptors]
    | testEq _ _ _ opcode =>
      have unchanged := (accepted_testEq_counters definitions opcode accepted).2
      rw [unchanged]
      simp [strictInstructionInputDescriptors]
    | copy _ _ opcode =>
      have unchanged := (accepted_copy_counters definitions opcode accepted).2
      rw [unchanged]
      simp [strictInstructionInputDescriptors]
    | impact _ _ opcode =>
      have unchanged := accepted_impact_inputCount opcode accepted
      rw [unchanged]
      simp [strictInstructionInputDescriptors]
    | output _ opcode =>
      have unchanged := (accepted_output_counters opcode accepted).2
      rw [unchanged]
      simp [strictInstructionInputDescriptors]
    | constrainEq _ _ opcode =>
      have unchanged := (accepted_constrainEq_counters definitions opcode accepted).2
      rw [unchanged]
      simp [strictInstructionInputDescriptors]

/-- Checked input descriptors compose over the full accepted strict-profile
trace. Non-input rows preserve the live cursor through producer-specific
counter lemmas, while input rows advance once and match visibility and name. -/
theorem validateInstructionLoop_input_descriptors_of_trace {expected : Expected}
    {items : List (Json × Nat)} {instructions : List Instruction}
    {initial final : State}
    (inputSchema : ∀ requirement ∈ expected.inputs,
      requirement.ty.isForeign = false)
    (initialDefinitions : NativeDefinitions initial)
    (trace : NativeDefinitionTrace items instructions)
    (accepted : validateInstructionLoop expected items initial = .ok final) :
    (expected.inputs.take final.inputCount).map expectedInputDescriptor =
      (expected.inputs.take initial.inputCount).map expectedInputDescriptor ++
        instructions.flatMap strictInstructionInputDescriptors := by
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
      have headDescriptors := accepted_supportedScalarOpcode_input_descriptors_step
        initialDefinitions inputSchema head checked
      have restDescriptors := ih nextDefinitions accepted
      rw [restDescriptors, headDescriptors]
      simp [strictInstructionInputDescriptors, List.append_assoc]

/-- An actually lowered entrypoint whose JSON also passes the strict relation
decoder and checked scalar opcode profile exposes exactly the producer's
ordered input descriptors. The strict decoder enforces an empty root input
header. The producer's validated raw-input count therefore proves that the
raw seed is empty. Source input types remain restricted to the nonforeign
fragment; this theorem establishes names and visibility, not assignment
value equality. -/
theorem lowerEntrypoint_inputDescriptors_of_checkedScalarProfile
    (state : List StateDecl) (entry : Entrypoint)
    (json : Lean.Json) (program : NativeRelation.Program)
    (lowered : Backend.Zkir.lowerEntrypoint state entry = .ok json)
    (decoded : NativeRelationJson.decode json = .ok program)
    (inputSchema : ∀ expected,
      Backend.Native.expectedEntrypoint state (Passes.pruneEntrypoint entry) =
        .ok expected →
      ∀ requirement ∈ expected.inputs, requirement.ty.isForeign = false)
    (checkedProfile : ∃ instructions : Array Lean.Json,
      Backend.Native.arrayField json "instructions" = .ok instructions ∧
      checkedScalarOpcodeProfile (instructions.toList.zipIdx) program.instructions = true) :
    ∃ expected,
      Backend.Native.expectedEntrypoint state (Passes.pruneEntrypoint entry) =
        .ok expected ∧
      expected.rawInputs = [] ∧
      program.instructions.flatMap strictInstructionInputDescriptors =
        expected.inputs.map expectedInputDescriptor := by
  obtain ⟨_, expected, _, expectedAccepted, validated, _⟩ :=
    Backend.Zkir.lowerEntrypoint_validation_and_instructions state entry json lowered
  obtain ⟨headerInstructions, rawInputsHeader, headerInstructionsParsed,
    decodedRows⟩ := NativeRelationInstructionProjection.decode_headerAndInstructions decoded
  obtain ⟨profileInstructions, profileParsed, profile⟩ := checkedProfile
  obtain ⟨expectedRawInputsEmpty, driverInstructions, final, driver⟩ :=
    validate_driver_result_empty_header validated rawInputsHeader
  have driverMatchesHeader : driverInstructions = headerInstructions :=
    Except.ok.inj (driver.instructionsParsed.symm.trans headerInstructionsParsed)
  have profileMatchesHeader : profileInstructions = headerInstructions :=
    Except.ok.inj (profileParsed.symm.trans headerInstructionsParsed)
  let items := headerInstructions.toList.zipIdx
  have decodedItems : (items.map Prod.fst).mapM NativeRelationJson.decodeInstruction =
      .ok program.instructions := by
    simpa [items, List.zipIdx_map_fst] using decodedRows
  have checkedTrace : NativeDefinitionTrace items program.instructions := by
    apply NativeDefinitionTrace.ofDecodedCheckedProfile decodedItems
    simpa [items, profileMatchesHeader] using profile
  have driverTrace : validateInstructionLoop expected items {} = .ok final := by
    simpa [items, driverMatchesHeader] using driver.instructionTrace
  have inputDescriptors := validateInstructionLoop_input_descriptors_of_trace
    (inputSchema expected expectedAccepted) empty_nativeDefinitions checkedTrace driverTrace
  have exactDescriptors :
      program.instructions.flatMap strictInstructionInputDescriptors =
        expected.inputs.map expectedInputDescriptor := by
    rw [driver.inputCount, driver.seedInputCount] at inputDescriptors
    simpa only [List.take_length, List.take_zero, List.map_nil, List.nil_append]
      using inputDescriptors.symm
  exact ⟨expected, expectedAccepted, expectedRawInputsEmpty, exactDescriptors⟩

end Noctium.Verification.NativeInputOrdinalTrace
