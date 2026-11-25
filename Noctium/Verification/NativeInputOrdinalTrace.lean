import Noctium.Verification.NativeInputOrdinal
import Noctium.Verification.NativeRelationInstructionProjection
import Noctium.Verification.ScalarValidationOpcodeProfile
import Noctium.Verification.ScalarValidationProjection
import Noctium.Verification.ScalarValidationNativeDefinitions

namespace Noctium.Verification.NativeInputOrdinalTrace

open Lean Backend.Native NativeRelation NativeRelationJson
open Noctium.Verification.NativeInputOrdinal
open Noctium.Verification.ScalarValidationArithmeticLoop
open Noctium.Verification.ScalarValidationHashMeaning
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
    | hash _ _ opcode =>
      obtain ⟨_, _, _, _, _, defined⟩ := accepted_hash_definition opcode accepted
      have unchanged := (defineResult_counters defined).2
      rw [unchanged]
      simp [strictInstructionInputDescriptors]
    | not _ _ opcode =>
      obtain ⟨_, _, _, _, _, _, defined⟩ :=
        accepted_not_components definitions opcode accepted
      have unchanged := (defineResult_counters defined).2
      rw [unchanged]
      simp [strictInstructionInputDescriptors]
    | select _ _ _ _ opcode =>
      obtain ⟨_, _, _, _, _, _, _, _, _, _, _, _, defined⟩ :=
        accepted_native_select_components definitions opcode accepted
      have unchanged := (defineResult_counters defined).2
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
ordered input descriptors for any accepted rewrite mode. The strict decoder
enforces an empty root input header. The producer's validated raw-input count
therefore proves that the raw seed is empty. Source input types remain
restricted to the nonforeign fragment; this theorem establishes names and
visibility, not assignment value equality. -/
theorem lowerEntrypoint_inputDescriptors_of_checkedScalarProfile
    (rewrites : Backend.Zkir.Rewrites)
    (state : List StateDecl) (entry : Entrypoint)
    (json : Lean.Json) (program : NativeRelation.Program)
    (lowered : Backend.Zkir.lowerEntrypoint state entry rewrites = .ok json)
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
    Backend.Zkir.lowerEntrypoint_validation_and_instructions_with_rewrites
      state entry rewrites json lowered
  obtain ⟨headerInstructions, rawInputsHeader, headerInstructionsParsed,
    decodedRows⟩ := NativeRelationInstructionProjection.decode_headerAndInstructions decoded
  obtain ⟨profileInstructions, profileParsed, profile⟩ := checkedProfile
  let validatedExpected := Backend.Zkir.optimizedExpected rewrites expected
  obtain ⟨validatedRawInputsEmpty, driverInstructions, final, driver⟩ :=
    validate_driver_result_empty_header (expected := validatedExpected) validated rawInputsHeader
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
  have driverTrace : validateInstructionLoop validatedExpected items {} = .ok final := by
    simpa [items, driverMatchesHeader] using driver.instructionTrace
  have validatedInputsUnchanged : validatedExpected.inputs = expected.inputs := by
    cases rewrites <;> rfl
  have validatedInputSchema : ∀ requirement ∈ validatedExpected.inputs,
      requirement.ty.isForeign = false := by
    intro requirement member
    rw [validatedInputsUnchanged] at member
    exact inputSchema expected expectedAccepted requirement member
  have inputDescriptors := validateInstructionLoop_input_descriptors_of_trace
    validatedInputSchema empty_nativeDefinitions checkedTrace driverTrace
  have validatedDescriptors :
      program.instructions.flatMap strictInstructionInputDescriptors =
        validatedExpected.inputs.map expectedInputDescriptor := by
    rw [driver.inputCount, driver.seedInputCount] at inputDescriptors
    simpa only [List.take_length, List.take_zero, List.map_nil, List.nil_append]
      using inputDescriptors.symm
  have rawInputsUnchanged : validatedExpected.rawInputs = expected.rawInputs := by
    cases rewrites <;> rfl
  have expectedRawInputsEmpty : expected.rawInputs = [] := by
    rw [← rawInputsUnchanged]
    exact validatedRawInputsEmpty
  have exactDescriptors :
      program.instructions.flatMap strictInstructionInputDescriptors =
        expected.inputs.map expectedInputDescriptor := by
    rw [← validatedInputsUnchanged]
    exact validatedDescriptors
  exact ⟨expected, expectedAccepted, expectedRawInputsEmpty, exactDescriptors⟩

private theorem validate_decoded_input_trace_of_checkedScalarProfile
    {expected : Expected} {json : Lean.Json} {program : NativeRelation.Program}
    {rows : Array Lean.Json}
    (nativeAccepted : Backend.Native.validate expected json = .ok ())
    (decoded : NativeRelationJson.decode json = .ok program)
    (rowsParsed : Backend.Native.arrayField json "instructions" = .ok rows)
    (profile : checkedScalarOpcodeProfile (rows.toList.zipIdx) program.instructions = true) :
    ∃ final : State,
      NativeDefinitionTrace (rows.toList.zipIdx) program.instructions ∧
      validateInstructionLoop expected (rows.toList.zipIdx) {} = .ok final ∧
      final.inputCount = expected.inputs.length := by
  obtain ⟨headerInstructions, rawInputsHeader, headerInstructionsParsed,
    decodedRows⟩ := NativeRelationInstructionProjection.decode_headerAndInstructions decoded
  have rowsEq : headerInstructions = rows :=
    Except.ok.inj (headerInstructionsParsed.symm.trans rowsParsed)
  obtain ⟨_, producerInstructions, final, driver⟩ :=
    ScalarValidationProjection.validate_driver_result_empty_header
      (expected := expected) nativeAccepted rawInputsHeader
  have driverRowsEq : producerInstructions = rows :=
    Except.ok.inj (driver.instructionsParsed.symm.trans rowsParsed)
  have decodedRowsOnRows : rows.toList.mapM NativeRelationJson.decodeInstruction =
      .ok program.instructions := by
    rw [← rowsEq]
    exact decodedRows
  have decodedItems : ((rows.toList.zipIdx).map Prod.fst).mapM
      NativeRelationJson.decodeInstruction = .ok program.instructions := by
    simpa only [List.zipIdx_map_fst] using decodedRowsOnRows
  have trace : NativeDefinitionTrace (rows.toList.zipIdx) program.instructions :=
    NativeDefinitionTrace.ofDecodedCheckedProfile decodedItems profile
  have driverTrace : validateInstructionLoop expected (rows.toList.zipIdx) {} = .ok final := by
    have actualTrace := driver.instructionTrace
    rw [driverRowsEq] at actualTrace
    exact actualTrace
  exact ⟨final, trace, driverTrace, driver.inputCount⟩

/-- An accepted native validation and strict decode expose exactly the checked
input descriptors in the expected schema. The raw rows are the same array
consumed by the producer, and the checked profile binds each decoded row to
its producer opcode. -/
theorem validate_decoded_input_descriptors_of_checkedScalarProfile
    {expected : Expected} {json : Lean.Json} {program : NativeRelation.Program}
    {rows : Array Lean.Json}
    (nativeAccepted : Backend.Native.validate expected json = .ok ())
    (decoded : NativeRelationJson.decode json = .ok program)
    (rowsParsed : Backend.Native.arrayField json "instructions" = .ok rows)
    (profile : checkedScalarOpcodeProfile (rows.toList.zipIdx) program.instructions = true)
    (schema : ∀ requirement ∈ expected.inputs, requirement.ty.isForeign = false) :
    program.instructions.flatMap strictInstructionInputDescriptors =
      expected.inputs.map expectedInputDescriptor := by
  obtain ⟨final, trace, accepted, finalCount⟩ :=
    validate_decoded_input_trace_of_checkedScalarProfile
      nativeAccepted decoded rowsParsed profile
  have descriptors := validateInstructionLoop_input_descriptors_of_trace
    schema empty_nativeDefinitions trace accepted
  rw [finalCount, (show ({} : State).inputCount = 0 from rfl)] at descriptors
  simpa only [List.take_length, List.take_zero, List.map_nil, List.nil_append]
    using descriptors.symm

theorem input_descriptor_identifiers_valid_of_trace
    {items : List (Lean.Json × Nat)} {instructions : List Instruction}
    (trace : NativeDefinitionTrace items instructions) :
    ∀ descriptor ∈ instructions.flatMap strictInstructionInputDescriptors,
      NativeRelationJson.validIdentifier descriptor.2 = true := by
  induction trace with
  | nil => simp
  | @cons raw index instruction tailItems tailInstructions head tail ih =>
    intro descriptor member
    simp only [List.flatMap_cons, List.mem_append] at member
    rcases member with headMember | tailMember
    · cases head.supported with
      | publicInput output opcode =>
        have descriptorEq : descriptor = (.public, output) := by
          simpa [strictInstructionInputDescriptors] using headMember
        subst descriptor
        exact strict_decoded_input_identifier_valid
          (by simpa [inputOpcode] using opcode) head.decoded
      | privateInput output opcode =>
        have descriptorEq : descriptor = (.private, output) := by
          simpa [strictInstructionInputDescriptors] using headMember
        subst descriptor
        exact strict_decoded_input_identifier_valid
          (by simpa [inputOpcode] using opcode) head.decoded
      | add _ _ _ _ => simp [strictInstructionInputDescriptors] at headMember
      | mul _ _ _ _ => simp [strictInstructionInputDescriptors] at headMember
      | neg _ _ _ => simp [strictInstructionInputDescriptors] at headMember
      | bits _ _ _ => simp [strictInstructionInputDescriptors] at headMember
      | boolean _ _ => simp [strictInstructionInputDescriptors] at headMember
      | lessThan _ _ _ _ _ => simp [strictInstructionInputDescriptors] at headMember
      | assertion _ _ => simp [strictInstructionInputDescriptors] at headMember
      | testEq _ _ _ _ => simp [strictInstructionInputDescriptors] at headMember
      | copy _ _ _ => simp [strictInstructionInputDescriptors] at headMember
      | impact _ _ _ => simp [strictInstructionInputDescriptors] at headMember
      | output _ _ => simp [strictInstructionInputDescriptors] at headMember
      | hash _ _ _ => simp [strictInstructionInputDescriptors] at headMember
      | not _ _ _ => simp [strictInstructionInputDescriptors] at headMember
      | select _ _ _ _ _ => simp [strictInstructionInputDescriptors] at headMember
      | constrainEq _ _ _ => simp [strictInstructionInputDescriptors] at headMember
    · exact ih descriptor tailMember

/-- Every input name in an accepted producer program is valid in the strict
relation representation. This connects the actual validator's ordered input
trace to the strict decoder's own identifier check. -/
theorem validate_decoded_input_identifiers_of_checkedScalarProfile
    {expected : Expected} {json : Lean.Json} {program : NativeRelation.Program}
    {rows : Array Lean.Json}
    (nativeAccepted : Backend.Native.validate expected json = .ok ())
    (decoded : NativeRelationJson.decode json = .ok program)
    (rowsParsed : Backend.Native.arrayField json "instructions" = .ok rows)
    (profile : checkedScalarOpcodeProfile (rows.toList.zipIdx) program.instructions = true)
    (schema : ∀ requirement ∈ expected.inputs, requirement.ty.isForeign = false) :
    ∀ requirement ∈ expected.inputs,
      NativeRelationJson.validIdentifier requirement.identifier = true := by
  have descriptors := validate_decoded_input_descriptors_of_checkedScalarProfile
    nativeAccepted decoded rowsParsed profile schema
  obtain ⟨_, trace, _, _⟩ := validate_decoded_input_trace_of_checkedScalarProfile
    nativeAccepted decoded rowsParsed profile
  have validDescriptors := input_descriptor_identifiers_valid_of_trace trace
  intro requirement member
  have descriptorMember : expectedInputDescriptor requirement ∈
      program.instructions.flatMap strictInstructionInputDescriptors := by
    rw [descriptors]
    exact List.mem_map.mpr ⟨requirement, member, rfl⟩
  change NativeRelationJson.validIdentifier
    (expectedInputDescriptor requirement).2 = true
  exact validDescriptors _ descriptorMember


end Noctium.Verification.NativeInputOrdinalTrace
