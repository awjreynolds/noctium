import Noctium.Verification.GenericStateLedgerAllocation
import Noctium.Verification.ScalarCallHeaderProjection
import Noctium.Verification.ScalarCallInstructionProjection
import Noctium.Verification.NativeInputOrdinalTrace
import Noctium.Verification.ScalarValidationRawSeedMeaning

namespace Noctium.Verification.ScalarLedgerWitnessPreflight

open Lean Backend Backend.Native NativeRelation NativeRelationJson ScalarNormalization
open NativeInputOrdinalTrace ScalarValidationOpcodeProfile
open ScalarValidationArithmeticLoop

/-- The default raw call uses the actual instruction array of the pruned
entrypoint. Call arguments are supplied by the separate header. -/
def defaultEntrypointRows (entry : Entrypoint) (plan : Impact.Plan) : Array Json :=
  ((Zkir.lowerEntrypointBody (Passes.pruneEntrypoint entry) plan).run {}).2.instructions

/-- The producer's validated raw seed and instruction trace agree with the
decoded header and body. Both sources of scalar bindings carry valid names. -/
theorem validate_scalarCall_input_schedule {expected : Expected}
    {json : Json} {call : ScalarCall} {rows : Array Json}
    (accepted : Native.validate expected json = .ok ())
    (decoded : decodeScalarCall json = .ok call)
    (rowsParsed : Native.arrayField json "instructions" = .ok rows)
    (rowsDecoded : rows.toList.mapM decodeInstruction = .ok call.body.instructions)
    (profile : checkedScalarOpcodeProfile rows.toList.zipIdx call.body.instructions = true)
    (schema : ∀ requirement ∈ expected.rawInputs ++ expected.inputs,
      requirement.ty.isForeign = false) :
    call.arguments = expected.rawInputs.map (·.identifier) ∧
      call.body.instructions.flatMap strictInstructionInputDescriptors =
        expected.inputs.map expectedInputDescriptor ∧
      ∀ requirement ∈ expected.rawInputs ++ expected.inputs,
        validIdentifier requirement.identifier = true := by
  have header := ScalarCallHeaderProjection.validate_decodeScalarCall_header_names accepted decoded
  have rawNames := ScalarCallHeaderProjection.decodeScalarCall_argument_identifiers decoded
  obtain ⟨instructions, rawInputs, seed, final, driver⟩ :=
    ScalarValidationProjection.validate_driver_result accepted
  have sameRows : instructions = rows :=
    Except.ok.inj (driver.instructionsParsed.symm.trans rowsParsed)
  have driverTrace : validateInstructionLoop expected rows.toList.zipIdx seed = .ok final := by
    rw [← sameRows]
    exact driver.instructionTrace
  have indexedDecoded :
      (rows.toList.zipIdx.map Prod.fst).mapM decodeInstruction = .ok call.body.instructions := by
    simpa only [List.zipIdx_map_fst] using rowsDecoded
  have trace := NativeDefinitionTrace.ofDecodedCheckedProfile indexedDecoded profile
  have rawSchema : ∀ requirement ∈ expected.rawInputs, requirement.ty.isForeign = false :=
    fun requirement present => schema requirement (List.mem_append_left _ present)
  have inputSchema : ∀ requirement ∈ expected.inputs, requirement.ty.isForeign = false :=
    fun requirement present => schema requirement (List.mem_append_right _ present)
  obtain ⟨_, seedDefinitions⟩ :=
    ScalarValidationRawSeedMeaning.seedRawInputs_meaning_and_nativeDefinitions
      (hash := fun _ => zero) (inputs := fun _ => zero) (witness := fun _ => zero)
      rawSchema (fun _ _ => rfl) driver.seededRawInputs
  have tape := validateInstructionLoop_input_descriptors_of_trace
    inputSchema seedDefinitions trace driverTrace
  rw [driver.inputCount, seedRawInputs_inputCount driver.seededRawInputs] at tape
  have body : call.body.instructions.flatMap strictInstructionInputDescriptors =
      expected.inputs.map expectedInputDescriptor := by
    simpa only [List.take_length, List.take_zero, List.map_nil, List.nil_append] using tape.symm
  refine ⟨header, body, ?_⟩
  intro requirement member
  rcases List.mem_append.mp member with raw | emitted
  · apply rawNames
    rw [header]
    exact List.mem_map.mpr ⟨requirement, raw, rfl⟩
  · apply input_descriptor_identifiers_valid_of_trace trace
      (expectedInputDescriptor requirement)
    rw [body]
    exact List.mem_map.mpr ⟨requirement, emitted, rfl⟩

/-- Witness construction starts from the byte-exact default call relation.
The proof separates its raw input names from its transcript descriptors and
uses the native producer's output-slot budget for fresh names. -/
theorem lowerEntrypoint_witness_preflight (state : List StateDecl) (entry : Entrypoint)
    (plan : Impact.Plan) {json : Json} {call : ScalarCall}
    (lowered : Zkir.lowerEntrypoint state entry = .ok json)
    (decoded : decodeScalarCall json = .ok call)
    (planAccepted : Impact.lower state (Passes.pruneEntrypoint entry) = .ok plan)
    (profile : checkedScalarOpcodeProfile
      (defaultEntrypointRows entry plan).toList.zipIdx call.body.instructions = true)
    (schema : ∀ expected,
      Native.expectedEntrypoint state (Passes.pruneEntrypoint entry) = .ok expected →
        ∀ requirement ∈ expected.rawInputs ++ expected.inputs, requirement.ty.isForeign = false) :
    ∃ expected,
      Native.expectedEntrypoint state (Passes.pruneEntrypoint entry) = .ok expected ∧
      Native.validate expected json = .ok () ∧
      Native.arrayField json "instructions" = .ok (defaultEntrypointRows entry plan) ∧
      (defaultEntrypointRows entry plan).toList.mapM decodeInstruction =
        .ok call.body.instructions ∧
      call.arguments = expected.rawInputs.map (·.identifier) ∧
      call.body.instructions.flatMap strictInstructionInputDescriptors =
        expected.inputs.map expectedInputDescriptor ∧
      (∀ requirement ∈ expected.rawInputs ++ expected.inputs,
        validIdentifier requirement.identifier = true) ∧
      ((Zkir.lowerEntrypointBody (Passes.pruneEntrypoint entry) plan).run {}).2.next ≤
        Native.maxInstructions * Native.maxVectorLength ∧
      call.body.instructions.length ≤ Native.maxInstructions := by
  obtain ⟨actualPlan, expected, rows, actualAccepted, expectedAccepted, nativeAccepted,
    parsed, exactRows, decodedRows⟩ :=
    ScalarCallInstructionProjection.lowerEntrypoint_decodeScalarCall_instructionProjection
      lowered decoded
  have samePlan := Except.ok.inj (actualAccepted.symm.trans planAccepted)
  subst actualPlan
  subst rows
  obtain ⟨header, body, identifiers⟩ :=
    validate_scalarCall_input_schedule nativeAccepted decoded parsed decodedRows profile
      (schema expected expectedAccepted)
  obtain ⟨boundedPlan, boundedAccepted, budget⟩ :=
    GenericStateLedgerAllocation.lowerEntrypoint_budget state entry json lowered
  have sameBounded := Except.ok.inj (boundedAccepted.symm.trans planAccepted)
  subst boundedPlan
  have instructionBudget :=
    NativeRelationInstructionProjection.decodedRows_budget nativeAccepted parsed decodedRows
  exact ⟨expected, expectedAccepted, nativeAccepted, parsed, decodedRows, header, body,
    identifiers, budget, instructionBudget⟩

end Noctium.Verification.ScalarLedgerWitnessPreflight
