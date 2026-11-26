import Noctium.Verification.NativeInputOrdinalTrace
import Noctium.Verification.ScalarAllocationOutputFrame

namespace Noctium.Verification.ScalarAdmission

open Lean Backend Backend.Native NativeRelation
open NativeInputOrdinalTrace

/-- The producer and strict decoder agree on the ordered scalar input roles and names. -/
theorem input_schema {expected : Expected} {json : Json} {program : Program}
    (accepted : validate expected json = .ok ())
    (decoded : NativeRelationJson.decode json = .ok program) :
    program.instructions.flatMap strictInstructionInputDescriptors =
      expected.inputs.map expectedInputDescriptor :=
  validate_decoded_input_descriptors accepted decoded

/-- Successful strict decoding checks the native identifier limits for admitted inputs. -/
theorem input_identifiers {expected : Expected} {json : Json} {program : Program}
    (accepted : validate expected json = .ok ())
    (decoded : NativeRelationJson.decode json = .ok program) :
    ∀ input ∈ expected.inputs, NativeRelationJson.validIdentifier input.identifier = true :=
  validate_decoded_input_identifiers accepted decoded

theorem instruction_bound {expected : Expected} {json : Json} {program : Program}
    (accepted : validate expected json = .ok ())
    (decoded : NativeRelationJson.decode json = .ok program) :
    program.instructions.length ≤ maxInstructions :=
  NativeRelationInstructionProjection.decodedInstruction_budget accepted decoded

/-- Source input identifiers and row counts follow from the producer and strict decoder. -/
theorem lowerCircuit_admission (circuit : Circuit) (json : Json) (program : Program)
    (lowered : Zkir.lowerCircuit circuit = .ok json)
    (decoded : NativeRelationJson.decode json = .ok program) :
    program.instructions.length ≤ maxInstructions ∧
    program.instructions.flatMap strictInstructionInputDescriptors =
      (circuit.inputs.flatMap Input.requirements).map expectedInputDescriptor ∧
    (∀ input ∈ circuit.inputs.flatMap Input.requirements,
      NativeRelationJson.validIdentifier input.identifier = true) := by
  obtain ⟨expected, source, accepted⟩ := Zkir.lowerCircuit_validated circuit json lowered
  obtain ⟨_, _, _, _, _, _, _, _, inputShape, _⟩ :=
    ScalarNormalization.expectedCircuit_parts (Passes.pruneCircuit circuit) expected source
  rw [Passes.pruneCircuit] at inputShape
  rw [← inputShape]
  exact ⟨instruction_bound accepted decoded, input_schema accepted decoded,
    input_identifiers accepted decoded⟩

theorem lowerBody_instruction_count (circuit : Circuit) (json : Json) (program : Program)
    (lowered : Zkir.lowerCircuit circuit = .ok json)
    (decoded : NativeRelationJson.decode json = .ok program) :
    ((Zkir.lowerBody (Passes.pruneCircuit circuit)).run {}).2.instructions.size =
      program.instructions.length := by
  obtain ⟨rows, parsed, trace⟩ := NativeRelationInstructionProjection.decode_instructionProjection decoded
  rw [Zkir.lowerCircuit_instructions circuit json lowered] at parsed
  cases parsed
  exact NativeRelationInstructionProjection.decodedRows_count trace

/-- Generated names use the capacity of the accepted producer's output slots. -/
theorem lowerBody_budget (circuit : Circuit) (json : Json)
    (lowered : Zkir.lowerCircuit circuit = .ok json) :
    ((Zkir.lowerBody (Passes.pruneCircuit circuit)).run {}).2.next ≤
      maxInstructions * maxVectorLength :=
  ScalarAllocationOutputFrame.lowerCircuit_names_fit_producerCapacity circuit lowered

theorem admitted_fresh_identifier (circuit : Circuit) (json : Json)
    (lowered : Zkir.lowerCircuit circuit = .ok json) (index : Nat)
    (bound : index < ((Zkir.lowerBody (Passes.pruneCircuit circuit)).run {}).2.next) :
    NativeRelationJson.validIdentifier s!"%v{index}" = true :=
  NativeRelationJson.generatedIdentifier_fits_output_capacity index
    (Nat.lt_of_lt_of_le bound (lowerBody_budget circuit json lowered))

end Noctium.Verification.ScalarAdmission
