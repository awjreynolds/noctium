import Noctium.Verification.GenericStateCircuitParts
import Noctium.Verification.ScalarAdmission
import Noctium.Verification.ScalarLedgerSourceIdentifiers

namespace Noctium.Verification.GenericStateLedgerIdentifiers
open Backend NativeRelationJson

/-- Strict native decoding admits actual scalar source inputs and plain
post-public scalar reads, and confirms that the accepted call has no raw
header inputs. -/
theorem accepted_input_identifiers (state : List StateDecl)
    (entry : Entrypoint) (plan : Impact.Plan)
    (expected : Native.Expected) (json : Lean.Json)
    (relation : NativeRelation.Program)
    (planAccepted : Impact.lower state entry = .ok plan)
    (expectedAccepted : Native.expectedEntrypoint state entry = .ok expected)
    (validated : Native.validate expected json = .ok ())
    (decoded : NativeRelationJson.decode json = .ok relation) :
    expected.rawInputs = [] ∧
    (∀ input ∈ entry.circuit.inputs, ScalarNormalization.ScalarType input.ty →
      validIdentifier ("%input_" ++ input.name) = true) ∧
    (∀ read ∈ plan.reads.drop
      (Impact.publicInputReadCount entry.circuit.inputs),
      read.components = [] → read.guard = none → ScalarNormalization.ScalarType read.ty →
        validIdentifier ("%input_" ++ read.name) = true) := by
  have admitted := ScalarAdmission.input_identifiers validated decoded
  obtain ⟨_, headerEmpty, _, _⟩ :=
    NativeRelationInstructionProjection.decode_headerAndInstructions decoded
  have rawEmpty := ScalarValidationProjection.validate_driver_result_empty_header
    validated headerEmpty
  have identifiers : ∀ requirement ∈ expected.rawInputs ++ expected.inputs,
      validIdentifier requirement.identifier = true := by
    intro requirement member
    rw [rawEmpty.1] at member
    exact admitted requirement member
  have sourceAndRead := ScalarLedgerSourceIdentifiers.accepted_source_identifiers
    state entry plan expected planAccepted expectedAccepted identifiers
  exact ⟨rawEmpty.1, sourceAndRead⟩

end Noctium.Verification.GenericStateLedgerIdentifiers
