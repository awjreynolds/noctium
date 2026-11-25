import Noctium.Verification.ScalarLedgerWitnessPreflight
import Noctium.Verification.ScalarLowering
import Noctium.Verification.ScalarValidatedProgram

namespace Noctium.Verification.ScalarLedgerWitnessProjection

open Lean Backend NativeRelation NativeRelationJson ScalarLowering
open NativeInputOrdinalTrace ScalarLedgerWitnessPreflight

/-- A meaning proof for the exact emitted body supplies instruction
satisfaction. The accepted descriptor order binds both transcript streams
to the seed, and the raw arguments use their separate header order. -/
theorem call_satisfies_seeded_inputs (entry : Entrypoint) (plan : Impact.Plan)
    (hash : Hash) (inputs witness : NativeRelation.Assignment)
    (expected : Native.Expected) (call : ScalarCall)
    (rows : (defaultEntrypointRows entry plan).toList.mapM decodeInstruction =
      .ok call.body.instructions)
    (header : call.arguments = expected.rawInputs.map (·.identifier))
    (descriptors : call.body.instructions.flatMap strictInstructionInputDescriptors =
      expected.inputs.map expectedInputDescriptor)
    (inputAgreement : ∀ requirement ∈ expected.rawInputs ++ expected.inputs,
      witness requirement.identifier = inputs requirement.identifier)
    (meaning : LowerStateMeaning hash witness
      ((Zkir.lowerEntrypointBody (Passes.pruneEntrypoint entry) plan).run {}).2) :
    CircuitSatisfies hash call.body
        ⟨ScalarValidatedProgram.inputValues expected .public inputs,
          ScalarValidatedProgram.inputValues expected .private inputs⟩
        witness (call.body.groups witness) ∧
      call.arguments.map witness = expected.rawInputs.map (fun input => inputs input.identifier) := by
  have ordered (visibility : Visibility) :
      call.body.inputValues visibility witness =
        ScalarValidatedProgram.inputValues expected visibility inputs := by
    rw [ScalarValidatedProgram.inputValues_of_descriptors descriptors]
    unfold ScalarValidatedProgram.inputValues
    have same (requirements : List Native.InputRequirement)
        (agreement : ∀ requirement ∈ requirements,
          witness requirement.identifier = inputs requirement.identifier) :
        (requirements.filterMap fun requirement => if requirement.visibility == visibility then
          some (witness requirement.identifier) else none) =
        (requirements.filterMap fun requirement => if requirement.visibility == visibility then
          some (inputs requirement.identifier) else none) := by
      induction requirements with
      | nil => rfl
      | cons first rest ih =>
        simp only [List.filterMap_cons, agreement first (by simp)]
        rw [ih (fun item member => agreement item (List.mem_cons_of_mem _ member))]
    exact same _ (fun requirement member =>
      inputAgreement requirement (List.mem_append_right _ member))
  refine ⟨⟨meaning.holds _ rows, ordered _, ordered _, rfl⟩, ?_⟩
  rw [header, List.map_map]
  apply List.map_congr_left
  intro requirement member
  exact inputAgreement requirement (List.mem_append_left _ member)

end Noctium.Verification.ScalarLedgerWitnessProjection
