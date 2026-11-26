import Noctium.Verification.ScalarValidatedProgram

namespace Noctium.Verification.ScalarValidation

open Lean Backend.Native NativeRelation
open ScalarNormalization (interpret)
open NativeInputOrdinalTrace NativeRelationInstructionProjection

export ScalarValidationMeaning (bind_ok lookup_member)

/-- The producer's input names are the only bindings shared by the source
assignment and the satisfying witness. Each assignment is free elsewhere. -/
def InputAgreement (expected : Expected) (inputs witness : Assignment) : Prop :=
  ∀ requirement ∈ expected.inputs, witness requirement.identifier = inputs requirement.identifier

abbrev inputSchema := expectedInputDescriptor

def schemaValues (witness : Assignment) (visibility : Visibility)
    (schema : List (Visibility × String)) : List Scalar :=
  schema.filterMap fun (found, name) => if found == visibility then some (witness name) else none

theorem decode_result {program : Json} {relation : Program}
    (decoded : NativeRelationJson.decode program = .ok relation) :
    ∃ instructions : Array Json,
      arrayField program "instructions" = .ok instructions ∧
      instructions.toList.mapM NativeRelationJson.decodeInstruction = .ok relation.instructions :=
  decode_instructionProjection decoded

/-- An arbitrary satisfying witness for the accepted strict relation agrees
with the source assignment on the ordered input streams, established assertions
and bounds, Impact groups and host-observed returns. -/
theorem validate_sound
    {hash : Hash} {inputs witness : Assignment} {expected : Expected}
    {program : Json} {relation : Program} {streams : InputStreams}
    {publicGroups : List (List Scalar)}
    (inputAgreement : InputAgreement expected inputs witness)
    (accepted : validate expected program = .ok ())
    (decoded : NativeRelationJson.decode program = .ok relation)
    (satisfies : CircuitSatisfies hash relation streams witness publicGroups) :
    ScalarValidatedProgram.Sound hash inputs witness expected relation streams publicGroups :=
  ScalarValidatedProgram.validate_sound accepted decoded inputAgreement satisfies

/-- The checked relation determines its ordered Impact fields and host
outputs for any satisfying instruction assignment. -/
theorem validate_observations
    {hash : Hash} {inputs witness : Assignment} {expected : Expected}
    {program : Json} {relation : Program}
    (inputAgreement : InputAgreement expected inputs witness)
    (accepted : validate expected program = .ok ())
    (decoded : NativeRelationJson.decode program = .ok relation)
    (holds : ∀ instruction ∈ relation.instructions, instruction.Holds hash witness) :
    ((relation.groups witness).map (List.map some) = expected.groups.map (List.map (interpret hash inputs))) ∧
      (relation.returns witness).map some = expected.returns.map (interpret hash inputs) := by
  have satisfies : CircuitSatisfies hash relation
      ⟨relation.inputValues .public witness, relation.inputValues .private witness⟩
      witness (relation.groups witness) := ⟨holds, rfl, rfl, rfl⟩
  have sound := validate_sound inputAgreement accepted decoded satisfies
  exact ⟨sound.impact, sound.returns⟩

theorem validate_observed_returns
    {hash : Hash} {inputs witness : Assignment} {expected : Expected}
    {program : Json} {relation : Program} {streams : InputStreams}
    {publicGroups : List (List Scalar)} {returns : List Scalar}
    (inputAgreement : InputAgreement expected inputs witness)
    (accepted : validate expected program = .ok ())
    (decoded : NativeRelationJson.decode program = .ok relation)
    (satisfies : Satisfies hash relation streams witness publicGroups returns) :
    ScalarValidatedProgram.Sound hash inputs witness expected relation streams publicGroups ∧
      returns.map some = expected.returns.map (interpret hash inputs) := by
  have sound := validate_sound inputAgreement accepted decoded satisfies.circuit
  exact ⟨sound, (congrArg (List.map some) satisfies.outputs).symm.trans sound.returns⟩

end Noctium.Verification.ScalarValidation
