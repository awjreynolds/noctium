import Noctium.Verification.ScalarValidation
import Noctium.Verification.ScalarCircuit
import Noctium.Verification.ScalarInstructionEncoding

namespace Noctium.Verification.ScalarAdmission
open Lean Backend.Native NativeRelation

private theorem bind_ok (first : Except ε α) (next : α → Except ε β) (value : β) :
    Except.bind first next = .ok value ↔ ∃ intermediate, first = .ok intermediate ∧ next intermediate = .ok value := by
  cases first <;> simp [Except.bind]

private theorem bind_pure (value : α) (next : α → Except ε β) :
    Except.bind (.ok value) next = next value := rfl

/-- Actual validator admission fixes the full input role/name schedule. -/
theorem input_schema {expected : Expected} {json : Json} {program : Program}
    (accepted : validate expected json = .ok ())
    (decoded : NativeRelationJson.decode json = .ok program) :
    program.instructions.flatMap ScalarValidation.instructionInputs = expected.inputs.map ScalarValidation.inputSchema := by
  obtain ⟨instructions, state, parsed, finalOutput, trace, final⟩ := ScalarValidation.validate_result accepted
  obtain ⟨decodedInstructions, decodedParsed, decodedTrace⟩ := ScalarValidation.decode_result decoded
  rw [parsed] at decodedParsed
  cases decodedParsed
  have schema := ScalarValidation.validationLoop_inputs trace
    (by simpa only [ScalarValidation.zipIdx_values] using decodedTrace)
  rw [final.inputs] at schema
  simpa only [List.take_length, List.take_zero, List.map_nil, List.nil_append] using schema.symm

private theorem decoded_input_valid {raw : Json} {visibility : Visibility} {name : String}
    (decoded : NativeRelationJson.decodeInstruction raw = .ok (.input visibility name)) :
    NativeRelationJson.validIdentifier name = true := by
  have opcode := ScalarValidation.decoded_opcode decoded
  cases visibility with
  | «public» =>
    change NativeRelationJson.stringField raw "op" = .ok "public_input" at opcode
    simp only [NativeRelationJson.decodeInstruction, opcode, bind, bind_pure] at decoded
    simp only [bind_ok] at decoded
    rcases decoded with ⟨_, shape, _, guardParsed, _, guard, _, tyParsed, _, ty, output, outputParsed, _, valid, result⟩
    cases result
    exact ScalarValidation.ensure_ok.mp valid
  | «private» =>
    change NativeRelationJson.stringField raw "op" = .ok "private_input" at opcode
    simp only [NativeRelationJson.decodeInstruction, opcode, bind, bind_pure] at decoded
    simp only [bind_ok] at decoded
    rcases decoded with ⟨_, shape, _, guardParsed, _, guard, _, tyParsed, _, ty, output, outputParsed, _, valid, result⟩
    cases result
    exact ScalarValidation.ensure_ok.mp valid

private theorem mapM_member {function : α → Except String β} {values : List α} {results : List β}
    (success : values.mapM function = .ok results) (result : β) (member : result ∈ results) :
    ∃ value ∈ values, function value = .ok result := by
  induction values generalizing results with
  | nil => cases success; simp at member
  | cons value rest ih =>
    simp only [List.mapM_cons, bind, bind_ok] at success
    rcases success with ⟨first, firstResult, tail, tailResult, equal⟩
    cases equal
    rcases List.mem_cons.mp member with equal | member
    · subst first
      exact ⟨value, by simp, firstResult⟩
    · obtain ⟨found, foundMember, foundResult⟩ := ih tailResult member
      exact ⟨found, List.mem_cons_of_mem _ foundMember, foundResult⟩

/-- Native input identifier validity comes from actual entry checks, rather than
from source type validation, which imposes no native name byte limit. -/
theorem input_identifiers {expected : Expected} {json : Json} {program : Program}
    (accepted : validate expected json = .ok ())
    (decoded : NativeRelationJson.decode json = .ok program) :
    ∀ input ∈ expected.inputs, NativeRelationJson.validIdentifier input.identifier = true := by
  obtain ⟨instructions, parsed, decodedTrace⟩ := ScalarValidation.decode_result decoded
  have schema := input_schema accepted decoded
  intro input member
  have found : (input.visibility, input.identifier) ∈ program.instructions.flatMap ScalarValidation.instructionInputs := by
    rw [schema]
    exact List.mem_map.mpr ⟨input, member, rfl⟩
  obtain ⟨instruction, instructionMember, inputMember⟩ := List.mem_flatMap.mp found
  cases instruction <;> simp [ScalarValidation.instructionInputs] at inputMember
  next visibility name =>
    obtain ⟨rfl, rfl⟩ := inputMember
    obtain ⟨raw, rawMember, rawDecoded⟩ := mapM_member decodedTrace _ instructionMember
    exact decoded_input_valid rawDecoded

private theorem mapM_length {function : α → Except String β} {values : List α} {results : List β}
    (success : values.mapM function = .ok results) : results.length = values.length := by
  induction values generalizing results with
  | nil => cases success; rfl
  | cons value rest ih =>
    simp only [List.mapM_cons, bind, bind_ok] at success
    rcases success with ⟨first, firstResult, tail, tailResult, equal⟩
    cases equal
    simp only [List.length_cons, ih tailResult]

theorem instruction_bound {expected : Expected} {json : Json} {program : Program}
    (accepted : validate expected json = .ok ())
    (decoded : NativeRelationJson.decode json = .ok program) :
    program.instructions.length ≤ maxInstructions := by
  unfold validate at accepted
  simp only [ScalarValidation.bind_ok] at accepted
  rcases accepted with ⟨_, _, version, _, _, _, _, _, _, _, _, _, _, _, _, _,
    _, _, _, _, _, _, _, _, _, _, _, _, instructions, parsedInstructions,
    _, resources, _, finalOutput, state, trace, _, inputCount, _, groupCount,
    _, assertionCount, _, inputBounds, _, bounds, _⟩
  have resourceBound := ScalarValidation.ensure_ok.mp resources
  simp only [Bool.and_eq_true, decide_eq_true_eq] at resourceBound
  obtain ⟨decodedInstructions, decodedParsed, decodedTrace⟩ := ScalarValidation.decode_result decoded
  rw [parsedInstructions] at decodedParsed
  cases decodedParsed
  rw [mapM_length decodedTrace]
  exact resourceBound.1.1.1.1

/-- Source input name and resource facts are consequences of the actual
mandatory gate on the emitted program. They are not new source restrictions. -/
theorem lowerCircuit_admission (circuit : Circuit) (json : Json) (program : Program)
    (lowered : Backend.Zkir.lowerCircuit circuit = .ok json)
    (decoded : NativeRelationJson.decode json = .ok program) :
    program.instructions.length ≤ maxInstructions ∧
    program.instructions.flatMap ScalarValidation.instructionInputs =
      circuit.inputs.map (fun input => (input.visibility, "%input_" ++ input.name)) ∧
    (∀ input ∈ circuit.inputs, NativeRelationJson.validIdentifier ("%input_" ++ input.name) = true) := by
  obtain ⟨expected, source, accepted⟩ := Backend.Zkir.lowerCircuit_validated circuit json lowered
  obtain ⟨_, _, _, _, _, _, _, _, _, inputShape, _, _⟩ :=
    ScalarNormalization.expectedCircuit_parts (Passes.pruneCircuit circuit) expected source
  refine ⟨instruction_bound accepted decoded, ?_, ?_⟩
  · have schema := input_schema accepted decoded
    simpa only [inputShape, List.map_map, Function.comp_def, ScalarValidation.inputSchema, Passes.pruneCircuit] using schema
  · intro input member
    apply input_identifiers accepted decoded
      {identifier := "%input_" ++ input.name, visibility := input.visibility, ty := input.ty}
    rw [inputShape]
    exact List.mem_map.mpr ⟨input, member, rfl⟩

theorem admitted_fresh_identifier (circuit : Circuit) (json : Json) (program : Program)
    (lowered : Backend.Zkir.lowerCircuit circuit = .ok json)
    (decoded : NativeRelationJson.decode json = .ok program) (index : Nat)
    (bound : index ≤ program.instructions.length) :
    NativeRelationJson.validIdentifier s!"%v{index}" = true := by
  apply ScalarInstructionEncoding.fresh_identifier index
  exact Nat.le_trans
    (Nat.le_trans bound (lowerCircuit_admission circuit json program lowered decoded).1)
    (by decide)

theorem lowerBody_instruction_count (circuit : Circuit) (json : Json) (program : Program)
    (lowered : Backend.Zkir.lowerCircuit circuit = .ok json)
    (decoded : NativeRelationJson.decode json = .ok program) :
    ((Backend.Zkir.lowerBody (Passes.pruneCircuit circuit)).run {}).2.instructions.size = program.instructions.length := by
  obtain ⟨instructions, parsed, trace⟩ := ScalarValidation.decode_result decoded
  rw [Backend.Zkir.lowerCircuit_instructions circuit json lowered] at parsed
  cases parsed
  simpa using (mapM_length trace).symm

end Noctium.Verification.ScalarAdmission
