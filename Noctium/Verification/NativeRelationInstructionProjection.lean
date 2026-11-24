import Noctium.Backend.Zkir
import Noctium.Verification.NativeRelationJson

namespace Noctium.Verification.NativeRelationInstructionProjection

open Lean Backend NativeRelation

private theorem bind_ok {α β : Type} {value : Except String α} {next : α → Except String β}
    {result : β} : (value >>= next) = .ok result ↔
      ∃ found, value = .ok found ∧ next found = .ok result := by
  cases value <;> simp [Bind.bind, Except.bind]

/-- Recover the checked raw instruction array and its exact decoded vector
from the successful relation decoder. -/
theorem decode_instructionProjection {json : Json} {program : NativeRelation.Program}
    (decoded : NativeRelationJson.decode json = .ok program) :
    ∃ instructions : Array Json,
      Native.arrayField json "instructions" = .ok instructions ∧
      instructions.toList.mapM NativeRelationJson.decodeInstruction = .ok program.instructions := by
  unfold NativeRelationJson.decode at decoded
  simp only [bind_ok] at decoded
  rcases decoded with ⟨_, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _,
    _, _, _, _, _, _, instructions, parsed, decodedInstructions, decodedParsed, result⟩
  cases result
  exact ⟨instructions, parsed, decodedParsed⟩

/-- Connect accepted entrypoint lowering, its validated Impact plan, and the
exact vector parsed by the strict native relation decoder. The raw JSON array
is identified with the body's emitted array before decoding. Instruction
array length and SSA output capacity stay as separate quantities. -/
theorem lowerEntrypoint_instructionProjection (state : List StateDecl)
    (entry : Entrypoint) (json : Json) (program : NativeRelation.Program)
    (lowered : Zkir.lowerEntrypoint state entry = .ok json)
    (decoded : NativeRelationJson.decode json = .ok program) :
    ∃ plan expected instructions,
      Impact.lower state (Passes.pruneEntrypoint entry) = .ok plan ∧
      Native.expectedEntrypoint state (Passes.pruneEntrypoint entry) = .ok expected ∧
      Native.validate expected json = .ok () ∧
      Native.arrayField json "instructions" = .ok instructions ∧
      instructions = ((Zkir.lowerEntrypointBody (Passes.pruneEntrypoint entry) plan).run {}).2.instructions ∧
      instructions.toList.mapM NativeRelationJson.decodeInstruction = .ok program.instructions := by
  obtain ⟨plan, expected, impactAccepted, expectedAccepted, producerAccepted, bodyInstructions⟩ :=
    Zkir.lowerEntrypoint_validation_and_instructions state entry json lowered
  obtain ⟨instructions, parsed, decodedInstructions⟩ := decode_instructionProjection decoded
  have exactBodyInstructions :
      instructions = ((Zkir.lowerEntrypointBody (Passes.pruneEntrypoint entry) plan).run {}).2.instructions :=
    Except.ok.inj (parsed.symm.trans bodyInstructions)
  exact ⟨plan, expected, instructions, impactAccepted, expectedAccepted, producerAccepted,
    parsed, exactBodyInstructions, decodedInstructions⟩

end Noctium.Verification.NativeRelationInstructionProjection
