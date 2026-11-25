import Noctium.Backend.Zkir
import Noctium.Verification.NativeRelationJson
import Noctium.Verification.ScalarValidationProjection

namespace Noctium.Verification.NativeRelationInstructionProjection

open Lean Backend NativeRelation

private theorem bind_ok {α β : Type} {value : Except String α} {next : α → Except String β}
    {result : β} : (value >>= next) = .ok result ↔
      ∃ found, value = .ok found ∧ next found = .ok result := by
  cases value <;> simp [Bind.bind, Except.bind]

private theorem ensure_ok {condition : Bool} {message : String} :
    Native.ensure condition message = .ok () ↔ condition = true := by
  cases condition <;> simp [Native.ensure] <;> rfl

/-- The strict decoder checks the empty call header and reads the exact
instruction array used by producer validation. -/
theorem decode_headerAndInstructions {json : Json} {program : NativeRelation.Program}
    (decoded : NativeRelationJson.decode json = .ok program) :
    ∃ instructions : Array Json,
      Native.arrayField json "inputs" = .ok #[] ∧
      Native.arrayField json "instructions" = .ok instructions ∧
      instructions.toList.mapM NativeRelationJson.decodeInstruction = .ok program.instructions := by
  unfold NativeRelationJson.decode at decoded
  simp only [bind_ok] at decoded
  rcases decoded with ⟨_, _, _, _, _, _, _, _, _, _, _, _, header, headerParsed,
    emptyCheck, headerChecked, _, _, _, _, _, _, _, _,
    instructions, parsed, decodedInstructions, decodedParsed, result⟩
  cases result
  cases emptyCheck
  have empty : header = #[] := Array.isEmpty_iff.mp
    (ensure_ok.mp (show Native.ensure header.isEmpty
      "native root input declarations are unsupported" = .ok () from headerChecked))
  exact ⟨instructions, empty ▸ headerParsed, parsed, decodedParsed⟩

/-- Recover the checked raw instruction array and its exact decoded vector
from the successful relation decoder. -/
theorem decode_instructionProjection {json : Json} {program : NativeRelation.Program}
    (decoded : NativeRelationJson.decode json = .ok program) :
    ∃ instructions : Array Json,
      Native.arrayField json "instructions" = .ok instructions ∧
      instructions.toList.mapM NativeRelationJson.decodeInstruction = .ok program.instructions := by
  obtain ⟨instructions, _, parsed, rows⟩ := decode_headerAndInstructions decoded
  exact ⟨instructions, parsed, rows⟩

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

private theorem mapM_length {function : α → Except String β} {values : List α}
    {results : List β} (success : values.mapM function = .ok results) :
    results.length = values.length := by
  induction values generalizing results with
  | nil => cases success; rfl
  | cons value rest ih =>
    cases first : function value with
    | error error =>
      simp [List.mapM_cons, first, bind, Except.bind] at success
    | ok head =>
      cases tailResult : rest.mapM function with
      | error error =>
        simp [List.mapM_cons, first, tailResult, bind, Except.bind] at success
      | ok tail =>
        have successEq := success
        simp only [List.mapM_cons, first, tailResult, bind, Except.bind] at successEq
        change Except.ok (head :: tail) = Except.ok results at successEq
        have resultEq : head :: tail = results := by
          exact Except.ok.inj successEq
        cases resultEq
        have tailSuccess : rest.mapM function = .ok tail := tailResult
        simp only [List.length_cons, ih tailSuccess]

/-- The production resource limit bounds exactly the rows consumed by
the strict relation decoder, independently of allocated SSA names. -/
theorem decodedInstruction_budget {expected : Native.Expected}
    {json : Json} {program : NativeRelation.Program}
    (validated : Native.validate expected json = .ok ())
    (decoded : NativeRelationJson.decode json = .ok program) :
    program.instructions.length ≤ Native.maxInstructions := by
  obtain ⟨rows, rowsParsed, decoding⟩ := decode_instructionProjection decoded
  obtain ⟨accepted, _, _, _, driver⟩ :=
    ScalarValidationProjection.validate_driver_result validated
  have sameRows := Except.ok.inj (rowsParsed.symm.trans driver.instructionsParsed)
  rw [mapM_length decoding, sameRows]
  simpa using driver.instructionCount

/-- The accepted producer's instruction limit applies to the exact decoded
vector. SSA output-slot capacity stays with the separate output-capacity frame. -/
theorem lowerEntrypoint_decodedInstructionBudget (state : List StateDecl)
    (entry : Entrypoint) (json : Json) (program : NativeRelation.Program)
    (lowered : Zkir.lowerEntrypoint state entry = .ok json)
    (decoded : NativeRelationJson.decode json = .ok program) :
    ∃ plan expected instructions,
      Impact.lower state (Passes.pruneEntrypoint entry) = .ok plan ∧
      Native.expectedEntrypoint state (Passes.pruneEntrypoint entry) = .ok expected ∧
      Native.validate expected json = .ok () ∧
      Native.arrayField json "instructions" = .ok instructions ∧
      instructions = ((Zkir.lowerEntrypointBody (Passes.pruneEntrypoint entry) plan).run {}).2.instructions ∧
      instructions.toList.mapM NativeRelationJson.decodeInstruction = .ok program.instructions ∧
      program.instructions.length ≤ Native.maxInstructions := by
  obtain ⟨plan, expected, instructions, impactAccepted, expectedAccepted, producerAccepted,
    parsed, exactBodyInstructions, decodedInstructions⟩ :=
    lowerEntrypoint_instructionProjection state entry json program lowered decoded
  exact ⟨plan, expected, instructions, impactAccepted, expectedAccepted, producerAccepted,
    parsed, exactBodyInstructions, decodedInstructions,
    decodedInstruction_budget producerAccepted decoded⟩

end Noctium.Verification.NativeRelationInstructionProjection
