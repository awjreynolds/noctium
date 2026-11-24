import Noctium.Backend.Zkir
import Noctium.Verification.NativeRelationJson

namespace Noctium.Verification.NativeRelationInstructionProjection

open Lean Backend NativeRelation

private theorem bind_ok {α β : Type} {value : Except String α} {next : α → Except String β}
    {result : β} : (value >>= next) = .ok result ↔
      ∃ found, value = .ok found ∧ next found = .ok result := by
  cases value <;> simp [Bind.bind, Except.bind]

private theorem ensure_ok {condition : Bool} {message : String} :
    Native.ensure condition message = .ok () ↔ condition = true := by
  cases condition <;> simp [Native.ensure] <;> rfl

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

private theorem validated_instructionArray_budget {expected : Native.Expected} {json : Json}
    (accepted : Native.validate expected json = .ok ()) :
    ∃ instructions : Array Json,
      Native.arrayField json "instructions" = .ok instructions ∧
      instructions.size ≤ Native.maxInstructions := by
  unfold Native.validate at accepted
  simp only [bind_ok] at accepted
  rcases accepted with ⟨guardValue, guardParsed, programFields, programFieldsParsed,
    versionJson, versionParsed, versionFields, versionFieldsParsed,
    major, majorParsed, minor, minorParsed, versionCheck, versionCheckParsed,
    instructions, parsedInstructions, resources, resourceParsed,
    rawInputs, rawInputsParsed, rawInputCount, rawInputCountParsed,
    inputNames, inputNamesParsed, seedState, seedStateParsed,
    returns, returnsParsed, returnCount, returnCountParsed,
    outputTypes, outputTypesParsed,
    commitmentJson, commitmentParsed, commitment, commitmentParsedBool,
    commitmentCheck, commitmentCheckParsed, finalOutput, finalOutputParsed,
    finalState, instructionTrace,
    inputCount, inputCountParsed, groupCount, groupCountParsed,
    assertionCount, assertionCountParsed,
    inputChecks, inputChecksParsed, coordinateChecks, coordinateChecksParsed,
    boundChecks, boundChecksParsed, _⟩
  have resourcesBool := ensure_ok.mp resourceParsed
  have resources1 := (Bool.and_eq_true_iff.mp resourcesBool).1
  have resources2 := (Bool.and_eq_true_iff.mp resources1).1
  have resources3 := (Bool.and_eq_true_iff.mp resources2).1
  have instructionCapBool := (Bool.and_eq_true_iff.mp resources3).1
  have instructionCap := of_decide_eq_true instructionCapBool
  refine ⟨instructions, parsedInstructions, ?_⟩
  simpa using instructionCap

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
  obtain ⟨acceptedInstructions, acceptedArray, instructionCount⟩ :=
    validated_instructionArray_budget producerAccepted
  have sameInstructions : acceptedInstructions = instructions :=
    Except.ok.inj (acceptedArray.symm.trans parsed)
  have rawCount : instructions.toList.length ≤ Native.maxInstructions := by
    rw [← sameInstructions]
    simpa using instructionCount
  have decodedCount := mapM_length decodedInstructions
  refine ⟨plan, expected, instructions, impactAccepted, expectedAccepted, producerAccepted,
    parsed, exactBodyInstructions, decodedInstructions, ?_⟩
  rw [decodedCount]
  exact rawCount

end Noctium.Verification.NativeRelationInstructionProjection
