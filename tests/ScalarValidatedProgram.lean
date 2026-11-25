import Noctium.Compiler
import Noctium.Verification.NativeRelationJson
import Noctium.Verification.ScalarValidationOpcodeProfile
import Noctium.Verification.ScalarValidatedProgram

open Lean Noctium Noctium.Backend Noctium.Verification
open NativeRelation NativeRelationJson ScalarValidationOpcodeProfile

section
open scoped Noctium
noctium_circuit scalarValidatedProgramExample where
  public expected : Native
  private secret : Native
  assert eq(secret, expected)
  output result : Native := disclose(secret)
end
end

private def compiledArtifact : Json :=
  (Zkir.lowerCircuit scalarValidatedProgramExample).toOption.getD Json.null

private def emptyProgram : Program :=
  {instructions := [], outputArity := 0, communicationsCommitment := _root_.Bool.false}

private def decodedArtifact : Program :=
  (NativeRelationJson.decode compiledArtifact).toOption.getD emptyProgram

private def emittedRows : Array Json :=
  (Native.arrayField compiledArtifact "instructions").toOption.getD #[]

private theorem compiledArtifactEvidence :
    (Zkir.lowerCircuit scalarValidatedProgramExample).isOk = Bool.true ∧
    (NativeRelationJson.decode compiledArtifact).isOk = Bool.true ∧
    (Native.arrayField compiledArtifact "instructions").isOk = Bool.true ∧
    checkedScalarOpcodeProfile (emittedRows.toList.zipIdx) decodedArtifact.instructions = Bool.true := by
  native_decide

private theorem compiledArtifactAccepted :
    Zkir.lowerCircuit scalarValidatedProgramExample = .ok compiledArtifact := by
  have successful := compiledArtifactEvidence.1
  cases lowered : Zkir.lowerCircuit scalarValidatedProgramExample with
  | error message => simp [lowered, Except.isOk, Except.toBool] at successful
  | ok program => simp [compiledArtifact, lowered, Except.toOption]

private theorem compiledArtifactDecoded :
    NativeRelationJson.decode compiledArtifact = .ok decodedArtifact := by
  have successful := compiledArtifactEvidence.2.1
  cases decoded : NativeRelationJson.decode compiledArtifact with
  | error message => simp [decoded, Except.isOk, Except.toBool] at successful
  | ok program => simp [decodedArtifact, decoded, Except.toOption]

private theorem compiledArtifactRows :
    Native.arrayField compiledArtifact "instructions" = .ok emittedRows := by
  have successful := compiledArtifactEvidence.2.2.1
  cases rows : Native.arrayField compiledArtifact "instructions" with
  | error message => simp [rows, Except.isOk, Except.toBool] at successful
  | ok values => simp [emittedRows, rows, Except.toOption]

private theorem compiledArtifactHasScalarProfile :
    checkedScalarOpcodeProfile (emittedRows.toList.zipIdx) decodedArtifact.instructions = Bool.true :=
  compiledArtifactEvidence.2.2.2

/-- Soundness of the validator on the actual relation emitted for this
source circuit, for every satisfying witness. -/
theorem compiledScalarCircuit_is_sound
    {hash : Hash} {streams : InputStreams} {assignment : Assignment}
    {groups : List (List Scalar)}
    (satisfies : CircuitSatisfies hash decodedArtifact streams assignment groups) :
    ∃ expected,
      Native.expectedCircuit (Passes.pruneCircuit scalarValidatedProgramExample) =
        .ok expected ∧
      Noctium.Verification.ScalarValidatedProgram.Sound
        hash assignment expected decodedArtifact streams groups := by
  obtain ⟨expected, expectedAccepted, producerAccepted⟩ :=
    Zkir.lowerCircuit_validated scalarValidatedProgramExample compiledArtifact
      compiledArtifactAccepted
  have sourceParts := ScalarNormalization.expectedCircuit_parts
    (Passes.pruneCircuit scalarValidatedProgramExample) expected expectedAccepted
  obtain ⟨_, _, _, _, _, _, _, _, inputsMatchSource, _⟩ := sourceParts
  have inputSchema : ∀ requirement ∈ expected.inputs,
      requirement.ty.isForeign = Bool.false := by
    intro requirement present
    rw [inputsMatchSource] at present
    simp [scalarValidatedProgramExample, Passes.pruneCircuit,
      Noctium.Backend.Native.Input.requirements] at present
    rcases present with rfl | rfl <;> rfl
  have inputGuards : ∀ requirement ∈ expected.inputs, requirement.activityGuard = none := by
    intro requirement present
    rw [inputsMatchSource] at present
    simp [scalarValidatedProgramExample, Passes.pruneCircuit,
      Noctium.Backend.Native.Input.requirements] at present
    rcases present with rfl | rfl <;> rfl
  refine ⟨expected, expectedAccepted, ?_⟩
  exact Noctium.Verification.ScalarValidatedProgram.validate_sound
    producerAccepted compiledArtifactDecoded compiledArtifactRows
    compiledArtifactHasScalarProfile inputSchema inputGuards satisfies
