import Noctium.Frontend
import Noctium.Verification.GenericStateCircuitParts
import Noctium.Verification.RangeDedupAcceptedArray
import Noctium.Verification.ScalarValidationProjection
import Noctium.Verification.ScalarValidationRawSeedMeaning

open scoped Noctium

noctium_circuit returnInput where
  private amount : Native
  public enabled : Bool
end

noctium_contract NativeReturns where
  cell balance : Native
  counter count
  entry readValues uses returnInput where
    read balance as currentBalance
    read count as currentCount
    return balanceValue : Native := currentBalance
    return countValue : UInt 64 := currentCount
    return enabledValue : Bool := enabled
  end
  entry advance uses returnInput arguments [amount] where
    read balance as beforeBalance
    write balance := disclose(add(beforeBalance, amount))
    increment count by 1
    read balance as afterBalance
    read count as afterCount
    return balanceValue : Native := afterBalance
    return countValue : UInt 64 := afterCount
    return enabledValue : Bool := enabled
  end
end

private def nativeReturnsEntry (name : String) : Noctium.Entrypoint :=
  match NativeReturns.entrypoints.find? (·.name == name) with
  | some found => found
  | none => {name := "missing", circuit := {name := "missing"}}

private def nativeReturnsPrivateLeak : Noctium.Entrypoint :=
  let ep := nativeReturnsEntry "readValues"
  let leaked : Noctium.Output :=
    {name := "leaked", ty := .native,
      value := (.ref "amount" : Noctium.Expr .native)}
  {ep with returns := [leaked]}

#guard match Noctium.Disclosure.entrypoint
    nativeReturnsPrivateLeak with
  | .error _ => Bool.true
  | .ok _ => Bool.false

private def callArgumentSchema (names : List String) (visibility : Noctium.Visibility := .private)
    (ty : Noctium.Ty := .native) : Except Noctium.Diagnostic Unit :=
  ({name := "arguments", circuit := {name := "arguments", inputs := [
      {name := "value", ty, visibility}]}, callInputs := names} : Noctium.Entrypoint).validate
    Noctium.Capabilities.crypto []

#guard (callArgumentSchema ["value"]).isOk
#guard !(callArgumentSchema ["missing"]).isOk
#guard !(callArgumentSchema ["value", "value"]).isOk
#guard !(callArgumentSchema ["value"] .public).isOk
#guard (callArgumentSchema ["value"] .private (.uint 7)).isOk

namespace NativeReturnsProof

open Noctium Noctium.Backend Noctium.Verification
open NativeRelation ScalarValidationMeaning ScalarValidationProjection
open ScalarValidationArithmeticLoop (NativeDefinitions)

private def advance := nativeReturnsEntry "advance"

#guard (Zkir.lowerEntrypoint NativeReturns.state advance).isOk

/-- The actual advance call seeds the ledger validator with its source amount
before any transcript instruction. The witness uses the same argument. -/
theorem acceptedAdvanceSeedMeaning
    {hash : Hash} {inputs assignment : Assignment} {program : Lean.Json}
    (lowered : Zkir.lowerEntrypoint NativeReturns.state advance = .ok program)
    (amountAgrees : assignment "%input_amount" = inputs "%input_amount") :
    ∃ expected instructions rawInputs seed final,
      Native.expectedEntrypoint NativeReturns.state (Passes.pruneEntrypoint advance) =
        .ok expected ∧
      expected.rawInputs = [{identifier := "%input_amount", visibility := .private, ty := .native}] ∧
      NativeValidationDriverFacts expected program instructions rawInputs seed final ∧
      StateMeaning hash inputs assignment seed ∧ NativeDefinitions seed := by
  obtain ⟨_, expected, _, schedule, validated, _⟩ :=
    Zkir.lowerEntrypoint_validation_and_instructions NativeReturns.state advance program lowered
  have ordered : expected.rawInputs =
      [{identifier := "%input_amount", visibility := .private, ty := .native}] :=
    GenericStateCircuitParts.expectedEntrypoint_rawInputs NativeReturns.state
      (Passes.pruneEntrypoint advance) expected schedule
  obtain ⟨instructions, rawInputs, seed, final, driver⟩ := validate_driver_result validated
  refine ⟨expected, instructions, rawInputs, seed, final, schedule, ordered, driver, ?_⟩
  apply ScalarValidationRawSeedMeaning.seedRawInputs_meaning_and_nativeDefinitions
    _ _ driver.seededRawInputs
  · intro requirement inHeader
    rw [ordered] at inHeader
    rw [List.mem_singleton.mp inHeader]
    rfl
  · intro requirement inHeader
    rw [ordered] at inHeader
    rw [List.mem_singleton.mp inHeader]
    exact amountAgrees

/-- Carry the actual seeded argument meaning through every accepted decoded
instruction in the scalar profile, for any assignment satisfying those rows. -/
theorem acceptedAdvanceTraceMeaning
    {hash : Hash} {inputs assignment : Assignment} {program : Lean.Json}
    {rows : Array Lean.Json} {decodedRows : List Instruction}
    (lowered : Zkir.lowerEntrypoint NativeReturns.state advance = .ok program)
    (amountAgrees : assignment "%input_amount" = inputs "%input_amount")
    (parsed : Native.arrayField program "instructions" = .ok rows)
    (decoded : rows.toList.mapM NativeRelationJson.decodeInstruction = .ok decodedRows)
    (profile : ScalarValidationOpcodeProfile.checkedScalarOpcodeProfile rows.toList.zipIdx
      decodedRows = Bool.true)
    (nativeInputs : ∀ expected,
      Native.expectedEntrypoint NativeReturns.state (Passes.pruneEntrypoint advance) = .ok expected →
      ∀ requirement ∈ expected.inputs, requirement.ty.isForeign = Bool.false)
    (agreement : ∀ expected,
      Native.expectedEntrypoint NativeReturns.state (Passes.pruneEntrypoint advance) = .ok expected →
      ∀ requirement ∈ expected.inputs, assignment requirement.identifier = inputs requirement.identifier)
    (holds : ∀ instruction ∈ decodedRows, Instruction.Holds hash assignment instruction) :
    ∃ expected rawInputs seed final,
      NativeValidationDriverFacts expected program rows rawInputs seed final ∧
      StateMeaning hash inputs assignment final ∧ NativeDefinitions final := by
  obtain ⟨expected, exactRows, rawInputs, seed, final, schedule, _, driver, initialMeaning,
    initialDefinitions⟩ := acceptedAdvanceSeedMeaning (hash := hash) lowered amountAgrees
  have sameRows := Except.ok.inj (driver.instructionsParsed.symm.trans parsed)
  subst exactRows
  have indexedDecoded : (rows.toList.zipIdx.map Prod.fst).mapM
      NativeRelationJson.decodeInstruction = .ok decodedRows := by
    simpa [List.zipIdx_map_fst] using decoded
  have steps := RangeDedupAcceptedArray.checkedScalarOpcodeProfile_acceptedMeaningSteps
    indexedDecoded profile holds
  obtain ⟨meaning, definitions, _⟩ :=
    RangeDedupAcceptedArray.accepted_loop_meaning_at_steps initialMeaning initialDefinitions
      (nativeInputs expected schedule) (agreement expected schedule) steps driver.instructionTrace
  exact ⟨expected, rawInputs, seed, final, driver, meaning, definitions⟩

private def advanceCallChecksScalarProfile : Except String _root_.Bool := do
  let artifact ← (Zkir.lowerEntrypoint NativeReturns.state advance).mapError (·.message)
  let call ← NativeRelationJson.decodeScalarCall artifact
  let rows ← Native.arrayField artifact "instructions"
  let decodedRows ← rows.toList.mapM NativeRelationJson.decodeInstruction
  return call.arguments == ["%input_amount"] && decodedRows == call.body.instructions &&
    ScalarValidationOpcodeProfile.checkedScalarOpcodeProfile rows.toList.zipIdx decodedRows

#guard advanceCallChecksScalarProfile.toOption == some Bool.true

end NativeReturnsProof
