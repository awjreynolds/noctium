import Noctium.Frontend
import Noctium.Verification.GenericStateCircuitParts
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
      StateMeaning hash inputs assignment seed := by
  obtain ⟨_, expected, _, schedule, validated, _⟩ :=
    Zkir.lowerEntrypoint_validation_and_instructions NativeReturns.state advance program lowered
  have ordered : expected.rawInputs =
      [{identifier := "%input_amount", visibility := .private, ty := .native}] :=
    GenericStateCircuitParts.expectedEntrypoint_rawInputs NativeReturns.state
      (Passes.pruneEntrypoint advance) expected schedule
  obtain ⟨instructions, rawInputs, seed, final, driver⟩ := validate_driver_result validated
  refine ⟨expected, instructions, rawInputs, seed, final, schedule, ordered, driver, ?_⟩
  apply ScalarValidationRawSeedMeaning.seedRawInputs_meaning _ _ driver.seededRawInputs
  · intro requirement inHeader
    rw [ordered] at inHeader
    rw [List.mem_singleton.mp inHeader]
    rfl
  · intro requirement inHeader
    rw [ordered] at inHeader
    rw [List.mem_singleton.mp inHeader]
    exact amountAgrees

end NativeReturnsProof
