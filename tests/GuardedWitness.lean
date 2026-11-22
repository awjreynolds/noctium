import Noctium.Frontend

open Noctium Noctium.Helpers

def guardedWitnessProgram : Program := {
  composites := {structures := [{id := "GuardedWitness.Empty", fields := []}]}
  witnesses := [
    {name := "flag", operation := "noctium.flag.v1", capability := "flag", result := .scalar .bool},
    {name := "yesAmount", operation := "noctium.yes.v1", capability := "yes", result := .scalar .native},
    {name := "noAmount", operation := "noctium.no.v1", capability := "no", result := .scalar .native},
    {name := "unit", operation := "noctium.unit.v1", capability := "unit", result := .unit},
    {name := "empty", operation := "noctium.empty.v1", capability := "empty",
      result := .composite (.structure "GuardedWitness.Empty")},
    {name := "tail", operation := "noctium.tail.v1", capability := "tail",
      parameters := [{name := "expected", type := .scalar .native}], result := .scalar .native}]
  declarations := [{
    id := ⟨0, 0⟩
    name := "main"
    parameters := [⟨"expected", .native⟩]
    result := .scalar .native
    body := [
      .bind "choice" (.scalar .bool) (.witnessCall "choice" "flag" []),
      .branch (.disclose {} (.ref "choice")) [
        .bind "amount" (.scalar .native) (.witnessCall "yes-amount" "yesAmount" []),
        .assert (.eq (.ref "amount") (.ref "expected")),
        .evaluate (.witnessCall "yes-unit" "unit" []),
        .stage "private" "guarded/last" (.scalar .native) (.ref "amount")] [
        .evaluate (.witnessCall "no-empty" "empty" []),
        .bind "amount" (.scalar .native) (.witnessCall "no-amount" "noAmount" []),
        .assert (.eq (.ref "amount") (.ref "expected")),
        .stage "private" "guarded/last" (.scalar .native) (.ref "amount")],
      .bind "after" (.scalar .native) (.witnessCall "after" "tail" [.ref "expected"]),
      .assert (.eq (.ref "after") (.ref "expected")),
      .return (some (.ref "expected"))]}]
  exports := [{name := "claim", target := ⟨0, 0⟩, inputs := [
    {name := "expected", ty := .native, visibility := .public}]}]
}

open scoped Noctium

noctium_witness_circuit guardedWitnessValues from guardedWitnessProgram entry "claim"

noctium_contract GuardedWitness where
  cell total : Native
  entry claim uses guardedWitnessValues where
    write total := result
    return observed : Native := result
  end
end

#guard (Witness.compile guardedWitnessProgram "claim").isOk
#guard !(Helpers.compile (Witness.eraseProgram guardedWitnessProgram) "claim").isOk

private def noReleaseProgram : Program := {
  guardedWitnessProgram with declarations := guardedWitnessProgram.declarations.map fun declaration =>
    {declaration with body := [
      .bind "choice" (.scalar .bool) (.witnessCall "choice" "flag" []),
      .branch (.ref "choice") [.return (some (.native 1))] [.return (some (.native 2))]]}
}

#guard !(Witness.compile noReleaseProgram "claim").isOk
