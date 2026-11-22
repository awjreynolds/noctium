import Noctium.Frontend

open scoped Noctium
open Noctium Noctium.Helpers

def ledgerWitnessProgram : Program := {
  ledger := [{name := "balance", kind := .cell .native}]
  witnesses := [{
    name := "derive"
    operation := "noctium.derive.v1"
    capability := "derive"
    parameters := [{name := "balance", type := .scalar .native}]
    result := .scalar .native}]
  declarations := [{
    id := ⟨0, 0⟩
    name := "advance"
    parameters := [⟨"enabled", .bool⟩, ⟨"expected", .native⟩]
    result := .scalar .native
    body := [
      .branch (.disclose {} (.ref "enabled")) [
        .readCell "balance" "before" .native,
        .bind "delta" (.scalar .native) (.witnessCall "derive-balance" "derive" [.ref "before"]),
        .writeCell "balance" .native (.disclose {} (.binary .add (.ref "before") (.ref "delta"))),
        .readCell "balance" "after" .native,
        .assert (.eq (.ref "after") (.ref "expected")),
        .stage "private" "ledger/last" (.scalar .native) (.ref "delta"),
        .return (some (.ref "after"))] [.return (some (.native 0))]]}]
  exports := [{name := "advance", target := ⟨0, 0⟩, inputs := [
    {name := "enabled", ty := .bool, visibility := .private},
    {name := "expected", ty := .native, visibility := .public}]}]
}

noctium_contract StructuredLedgerWitness where
  cell balance : Native
  entry advance from ledgerWitnessProgram entry "advance" end
end

#guard (Witness.compileLedger ledgerWitnessProgram "advance" StructuredLedgerWitness.state).isOk

private def undisclosedUpdate : Program := {
  ledgerWitnessProgram with declarations := [{
    id := ⟨0, 0⟩
    name := "advance"
    parameters := [⟨"enabled", .bool⟩, ⟨"expected", .native⟩]
    result := .scalar .native
    body := [
      .readCell "balance" "before" .native,
      .bind "delta" (.scalar .native) (.witnessCall "derive-balance" "derive" [.ref "before"]),
      .writeCell "balance" .native (.ref "delta"),
      .return (some (.ref "before"))]}]
}

#guard !(Witness.compileLedger undisclosedUpdate "advance" StructuredLedgerWitness.state).isOk
