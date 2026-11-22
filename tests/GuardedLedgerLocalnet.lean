import Noctium.Frontend

open scoped Noctium
open Noctium Noctium.Helpers

def guardedLedgerProgram : Program := {
  ledger := [{name := "balance", kind := .cell .native}, {name := "mark", kind := .cell .native}]
  witnesses := [{
    name := "derive"
    operation := "noctium.derive.v1"
    capability := "derive"
    parameters := [{name := "balance", type := .scalar .native}]
    result := .scalar .native}]
  declarations := [{
    id := ⟨0, 0⟩
    name := "advance"
    parameters := [⟨"outer", .bool⟩, ⟨"inner", .bool⟩, ⟨"bound", .native⟩, ⟨"expected", .native⟩]
    result := .scalar .native
    body := [
      .branch (.disclose {} (.ref "outer")) [
        .branch (.disclose {} (.ref "inner")) [
          .bind "checked" (.scalar (.uint 7)) (.cast (.uint 7) (.ref "bound")),
          .writeCell "mark" .native (.native 1),
          .readCell "balance" "before" .native,
          .bind "delta" (.scalar .native) (.witnessCall "derive-balance" "derive" [.ref "before"]),
          .writeCell "balance" .native (.disclose {} (.binary .add (.ref "before") (.ref "delta"))),
          .readCell "balance" "after" .native,
          .assert (.eq (.ref "after") (.ref "expected")),
          .stage "private" "ledger/last" (.scalar .native) (.ref "delta")]
        [.writeCell "mark" .native (.native 2)]]
      [.writeCell "mark" .native (.native 3)],
      .readCell "balance" "current" .native,
      .return (some (.ref "current"))]}]
  exports := [{name := "advance", target := ⟨0, 0⟩, inputs := [
    {name := "outer", ty := .bool, visibility := .private},
    {name := "inner", ty := .bool, visibility := .private},
    {name := "bound", ty := .native, visibility := .public},
    {name := "expected", ty := .native, visibility := .public}]}]
}

noctium_contract GuardedLedgerLocalnet where
  cell balance : Native
  cell mark : Native
  entry advance from guardedLedgerProgram entry "advance" end
end
