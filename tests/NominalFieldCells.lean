import Noctium.Frontend

open scoped Noctium
open Noctium.Helpers

namespace NominalFieldCells

noctium_field_type Amount := Field
noctium_field_type Count := Field

noctium_circuit arguments where
  public enabled : Bool
  public next : Amount
  public raw : Native
  public other : Count
end

private def nominalFieldCellHelper : Program := {
  ledger := [
    {name := "balance", kind := .cell .native},
    {name := "cap", kind := .cell .native, «sealed» := Bool.true}]
  declarations := [{
    id := ⟨0, 0⟩
    name := "update"
    parameters := [
      ⟨"enabled", .bool⟩, ⟨"next", .native⟩, ⟨"raw", .native⟩, ⟨"other", .native⟩]
    nominalFieldParameters := [
      ("next", "NominalFieldCells.Amount"), ("other", "NominalFieldCells.Count")]
    result := .scalar .native
    nominalFieldResult := some "NominalFieldCells.Amount"
    body := [
      .readCell "balance" "before" .native,
      .branch (.ref "enabled") [
        .bind "updated" (.scalar .native)
          (.binary .add (.ref "next")
            (.castNominalField "NominalFieldCells.Amount" (.ref "raw"))),
        .writeCell "balance" .native (.disclose {} (.ref "updated")),
        .readCell "balance" "after" .native,
        .return (some (.ref "after"))
      ] [
        .return (some (.ref "before"))
      ]]
  }]
  exports := [{name := "update", target := ⟨0, 0⟩, inputs := [
    {name := "enabled", ty := .bool, visibility := .public},
    {name := "next", ty := .native, visibility := .public},
    {name := "raw", ty := .native, visibility := .public},
    {name := "other", ty := .native, visibility := .public}]}]
}

private def mismatchedNominalFieldCellHelper : Program := {
  ledger := [{name := "balance", kind := .cell .native}]
  declarations := [{
    id := ⟨0, 0⟩
    name := "writeOtherField"
    parameters := [⟨"other", .native⟩]
    nominalFieldParameters := [("other", "NominalFieldCells.Count")]
    result := .unit
    body := [.writeCell "balance" .native (.ref "other"), .return none]
  }]
  exports := [{name := "writeOtherField", target := ⟨0, 0⟩, inputs := [
    {name := "other", ty := .native, visibility := .public}]}]
}

noctium_contract Account where
  cell balance : Amount
  sealed cell cap : Amount
  constructor(seed : Amount, rawCap : Native) where
    initialize balance := seed
    initialize cap := cast(Amount, rawCap)
  end

  entry update uses arguments where
    when enabled write balance := add(next, cast(Amount, raw))
    read balance as stored
    read cap as capValue
    return balanceAfter : Amount := stored
    return capAfter : Native := cast(Native, capValue)
  end

  entry updateWithHelper from nominalFieldCellHelper entry "update" end
end

/-- error: nominal Field values require an explicit cast and must match the target type -/
#guard_msgs (substring := true) in
noctium_contract RejectConstructorAlias where
  cell balance : Amount
  constructor(seed : Count) where
    initialize balance := seed
  end
end

/-- error: nominal Field values require an explicit cast and must match the target type -/
#guard_msgs (substring := true) in
noctium_contract RejectRawWrite where
  cell balance : Amount
  entry update uses arguments where
    when enabled write balance := raw
  end
end

/-- error: nominal Field values require an explicit cast and must match the target type -/
#guard_msgs (substring := true) in
noctium_contract RejectOtherAlias where
  cell balance : Amount
  entry update uses arguments where
    write balance := other
  end
end

/-- error: nominal Field values require an explicit cast and must match the target type -/
#guard_msgs (substring := true) in
noctium_contract RejectReadErasure where
  cell balance : Amount
  entry readBalance uses arguments where
    read balance as stored
    return rawBalance : Native := stored
  end
end

private def erasedCellReader : Noctium.Helpers.Program := {
  ledger := [{name := "balance", kind := .cell .native}]
  declarations := [{
    id := ⟨0, 0⟩, name := "get", result := .scalar .native,
    body := [.readCell "balance" "value" .native, .return (some (.ref "value"))]}]
  exports := [{name := "get", target := ⟨0, 0⟩}]}

/-- error: :1:1: nominal Field values require an explicit cast and must match the target type -/
#guard_msgs (substring := true) in
noctium_contract RejectStructuredErasure where
  cell balance : Amount
  entry get from erasedCellReader entry "get" end
end

/-- error: :1:1: nominal Field values require an explicit cast and must match the target type -/
#guard_msgs (substring := true) in
noctium_contract RejectStructuredFieldWrite where
  cell balance : Amount
  entry writeOtherField from mismatchedNominalFieldCellHelper entry "writeOtherField" end
end

end NominalFieldCells
