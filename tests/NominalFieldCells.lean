import Noctium.Frontend

open scoped Noctium

namespace NominalFieldCells

noctium_field_type Amount := Field
noctium_field_type Count := Field

noctium_circuit arguments where
  public enabled : Bool
  public next : Amount
  public raw : Native
  public other : Count
end

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

/-- error: structured helpers do not support nominal Field Cells -/
#guard_msgs (substring := true) in
noctium_contract RejectStructuredErasure where
  cell balance : Amount
  entry get from erasedCellReader entry "get" end
end

end NominalFieldCells
