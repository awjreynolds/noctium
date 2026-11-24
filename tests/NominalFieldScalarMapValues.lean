import Noctium.Frontend

open scoped Noctium
open Noctium

namespace NominalFieldScalarMapValues

noctium_field_type Amount := Field
noctium_field_type Count := Field

noctium_circuit roundTripInput where
  private key : Amount
  private value : Count
end

noctium_circuit wrongKeyInput where
  private key : Count
  private value : Count
end

noctium_circuit rawKeyInput where
  private key : Native
  private value : Count
end

noctium_circuit wrongValueInput where
  private key : Amount
  private value : Amount
end

noctium_circuit rawValueInput where
  private key : Amount
  private value : Native
end

noctium_contract ScalarMap where
  map balances : Amount => Count

  entry roundTrip uses roundTripInput where
    insert balances[disclose(key)] := disclose(value)
    member balances[disclose(key)] as present
    read balances[disclose(key)] as stored
    return found : Bool := present
    return result : Count := stored
  end
end

noctium_contract ConstructorScalarMap where
  map balances : Amount => Count

  constructor(seed : Amount, value : Count) where
    insert balances[seed] := value
  end
end

private def mapEntry : Entrypoint :=
  (ScalarMap.entrypoints.find? (·.name == "roundTrip")).getD
    {name := "missing", circuit := {name := "missing"}}

private def context : EvalContext := {
  modulus := Field.modulus
  poseidon2 := fun _ _ _ => .error "unused by nominal Field scalar Map fixture"
}

private def initialState : LedgerState := {maps := [("balances", [])]}

#guard (ScalarMap.validate Capabilities.source).isOk
#guard (mapEntry.validate Capabilities.source ScalarMap.state).isOk
#guard (ConstructorScalarMap.validate Capabilities.source).isOk

#guard match ScalarMap.state with
  | [{kind := .map .native .native, ..}] => _root_.Bool.true
  | _ => _root_.Bool.false

#guard match mapEntry.run context [
    ("key", .native 17), ("value", .native 42)] initialState with
  | .ok (outputs, state) =>
      outputs.lookup "found" == some (.bool _root_.Bool.true) &&
      outputs.lookup "result" == some (.native 42) &&
      state.maps.lookup "balances" == some [(.native 17, .native 42)]
  | .error _ => _root_.Bool.false

/- error: nominal Field values require an explicit cast and must match the target type -/
#guard_msgs (substring := true) in
noctium_contract RejectWrongRootMapKey where
  map balances : Amount => Count

  entry roundTrip uses wrongKeyInput where
    insert balances[disclose(key)] := disclose(value)
  end
end

/- error: nominal Field values require an explicit cast and must match the target type -/
#guard_msgs (substring := true) in
noctium_contract RejectRawRootMapKey where
  map balances : Amount => Count

  entry roundTrip uses rawKeyInput where
    insert balances[disclose(key)] := disclose(value)
  end
end

/- error: nominal Field values require an explicit cast and must match the target type -/
#guard_msgs (substring := true) in
noctium_contract RejectWrongRootMapValue where
  map balances : Amount => Count

  entry roundTrip uses wrongValueInput where
    insert balances[disclose(key)] := disclose(value)
  end
end

/- error: nominal Field values require an explicit cast and must match the target type -/
#guard_msgs (substring := true) in
noctium_contract RejectRawRootMapValue where
  map balances : Amount => Count

  entry roundTrip uses rawValueInput where
    insert balances[disclose(key)] := disclose(value)
  end
end

/- error: nominal Field values require an explicit cast and must match the target type -/
#guard_msgs (substring := true) in
noctium_contract RejectReadErasure where
  map balances : Amount => Count

  entry lookup uses roundTripInput where
    read balances[disclose(key)] as stored
    return raw : Native := stored
  end
end

private def uncheckedStore : Helpers.Program := {
  ledger := [{name := "balances", kind := .map .native .native}]
  declarations := [{
    id := ⟨0, 0⟩
    name := "store"
    body := [.writeMap "balances" .native .native (.native 17) (.native 42), .return none]
  }]
  exports := [{name := "store", target := ⟨0, 0⟩}]
}

/- error: structured helpers do not support nominal Field Map values -/
#guard_msgs (substring := true) in
noctium_contract RejectHelperValueErasure where
  map balances : Native => Count
  entry store from uncheckedStore entry "store" end
end

end NominalFieldScalarMapValues
