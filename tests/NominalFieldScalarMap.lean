import Noctium.Frontend

open scoped Noctium
open Noctium

namespace NominalFieldScalarMap

noctium_field_type Amount := Field
noctium_field_type Count := Field

noctium_circuit mapInputs where
  private key : Amount
  private value : Native
  public enabled : Bool
end

noctium_circuit wrongAliasInputs where
  private key : Count
end

noctium_circuit rawKeyInputs where
  private key : Native
end

noctium_circuit nominalValueInputs where
  private key : Amount
  private value : Amount
end

noctium_contract ScalarMap where
  map balances : Amount => Native

  entry lifecycle uses mapInputs where
    absent balances[disclose(key)]
    when enabled insert balances[disclose(key)] := disclose(value)
    member balances[disclose(key)] as present
    read balances[disclose(key)] as stored
    insertDefault balances[disclose(key)]
    read balances[disclose(key)] as defaulted
    when enabled remove balances[disclose(key)]
    remove balances[disclose(key)]
    member balances[disclose(key)] as presentAfterRemove
    absent balances[disclose(key)]
    return wasInserted : Bool := present
    return storedValue : Native := stored
    return defaultValue : Native := defaulted
    return remains : Bool := presentAfterRemove
  end

end

noctium_contract ConstructorScalarMap where
  map balances : Amount => Native

  constructor(seed : Amount, raw : Native) where
    insert balances[seed] := cast(Native, raw)
  end
end

private def scalarMapEntry : Entrypoint :=
  (ScalarMap.entrypoints.find? (·.name == "lifecycle")).getD
    {name := "missing", circuit := {name := "missing"}}

private def scalarMapContext : EvalContext := {
  modulus := Field.modulus
  poseidon2 := fun _ _ _ => .error "unused by nominal Field scalar Map fixture"
}

private def scalarMapInitialState : LedgerState := {maps := [("balances", [])]}

private def scalarMapRun (key value : Nat) (enabled : _root_.Bool) :=
  scalarMapEntry.run scalarMapContext [
    ("key", .native key), ("value", .native value), ("enabled", .bool enabled)]
      scalarMapInitialState

#guard (ScalarMap.validate Capabilities.source).isOk
#guard (scalarMapEntry.validate Capabilities.source ScalarMap.state).isOk
#guard (ConstructorScalarMap.validate Capabilities.source).isOk

#guard match ScalarMap.state with
  | [{kind := .map .native .native, ..}] => _root_.Bool.true
  | _ => _root_.Bool.false

#guard match scalarMapRun 17 42 _root_.Bool.true with
  | .ok (outputs, state) =>
      outputs.lookup "wasInserted" == some (.bool _root_.Bool.true) &&
      outputs.lookup "storedValue" == some (.native 42) &&
      outputs.lookup "defaultValue" == some (.native 0) &&
      outputs.lookup "remains" == some (.bool _root_.Bool.false) &&
      state.maps.lookup "balances" == some []
  | .error _ => _root_.Bool.false

/- error: nominal Field values require an explicit cast and must match the target type -/
#guard_msgs (substring := true) in
noctium_contract RejectWrongRootMapKey where
  map balances : Amount => Native

  entry lookup uses wrongAliasInputs where
    read balances[disclose(key)] as stored
    return result : Native := stored
  end
end

/- error: nominal Field values require an explicit cast and must match the target type -/
#guard_msgs (substring := true) in
noctium_contract RejectRawRootMapKey where
  map balances : Amount => Native

  entry lookup uses rawKeyInputs where
    read balances[disclose(key)] as stored
    return result : Native := stored
  end
end

/- error: nominal Field values require an explicit cast and must match the target type -/
#guard_msgs (substring := true) in
noctium_contract RejectNominalRootMapValueErasure where
  map balances : Amount => Native

  entry store uses nominalValueInputs where
    insert balances[disclose(key)] := disclose(value)
  end
end

/- error: nominal Field effects require a direct scalar Cell write -/
#guard_msgs (substring := true) in
noctium_contract RejectNominalRootMapGuard where
  map balances : Amount => Native

  entry lookup uses mapInputs where
    when eq(key, key) remove balances[disclose(key)]
  end
end

/- error: nominal Field values require an explicit cast and must match the target type -/
#guard_msgs (substring := true) in
noctium_contract RejectRawRootMapConstructorKey where
  map balances : Amount => Native

  constructor(seed : Native, value : Native) where
    insert balances[seed] := value
  end
end

end NominalFieldScalarMap
