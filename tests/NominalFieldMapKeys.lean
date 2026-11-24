import Noctium.Frontend

open scoped Noctium
open Noctium

namespace NominalFieldMapKeys

noctium_field_type Amount := Field
noctium_field_type Count := Field

noctium_circuit amountKeyWriteInput where
  private amount : Amount
  private value : Native
end

noctium_circuit amountKeyLookupInput where
  private amount : Amount
end

noctium_circuit guardedAmountKeyWriteInput where
  public enabled : Bool
  private amount : Amount
  private value : Native
end

noctium_circuit wrongAmountKeyWriteInput where
  private amount : Count
  private value : Native
end

noctium_circuit wrongAmountKeyLookupInput where
  private amount : Count
end

noctium_circuit amountKeyAliasedValueInput where
  private amount : Amount
  private value : Amount
end

noctium_contract RecordMapKeys where
  tree balances : struct Key {
    amount : Amount
  } => Native

  entry store uses amountKeyWriteInput arguments [amount, value] where
    insert balances[fields(disclose(amount))] := disclose(value)
  end

  entry guardedStore uses guardedAmountKeyWriteInput arguments [amount, value] where
    when enabled insert balances[fields(disclose(amount))] := disclose(value)
  end

  entry storeExplicitlyCastedValue uses amountKeyAliasedValueInput arguments [amount, value] where
    insert balances[fields(disclose(amount))] := disclose(cast(Native, value))
  end

  entry lookup uses amountKeyLookupInput arguments [amount] where
    read balances[fields(disclose(amount))] as stored
    return result : Native := stored
  end

  entry contains uses amountKeyLookupInput arguments [amount] where
    member balances[fields(disclose(amount))] as present
    return result : Bool := present
  end
end

private def recordMapEntry (name : String) : Entrypoint :=
  (RecordMapKeys.entrypoints.find? (·.name == name)).getD
    {name := "missing", circuit := {name := "missing"}}

private def recordMapContext : EvalContext := {
  modulus := Field.modulus
  poseidon2 := fun _ _ _ => .error "unused by nominal Field record Map fixture"
}

private def recordMapInitialState : LedgerState := {trees := [("balances", .map [])]}

private def recordMapCastedStoreRun (amount value : Nat) (state : LedgerState) :=
  (recordMapEntry "storeExplicitlyCastedValue").run recordMapContext [
    ("amount", .native amount), ("value", .native value)] state

private def recordMapLookupRun (amount : Nat) (state : LedgerState) :=
  (recordMapEntry "lookup").run recordMapContext [("amount", .native amount)] state

#guard match RecordMapKeys.state with
  | [{kind := .tree (.recordMapKey environment type .native), ..}] =>
      match LedgerValueType.recordMapKeyFields environment type with
      | .ok fields => fields == [("amount", .native)]
      | .error _ => _root_.Bool.false
  | _ => _root_.Bool.false

#guard ((recordMapEntry "store").validate Capabilities.source RecordMapKeys.state).isOk
#guard ((recordMapEntry "guardedStore").validate Capabilities.source RecordMapKeys.state).isOk
#guard ((recordMapEntry "storeExplicitlyCastedValue").validate Capabilities.source RecordMapKeys.state).isOk
#guard ((recordMapEntry "lookup").validate Capabilities.source RecordMapKeys.state).isOk
#guard ((recordMapEntry "contains").validate Capabilities.source RecordMapKeys.state).isOk

#guard match recordMapCastedStoreRun 17 42 recordMapInitialState with
  | .ok (_, state) => match recordMapLookupRun 17 state with
      | .ok (outputs, _) => outputs.lookup "result" == some (.native 42)
      | .error _ => _root_.Bool.false
  | .error _ => _root_.Bool.false

/-- error: nominal Field values require an explicit cast and must match the target type -/
#guard_msgs (substring := true) in
noctium_contract RejectWrongMapKeyWrite where
  tree balances : struct Key {
    amount : Amount
  } => Native

  entry store uses wrongAmountKeyWriteInput arguments [amount, value] where
    insert balances[fields(disclose(amount))] := disclose(value)
  end
end

/- error: nominal Field values require an explicit cast and must match the target type -/
#guard_msgs (substring := true) in
noctium_contract RejectNominalRecordMapValueErasure where
  tree balances : struct Key {
    amount : Amount
  } => Native

  entry store uses amountKeyAliasedValueInput arguments [amount, value] where
    insert balances[fields(disclose(amount))] := disclose(value)
  end
end

/-- error: nominal Field effects require a direct scalar Cell write -/
#guard_msgs (substring := true) in
noctium_contract RejectNominalMapKeyGuard where
  tree balances : struct Key {
    amount : Amount
  } => Native

  entry lookup uses amountKeyWriteInput arguments [amount, value] where
    when eq(amount, amount) insert balances[fields(disclose(amount))] := disclose(value)
  end
end

/-- error: nominal Field values require an explicit cast and must match the target type -/
#guard_msgs (substring := true) in
noctium_contract RejectWrongMapKeyLookup where
  tree balances : struct Key {
    amount : Amount
  } => Native

  entry lookup uses wrongAmountKeyLookupInput arguments [amount] where
    read balances[fields(disclose(amount))] as stored
    return result : Native := stored
  end
end

end NominalFieldMapKeys
