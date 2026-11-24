import Noctium.Frontend

open scoped Noctium
open Noctium

namespace NominalFieldRecordMap

noctium_field_type Amount := Field
noctium_field_type Count := Field

noctium_circuit matchingInputs where
  private keyAmount : Amount
  private memoAmount : Amount
end

noctium_circuit wrongKeyAliasInputs where
  private keyAmount : Count
  private memoAmount : Amount
end

noctium_circuit wrongMemoAliasInputs where
  private keyAmount : Amount
  private memoAmount : Count
end

noctium_contract RecordMap where
  tree records : struct Key {
    amount : Amount
  } => struct Memo {
    amount : Amount
  }

  entry roundTrip uses matchingInputs arguments [keyAmount, memoAmount] where
    insert records[fields(disclose(keyAmount))] := fields(disclose(memoAmount))
    member records[fields(disclose(keyAmount))] as present
    read records[fields(disclose(keyAmount))] as stored
    return found : Bool := present
    return amount : Amount := stored_amount
  end
end

private def recordMapEntry : Entrypoint :=
  (RecordMap.entrypoints.find? (·.name == "roundTrip")).getD
    {name := "missing", circuit := {name := "missing"}}

private def recordMapContext : EvalContext := {
  modulus := Field.modulus
  poseidon2 := fun _ _ _ => .error "unused by nominal Field record Map fixture"
}

private def recordMapInitialState : LedgerState := {trees := [("records", .map [])]}

private def recordMapRun (keyAmount memoAmount : Nat) (state : LedgerState) :=
  recordMapEntry.run recordMapContext [
    ("keyAmount", .native keyAmount), ("memoAmount", .native memoAmount)] state

#guard (RecordMap.validate Capabilities.source).isOk
#guard (recordMapEntry.validate Capabilities.source RecordMap.state).isOk

#guard match RecordMap.state with
  | [{kind := .tree (.recordMapComposite keyEnvironment keyType valueEnvironment valueType), ..}] =>
      match LedgerValueType.recordMapKeyFields keyEnvironment keyType,
          LedgerValueType.mapRecordWriteFields valueEnvironment valueType with
      | .ok keyFields, .ok valueFields =>
          keyFields == [("amount", .native)] && valueFields == [("amount", .native)]
      | _, _ => _root_.Bool.false
  | _ => _root_.Bool.false

#guard match recordMapRun 17 42 recordMapInitialState with
  | .ok (outputs, state) =>
      outputs.lookup "found" == some (.bool _root_.Bool.true) &&
      outputs.lookup "amount" == some (.native 42) &&
      state.trees.lookup "records" == some (.map [
        (.record [(.native, [17])],
          .composite (.structure "NominalFieldRecordMap.RecordMap.Memo") [.native 42])])
  | .error _ => _root_.Bool.false

/- error: nominal Field values require an explicit cast and must match the target type -/
#guard_msgs (substring := true) in
noctium_contract RejectWrongRecordKeyAlias where
  tree records : struct Key {
    amount : Amount
  } => struct Memo {
    amount : Amount
  }

  entry store uses wrongKeyAliasInputs arguments [keyAmount, memoAmount] where
    insert records[fields(disclose(keyAmount))] := fields(disclose(memoAmount))
  end
end

/- error: nominal Field values require an explicit cast and must match the target type -/
#guard_msgs (substring := true) in
noctium_contract RejectWrongRecordValueAlias where
  tree records : struct Key {
    amount : Amount
  } => struct Memo {
    amount : Amount
  }

  entry store uses wrongMemoAliasInputs arguments [keyAmount, memoAmount] where
    insert records[fields(disclose(keyAmount))] := fields(disclose(memoAmount))
  end
end

end NominalFieldRecordMap
