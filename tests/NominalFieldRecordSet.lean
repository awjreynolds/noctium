import Noctium.Frontend

open scoped Noctium
open Noctium

namespace NominalFieldRecordSet

noctium_field_type Amount := Field
noctium_field_type Count := Field

noctium_circuit matchingInputs where
  private amount : Amount
  public adding : Bool
  public removing : Bool
end

noctium_circuit wrongAliasInputs where
  private amount : Count
  public adding : Bool
  public removing : Bool
end

noctium_contract RecordSet where
  set members : struct Key {
    amount : Amount
  }

  entry update uses matchingInputs where
    member members[fields(disclose(amount))] as presentBefore
    when adding insert members[fields(disclose(amount))]
    member members[fields(disclose(amount))] as presentAfterInsert
    when removing remove members[fields(disclose(amount))]
    member members[fields(disclose(amount))] as presentAfterRemove
    return before : Bool := presentBefore
    return afterInsert : Bool := presentAfterInsert
    return afterRemove : Bool := presentAfterRemove
  end
end

private def recordSetEntry : Entrypoint :=
  (RecordSet.entrypoints.find? (·.name == "update")).getD
    {name := "missing", circuit := {name := "missing"}}

private def recordSetContext : EvalContext := {
  modulus := Field.modulus
  poseidon2 := fun _ _ _ => .error "unused by nominal Field record Set fixture"
}

private def recordSetInitialState : LedgerState := {trees := [("members", .map [])]}

private def recordSetRun (amount : Nat) (adding removing : _root_.Bool) (state : LedgerState) :=
  recordSetEntry.run recordSetContext [
    ("amount", .native amount), ("adding", .bool adding), ("removing", .bool removing)] state

#guard (RecordSet.validate Capabilities.source).isOk
#guard (recordSetEntry.validate Capabilities.source RecordSet.state).isOk

#guard match RecordSet.state with
  | [{kind := .tree (.recordSet environment type), ..}] =>
      match LedgerValueType.recordSetKeyFields environment type with
      | .ok fields => fields == [("amount", .native)]
      | .error _ => _root_.Bool.false
  | _ => _root_.Bool.false

#guard match recordSetRun 17 _root_.Bool.true _root_.Bool.false recordSetInitialState with
  | .ok (outputs, state) =>
      outputs.lookup "before" == some (.bool _root_.Bool.false) &&
      outputs.lookup "afterInsert" == some (.bool _root_.Bool.true) &&
      outputs.lookup "afterRemove" == some (.bool _root_.Bool.true) &&
      state.trees.lookup "members" == some (.map [
        (.record [(.native, [17])], .null)])
  | .error _ => _root_.Bool.false

#guard match recordSetRun 17 _root_.Bool.false _root_.Bool.true
    (match recordSetRun 17 _root_.Bool.true _root_.Bool.false recordSetInitialState with
      | .ok (_, state) => state
      | .error _ => recordSetInitialState) with
  | .ok (outputs, state) =>
      outputs.lookup "before" == some (.bool _root_.Bool.true) &&
      outputs.lookup "afterRemove" == some (.bool _root_.Bool.false) &&
      state.trees.lookup "members" == some (.map [])
  | .error _ => _root_.Bool.false

/- error: nominal Field values require an explicit cast and must match the target type -/
#guard_msgs (substring := true) in
noctium_contract RejectWrongRecordSetAlias where
  set members : struct Key {
    amount : Amount
  }

  entry update uses wrongAliasInputs where
    member members[fields(disclose(amount))] as present
    when adding insert members[fields(disclose(amount))]
    when removing remove members[fields(disclose(amount))]
  end
end

end NominalFieldRecordSet
