import Noctium.Frontend
import Noctium.Backend.Impact
import Noctium.Backend.Zkir

open scoped Noctium
open Noctium

namespace NestedNominalFieldRecordSet

noctium_field_type Amount := Field
noctium_field_type Count := Field

noctium_circuit initializeInputs where
  public owner : Bytes 32
end

noctium_circuit updateInputs where
  public owner : Bytes 32
  private amount : Amount
  public adding : Bool
  public removing : Bool
end

noctium_circuit wrongAliasInputs where
  public owner : Bytes 32
  private amount : Count
end

noctium_circuit nominalOwnerInputs where
  private owner : Amount
  private amount : Amount
end

noctium_circuit nominalGuardInputs where
  public owner : Bytes 32
  private amount : Amount
  private guard : Amount
end

noctium_contract NestedRecordSet where
  tree buckets : Bytes32 => Set struct Key {
    amount : Amount
  }

  entry initBucket uses initializeInputs where
    insert buckets[owner] := emptyMap
  end

  entry update uses updateInputs where
    member buckets[owner][fields(disclose(amount))] as beforeMember
    when adding insert buckets[owner][fields(disclose(amount))]
    member buckets[owner][fields(disclose(amount))] as afterInsert
    when removing remove buckets[owner][fields(disclose(amount))]
    member buckets[owner][fields(disclose(amount))] as afterRemove
    return before : Bool := beforeMember
    return inserted : Bool := afterInsert
    return removed : Bool := afterRemove
  end
end

private def getEntry (name : String) : Entrypoint :=
  (NestedRecordSet.entrypoints.find? (·.name == name)).getD
    {name := "missing", circuit := {name := "missing"}}

private def context : EvalContext := {
  modulus := Field.modulus
  poseidon2 := fun _ _ _ => .error "unused by nested nominal Field record Set fixture"
}

private def initialState : LedgerState := {trees := [("buckets", .map [])]}
private def ownerBytes : List Nat := List.replicate 32 7

private def initRun (state : LedgerState) :=
  (getEntry "initBucket").run context [("owner", .bytes 32 ownerBytes)] state

private def update (amount : Nat) (adding removing : _root_.Bool) (state : LedgerState) :=
  (getEntry "update").run context [
    ("owner", .bytes 32 ownerBytes), ("amount", .native amount),
    ("adding", .bool adding), ("removing", .bool removing)] state

#guard (NestedRecordSet.validate Capabilities.source).isOk
#guard ((getEntry "initBucket").validate Capabilities.source NestedRecordSet.state).isOk
#guard ((getEntry "update").validate Capabilities.source NestedRecordSet.state).isOk

#guard match NestedRecordSet.state with
  | [{kind := .tree (.map (.bytes 32) (.recordSet environment type)), ..}] =>
      match LedgerValueType.recordSetKeyFields environment type with
      | .ok fields => fields == [("amount", .native)]
      | .error _ => _root_.Bool.false
  | _ => _root_.Bool.false

#guard match initRun initialState with
  | .ok (_, state) =>
      state.trees.lookup "buckets" == some (.map [(.bytes 32 ownerBytes, .map [])])
  | .error _ => _root_.Bool.false

#guard match initRun initialState with
  | .ok (_, state) =>
      match update 17 _root_.Bool.true _root_.Bool.false state with
      | .ok (outputs, afterInsert) =>
          outputs.lookup "before" == some (.bool _root_.Bool.false) &&
          outputs.lookup "inserted" == some (.bool _root_.Bool.true) &&
          outputs.lookup "removed" == some (.bool _root_.Bool.true) &&
          afterInsert.trees.lookup "buckets" == some (.map [(.bytes 32 ownerBytes,
            .map [(.record [(.native, [17])], .null)])]) &&
          (match update 17 _root_.Bool.false _root_.Bool.true afterInsert with
          | .ok (removed, afterRemove) =>
              removed.lookup "before" == some (.bool _root_.Bool.true) &&
              removed.lookup "inserted" == some (.bool _root_.Bool.true) &&
              removed.lookup "removed" == some (.bool _root_.Bool.false) &&
              afterRemove.trees.lookup "buckets" == state.trees.lookup "buckets"
          | .error _ => _root_.Bool.false)
      | .error _ => _root_.Bool.false
  | .error _ => _root_.Bool.false

#guard !(update 17 _root_.Bool.false _root_.Bool.false initialState).isOk

#guard match Backend.Impact.lower NestedRecordSet.state (getEntry "update") with
  | .ok plan => plan.operations.any (fun op => match op with
      | .indexPath 0 pushPath keys => pushPath && keys.length == 1
      | _ => _root_.Bool.false)
  | .error _ => _root_.Bool.false

#guard (Noctium.Backend.Zkir.lowerEntrypoint NestedRecordSet.state
  (getEntry "update")).isOk

/- error: nominal Field values require an explicit cast and must match the target type -/
#guard_msgs (substring := true) in
noctium_contract RejectWrongAlias where
  tree buckets : Bytes32 => Set struct Key {
    amount : Amount
  }
  entry update uses wrongAliasInputs where
    member buckets[owner][fields(disclose(amount))] as present
  end
end

/- error: nominal Field effects require a direct scalar Cell write -/
#guard_msgs (substring := true) in
noctium_contract RejectNominalOwner where
  tree buckets : Bytes32 => Set struct Key {
    amount : Amount
  }
  entry update uses nominalOwnerInputs where
    insert buckets[owner][fields(disclose(amount))]
  end
end

/- error: nominal Field effects require a direct scalar Cell write -/
#guard_msgs (substring := true) in
noctium_contract RejectNominalGuard where
  tree buckets : Bytes32 => Set struct Key {
    amount : Amount
  }
  entry update uses nominalGuardInputs where
    when eq(guard, guard) insert buckets[owner][fields(disclose(amount))]
  end
end

end NestedNominalFieldRecordSet
