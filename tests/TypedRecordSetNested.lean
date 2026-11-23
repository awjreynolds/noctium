import Noctium.Frontend
import Noctium.Backend.Impact
import Noctium.Backend.Zkir
import Noctium.Compiler

open scoped Noctium
open Lean
open Noctium

noctium_circuit recordSetInitializeInputs where
  public owner : Bytes 32
end

noctium_circuit recordSetUpdateInputs where
  public owner : Bytes 32
  public active : Bool
  public amount : UInt 16
  public adding : Bool
  public removing : Bool
end

noctium_contract NestedRecordSet where
  tree buckets : Bytes32 => Set struct Memo {
    active : Bool
    amount : UInt 16
  }

  entry initOwner uses recordSetInitializeInputs where
    insert buckets[owner] := emptyMap
  end

  entry update uses recordSetUpdateInputs where
    member buckets[owner][fields(active, amount)] as beforeMember
    when adding insert buckets[owner][fields(active, amount)]
    when removing remove buckets[owner][fields(active, amount)]
    member buckets[owner][fields(active, amount)] as afterMember
    size buckets[owner] as afterSize
    return presentBefore : Bool := beforeMember
    return presentAfter : Bool := afterMember
    return bucketSize : UInt 64 := afterSize
  end
end

private def nestedRecordSetEntry (name : String) : Entrypoint :=
  (NestedRecordSet.entrypoints.find? (·.name == name)).getD
    {name := "missing", circuit := {name := "missing"}}

private def nestedRecordSetContext : EvalContext := {
  modulus := Field.modulus
  poseidon2 := fun _ _ _ => .error "unused by nested record Set fixture"
}

private def nestedRecordSetInitial : LedgerState := {trees := [("buckets", .map [])]}

private def nestedRecordSetInitialize (owner : List Nat) (state : LedgerState) :=
  (nestedRecordSetEntry "initOwner").run nestedRecordSetContext
    [("owner", .bytes 32 owner)] state

private def nestedRecordSetUpdate (owner : List Nat) (active : _root_.Bool)
    (amount : Nat) (adding removing : _root_.Bool) (state : LedgerState) :=
  (nestedRecordSetEntry "update").run nestedRecordSetContext [
    ("owner", .bytes 32 owner), ("active", .bool active),
    ("amount", .uint 65535 amount), ("adding", .bool adding),
    ("removing", .bool removing)] state

private def nestedOwner : List Nat := List.replicate 32 7

private partial def hasSelectedRecordSetInsert : List Backend.Impact.Op → _root_.Bool
  | .indexPath 0 pushPath keys :: .pushFields _ fields storage :: rest =>
      (pushPath && keys.length == 1 && !storage &&
        fields.map LedgerFieldExpr.ty == [.bool, .uint 65535]) ||
        hasSelectedRecordSetInsert rest
  | _ :: rest => hasSelectedRecordSetInsert rest
  | [] => _root_.Bool.false

#guard (NestedRecordSet.validate Capabilities.source).isOk
#guard ((nestedRecordSetEntry "initOwner").validate Capabilities.source NestedRecordSet.state).isOk
#guard ((nestedRecordSetEntry "update").validate Capabilities.source NestedRecordSet.state).isOk

#guard match nestedRecordSetInitialize nestedOwner nestedRecordSetInitial with
  | .ok (_, state) => state.trees.lookup "buckets" == some (.map [(.bytes 32 nestedOwner, .map [])])
  | .error _ => _root_.Bool.false

#guard match nestedRecordSetInitialize nestedOwner nestedRecordSetInitial with
  | .ok (_, state) =>
      match nestedRecordSetUpdate nestedOwner _root_.Bool.true 513 _root_.Bool.true _root_.Bool.false state with
      | .ok (outputs, after) =>
          outputs.lookup "presentBefore" == some (.bool _root_.Bool.false) &&
          outputs.lookup "presentAfter" == some (.bool _root_.Bool.true) &&
          outputs.lookup "bucketSize" == some (.uint (2 ^ 64 - 1) 1) &&
          after.trees.lookup "buckets" == some (.map [(.bytes 32 nestedOwner, .map [
            (.record [(.bool, [1]), (.uint 65535, [513])], .null)])])
      | .error _ => _root_.Bool.false
  | .error _ => _root_.Bool.false

#guard match nestedRecordSetInitialize nestedOwner nestedRecordSetInitial with
  | .ok (_, state) =>
      match nestedRecordSetUpdate nestedOwner _root_.Bool.true 513 _root_.Bool.true _root_.Bool.false state with
      | .ok (_, inserted) =>
          match nestedRecordSetUpdate nestedOwner _root_.Bool.true 513 _root_.Bool.true _root_.Bool.false inserted with
          | .ok (duplicate, afterDuplicate) =>
              match nestedRecordSetUpdate nestedOwner _root_.Bool.false 513 _root_.Bool.true _root_.Bool.false afterDuplicate with
              | .ok (distinct, afterDistinct) =>
                  match nestedRecordSetUpdate nestedOwner _root_.Bool.true 514 _root_.Bool.false _root_.Bool.false afterDistinct with
                  | .ok (noInsertion, afterNoInsertion) =>
                      match nestedRecordSetUpdate nestedOwner _root_.Bool.true 513 _root_.Bool.false _root_.Bool.true afterNoInsertion with
                      | .ok (removed, afterRemove) =>
                          duplicate.lookup "presentBefore" == some (.bool _root_.Bool.true) &&
                          duplicate.lookup "presentAfter" == some (.bool _root_.Bool.true) &&
                          duplicate.lookup "bucketSize" == some (.uint (2 ^ 64 - 1) 1) &&
                          distinct.lookup "presentBefore" == some (.bool _root_.Bool.false) &&
                          distinct.lookup "bucketSize" == some (.uint (2 ^ 64 - 1) 2) &&
                          noInsertion.lookup "presentBefore" == some (.bool _root_.Bool.false) &&
                          noInsertion.lookup "bucketSize" == some (.uint (2 ^ 64 - 1) 2) &&
                          removed.lookup "presentBefore" == some (.bool _root_.Bool.true) &&
                          removed.lookup "presentAfter" == some (.bool _root_.Bool.false) &&
                          removed.lookup "bucketSize" == some (.uint (2 ^ 64 - 1) 1) &&
                          afterRemove.trees.lookup "buckets" == some (.map [(.bytes 32 nestedOwner, .map [
                            (.record [(.bool, [0]), (.uint 65535, [513])], .null)])])
                      | .error _ => _root_.Bool.false
                  | .error _ => _root_.Bool.false
              | .error _ => _root_.Bool.false
          | .error _ => _root_.Bool.false
      | .error _ => _root_.Bool.false
  | .error _ => _root_.Bool.false

#guard match Backend.Impact.lower NestedRecordSet.state (nestedRecordSetEntry "update") with
  | .ok plan =>
      hasSelectedRecordSetInsert plan.operations &&
      plan.operations.any (fun op => match op with
        | .indexPath 0 _ [.bytes32 (.ref "owner")] => _root_.Bool.true
        | _ => _root_.Bool.false)
  | .error _ => _root_.Bool.false

#guard match Backend.Impact.lower NestedRecordSet.state (nestedRecordSetEntry "update") with
  | .ok plan => plan.operations.any (fun op => match op with
      | .mapRemoveRecord 0 _ keys values => keys.length == 1 &&
          values.map LedgerFieldExpr.ty == [.bool, .uint 65535]
      | _ => _root_.Bool.false)
  | .error _ => _root_.Bool.false

#guard (Noctium.Backend.Zkir.lowerEntrypoint NestedRecordSet.state
  (nestedRecordSetEntry "update")).isOk
