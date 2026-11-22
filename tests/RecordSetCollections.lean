import Noctium.Frontend
import Noctium.Backend.Impact

open scoped Noctium
open Noctium

noctium_circuit recordSetCollectionInputs where
  public active : Bool
  public amount : UInt 16
  public adding : Bool
  public clear : Bool
end

noctium_contract RecordSetCollections where
  set memoSet : struct Memo {
    active : Bool
    amount : UInt 16
  }

  entry update uses recordSetCollectionInputs where
    when adding insert memoSet[fields(active, amount)]
    when clear reset memoSet
    size memoSet as itemCount
    isEmpty memoSet as wasEmpty
    return size : UInt 64 := itemCount
    return isEmpty : Bool := wasEmpty
  end
end

private def recordSetCollectionEntry : Entrypoint :=
  (RecordSetCollections.entrypoints.find? (·.name == "update")).getD
    {name := "missing", circuit := {name := "missing"}}

#guard (RecordSetCollections.validate Capabilities.source).isOk
#guard (recordSetCollectionEntry.validate Capabilities.source RecordSetCollections.state).isOk

#guard match RecordSetCollections.state with
  | [{kind := .tree (.recordSet environment type), ..}] =>
      match LedgerValueType.ledgerRecordWriteFields environment type with
      | .ok fields => fields == [("active", .bool), ("amount", .uint 65535)]
      | .error _ => _root_.Bool.false
  | _ => _root_.Bool.false

#guard match Backend.Impact.lower RecordSetCollections.state recordSetCollectionEntry with
  | .ok plan =>
      plan.activityGuards.length == plan.operations.length &&
      plan.operations.any (fun operation => match operation with
        | .mapSize 0 [] _ | .mapIsEmpty 0 [] _ => _root_.Bool.true
        | _ => _root_.Bool.false) &&
      plan.operations.any (fun operation => match operation with
        | .indexPath 0 _root_.Bool.true [] => _root_.Bool.true
        | _ => _root_.Bool.false) &&
      let guards := plan.activityGuards
      (guards.take 8).all (fun guard => match guard with
        | none => _root_.Bool.true
        | _ => _root_.Bool.false) &&
      (guards.drop 8 |>.take 5).all (fun guard => match guard with
        | some (.ref "adding") => _root_.Bool.true
        | _ => _root_.Bool.false) &&
      (guards.drop 13 |>.take 4).all (fun guard => match guard with
        | some (.ref "clear") => _root_.Bool.true
        | _ => _root_.Bool.false) &&
      (guards.drop 17).length == 2 &&
      (guards.drop 17).all (fun guard => match guard with
        | none => _root_.Bool.true
        | _ => _root_.Bool.false) &&
      plan.fieldGroups.map List.length ==
        [5, 4, 5, 4, 5, 4, 5, 4, 4, 7, 5, 1, 1, 5, 5, 1, 1, 1, 4, 1, 4, 1, 4, 1, 5, 1, 4]
  | .error _ => _root_.Bool.false

private def sealedRecordSetResetRejected : _root_.Bool :=
  let candidate := {recordSetCollectionEntry with
    circuit := {name := "sealedReset"}
    returns := []
    effects := [.emptyMapPath "memoSet" []]
    effectGuards := [none]}
  let sealedState := RecordSetCollections.state.map fun declaration =>
    {declaration with «sealed» := _root_.Bool.true}
  match candidate.validate Capabilities.source sealedState with
  | .error diagnostic =>
      diagnostic.message == "sealed state 'memoSet' cannot be written by an entrypoint"
  | .ok _ => _root_.Bool.false

#guard sealedRecordSetResetRejected

private def recordSetCollectionContext : EvalContext := {
  modulus := Field.modulus
  poseidon2 := fun _ _ _ => .error "unused by record Set collection fixture"
}

private def recordSetCollectionInitial : LedgerState := {
  trees := [("memoSet", .map [])]
}

private def recordSetCollectionRun (active : _root_.Bool) (amount : Nat)
    (adding clear : _root_.Bool) (state : LedgerState) :=
  recordSetCollectionEntry.run recordSetCollectionContext [
    ("active", .bool active), ("amount", .uint 65535 amount),
    ("adding", .bool adding), ("clear", .bool clear)] state

#guard match recordSetCollectionRun _root_.Bool.true 513 _root_.Bool.false _root_.Bool.false
    recordSetCollectionInitial with
  | .ok (outputs, state) =>
      outputs.lookup "size" == some (.uint (2 ^ 64 - 1) 0) &&
      outputs.lookup "isEmpty" == some (.bool _root_.Bool.true) &&
      state.trees.lookup "memoSet" == some (.map [])
  | .error _ => _root_.Bool.false

#guard match recordSetCollectionRun _root_.Bool.true 513 _root_.Bool.true _root_.Bool.false
    recordSetCollectionInitial with
  | .ok (outputs, state) =>
      outputs.lookup "size" == some (.uint (2 ^ 64 - 1) 1) &&
      outputs.lookup "isEmpty" == some (.bool _root_.Bool.false) &&
      state.trees.lookup "memoSet" == some (.map [
        (.record [(.bool, [1]), (.uint 65535, [513])], .null)])
  | .error _ => _root_.Bool.false

#guard match recordSetCollectionRun _root_.Bool.false 513 _root_.Bool.true _root_.Bool.false
    (match recordSetCollectionRun _root_.Bool.true 513 _root_.Bool.true _root_.Bool.false
        recordSetCollectionInitial with
      | .ok (_, state) => state
      | .error _ => recordSetCollectionInitial) with
  | .ok (outputs, state) =>
      outputs.lookup "size" == some (.uint (2 ^ 64 - 1) 2) &&
      outputs.lookup "isEmpty" == some (.bool _root_.Bool.false) &&
      match state.trees.lookup "memoSet" with
      | some (.map entries) => entries.length == 2 && entries.contains
          (.record [(.bool, [1]), (.uint 65535, [513])], .null) && entries.contains
          (.record [(.bool, [0]), (.uint 65535, [513])], .null)
      | _ => _root_.Bool.false
  | .error _ => _root_.Bool.false

#guard match recordSetCollectionRun _root_.Bool.false 513 _root_.Bool.false _root_.Bool.false
    (match recordSetCollectionRun _root_.Bool.false 513 _root_.Bool.true _root_.Bool.false
        (match recordSetCollectionRun _root_.Bool.true 513 _root_.Bool.true _root_.Bool.false
            recordSetCollectionInitial with
          | .ok (_, state) => state
          | .error _ => recordSetCollectionInitial) with
      | .ok (_, state) => state
      | .error _ => recordSetCollectionInitial) with
  | .ok (outputs, state) =>
      outputs.lookup "size" == some (.uint (2 ^ 64 - 1) 2) &&
      outputs.lookup "isEmpty" == some (.bool _root_.Bool.false) &&
      match state.trees.lookup "memoSet" with
      | some (.map entries) => entries.length == 2
      | _ => _root_.Bool.false
  | .error _ => _root_.Bool.false

#guard match recordSetCollectionRun _root_.Bool.false 513 _root_.Bool.false _root_.Bool.true
    (match recordSetCollectionRun _root_.Bool.false 513 _root_.Bool.true _root_.Bool.false
        (match recordSetCollectionRun _root_.Bool.true 513 _root_.Bool.true _root_.Bool.false
            recordSetCollectionInitial with
          | .ok (_, state) => state
          | .error _ => recordSetCollectionInitial) with
      | .ok (_, state) => state
      | .error _ => recordSetCollectionInitial) with
  | .ok (outputs, state) =>
      outputs.lookup "size" == some (.uint (2 ^ 64 - 1) 0) &&
      outputs.lookup "isEmpty" == some (.bool _root_.Bool.true) &&
      state.trees.lookup "memoSet" == some (.map [])
  | .error _ => _root_.Bool.false
