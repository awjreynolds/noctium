import Noctium.Frontend
import Noctium.Backend.Impact
import Noctium.Backend.Zkir
import Noctium.Compiler

open scoped Noctium
open Lean
open Noctium

noctium_circuit recordMapCollectionInputs where
  public active : Bool
  public amount : UInt 16
  public adding : Bool
  public clear : Bool
end

noctium_contract RecordMapCollections where
  tree scalars : struct Memo {
    active : Bool
    amount : UInt 16
  } => UInt 16

  tree records : struct Memo {
    active : Bool
    amount : UInt 16
  } => struct Receipt {
    accepted : Bool
    code : UInt 16
  }

  entry update uses recordMapCollectionInputs where
    when adding insert scalars[fields(active, amount)] := amount
    when adding insert records[fields(active, amount)] := fields(active, amount)
    when clear reset scalars
    when clear reset records
    size scalars as currentScalarSize
    isEmpty scalars as currentScalarEmpty
    size records as currentRecordSize
    isEmpty records as currentRecordEmpty
    return scalarSize : UInt 64 := currentScalarSize
    return scalarEmpty : Bool := currentScalarEmpty
    return recordSize : UInt 64 := currentRecordSize
    return recordEmpty : Bool := currentRecordEmpty
  end
end

private def recordMapCollectionEntry : Entrypoint :=
  (RecordMapCollections.entrypoints.find? (·.name == "update")).getD
    {name := "missing", circuit := {name := "missing"}}

private def recordMapCollectionContext : EvalContext := {
  modulus := Field.modulus
  poseidon2 := fun _ _ _ => .error "unused by record Map collection fixture"
}

private def recordMapCollectionInitial : LedgerState := {
  trees := [("scalars", .map []), ("records", .map [])]
}

private def recordMapCollectionRun (active : _root_.Bool) (amount : Nat)
    (adding clear : _root_.Bool) (state : LedgerState) :=
  recordMapCollectionEntry.run recordMapCollectionContext [
    ("active", .bool active), ("amount", .uint 65535 amount),
    ("adding", .bool adding), ("clear", .bool clear)] state

#guard (RecordMapCollections.validate Capabilities.source).isOk
#guard (recordMapCollectionEntry.validate Capabilities.source RecordMapCollections.state).isOk

#guard match RecordMapCollections.state with
  | [{kind := .tree (.recordMapKey _ _ (.uint 65535)), ..},
     {kind := .tree (.recordMapComposite _ _ _ _), ..}] => _root_.Bool.true
  | _ => _root_.Bool.false

#guard match Backend.Impact.lower RecordMapCollections.state recordMapCollectionEntry with
  | .ok plan =>
      plan.operations.any (fun operation => match operation with
        | .mapSize 0 [] _ => _root_.Bool.true
        | _ => _root_.Bool.false) &&
      plan.operations.any (fun operation => match operation with
        | .mapIsEmpty 0 [] _ => _root_.Bool.true
        | _ => _root_.Bool.false) &&
      plan.operations.any (fun operation => match operation with
        | .mapSize 1 [] _ => _root_.Bool.true
        | _ => _root_.Bool.false) &&
      plan.operations.any (fun operation => match operation with
        | .mapIsEmpty 1 [] _ => _root_.Bool.true
        | _ => _root_.Bool.false) &&
      plan.operations.filterMap (fun operation => match operation with
        | .insert levels => some levels
        | _ => none) == [2, 2, 1, 1] &&
      plan.operations.countP (fun operation => match operation with
        | .newMap => _root_.Bool.true
        | _ => _root_.Bool.false) == 2
  | .error _ => _root_.Bool.false

private def sealedRecordMapResetRejected : _root_.Bool :=
  let candidate := {recordMapCollectionEntry with
    circuit := {name := "sealedReset"}
    returns := []
    effects := [.emptyMapPath "records" []]
    effectGuards := [none]}
  let sealedState := RecordMapCollections.state.map fun declaration =>
    if declaration.name == "records" then
      {declaration with «sealed» := _root_.Bool.true}
    else declaration
  match candidate.validate Capabilities.source sealedState with
  | .error diagnostic =>
      diagnostic.message == "sealed state 'records' cannot be written by an entrypoint"
  | .ok _ => _root_.Bool.false

#guard sealedRecordMapResetRejected

private def recordMapCollectionNonemptyState : LedgerState :=
  {trees := [
    ("scalars", .map [
      (.record [(.bool, [1]), (.uint 65535, [513])], .scalar (.uint 65535 513))]),
    ("records", .map [
      (.record [(.bool, [1]), (.uint 65535, [513])],
        .composite (.structure "RecordMapCollections.Receipt") [.bool _root_.Bool.true, .uint 65535 513])])]
  }

#guard match recordMapCollectionRun _root_.Bool.true 513 _root_.Bool.false _root_.Bool.false
    recordMapCollectionInitial with
  | .ok (outputs, state) =>
      outputs.lookup "scalarSize" == some (.uint (2 ^ 64 - 1) 0) &&
      outputs.lookup "scalarEmpty" == some (.bool _root_.Bool.true) &&
      outputs.lookup "recordSize" == some (.uint (2 ^ 64 - 1) 0) &&
      outputs.lookup "recordEmpty" == some (.bool _root_.Bool.true) &&
      state == recordMapCollectionInitial
  | .error _ => _root_.Bool.false

#guard match recordMapCollectionRun _root_.Bool.true 513 _root_.Bool.true _root_.Bool.false
    recordMapCollectionInitial with
  | .ok (outputs, state) =>
      outputs.lookup "scalarSize" == some (.uint (2 ^ 64 - 1) 1) &&
      outputs.lookup "scalarEmpty" == some (.bool _root_.Bool.false) &&
      outputs.lookup "recordSize" == some (.uint (2 ^ 64 - 1) 1) &&
      outputs.lookup "recordEmpty" == some (.bool _root_.Bool.false) &&
      state.trees.lookup "scalars" == some (.map [
        (.record [(.bool, [1]), (.uint 65535, [513])], .scalar (.uint 65535 513))]) &&
      state.trees.lookup "records" == some (.map [
        (.record [(.bool, [1]), (.uint 65535, [513])],
          .composite (.structure "RecordMapCollections.Receipt") [.bool _root_.Bool.true, .uint 65535 513])])
  | .error _ => _root_.Bool.false

#guard match recordMapCollectionRun _root_.Bool.false 700 _root_.Bool.false _root_.Bool.false
    recordMapCollectionNonemptyState with
  | .ok (outputs, state) =>
      outputs.lookup "scalarSize" == some (.uint (2 ^ 64 - 1) 1) &&
      outputs.lookup "scalarEmpty" == some (.bool _root_.Bool.false) &&
      outputs.lookup "recordSize" == some (.uint (2 ^ 64 - 1) 1) &&
      outputs.lookup "recordEmpty" == some (.bool _root_.Bool.false) &&
      state == recordMapCollectionNonemptyState
  | .error _ => _root_.Bool.false

#guard match recordMapCollectionRun _root_.Bool.false 513 _root_.Bool.false _root_.Bool.true
    recordMapCollectionNonemptyState with
  | .ok (outputs, state) =>
      outputs.lookup "scalarSize" == some (.uint (2 ^ 64 - 1) 0) &&
      outputs.lookup "scalarEmpty" == some (.bool _root_.Bool.true) &&
      outputs.lookup "recordSize" == some (.uint (2 ^ 64 - 1) 0) &&
      outputs.lookup "recordEmpty" == some (.bool _root_.Bool.true) &&
      state.trees.lookup "scalars" == some (.map []) &&
      state.trees.lookup "records" == some (.map [])
  | .error _ => _root_.Bool.false
