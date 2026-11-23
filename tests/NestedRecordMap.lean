import Noctium.Frontend
import Noctium.Backend.Impact
import Noctium.Backend.Zkir

open scoped Noctium
open Noctium

noctium_circuit nestedRecordMapOwnerInputs where
  public owner : Bytes32
end

noctium_circuit nestedRecordMapUpdateInputs where
  public owner : Bytes32
  private active : Bool
  private amount : UInt 16
  private value : UInt 16
end

noctium_circuit nestedRecordMapLookupInputs where
  public owner : Bytes32
  private active : Bool
  private amount : UInt 16
  public shouldRead : Bool
end

noctium_circuit nestedRecordMapRemoveInputs where
  public owner : Bytes32
  private active : Bool
  private amount : UInt 16
  public removeIt : Bool
end

noctium_contract NestedRecordMap where
  tree memos : Bytes32 => struct Memo {
    active : Bool
    amount : UInt 16
  } => UInt 16

  entry initializeOwner uses nestedRecordMapOwnerInputs where
    insert memos[owner] := emptyMap
  end

  entry upsert uses nestedRecordMapUpdateInputs where
    member memos[owner][fields(disclose(active), disclose(amount))] as wasPresent
    insert memos[owner][fields(disclose(active), disclose(amount))] := disclose(value)
    member memos[owner][fields(disclose(active), disclose(amount))] as isPresent
    read memos[owner][fields(disclose(active), disclose(amount))] as updatedValue
    return presentBefore : Bool := wasPresent
    return presentAfter : Bool := isPresent
    return storedValue : UInt 16 := updatedValue
  end

  entry lookup uses nestedRecordMapLookupInputs where
    member memos[owner][fields(disclose(active), disclose(amount))] as hasMemo
    when shouldRead read memos[owner][fields(disclose(active), disclose(amount))] as foundValue
    return present : Bool := hasMemo
    return storedValue : UInt 16 := foundValue
  end

  entry removeMemo uses nestedRecordMapRemoveInputs where
    member memos[owner][fields(disclose(active), disclose(amount))] as wasPresent
    when removeIt remove memos[owner][fields(disclose(active), disclose(amount))]
    member memos[owner][fields(disclose(active), disclose(amount))] as isPresent
    return presentBefore : Bool := wasPresent
    return presentAfter : Bool := isPresent
  end
end

private def nestedRecordMapEntry (name : String) : Entrypoint :=
  (NestedRecordMap.entrypoints.find? (·.name == name)).getD
    {name := "missing", circuit := {name := "missing"}}

private def nestedRecordMapContext : EvalContext := {
  modulus := Field.modulus
  poseidon2 := fun _ _ _ => .error "unused by nested record Map fixture"
}

private def nestedRecordMapOwner (byte : Nat) : Value :=
  .bytes 32 (List.replicate 32 byte)

private def nestedRecordMapKey (active : _root_.Bool) (amount : Nat) : Value :=
  .record [(.bool, [if active then 1 else 0]), (.uint 65535, [amount])]

private def nestedRecordMapInitial : LedgerState := {
  trees := [("memos", .map [])]
}

private def nestedRecordMapInitializeOwner (owner : Nat) (state : LedgerState) :=
  (nestedRecordMapEntry "initializeOwner").run nestedRecordMapContext
    [("owner", nestedRecordMapOwner owner)] state

private def nestedRecordMapUpsert (owner : Nat) (active : _root_.Bool)
    (amount value : Nat) (state : LedgerState) :=
  (nestedRecordMapEntry "upsert").run nestedRecordMapContext [
    ("owner", nestedRecordMapOwner owner),
    ("active", .bool active),
    ("amount", .uint 65535 amount),
    ("value", .uint 65535 value)] state

private def nestedRecordMapLookup (owner : Nat) (active : _root_.Bool)
    (amount : Nat) (shouldRead : _root_.Bool) (state : LedgerState) :=
  (nestedRecordMapEntry "lookup").run nestedRecordMapContext [
    ("owner", nestedRecordMapOwner owner),
    ("active", .bool active),
    ("amount", .uint 65535 amount),
    ("shouldRead", .bool shouldRead)] state

private def nestedRecordMapRemove (owner : Nat) (active : _root_.Bool)
    (amount : Nat) (removeIt : _root_.Bool) (state : LedgerState) :=
  (nestedRecordMapEntry "removeMemo").run nestedRecordMapContext [
    ("owner", nestedRecordMapOwner owner),
    ("active", .bool active),
    ("amount", .uint 65535 amount),
    ("removeIt", .bool removeIt)] state

private def nestedRecordMapExpected : LedgerState := {
  trees := [("memos", .map [
    (nestedRecordMapOwner 1, .map [
      (nestedRecordMapKey _root_.Bool.true 513, .scalar (.uint 65535 33))]),
    (nestedRecordMapOwner 2, .map [
      (nestedRecordMapKey _root_.Bool.true 513, .scalar (.uint 65535 99))])])]
}

private def nestedRecordMapOutputsMatch (outputs : List (String × Value))
    (expected : List (String × Value)) : _root_.Bool :=
  expected.all fun (name, value) => outputs.lookup name == some value

private def nestedRecordMapScenario : Except String _root_.Bool := do
  let (_, state) ← nestedRecordMapInitializeOwner 1 nestedRecordMapInitial
  let (_, state) ← nestedRecordMapInitializeOwner 2 state
  let (firstOutputs, state) ← nestedRecordMapUpsert 1 _root_.Bool.true 513 11 state
  unless nestedRecordMapOutputsMatch firstOutputs [
      ("presentBefore", .bool _root_.Bool.false), ("presentAfter", .bool _root_.Bool.true),
      ("storedValue", .uint 65535 11)] do
    throw "first nested Map insertion returned the wrong result"
  let (secondOutputs, state) ← nestedRecordMapUpsert 1 _root_.Bool.false 513 22 state
  unless nestedRecordMapOutputsMatch secondOutputs [
      ("presentBefore", .bool _root_.Bool.false), ("presentAfter", .bool _root_.Bool.true),
      ("storedValue", .uint 65535 22)] do
    throw "second nested record key returned the wrong result"
  let (siblingOutputs, state) ← nestedRecordMapUpsert 2 _root_.Bool.true 513 99 state
  unless nestedRecordMapOutputsMatch siblingOutputs [
      ("presentBefore", .bool _root_.Bool.false), ("presentAfter", .bool _root_.Bool.true),
      ("storedValue", .uint 65535 99)] do
    throw "sibling owner insertion returned the wrong result"
  let (duplicateOutputs, state) ← nestedRecordMapUpsert 1 _root_.Bool.true 513 11 state
  unless nestedRecordMapOutputsMatch duplicateOutputs [
      ("presentBefore", .bool _root_.Bool.true), ("presentAfter", .bool _root_.Bool.true),
      ("storedValue", .uint 65535 11)] do
    throw "repeated nested Map insertion did not preserve the selected value"
  let (_, state) ← nestedRecordMapUpsert 1 _root_.Bool.true 513 33 state
  let (changedFieldMiss, state) ← nestedRecordMapLookup 1 _root_.Bool.true 514 _root_.Bool.false state
  unless nestedRecordMapOutputsMatch changedFieldMiss [
      ("present", .bool _root_.Bool.false), ("storedValue", .uint 65535 0)] do
    throw "one-field record key difference did not miss"
  match nestedRecordMapLookup 1 _root_.Bool.true 514 _root_.Bool.true state with
  | .error _ => pure ()
  | .ok _ => throw "strict nested Map read accepted a missing record key"
  let (inactiveRemove, state) ← nestedRecordMapRemove 1 _root_.Bool.false 513 _root_.Bool.false state
  unless nestedRecordMapOutputsMatch inactiveRemove [
      ("presentBefore", .bool _root_.Bool.true), ("presentAfter", .bool _root_.Bool.true)] do
    throw "inactive nested Map removal returned the wrong result"
  let (removed, state) ← nestedRecordMapRemove 1 _root_.Bool.false 513 _root_.Bool.true state
  unless nestedRecordMapOutputsMatch removed [
      ("presentBefore", .bool _root_.Bool.true), ("presentAfter", .bool _root_.Bool.false)] do
    throw "nested Map removal returned the wrong result"
  let (retained, state) ← nestedRecordMapLookup 1 _root_.Bool.true 513 _root_.Bool.true state
  unless nestedRecordMapOutputsMatch retained [
      ("present", .bool _root_.Bool.true), ("storedValue", .uint 65535 33)] do
    throw "removing the sibling inner key changed the selected value"
  let (sibling, state) ← nestedRecordMapLookup 2 _root_.Bool.true 513 _root_.Bool.true state
  unless nestedRecordMapOutputsMatch sibling [
      ("present", .bool _root_.Bool.true), ("storedValue", .uint 65535 99)] do
    throw "nested Map operation changed the sibling outer bucket"
  unless state == nestedRecordMapExpected do
    throw "nested Map state differs from the expected buckets and typed keys"
  pure _root_.Bool.true

#guard (NestedRecordMap.validate Capabilities.source).isOk
#guard ((nestedRecordMapEntry "initializeOwner").validate Capabilities.source NestedRecordMap.state).isOk
#guard ((nestedRecordMapEntry "upsert").validate Capabilities.source NestedRecordMap.state).isOk
#guard ((nestedRecordMapEntry "lookup").validate Capabilities.source NestedRecordMap.state).isOk
#guard ((nestedRecordMapEntry "removeMemo").validate Capabilities.source NestedRecordMap.state).isOk

#guard match Backend.Impact.lower NestedRecordMap.state (nestedRecordMapEntry "upsert") with
  | .ok _ => _root_.Bool.true
  | .error _ => _root_.Bool.false

#guard match Backend.Zkir.lowerEntrypoint NestedRecordMap.state (nestedRecordMapEntry "upsert") with
  | .ok _ => _root_.Bool.true
  | .error _ => _root_.Bool.false

#guard match nestedRecordMapScenario with
  | .ok _root_.Bool.true => _root_.Bool.true
  | _ => _root_.Bool.false
