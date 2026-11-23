import Noctium.Frontend
import Noctium.Backend.Impact
import Noctium.Backend.Zkir
import Noctium.Disclosure

open scoped Noctium
open Noctium

noctium_circuit nestedRecordMapDefaultsOwnerInputs where
  public owner : Bytes32
end

noctium_circuit nestedRecordMapDefaultsSeedInputs where
  public owner : Bytes32
  private active : Bool
  private amount : UInt 16
  private value : UInt 16
end

noctium_circuit nestedRecordMapDefaultsInputs where
  public owner : Bytes32
  private active : Bool
  private amount : UInt 16
  public enabled : Bool
end

noctium_circuit nestedRecordMapDefaultsUnconditionalInputs where
  public owner : Bytes32
  private active : Bool
  private amount : UInt 16
end

noctium_contract NestedRecordMapDefaults where
  tree memos : Bytes32 => struct Memo {
    active : Bool
    amount : UInt 16
  } => UInt 16

  entry initializeOwner uses nestedRecordMapDefaultsOwnerInputs where
    insert memos[owner] := emptyMap
  end

  entry seedMemo uses nestedRecordMapDefaultsSeedInputs where
    insert memos[owner][fields(disclose(active), disclose(amount))] := disclose(value)
  end

  entry defaultMemo uses nestedRecordMapDefaultsInputs where
    member memos[owner][fields(disclose(active), disclose(amount))] as wasPresent
    when enabled insertDefault memos[owner][fields(disclose(active), disclose(amount))]
    member memos[owner][fields(disclose(active), disclose(amount))] as isPresent
    read memos[owner][fields(disclose(active), disclose(amount))] as selectedValue
    size memos[owner] as currentSize
    return presentBefore : Bool := wasPresent
    return presentAfter : Bool := isPresent
    return chosenValue : UInt 16 := selectedValue
    return bucketSize : UInt 64 := currentSize
  end

  entry defaultMemoUnconditional uses nestedRecordMapDefaultsUnconditionalInputs where
    member memos[owner][fields(disclose(active), disclose(amount))] as wasPresent
    insertDefault memos[owner][fields(disclose(active), disclose(amount))]
    member memos[owner][fields(disclose(active), disclose(amount))] as isPresent
    read memos[owner][fields(disclose(active), disclose(amount))] as selectedValue
    size memos[owner] as currentSize
    return presentBefore : Bool := wasPresent
    return presentAfter : Bool := isPresent
    return chosenValue : UInt 16 := selectedValue
    return bucketSize : UInt 64 := currentSize
  end
end

private def nestedRecordMapDefaultsEntry (name : String) : Entrypoint :=
  (NestedRecordMapDefaults.entrypoints.find? (·.name == name)).getD
    {name := "missing", circuit := {name := "missing"}}

private def nestedRecordMapDefaultsContext : EvalContext := {
  modulus := Field.modulus
  poseidon2 := fun _ _ _ => .error "unused by nested record Map defaults fixture"
}

private def nestedRecordMapDefaultsOwner (byte : Nat) : Value :=
  .bytes 32 (List.replicate 32 byte)

private def nestedRecordMapDefaultsKey (active : _root_.Bool) (amount : Nat) : Value :=
  .record [(.bool, [if active then 1 else 0]), (.uint 65535, [amount])]

private def nestedRecordMapDefaultsInitial : LedgerState := {
  trees := [("memos", .map [])]
}

private def nestedRecordMapDefaultsInitialize (owner : Nat) (state : LedgerState) :=
  (nestedRecordMapDefaultsEntry "initializeOwner").run nestedRecordMapDefaultsContext
    [("owner", nestedRecordMapDefaultsOwner owner)] state

private def nestedRecordMapDefaultsSeed (owner : Nat) (active : _root_.Bool)
    (amount value : Nat) (state : LedgerState) :=
  (nestedRecordMapDefaultsEntry "seedMemo").run nestedRecordMapDefaultsContext [
    ("owner", nestedRecordMapDefaultsOwner owner),
    ("active", .bool active), ("amount", .uint 65535 amount),
    ("value", .uint 65535 value)] state

private def nestedRecordMapDefaultsApply (owner : Nat) (active : _root_.Bool)
    (amount : Nat) (enabled : _root_.Bool) (state : LedgerState) :=
  (nestedRecordMapDefaultsEntry "defaultMemo").run nestedRecordMapDefaultsContext [
    ("owner", nestedRecordMapDefaultsOwner owner), ("active", .bool active),
    ("amount", .uint 65535 amount), ("enabled", .bool enabled)] state

private def nestedRecordMapDefaultsApplyUnconditional (owner : Nat) (active : _root_.Bool)
    (amount : Nat) (state : LedgerState) :=
  (nestedRecordMapDefaultsEntry "defaultMemoUnconditional").run
    nestedRecordMapDefaultsContext [
      ("owner", nestedRecordMapDefaultsOwner owner), ("active", .bool active),
      ("amount", .uint 65535 amount)] state

private def nestedRecordMapDefaultsOutputsMatch (outputs : List (String × Value))
    (expected : List (String × Value)) : _root_.Bool :=
  expected.all fun (name, value) => outputs.lookup name == some value

#guard (NestedRecordMapDefaults.validate Capabilities.source).isOk
#guard ((nestedRecordMapDefaultsEntry "initializeOwner").validate Capabilities.source
  NestedRecordMapDefaults.state).isOk
#guard ((nestedRecordMapDefaultsEntry "seedMemo").validate Capabilities.source
  NestedRecordMapDefaults.state).isOk
#guard ((nestedRecordMapDefaultsEntry "defaultMemo").validate Capabilities.source
  NestedRecordMapDefaults.state).isOk
#guard ((nestedRecordMapDefaultsEntry "defaultMemoUnconditional").validate Capabilities.source
  NestedRecordMapDefaults.state).isOk
#guard (Disclosure.entrypoint (nestedRecordMapDefaultsEntry "seedMemo")).isOk
#guard (Disclosure.entrypoint (nestedRecordMapDefaultsEntry "defaultMemo")).isOk
#guard (Disclosure.entrypoint (nestedRecordMapDefaultsEntry "defaultMemoUnconditional")).isOk

#guard match Backend.Impact.lower NestedRecordMapDefaults.state
    (nestedRecordMapDefaultsEntry "defaultMemo") with
  | .ok plan => plan.operations.any fun operation => match operation with
      | .indexPath 0 _root_.Bool.true keys => keys.length == 1
      | _ => _root_.Bool.false
  | .error _ => _root_.Bool.false

#guard match Backend.Zkir.lowerEntrypoint NestedRecordMapDefaults.state
    (nestedRecordMapDefaultsEntry "defaultMemo") with
  | .ok _ => _root_.Bool.true
  | .error _ => _root_.Bool.false

#guard match Backend.Zkir.lowerEntrypoint NestedRecordMapDefaults.state
    (nestedRecordMapDefaultsEntry "defaultMemoUnconditional") with
  | .ok _ => _root_.Bool.true
  | .error _ => _root_.Bool.false

#guard match Backend.Impact.lower NestedRecordMapDefaults.state
    (nestedRecordMapDefaultsEntry "defaultMemoUnconditional") with
  | .ok _ => _root_.Bool.true
  | .error _ => _root_.Bool.false

private def nestedRecordMapDefaultsScenario : Except String _root_.Bool := do
  let (_, state) ← nestedRecordMapDefaultsInitialize 1 nestedRecordMapDefaultsInitial
  let (_, state) ← nestedRecordMapDefaultsInitialize 2 state
  let (_, state) ← nestedRecordMapDefaultsSeed 1 _root_.Bool.true 513 11 state
  let (_, state) ← nestedRecordMapDefaultsSeed 1 _root_.Bool.false 513 22 state
  let (_, state) ← nestedRecordMapDefaultsSeed 2 _root_.Bool.true 513 99 state
  let (missingOutputs, state) ← nestedRecordMapDefaultsApply 1 _root_.Bool.true 514
    _root_.Bool.true state
  unless nestedRecordMapDefaultsOutputsMatch missingOutputs [
      ("presentBefore", .bool _root_.Bool.false),
      ("presentAfter", .bool _root_.Bool.true),
      ("chosenValue", .uint 65535 0), ("bucketSize", .uint (2 ^ 64 - 1) 3)] do
    throw "guarded insertDefault did not insert the typed zero for a missing nested record key"
  let (existingOutputs, state) ← nestedRecordMapDefaultsApply 1 _root_.Bool.true 513
    _root_.Bool.true state
  unless nestedRecordMapDefaultsOutputsMatch existingOutputs [
      ("presentBefore", .bool _root_.Bool.true),
      ("presentAfter", .bool _root_.Bool.true),
      ("chosenValue", .uint 65535 0), ("bucketSize", .uint (2 ^ 64 - 1) 3)] do
    throw "guarded insertDefault did not replace the existing nested record-key value"
  let (inactiveOutputs, state) ← nestedRecordMapDefaultsApply 1 _root_.Bool.false 513
    _root_.Bool.false state
  unless nestedRecordMapDefaultsOutputsMatch inactiveOutputs [
      ("presentBefore", .bool _root_.Bool.true),
      ("presentAfter", .bool _root_.Bool.true),
      ("chosenValue", .uint 65535 22), ("bucketSize", .uint (2 ^ 64 - 1) 3)] do
    throw "inactive insertDefault changed the existing nested record-key value"
  let (unconditionalOutputs, state) ← nestedRecordMapDefaultsApplyUnconditional 2
    _root_.Bool.true 513 state
  unless nestedRecordMapDefaultsOutputsMatch unconditionalOutputs [
      ("presentBefore", .bool _root_.Bool.true),
      ("presentAfter", .bool _root_.Bool.true),
      ("chosenValue", .uint 65535 0), ("bucketSize", .uint (2 ^ 64 - 1) 1)] do
    throw "unguarded insertDefault did not replace the existing sibling value"
  unless state == {trees := [("memos", .map [
      (nestedRecordMapDefaultsOwner 2, .map [
        (nestedRecordMapDefaultsKey _root_.Bool.true 513, .scalar (.uint 65535 0))]),
      (nestedRecordMapDefaultsOwner 1, .map [
        (nestedRecordMapDefaultsKey _root_.Bool.true 513, .scalar (.uint 65535 0)),
        (nestedRecordMapDefaultsKey _root_.Bool.true 514, .scalar (.uint 65535 0)),
        (nestedRecordMapDefaultsKey _root_.Bool.false 513, .scalar (.uint 65535 22))])])]} do
    throw "nested record-key defaults changed a sibling key or owner"
  pure _root_.Bool.true

#guard match nestedRecordMapDefaultsScenario with
  | .ok _root_.Bool.true => _root_.Bool.true
  | _ => _root_.Bool.false
