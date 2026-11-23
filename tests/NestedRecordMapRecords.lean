import Noctium.Frontend
import Noctium.Backend.Impact
import Noctium.Backend.Zkir
import Noctium.Compiler

open scoped Noctium
open Lean
open Noctium

noctium_circuit nestedRecordMapRecordsOwnerInputs where
  public owner : Bytes32
end

noctium_circuit nestedRecordMapRecordsUpdateInputs where
  public owner : Bytes32
  private active : Bool
  private amount : UInt 16
  private accepted : Bool
  private code : UInt 16
end

noctium_circuit nestedRecordMapRecordsLookupInputs where
  public owner : Bytes32
  private active : Bool
  private amount : UInt 16
  public shouldRead : Bool
end

noctium_circuit nestedRecordMapRecordsRemoveInputs where
  public owner : Bytes32
  private active : Bool
  private amount : UInt 16
  public removeIt : Bool
end

noctium_contract NestedRecordMapRecords where
  tree memos : Bytes32 => struct Memo {
    active : Bool
    amount : UInt 16
  } => struct Receipt {
    accepted : Bool
    code : UInt 16
  }

  entry initializeOwner uses nestedRecordMapRecordsOwnerInputs where
    insert memos[owner] := emptyMap
  end

  entry upsert uses nestedRecordMapRecordsUpdateInputs where
    member memos[owner][fields(disclose(active), disclose(amount))] as wasPresent
    insert memos[owner][fields(disclose(active), disclose(amount))] :=
      fields(disclose(accepted), disclose(code))
    member memos[owner][fields(disclose(active), disclose(amount))] as isPresent
    read memos[owner][fields(disclose(active), disclose(amount))] as stored
    return presentBefore : Bool := wasPresent
    return presentAfter : Bool := isPresent
    return storedAccepted : Bool := stored_accepted
    return storedCode : UInt 16 := stored_code
  end

  entry lookup uses nestedRecordMapRecordsLookupInputs where
    member memos[owner][fields(disclose(active), disclose(amount))] as hasMemo
    when shouldRead read memos[owner][fields(disclose(active), disclose(amount))] as found
    return present : Bool := hasMemo
    return storedAccepted : Bool := found_accepted
    return storedCode : UInt 16 := found_code
  end

  entry removeMemo uses nestedRecordMapRecordsRemoveInputs where
    member memos[owner][fields(disclose(active), disclose(amount))] as wasPresent
    when removeIt remove memos[owner][fields(disclose(active), disclose(amount))]
    member memos[owner][fields(disclose(active), disclose(amount))] as isPresent
    return presentBefore : Bool := wasPresent
    return presentAfter : Bool := isPresent
  end
end

private def nestedRecordMapRecordsEntry (name : String) : Entrypoint :=
  (NestedRecordMapRecords.entrypoints.find? (·.name == name)).getD
    {name := "missing", circuit := {name := "missing"}}

private def nestedRecordMapRecordsContext : EvalContext := {
  modulus := Field.modulus
  poseidon2 := fun _ _ _ => .error "unused by nested composite-valued record Map fixture"
}

private def nestedRecordMapRecordsOwner (byte : Nat) : Value :=
  .bytes 32 (List.replicate 32 byte)

private def nestedRecordMapRecordsKey (active : _root_.Bool) (amount : Nat) : Value :=
  .record [(.bool, [if active then 1 else 0]), (.uint 65535, [amount])]

private def nestedRecordMapRecordsReceipt (accepted : _root_.Bool) (code : Nat) : LedgerValue :=
  .composite (.structure "NestedRecordMapRecords.Receipt")
    [.bool accepted, .uint 65535 code]

private def nestedRecordMapRecordsInitial : LedgerState := {
  trees := [("memos", .map [])]
}

private def nestedRecordMapRecordsInitialize (owner : Nat) (state : LedgerState) :=
  (nestedRecordMapRecordsEntry "initializeOwner").run nestedRecordMapRecordsContext
    [("owner", nestedRecordMapRecordsOwner owner)] state

private def nestedRecordMapRecordsUpsert (owner : Nat) (active : _root_.Bool)
    (amount : Nat) (accepted : _root_.Bool) (code : Nat) (state : LedgerState) :=
  (nestedRecordMapRecordsEntry "upsert").run nestedRecordMapRecordsContext [
    ("owner", nestedRecordMapRecordsOwner owner),
    ("active", .bool active),
    ("amount", .uint 65535 amount),
    ("accepted", .bool accepted),
    ("code", .uint 65535 code)] state

private def nestedRecordMapRecordsLookup (owner : Nat) (active : _root_.Bool)
    (amount : Nat) (shouldRead : _root_.Bool) (state : LedgerState) :=
  (nestedRecordMapRecordsEntry "lookup").run nestedRecordMapRecordsContext [
    ("owner", nestedRecordMapRecordsOwner owner),
    ("active", .bool active),
    ("amount", .uint 65535 amount),
    ("shouldRead", .bool shouldRead)] state

private def nestedRecordMapRecordsRemove (owner : Nat) (active : _root_.Bool)
    (amount : Nat) (removeIt : _root_.Bool) (state : LedgerState) :=
  (nestedRecordMapRecordsEntry "removeMemo").run nestedRecordMapRecordsContext [
    ("owner", nestedRecordMapRecordsOwner owner),
    ("active", .bool active),
    ("amount", .uint 65535 amount),
    ("removeIt", .bool removeIt)] state

private def nestedRecordMapRecordsOutputsMatch (outputs : List (String × Value))
    (expected : List (String × Value)) : _root_.Bool :=
  expected.all fun (name, value) => outputs.lookup name == some value

private def nestedRecordMapRecordsExpected : LedgerState := {
  trees := [("memos", .map [
    (nestedRecordMapRecordsOwner 1, .map [
      (nestedRecordMapRecordsKey _root_.Bool.true 513,
        nestedRecordMapRecordsReceipt _root_.Bool.true 41)]),
    (nestedRecordMapRecordsOwner 2, .map [
      (nestedRecordMapRecordsKey _root_.Bool.true 513,
        nestedRecordMapRecordsReceipt _root_.Bool.true 99)])])]
}

private def nestedRecordMapRecordsScenario : Except String _root_.Bool := do
  let (_, state) ← nestedRecordMapRecordsInitialize 1 nestedRecordMapRecordsInitial
  let (_, state) ← nestedRecordMapRecordsInitialize 2 state
  let (first, state) ← nestedRecordMapRecordsUpsert 1 _root_.Bool.true 513 _root_.Bool.false 7 state
  unless nestedRecordMapRecordsOutputsMatch first [
      ("presentBefore", .bool _root_.Bool.false), ("presentAfter", .bool _root_.Bool.true),
      ("storedAccepted", .bool _root_.Bool.false), ("storedCode", .uint 65535 7)] do
    throw "first nested record-value insertion returned the wrong value"
  let (_, state) ← nestedRecordMapRecordsUpsert 1 _root_.Bool.false 513 _root_.Bool.false 22 state
  let (_, state) ← nestedRecordMapRecordsUpsert 2 _root_.Bool.true 513 _root_.Bool.true 99 state
  let (overwrite, state) ← nestedRecordMapRecordsUpsert 1 _root_.Bool.true 513 _root_.Bool.true 41 state
  unless nestedRecordMapRecordsOutputsMatch overwrite [
      ("presentBefore", .bool _root_.Bool.true), ("presentAfter", .bool _root_.Bool.true),
      ("storedAccepted", .bool _root_.Bool.true), ("storedCode", .uint 65535 41)] do
    throw "nested record Map overwrite returned the wrong value"
  let (selected, state) ← nestedRecordMapRecordsLookup 1 _root_.Bool.true 513 _root_.Bool.true state
  unless nestedRecordMapRecordsOutputsMatch selected [
      ("present", .bool _root_.Bool.true), ("storedAccepted", .bool _root_.Bool.true),
      ("storedCode", .uint 65535 41)] do
    throw "nested record Map read returned the wrong selected value"
  let (sibling, state) ← nestedRecordMapRecordsLookup 1 _root_.Bool.false 513 _root_.Bool.true state
  unless nestedRecordMapRecordsOutputsMatch sibling [
      ("present", .bool _root_.Bool.true), ("storedAccepted", .bool _root_.Bool.false),
      ("storedCode", .uint 65535 22)] do
    throw "nested record Map write changed a sibling record key"
  let (otherOwner, state) ← nestedRecordMapRecordsLookup 2 _root_.Bool.true 513 _root_.Bool.true state
  unless nestedRecordMapRecordsOutputsMatch otherOwner [
      ("present", .bool _root_.Bool.true), ("storedAccepted", .bool _root_.Bool.true),
      ("storedCode", .uint 65535 99)] do
    throw "nested record Map write changed a sibling owner"
  let (miss, state) ← nestedRecordMapRecordsLookup 1 _root_.Bool.true 514 _root_.Bool.false state
  unless nestedRecordMapRecordsOutputsMatch miss [
      ("present", .bool _root_.Bool.false), ("storedAccepted", .bool _root_.Bool.false),
      ("storedCode", .uint 65535 0)] do
    throw "changed nested record field did not produce a guarded miss"
  match nestedRecordMapRecordsLookup 1 _root_.Bool.true 514 _root_.Bool.true state with
  | .error _ => pure ()
  | .ok _ => throw "strict nested composite-valued Map read accepted a missing key"
  let (inactiveRemove, state) ← nestedRecordMapRecordsRemove 1 _root_.Bool.false 513 _root_.Bool.false state
  unless nestedRecordMapRecordsOutputsMatch inactiveRemove [
      ("presentBefore", .bool _root_.Bool.true), ("presentAfter", .bool _root_.Bool.true)] do
    throw "inactive nested record Map removal changed membership"
  let (removed, state) ← nestedRecordMapRecordsRemove 1 _root_.Bool.false 513 _root_.Bool.true state
  unless nestedRecordMapRecordsOutputsMatch removed [
      ("presentBefore", .bool _root_.Bool.true), ("presentAfter", .bool _root_.Bool.false)] do
    throw "nested record Map removal returned the wrong membership"
  let (retained, state) ← nestedRecordMapRecordsLookup 1 _root_.Bool.true 513 _root_.Bool.true state
  unless nestedRecordMapRecordsOutputsMatch retained [
      ("present", .bool _root_.Bool.true), ("storedAccepted", .bool _root_.Bool.true),
      ("storedCode", .uint 65535 41)] do
    throw "nested record Map removal changed the selected sibling key"
  let (retainedOwner, state) ← nestedRecordMapRecordsLookup 2 _root_.Bool.true 513 _root_.Bool.true state
  unless nestedRecordMapRecordsOutputsMatch retainedOwner [
      ("present", .bool _root_.Bool.true), ("storedAccepted", .bool _root_.Bool.true),
      ("storedCode", .uint 65535 99)] do
    throw "nested record Map removal changed a sibling owner"
  unless state == nestedRecordMapRecordsExpected do
    throw "nested composite-valued record Map state differs from expected buckets"
  pure _root_.Bool.true

#guard (NestedRecordMapRecords.validate Capabilities.source).isOk
#guard ((nestedRecordMapRecordsEntry "initializeOwner").validate
  Capabilities.source NestedRecordMapRecords.state).isOk
#guard ((nestedRecordMapRecordsEntry "upsert").validate
  Capabilities.source NestedRecordMapRecords.state).isOk
#guard ((nestedRecordMapRecordsEntry "lookup").validate
  Capabilities.source NestedRecordMapRecords.state).isOk
#guard ((nestedRecordMapRecordsEntry "removeMemo").validate
  Capabilities.source NestedRecordMapRecords.state).isOk
#guard (Disclosure.entrypoint (nestedRecordMapRecordsEntry "upsert")).isOk
#guard (Disclosure.entrypoint (nestedRecordMapRecordsEntry "lookup")).isOk
#guard (Disclosure.entrypoint (nestedRecordMapRecordsEntry "removeMemo")).isOk

#guard match Backend.Impact.lower NestedRecordMapRecords.state
    (nestedRecordMapRecordsEntry "upsert") with
  | .ok _ => _root_.Bool.true
  | .error _ => _root_.Bool.false

#guard match Backend.Zkir.lowerEntrypoint NestedRecordMapRecords.state
    (nestedRecordMapRecordsEntry "upsert") with
  | .ok _ => _root_.Bool.true
  | .error _ => _root_.Bool.false

#guard match nestedRecordMapRecordsScenario with
  | .ok _root_.Bool.true => _root_.Bool.true
  | _ => _root_.Bool.false
