import Noctium.Frontend
import Noctium.Backend.Impact
import Noctium.Backend.Zkir

open scoped Noctium
open Noctium

noctium_circuit nestedFixedByteRecordMapOwnerInputs where
  public owner : Bytes 32
end

noctium_circuit nestedFixedByteRecordMapExerciseInputs where
  public owner : Bytes 32
  public tag : Bytes 1
  public firstId : Bytes 33
  public lateId : Bytes 33
  public firstScalar : UInt 16
  public lateScalar : UInt 16
  public firstAccepted : Bool
  public firstCode : UInt 16
  public lateAccepted : Bool
  public lateCode : UInt 16
end

noctium_circuit nestedFixedByteRecordMapInspectInputs where
  public owner : Bytes 32
  public tag : Bytes 1
  public firstId : Bytes 33
  public lateId : Bytes 33
end

noctium_contract NestedFixedByteRecordMap where
  tree scalars : Bytes 32 => struct ScalarKey {
    tag : Bytes 1
    id : Bytes 33
  } => UInt 16

  tree records : Bytes 32 => struct RecordKey {
    tag : Bytes 1
    id : Bytes 33
  } => struct Receipt {
    accepted : Bool
    code : UInt 16
  }

  entry initializeOwner uses nestedFixedByteRecordMapOwnerInputs where
    insert scalars[owner] := emptyMap
    insert records[owner] := emptyMap
  end

  entry exercise uses nestedFixedByteRecordMapExerciseInputs where
    member scalars[owner][fields(disclose(tag), disclose(firstId))] as scalarFirstBefore
    member scalars[owner][fields(disclose(tag), disclose(lateId))] as scalarLateBefore
    insert scalars[owner][fields(disclose(tag), disclose(firstId))] := disclose(firstScalar)
    insert scalars[owner][fields(disclose(tag), disclose(lateId))] := disclose(lateScalar)
    member scalars[owner][fields(disclose(tag), disclose(firstId))] as scalarFirstInserted
    member scalars[owner][fields(disclose(tag), disclose(lateId))] as scalarLateInserted
    read scalars[owner][fields(disclose(tag), disclose(firstId))] as scalarFirstValue
    read scalars[owner][fields(disclose(tag), disclose(lateId))] as scalarLateValue

    member records[owner][fields(disclose(tag), disclose(firstId))] as recordFirstBefore
    member records[owner][fields(disclose(tag), disclose(lateId))] as recordLateBefore
    insert records[owner][fields(disclose(tag), disclose(firstId))] :=
      fields(disclose(firstAccepted), disclose(firstCode))
    insert records[owner][fields(disclose(tag), disclose(lateId))] :=
      fields(disclose(lateAccepted), disclose(lateCode))
    member records[owner][fields(disclose(tag), disclose(firstId))] as recordFirstInserted
    member records[owner][fields(disclose(tag), disclose(lateId))] as recordLateInserted
    read records[owner][fields(disclose(tag), disclose(firstId))] as recordFirstValue
    read records[owner][fields(disclose(tag), disclose(lateId))] as recordLateValue

    remove scalars[owner][fields(disclose(tag), disclose(firstId))]
    remove records[owner][fields(disclose(tag), disclose(firstId))]
    member scalars[owner][fields(disclose(tag), disclose(firstId))] as scalarFirstAfter
    member scalars[owner][fields(disclose(tag), disclose(lateId))] as scalarLateAfter
    member records[owner][fields(disclose(tag), disclose(firstId))] as recordFirstAfter
    member records[owner][fields(disclose(tag), disclose(lateId))] as recordLateAfter
    read scalars[owner][fields(disclose(tag), disclose(lateId))] as scalarRetained
    read records[owner][fields(disclose(tag), disclose(lateId))] as recordRetained

    return scalarBeforeFirst : Bool := scalarFirstBefore
    return scalarBeforeLate : Bool := scalarLateBefore
    return scalarInsertedFirst : Bool := scalarFirstInserted
    return scalarInsertedLate : Bool := scalarLateInserted
    return scalarValueFirst : UInt 16 := scalarFirstValue
    return scalarValueLate : UInt 16 := scalarLateValue
    return recordBeforeFirst : Bool := recordFirstBefore
    return recordBeforeLate : Bool := recordLateBefore
    return recordInsertedFirst : Bool := recordFirstInserted
    return recordInsertedLate : Bool := recordLateInserted
    return recordAcceptedFirst : Bool := recordFirstValue_accepted
    return recordCodeFirst : UInt 16 := recordFirstValue_code
    return recordAcceptedLate : Bool := recordLateValue_accepted
    return recordCodeLate : UInt 16 := recordLateValue_code
    return scalarAfterFirst : Bool := scalarFirstAfter
    return scalarAfterLate : Bool := scalarLateAfter
    return recordAfterFirst : Bool := recordFirstAfter
    return recordAfterLate : Bool := recordLateAfter
    return scalarRetainedValue : UInt 16 := scalarRetained
    return recordRetainedAccepted : Bool := recordRetained_accepted
    return recordRetainedCode : UInt 16 := recordRetained_code
  end

  entry inspect uses nestedFixedByteRecordMapInspectInputs where
    member scalars[owner][fields(disclose(tag), disclose(firstId))] as scalarFirst
    member scalars[owner][fields(disclose(tag), disclose(lateId))] as scalarLate
    read scalars[owner][fields(disclose(tag), disclose(lateId))] as scalarValue
    member records[owner][fields(disclose(tag), disclose(firstId))] as recordFirst
    member records[owner][fields(disclose(tag), disclose(lateId))] as recordLate
    read records[owner][fields(disclose(tag), disclose(lateId))] as recordValue
    return scalarFirstPresent : Bool := scalarFirst
    return scalarLatePresent : Bool := scalarLate
    return scalarLateValue : UInt 16 := scalarValue
    return recordFirstPresent : Bool := recordFirst
    return recordLatePresent : Bool := recordLate
    return recordLateAccepted : Bool := recordValue_accepted
    return recordLateCode : UInt 16 := recordValue_code
  end
end

private def nestedFixedByteRecordMapEntry (name : String) : Entrypoint :=
  (NestedFixedByteRecordMap.entrypoints.find? (·.name == name)).getD
    {name := "missing", circuit := {name := "missing"}}

private def nestedFixedByteRecordMapContext : EvalContext := {
  modulus := Field.modulus
  poseidon2 := fun _ _ _ => .error "unused by nested fixed-byte record Map fixture"
}

private def nestedFixedByteRecordMapKeyEnvironment : Types.CompositeEnv := {
  structures := [{
    id := "NestedFixedByteRecordMap.Key"
    fields := [
      {name := "tag", type := .bytes 1},
      {name := "id", type := .bytes 33}
    ]
  }]
}

private def nestedFixedByteRecordMapValueEnvironment : Types.CompositeEnv := {
  structures := [{
    id := "NestedFixedByteRecordMap.BadValue"
    fields := [{name := "payload", type := .bytes 1}]
  }]
}

private def nestedFixedByteRecordMapOwner (byte : Nat) : Value :=
  .bytes 32 (List.replicate 32 byte)

private def nestedFixedByteRecordMapId (last : Nat) : List Nat :=
  List.replicate 32 3 ++ [last]

private def nestedFixedByteRecordMapKey (tag last : Nat) : Value :=
  .record [(.bytes 1, [tag]), (.bytes 33, nestedFixedByteRecordMapId last)]

private def nestedFixedByteRecordMapReceipt (accepted : _root_.Bool) (code : Nat) : LedgerValue :=
  .composite (.structure "NestedFixedByteRecordMap.Receipt")
    [.bool accepted, .uint 65535 code]

private def nestedFixedByteRecordMapInitial : LedgerState := {
  trees := [("scalars", .map []), ("records", .map [])]
}

private def nestedFixedByteRecordMapInitialize (owner : Nat) (state : LedgerState) :=
  (nestedFixedByteRecordMapEntry "initializeOwner").run nestedFixedByteRecordMapContext
    [("owner", nestedFixedByteRecordMapOwner owner)] state

private def nestedFixedByteRecordMapExercise (owner : Nat) (firstScalar lateScalar : Nat)
    (firstAccepted : _root_.Bool) (firstCode : Nat)
    (lateAccepted : _root_.Bool) (lateCode : Nat) (state : LedgerState) :=
  (nestedFixedByteRecordMapEntry "exercise").run nestedFixedByteRecordMapContext [
    ("owner", nestedFixedByteRecordMapOwner owner),
    ("tag", .bytes 1 [7]),
    ("firstId", .bytes 33 (nestedFixedByteRecordMapId 3)),
    ("lateId", .bytes 33 (nestedFixedByteRecordMapId 4)),
    ("firstScalar", .uint 65535 firstScalar),
    ("lateScalar", .uint 65535 lateScalar),
    ("firstAccepted", .bool firstAccepted),
    ("firstCode", .uint 65535 firstCode),
    ("lateAccepted", .bool lateAccepted),
    ("lateCode", .uint 65535 lateCode)] state

private def nestedFixedByteRecordMapInspect (owner : Nat) (state : LedgerState) :=
  (nestedFixedByteRecordMapEntry "inspect").run nestedFixedByteRecordMapContext [
    ("owner", nestedFixedByteRecordMapOwner owner),
    ("tag", .bytes 1 [7]),
    ("firstId", .bytes 33 (nestedFixedByteRecordMapId 3)),
    ("lateId", .bytes 33 (nestedFixedByteRecordMapId 4))] state

private def nestedFixedByteRecordMapOutputsMatch (outputs : List (String × Value))
    (expected : List (String × Value)) : _root_.Bool :=
  expected.all fun (name, value) => outputs.lookup name == some value

private def nestedFixedByteRecordMapScenario : Except String _root_.Bool := do
  let (_, state) ← nestedFixedByteRecordMapInitialize 1 nestedFixedByteRecordMapInitial
  let (_, state) ← nestedFixedByteRecordMapInitialize 2 state
  let (first, state) ← nestedFixedByteRecordMapExercise 1 101 303 _root_.Bool.true 101
    _root_.Bool.false 303 state
  unless nestedFixedByteRecordMapOutputsMatch first [
      ("scalarBeforeFirst", .bool _root_.Bool.false),
      ("scalarBeforeLate", .bool _root_.Bool.false),
      ("scalarInsertedFirst", .bool _root_.Bool.true),
      ("scalarInsertedLate", .bool _root_.Bool.true),
      ("scalarValueFirst", .uint 65535 101),
      ("scalarValueLate", .uint 65535 303),
      ("recordBeforeFirst", .bool _root_.Bool.false),
      ("recordBeforeLate", .bool _root_.Bool.false),
      ("recordInsertedFirst", .bool _root_.Bool.true),
      ("recordInsertedLate", .bool _root_.Bool.true),
      ("recordAcceptedFirst", .bool _root_.Bool.true),
      ("recordCodeFirst", .uint 65535 101),
      ("recordAcceptedLate", .bool _root_.Bool.false),
      ("recordCodeLate", .uint 65535 303),
      ("scalarAfterFirst", .bool _root_.Bool.false),
      ("scalarAfterLate", .bool _root_.Bool.true),
      ("recordAfterFirst", .bool _root_.Bool.false),
      ("recordAfterLate", .bool _root_.Bool.true),
      ("scalarRetainedValue", .uint 65535 303),
      ("recordRetainedAccepted", .bool _root_.Bool.false),
      ("recordRetainedCode", .uint 65535 303)] do
    throw "nested fixed-byte record Map insertion or removal returned the wrong value"
  let (second, state) ← nestedFixedByteRecordMapExercise 2 707 909 _root_.Bool.false 707
    _root_.Bool.true 909 state
  unless nestedFixedByteRecordMapOutputsMatch second [
      ("scalarBeforeFirst", .bool _root_.Bool.false),
      ("scalarBeforeLate", .bool _root_.Bool.false),
      ("recordBeforeFirst", .bool _root_.Bool.false),
      ("recordBeforeLate", .bool _root_.Bool.false),
      ("scalarValueFirst", .uint 65535 707),
      ("scalarValueLate", .uint 65535 909),
      ("recordAcceptedFirst", .bool _root_.Bool.false),
      ("recordCodeFirst", .uint 65535 707),
      ("recordAcceptedLate", .bool _root_.Bool.true),
      ("recordCodeLate", .uint 65535 909),
      ("scalarAfterFirst", .bool _root_.Bool.false),
      ("scalarAfterLate", .bool _root_.Bool.true),
      ("recordAfterFirst", .bool _root_.Bool.false),
      ("recordAfterLate", .bool _root_.Bool.true),
      ("scalarRetainedValue", .uint 65535 909),
      ("recordRetainedAccepted", .bool _root_.Bool.true),
      ("recordRetainedCode", .uint 65535 909)] do
    throw "second parent did not keep an independent nested fixed-byte record Map"
  let (firstParent, state) ← nestedFixedByteRecordMapInspect 1 state
  unless nestedFixedByteRecordMapOutputsMatch firstParent [
      ("scalarFirstPresent", .bool _root_.Bool.false),
      ("scalarLatePresent", .bool _root_.Bool.true),
      ("scalarLateValue", .uint 65535 303),
      ("recordFirstPresent", .bool _root_.Bool.false),
      ("recordLatePresent", .bool _root_.Bool.true),
      ("recordLateAccepted", .bool _root_.Bool.false),
      ("recordLateCode", .uint 65535 303)] do
    throw "writing the second parent changed the first parent's nested Map values"
  let (secondParent, _) ← nestedFixedByteRecordMapInspect 2 state
  unless nestedFixedByteRecordMapOutputsMatch secondParent [
      ("scalarFirstPresent", .bool _root_.Bool.false),
      ("scalarLatePresent", .bool _root_.Bool.true),
      ("scalarLateValue", .uint 65535 909),
      ("recordFirstPresent", .bool _root_.Bool.false),
      ("recordLatePresent", .bool _root_.Bool.true),
      ("recordLateAccepted", .bool _root_.Bool.true),
      ("recordLateCode", .uint 65535 909)] do
    throw "nested Map lookup returned a value from the wrong parent bucket"
  let expected : LedgerState := {
    trees := [
      ("records", .map [
        (nestedFixedByteRecordMapOwner 2, .map [
          (nestedFixedByteRecordMapKey 7 4,
            nestedFixedByteRecordMapReceipt _root_.Bool.true 909)]),
        (nestedFixedByteRecordMapOwner 1, .map [
          (nestedFixedByteRecordMapKey 7 4,
            nestedFixedByteRecordMapReceipt _root_.Bool.false 303)])]),
      ("scalars", .map [
        (nestedFixedByteRecordMapOwner 2, .map [
          (nestedFixedByteRecordMapKey 7 4, .scalar (.uint 65535 909))]),
        (nestedFixedByteRecordMapOwner 1, .map [
          (nestedFixedByteRecordMapKey 7 4, .scalar (.uint 65535 303))])])]
  }
  unless state == expected do
    throw "nested fixed-byte record Map state differs from the expected parent buckets"
  pure _root_.Bool.true

#guard (NestedFixedByteRecordMap.validate Capabilities.source).isOk
#guard ((nestedFixedByteRecordMapEntry "initializeOwner").validate
  Capabilities.source NestedFixedByteRecordMap.state).isOk
#guard ((nestedFixedByteRecordMapEntry "exercise").validate
  Capabilities.source NestedFixedByteRecordMap.state).isOk
#guard ((nestedFixedByteRecordMapEntry "inspect").validate
  Capabilities.source NestedFixedByteRecordMap.state).isOk
#guard (Backend.Impact.lower NestedFixedByteRecordMap.state
  (nestedFixedByteRecordMapEntry "exercise")).isOk
#guard (Backend.Zkir.lowerEntrypoint NestedFixedByteRecordMap.state
  (nestedFixedByteRecordMapEntry "exercise")).isOk
#guard match NestedFixedByteRecordMap.state with
  | [
      {kind := .tree (.map (.bytes 32) (.recordMapKey keyEnvironment keyType (.uint 65535))), ..},
      {kind := .tree (.map (.bytes 32) (.recordMapComposite recordKeyEnvironment recordKeyType
        valueEnvironment valueType)), ..}] =>
      (LedgerValueType.recordMapKeyFieldsAtDepth keyEnvironment keyType 1).isOk &&
      (LedgerValueType.recordMapKeyFieldsAtDepth recordKeyEnvironment recordKeyType 1).isOk &&
      (LedgerValueType.ledgerRecordWriteFields valueEnvironment valueType).isOk
  | _ => _root_.Bool.false

#guard match LedgerValueType.validate Capabilities.source
    (.map (.bytes 32) (.map (.bytes 32) (.recordMapKey nestedFixedByteRecordMapKeyEnvironment
      (.structure "NestedFixedByteRecordMap.Key") (.uint 65535)))) with
  | .error _ => _root_.Bool.true
  | .ok _ => _root_.Bool.false

#guard match LedgerValueType.validate Capabilities.source
    (.map (.bytes 32) (.recordMapComposite nestedFixedByteRecordMapKeyEnvironment
      (.structure "NestedFixedByteRecordMap.Key") nestedFixedByteRecordMapValueEnvironment
      (.structure "NestedFixedByteRecordMap.BadValue"))) with
  | .error _ => _root_.Bool.true
  | .ok _ => _root_.Bool.false

#guard match nestedFixedByteRecordMapScenario with
  | .ok _root_.Bool.true => _root_.Bool.true
  | _ => _root_.Bool.false

#guard match (nestedFixedByteRecordMapEntry "exercise").run nestedFixedByteRecordMapContext [
    ("owner", nestedFixedByteRecordMapOwner 1),
    ("tag", .bytes 1 [7]),
    ("firstId", .bytes 33 (nestedFixedByteRecordMapId 3)),
    ("lateId", .bytes 32 (nestedFixedByteRecordMapId 4)),
    ("firstScalar", .uint 65535 101), ("lateScalar", .uint 65535 303),
    ("firstAccepted", .bool _root_.Bool.true), ("firstCode", .uint 65535 101),
    ("lateAccepted", .bool _root_.Bool.false), ("lateCode", .uint 65535 303)]
    nestedFixedByteRecordMapInitial with
  | .error _ => _root_.Bool.true
  | .ok _ => _root_.Bool.false
