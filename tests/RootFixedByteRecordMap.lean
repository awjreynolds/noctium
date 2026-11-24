import Noctium.Frontend
import Noctium.Backend.Impact
import Noctium.Backend.Zkir

open scoped Noctium
open Noctium

noctium_circuit rootFixedByteRecordMapInputs where
  public tag : Bytes 1
  public firstId : Bytes 33
  public lateId : Bytes 33
  public firstValue : UInt 16
  public lateValue : UInt 16
end

noctium_contract RootFixedByteRecordMap where
  tree memos : struct Key {
    tag : Bytes 1
    id : Bytes 33
  } => UInt 16

  entry update uses rootFixedByteRecordMapInputs where
    insert memos[fields(disclose(tag), disclose(firstId))] := disclose(firstValue)
    insert memos[fields(disclose(tag), disclose(lateId))] := disclose(lateValue)
    member memos[fields(disclose(tag), disclose(firstId))] as firstBefore
    member memos[fields(disclose(tag), disclose(lateId))] as lateBefore
    read memos[fields(disclose(tag), disclose(firstId))] as firstStored
    read memos[fields(disclose(tag), disclose(lateId))] as lateStored
    remove memos[fields(disclose(tag), disclose(firstId))]
    member memos[fields(disclose(tag), disclose(firstId))] as firstAfter
    member memos[fields(disclose(tag), disclose(lateId))] as lateAfter
    read memos[fields(disclose(tag), disclose(lateId))] as retainedValue
    return first : Bool := firstBefore
    return late : Bool := lateBefore
    return firstValueResult : UInt 16 := firstStored
    return lateValueResult : UInt 16 := lateStored
    return firstRemaining : Bool := firstAfter
    return lateRemaining : Bool := lateAfter
    return retained : UInt 16 := retainedValue
  end
end

private def rootFixedByteRecordMapEntry : Entrypoint :=
  (RootFixedByteRecordMap.entrypoints.find? (·.name == "update")).getD
    {name := "missing", circuit := {name := "missing"}}

private def rootFixedByteRecordMapContext : EvalContext := {
  modulus := Field.modulus
  poseidon2 := fun _ _ _ => .error "unused by fixed-byte record Map fixture"
}

private def byteRange (length : Nat) (fill : Nat) : List Nat := List.replicate length fill

private def rootFixedByteRecordMapRun (tag : List Nat) (firstId lateId : List Nat)
    (firstValue lateValue : Nat) :=
  rootFixedByteRecordMapEntry.run rootFixedByteRecordMapContext [
    ("tag", .bytes 1 tag), ("firstId", .bytes 33 firstId),
    ("lateId", .bytes 33 lateId),
    ("firstValue", .uint 65535 firstValue), ("lateValue", .uint 65535 lateValue)] {
      trees := [("memos", .map [])]
    }

#guard (RootFixedByteRecordMap.validate Capabilities.source).isOk
#guard (rootFixedByteRecordMapEntry.validate Capabilities.source RootFixedByteRecordMap.state).isOk
#guard (Backend.Impact.lower RootFixedByteRecordMap.state rootFixedByteRecordMapEntry).isOk
#guard (Backend.Zkir.lowerEntrypoint RootFixedByteRecordMap.state rootFixedByteRecordMapEntry).isOk
#guard match RootFixedByteRecordMap.state with
  | [{kind := .tree (.recordMapKey environment type valueTy), ..}] =>
      (LedgerValueType.recordMapKeyFields environment type).isOk &&
      (match LedgerValueType.ledgerRecordWriteFields environment type with
        | .error _ => _root_.Bool.true
        | .ok _ => _root_.Bool.false) &&
      (match LedgerValueType.validate Capabilities.source
        (.map (.bytes 32) (.recordMapKey environment type valueTy)) with
        | .ok _ => _root_.Bool.true
        | .error _ => _root_.Bool.false)
  | _ => _root_.Bool.false

#guard match rootFixedByteRecordMapRun [7] (byteRange 33 3) (byteRange 32 3 ++ [4]) 101 303 with
  | .ok (outputs, state) =>
      outputs.lookup "first" == some (.bool _root_.Bool.true) &&
      outputs.lookup "late" == some (.bool _root_.Bool.true) &&
      outputs.lookup "firstValueResult" == some (.uint 65535 101) &&
      outputs.lookup "lateValueResult" == some (.uint 65535 303) &&
      outputs.lookup "firstRemaining" == some (.bool _root_.Bool.false) &&
      outputs.lookup "lateRemaining" == some (.bool _root_.Bool.true) &&
      outputs.lookup "retained" == some (.uint 65535 303) &&
      state.trees.lookup "memos" == some (.map [
        (.record [(.bytes 1, [7]), (.bytes 33, byteRange 32 3 ++ [4])],
          .scalar (.uint 65535 303))])
  | .error _ => _root_.Bool.false

#guard match rootFixedByteRecordMapEntry.run rootFixedByteRecordMapContext [
    ("tag", .bytes 1 [7]), ("firstId", .bytes 33 (byteRange 33 3)),
    ("lateId", .bytes 32 (byteRange 32 3)),
    ("firstValue", .uint 65535 101), ("lateValue", .uint 65535 303)] {
      trees := [("memos", .map [])]
    } with
  | .error _ => _root_.Bool.true
  | .ok _ => _root_.Bool.false
