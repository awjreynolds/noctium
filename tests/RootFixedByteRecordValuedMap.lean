import Noctium.Frontend
import Noctium.Backend.Impact
import Noctium.Backend.Zkir

open scoped Noctium
open Noctium

noctium_circuit rootFixedByteRecordValuedMapInputs where
  public tag : Bytes 1
  public firstId : Bytes 33
  public lateId : Bytes 33
  public firstAccepted : Bool
  public firstCode : UInt 16
  public lateAccepted : Bool
  public lateCode : UInt 16
end

noctium_contract RootFixedByteRecordValuedMap where
  tree receipts : struct Key {
    tag : Bytes 1
    id : Bytes 33
  } => struct Receipt {
    accepted : Bool
    code : UInt 16
  }

  entry update uses rootFixedByteRecordValuedMapInputs where
    insert receipts[fields(disclose(tag), disclose(firstId))] :=
      fields(disclose(firstAccepted), disclose(firstCode))
    insert receipts[fields(disclose(tag), disclose(lateId))] :=
      fields(disclose(lateAccepted), disclose(lateCode))
    member receipts[fields(disclose(tag), disclose(firstId))] as firstBefore
    member receipts[fields(disclose(tag), disclose(lateId))] as lateBefore
    read receipts[fields(disclose(tag), disclose(firstId))] as firstStored
    read receipts[fields(disclose(tag), disclose(lateId))] as lateStored
    remove receipts[fields(disclose(tag), disclose(firstId))]
    member receipts[fields(disclose(tag), disclose(firstId))] as firstAfter
    member receipts[fields(disclose(tag), disclose(lateId))] as lateAfter
    read receipts[fields(disclose(tag), disclose(lateId))] as retained
    return first : Bool := firstBefore
    return late : Bool := lateBefore
    return firstAcceptedResult : Bool := firstStored_accepted
    return firstCodeResult : UInt 16 := firstStored_code
    return lateAcceptedResult : Bool := lateStored_accepted
    return lateCodeResult : UInt 16 := lateStored_code
    return firstRemaining : Bool := firstAfter
    return lateRemaining : Bool := lateAfter
    return retainedAccepted : Bool := retained_accepted
    return retainedCode : UInt 16 := retained_code
  end
end

private def rootFixedByteRecordValuedMapEntry : Entrypoint :=
  (RootFixedByteRecordValuedMap.entrypoints.find? (·.name == "update")).getD
    {name := "missing", circuit := {name := "missing"}}

private def rootFixedByteRecordValuedMapContext : EvalContext := {
  modulus := Field.modulus
  poseidon2 := fun _ _ _ => .error "unused by fixed-byte record Map fixture"
}

private def byteRange (length : Nat) (fill : Nat) : List Nat := List.replicate length fill

private def rootFixedByteRecordValuedMapRun (tag : List Nat) (firstId lateId : List Nat)
    (firstAccepted : _root_.Bool) (firstCode : Nat)
    (lateAccepted : _root_.Bool) (lateCode : Nat) :=
  rootFixedByteRecordValuedMapEntry.run rootFixedByteRecordValuedMapContext [
    ("tag", .bytes 1 tag), ("firstId", .bytes 33 firstId),
    ("lateId", .bytes 33 lateId), ("firstAccepted", .bool firstAccepted),
    ("firstCode", .uint 65535 firstCode), ("lateAccepted", .bool lateAccepted),
    ("lateCode", .uint 65535 lateCode)] {
      trees := [("receipts", .map [])]
    }

private def fixedByteRecordMapValueEnvironment : Types.CompositeEnv := {
  structures := [{
    id := "FixedByteRecordMapValue"
    fields := [{name := "payload", type := .bytes 1}]
  }]
}

#guard (RootFixedByteRecordValuedMap.validate Capabilities.source).isOk
#guard (rootFixedByteRecordValuedMapEntry.validate
  Capabilities.source RootFixedByteRecordValuedMap.state).isOk
#guard (Backend.Impact.lower
  RootFixedByteRecordValuedMap.state rootFixedByteRecordValuedMapEntry).isOk
#guard (Backend.Zkir.lowerEntrypoint
  RootFixedByteRecordValuedMap.state rootFixedByteRecordValuedMapEntry).isOk
#guard match RootFixedByteRecordValuedMap.state with
  | [{kind := .tree (.recordMapComposite keyEnvironment keyType valueEnvironment valueType), ..}] =>
      (LedgerValueType.recordMapKeyFields keyEnvironment keyType).isOk &&
      (match LedgerValueType.ledgerRecordWriteFields keyEnvironment keyType with
        | .error _ => _root_.Bool.true
        | .ok _ => _root_.Bool.false) &&
      (match LedgerValueType.ledgerRecordWriteFields valueEnvironment valueType with
        | .ok fields => fields == [("accepted", .bool), ("code", .uint 65535)]
        | .error _ => _root_.Bool.false) &&
      (LedgerValueType.validate Capabilities.source
        (.recordMapComposite keyEnvironment keyType valueEnvironment valueType)).isOk &&
      (match LedgerValueType.validate Capabilities.source
        (.map (.bytes 32) (.recordMapComposite keyEnvironment keyType valueEnvironment valueType)) with
        | .error _ => _root_.Bool.true
        | .ok _ => _root_.Bool.false) &&
      (match LedgerValueType.validate Capabilities.source
        (.recordMapComposite keyEnvironment keyType fixedByteRecordMapValueEnvironment
          (.structure "FixedByteRecordMapValue")) with
        | .error _ => _root_.Bool.true
        | .ok _ => _root_.Bool.false)
  | _ => _root_.Bool.false

#guard match rootFixedByteRecordValuedMapRun [7] (byteRange 33 3)
    (byteRange 32 3 ++ [4]) _root_.Bool.true 101 _root_.Bool.false 303 with
  | .ok (outputs, state) =>
      outputs.lookup "first" == some (.bool _root_.Bool.true) &&
      outputs.lookup "late" == some (.bool _root_.Bool.true) &&
      outputs.lookup "firstAcceptedResult" == some (.bool _root_.Bool.true) &&
      outputs.lookup "firstCodeResult" == some (.uint 65535 101) &&
      outputs.lookup "lateAcceptedResult" == some (.bool _root_.Bool.false) &&
      outputs.lookup "lateCodeResult" == some (.uint 65535 303) &&
      outputs.lookup "firstRemaining" == some (.bool _root_.Bool.false) &&
      outputs.lookup "lateRemaining" == some (.bool _root_.Bool.true) &&
      outputs.lookup "retainedAccepted" == some (.bool _root_.Bool.false) &&
      outputs.lookup "retainedCode" == some (.uint 65535 303) &&
      state.trees.lookup "receipts" == some (.map [
        (.record [(.bytes 1, [7]), (.bytes 33, byteRange 32 3 ++ [4])],
          .composite (.structure "RootFixedByteRecordValuedMap.Receipt")
            [.bool _root_.Bool.false, .uint 65535 303])])
  | .error _ => _root_.Bool.false

#guard match rootFixedByteRecordValuedMapEntry.run rootFixedByteRecordValuedMapContext [
    ("tag", .bytes 1 [7]), ("firstId", .bytes 33 (byteRange 33 3)),
    ("lateId", .bytes 32 (byteRange 32 3 ++ [4])),
    ("firstAccepted", .bool _root_.Bool.true), ("firstCode", .uint 65535 101),
    ("lateAccepted", .bool _root_.Bool.false), ("lateCode", .uint 65535 303)] {
      trees := [("receipts", .map [])]
    } with
  | .error _ => _root_.Bool.true
  | .ok _ => _root_.Bool.false
