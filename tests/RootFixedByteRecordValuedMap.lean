import Noctium.Frontend
import Noctium.Backend.Impact
import Noctium.Backend.Zkir

open scoped Noctium
open Noctium

noctium_circuit rootFixedByteRecordValuedMapInputs where
  public tag : Bytes 1
  public firstId : Bytes 33
  public lateId : Bytes 33
  public firstReceiptLabel : Bytes 1
  public firstReceiptDigest : Bytes 33
  public lateReceiptLabel : Bytes 1
  public lateReceiptDigest : Bytes 33
  public firstAccount : Bytes32
  public lateAccount : Bytes32
  public firstProfileLabel : Bytes 1
  public firstProfileDigest : Bytes 33
  public lateProfileLabel : Bytes 1
  public lateProfileDigest : Bytes 33
end

noctium_contract RootFixedByteRecordValuedMap where
  tree receipts : struct Key {
    tag : Bytes 1
    id : Bytes 33
  } => struct Receipt {
    label : Bytes 1
    digest : Bytes 33
  }

  tree profiles : Bytes32 => struct Profile {
    label : Bytes 1
    digest : Bytes 33
  }

  entry update uses rootFixedByteRecordValuedMapInputs where
    insert receipts[fields(disclose(tag), disclose(firstId))] :=
      fields(disclose(firstReceiptLabel), disclose(firstReceiptDigest))
    insert receipts[fields(disclose(tag), disclose(lateId))] :=
      fields(disclose(lateReceiptLabel), disclose(lateReceiptDigest))
    member receipts[fields(disclose(tag), disclose(firstId))] as firstBefore
    member receipts[fields(disclose(tag), disclose(lateId))] as lateBefore
    read receipts[fields(disclose(tag), disclose(firstId))] as firstStored
    read receipts[fields(disclose(tag), disclose(lateId))] as lateStored
    remove receipts[fields(disclose(tag), disclose(firstId))]
    member receipts[fields(disclose(tag), disclose(firstId))] as firstAfter
    member receipts[fields(disclose(tag), disclose(lateId))] as lateAfter
    read receipts[fields(disclose(tag), disclose(lateId))] as retained

    insert profiles[disclose(firstAccount)] :=
      fields(disclose(firstProfileLabel), disclose(firstProfileDigest))
    insert profiles[disclose(lateAccount)] :=
      fields(disclose(lateProfileLabel), disclose(lateProfileDigest))
    member profiles[disclose(firstAccount)] as firstProfileBefore
    member profiles[disclose(lateAccount)] as lateProfileBefore
    read profiles[disclose(firstAccount)] as firstProfileStored
    read profiles[disclose(lateAccount)] as lateProfileStored
    remove profiles[disclose(firstAccount)]
    member profiles[disclose(firstAccount)] as firstProfileAfter
    member profiles[disclose(lateAccount)] as lateProfileAfter
    read profiles[disclose(lateAccount)] as retainedProfile

    return first : Bool := firstBefore
    return late : Bool := lateBefore
    return firstStoredLabel : Bytes 1 := firstStored_label
    return firstStoredDigest : Bytes 33 := firstStored_digest
    return lateStoredLabel : Bytes 1 := lateStored_label
    return lateStoredDigest : Bytes 33 := lateStored_digest
    return firstRemaining : Bool := firstAfter
    return lateRemaining : Bool := lateAfter
    return retainedLabel : Bytes 1 := retained_label
    return retainedDigest : Bytes 33 := retained_digest

    return firstProfile : Bool := firstProfileBefore
    return lateProfile : Bool := lateProfileBefore
    return firstProfileStoredLabel : Bytes 1 := firstProfileStored_label
    return firstProfileStoredDigest : Bytes 33 := firstProfileStored_digest
    return lateProfileStoredLabel : Bytes 1 := lateProfileStored_label
    return lateProfileStoredDigest : Bytes 33 := lateProfileStored_digest
    return firstProfileRemaining : Bool := firstProfileAfter
    return lateProfileRemaining : Bool := lateProfileAfter
    return retainedProfileLabel : Bytes 1 := retainedProfile_label
    return retainedProfileDigest : Bytes 33 := retainedProfile_digest
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

private def rootFixedByteRecordValuedMapRun
    (tag firstId lateId : List Nat)
    (firstReceiptLabel : List Nat) (firstReceiptDigest : List Nat)
    (lateReceiptLabel : List Nat) (lateReceiptDigest : List Nat)
    (firstAccount lateAccount : List Nat)
    (firstProfileLabel : List Nat) (firstProfileDigest : List Nat)
    (lateProfileLabel : List Nat) (lateProfileDigest : List Nat) :=
  rootFixedByteRecordValuedMapEntry.run rootFixedByteRecordValuedMapContext [
    ("tag", .bytes 1 tag), ("firstId", .bytes 33 firstId),
    ("lateId", .bytes 33 lateId),
    ("firstReceiptLabel", .bytes 1 firstReceiptLabel),
    ("firstReceiptDigest", .bytes 33 firstReceiptDigest),
    ("lateReceiptLabel", .bytes 1 lateReceiptLabel),
    ("lateReceiptDigest", .bytes 33 lateReceiptDigest),
    ("firstAccount", .bytes 32 firstAccount), ("lateAccount", .bytes 32 lateAccount),
    ("firstProfileLabel", .bytes 1 firstProfileLabel),
    ("firstProfileDigest", .bytes 33 firstProfileDigest),
    ("lateProfileLabel", .bytes 1 lateProfileLabel),
    ("lateProfileDigest", .bytes 33 lateProfileDigest)] {
      trees := [("receipts", .map []), ("profiles", .map [])]
    }

private def fixedByteRecordValueEnvironment (id : String) : Types.CompositeEnv := {
  structures := [{
    id
    fields := [
      {name := "label", type := .bytes 1},
      {name := "digest", type := .bytes 33}]
  }]
}

private def fixedByteRecordKeyEnvironment : Types.CompositeEnv := {
  structures := [{
    id := "FixedByteRecordMapKey"
    fields := [
      {name := "tag", type := .bytes 1},
      {name := "id", type := .bytes 33}]
  }]
}

private def fixedByteRecordMapValueEnvironment := fixedByteRecordValueEnvironment "FixedByteMapValue"

private def qualifiedCoinRecordEnvironment : Types.CompositeEnv := {
  structures := [{
    id := "QualifiedCoin"
    fields := [
      {name := "nonce", type := .scalar (.bytes 32)},
      {name := "color", type := .scalar (.bytes 32)},
      {name := "value", type := .scalar (.uint (2 ^ 128 - 1))},
      {name := "mtIndex", type := .scalar (.uint (2 ^ 64 - 1))}]
  }]
}

#guard match LedgerValueType.mapRecordWriteFields qualifiedCoinRecordEnvironment
    (.structure "QualifiedCoin") with
  | .error message => message == "shielded coin records require their specialized write effect"
  | .ok _ => _root_.Bool.false

#guard (RootFixedByteRecordValuedMap.validate Capabilities.source).isOk
#guard (rootFixedByteRecordValuedMapEntry.validate
  Capabilities.source RootFixedByteRecordValuedMap.state).isOk
#guard (Backend.Impact.lower
  RootFixedByteRecordValuedMap.state rootFixedByteRecordValuedMapEntry).isOk
#guard (Backend.Zkir.lowerEntrypoint
  RootFixedByteRecordValuedMap.state rootFixedByteRecordValuedMapEntry).isOk
#guard match RootFixedByteRecordValuedMap.state with
  | [
      {kind := .tree (.recordMapComposite keyEnvironment keyType valueEnvironment valueType), ..},
      {kind := .tree (.map (.bytes 32) (.composite scalarEnvironment scalarType)), ..}] =>
      (LedgerValueType.recordMapKeyFields keyEnvironment keyType).isOk &&
      (match LedgerValueType.mapRecordWriteFields valueEnvironment valueType with
        | .ok fields => fields == [("label", .bytes 1), ("digest", .bytes 33)]
        | .error _ => _root_.Bool.false) &&
      (match LedgerValueType.ledgerRecordWriteFields valueEnvironment valueType with
        | .error _ => _root_.Bool.true
        | .ok _ => _root_.Bool.false) &&
      (LedgerValueType.validate Capabilities.source
        (.recordMapComposite keyEnvironment keyType valueEnvironment valueType)).isOk &&
      (LedgerValueType.mapRecordFields scalarEnvironment scalarType).isOk &&
      (LedgerValueType.validate Capabilities.source
        (.map (.bytes 32) (.composite scalarEnvironment scalarType))).isOk &&
      (LedgerValueType.validate Capabilities.source
        (.map (.bytes 32) (.map (.bytes 32)
          (.composite scalarEnvironment scalarType)))).isOk &&
      (match LedgerValueType.validate Capabilities.source
        (.map (.bytes 32) (.recordMapComposite keyEnvironment keyType valueEnvironment valueType)) with
        | .ok _ => _root_.Bool.true
        | .error _ => _root_.Bool.false) &&
      (match LedgerValueType.validate Capabilities.source
        (.map (.bytes 32) (.map (.bytes 32)
          (.recordMapComposite keyEnvironment keyType valueEnvironment valueType))) with
        | .error _ => _root_.Bool.true
        | .ok _ => _root_.Bool.false) &&
      (match LedgerValueType.recordMapKeyFieldsAtDepth keyEnvironment keyType 2 with
        | .error _ => _root_.Bool.true
        | .ok _ => _root_.Bool.false) &&
      (match LedgerValueType.mapRecordWriteFields fixedByteRecordMapValueEnvironment
        (.structure "FixedByteMapValue") with
        | .ok _ => _root_.Bool.true
        | .error _ => _root_.Bool.false)
  | _ => _root_.Bool.false

#guard match rootFixedByteRecordValuedMapRun [7] (byteRange 33 3)
    (byteRange 32 3 ++ [4]) [11] (byteRange 33 21) [12] (byteRange 33 22)
    (byteRange 32 5) (byteRange 32 6) [31] (byteRange 33 41) [32] (byteRange 33 42) with
  | .ok (outputs, state) =>
      outputs.lookup "first" == some (.bool _root_.Bool.true) &&
      outputs.lookup "late" == some (.bool _root_.Bool.true) &&
      outputs.lookup "firstStoredLabel" == some (.bytes 1 [11]) &&
      outputs.lookup "firstStoredDigest" == some (.bytes 33 (byteRange 33 21)) &&
      outputs.lookup "lateStoredLabel" == some (.bytes 1 [12]) &&
      outputs.lookup "lateStoredDigest" == some (.bytes 33 (byteRange 33 22)) &&
      outputs.lookup "firstRemaining" == some (.bool _root_.Bool.false) &&
      outputs.lookup "lateRemaining" == some (.bool _root_.Bool.true) &&
      outputs.lookup "retainedLabel" == some (.bytes 1 [12]) &&
      outputs.lookup "retainedDigest" == some (.bytes 33 (byteRange 33 22)) &&
      outputs.lookup "firstProfile" == some (.bool _root_.Bool.true) &&
      outputs.lookup "lateProfile" == some (.bool _root_.Bool.true) &&
      outputs.lookup "firstProfileStoredLabel" == some (.bytes 1 [31]) &&
      outputs.lookup "firstProfileStoredDigest" == some (.bytes 33 (byteRange 33 41)) &&
      outputs.lookup "lateProfileStoredLabel" == some (.bytes 1 [32]) &&
      outputs.lookup "lateProfileStoredDigest" == some (.bytes 33 (byteRange 33 42)) &&
      outputs.lookup "firstProfileRemaining" == some (.bool _root_.Bool.false) &&
      outputs.lookup "lateProfileRemaining" == some (.bool _root_.Bool.true) &&
      outputs.lookup "retainedProfileLabel" == some (.bytes 1 [32]) &&
      outputs.lookup "retainedProfileDigest" == some (.bytes 33 (byteRange 33 42)) &&
      state.trees.lookup "receipts" == some (.map [
        (.record [(.bytes 1, [7]), (.bytes 33, byteRange 32 3 ++ [4])],
          .composite (.structure "RootFixedByteRecordValuedMap.Receipt")
            [.bytes 1 [12], .bytes 33 (byteRange 33 22)])]) &&
      state.trees.lookup "profiles" == some (.map [
        (.bytes 32 (byteRange 32 6),
          .composite (.structure "RootFixedByteRecordValuedMap.Profile")
            [.bytes 1 [32], .bytes 33 (byteRange 33 42)])])
  | .error _ => _root_.Bool.false

#guard match rootFixedByteRecordValuedMapRun [7] (byteRange 33 3) (byteRange 32 3)
    [11] (byteRange 33 21) [12] (byteRange 33 22)
    (byteRange 32 5) (byteRange 32 6) [31] (byteRange 33 41) [32] (byteRange 33 42) with
  | .error _ => _root_.Bool.true
  | .ok _ => _root_.Bool.false

#guard match rootFixedByteRecordValuedMapRun [7] (byteRange 33 3) (byteRange 32 3 ++ [4])
    [11] (byteRange 33 21) [12] (byteRange 32 22)
    (byteRange 32 5) (byteRange 32 6) [31] (byteRange 33 41) [32] (byteRange 33 42) with
  | .error _ => _root_.Bool.true
  | .ok _ => _root_.Bool.false

#guard match rootFixedByteRecordValuedMapRun [7] (byteRange 33 3) (byteRange 32 3 ++ [4])
    [11] (byteRange 33 21) [12] (byteRange 33 22)
    (byteRange 32 5) (byteRange 32 6) [31] (byteRange 33 41) [32] (byteRange 32 42) with
  | .error _ => _root_.Bool.true
  | .ok _ => _root_.Bool.false
