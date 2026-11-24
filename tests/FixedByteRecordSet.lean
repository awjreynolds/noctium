import Noctium.Frontend
import Noctium.Backend.Impact
import Noctium.Backend.Zkir

open scoped Noctium
open Noctium

noctium_circuit fixedByteRecordSetInputs where
  public owner : Bytes 32
  public siblingOwner : Bytes 32
  public tag : Bytes 1
  public firstId : Bytes 33
  public lateId : Bytes 33
  public missingKeyId : Bytes 33
end

noctium_contract FixedByteRecordSet where
  tree buckets : Bytes32 => Set struct Key {
    tag : Bytes 1
    id : Bytes 33
  }

  entry update uses fixedByteRecordSetInputs where
    insert buckets[owner] := emptyMap
    insert buckets[siblingOwner] := emptyMap
    insert buckets[owner][fields(disclose(tag), disclose(firstId))]
    insert buckets[owner][fields(disclose(tag), disclose(lateId))]
    insert buckets[siblingOwner][fields(disclose(tag), disclose(firstId))]
    member buckets[owner][fields(disclose(tag), disclose(firstId))] as firstPresent
    member buckets[owner][fields(disclose(tag), disclose(lateId))] as latePresent
    member buckets[owner][fields(disclose(tag), disclose(missingKeyId))] as missingKeyPresent
    member buckets[siblingOwner][fields(disclose(tag), disclose(firstId))] as siblingPresent
    size buckets[owner] as bucketSize
    size buckets[siblingOwner] as siblingSize
    return first : Bool := firstPresent
    return late : Bool := latePresent
    return missingKey : Bool := missingKeyPresent
    return sibling : Bool := siblingPresent
    return count : UInt 64 := bucketSize
    return siblingCount : UInt 64 := siblingSize
  end
end

private def fixedByteRecordSetEntry : Entrypoint :=
  (FixedByteRecordSet.entrypoints.find? (·.name == "update")).getD
    {name := "missing", circuit := {name := "missing"}}

private def fixedByteRecordSetContext : EvalContext := {
  modulus := Field.modulus
  poseidon2 := fun _ _ _ => .error "unused by fixed-byte record Set fixture"
}

private def byteRange (length : Nat) (fill : Nat) : List Nat := List.replicate length fill

private def recordSetHasMembers (value : LedgerValue) (expected : List Value) : _root_.Bool :=
  match value with
  | .map entries => entries.length == expected.length &&
      expected.all (fun key => entries.contains (key, .null))
  | _ => _root_.Bool.false

private def fixedByteRecordSetRun : Except String (List (String × Value) × LedgerState) :=
  fixedByteRecordSetEntry.run fixedByteRecordSetContext [
    ("owner", .bytes 32 (byteRange 32 1)),
    ("siblingOwner", .bytes 32 (byteRange 32 2)),
    ("tag", .bytes 1 [7]),
    ("firstId", .bytes 33 (byteRange 33 3)),
    ("lateId", .bytes 33 (byteRange 32 3 ++ [4])),
    ("missingKeyId", .bytes 33 (byteRange 32 3 ++ [5]))] {
      trees := [("buckets", .map [])]
    }

#guard (FixedByteRecordSet.validate Capabilities.source).isOk
#guard (fixedByteRecordSetEntry.validate Capabilities.source FixedByteRecordSet.state).isOk
#guard (Backend.Zkir.lowerEntrypoint FixedByteRecordSet.state fixedByteRecordSetEntry).isOk

#guard match fixedByteRecordSetRun with
  | .ok (outputs, state) =>
      outputs.lookup "first" == some (.bool _root_.Bool.true) &&
      outputs.lookup "late" == some (.bool _root_.Bool.true) &&
      outputs.lookup "missingKey" == some (.bool _root_.Bool.false) &&
      outputs.lookup "sibling" == some (.bool _root_.Bool.true) &&
      outputs.lookup "count" == some (.uint (2 ^ 64 - 1) 2) &&
      outputs.lookup "siblingCount" == some (.uint (2 ^ 64 - 1) 1) &&
      match state.trees.lookup "buckets" with
      | some (.map buckets) =>
          let selected := buckets.find? (fun pair => pair.1 == .bytes 32 (byteRange 32 1))
          let sibling := buckets.find? (fun pair => pair.1 == .bytes 32 (byteRange 32 2))
          buckets.length == 2 &&
          (match selected with
          | some (_, value) => recordSetHasMembers value [
              .record [(.bytes 1, [7]), (.bytes 33, byteRange 33 3)],
              .record [(.bytes 1, [7]), (.bytes 33, byteRange 32 3 ++ [4])]]
          | none => _root_.Bool.false) &&
          (match sibling with
          | some (_, value) => recordSetHasMembers value [
              .record [(.bytes 1, [7]), (.bytes 33, byteRange 33 3)]]
          | none => _root_.Bool.false)
      | _ => _root_.Bool.false
  | .error _ => _root_.Bool.false
