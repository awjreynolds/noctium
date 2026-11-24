import Noctium.Frontend
import Noctium.Backend.Zkir

open scoped Noctium
open Noctium

noctium_circuit nestedFixedByteMapOwnerInputs where
  public owner : Bytes32
end

noctium_circuit nestedFixedByteMapExerciseInputs where
  public ownerA : Bytes32
  public ownerB : Bytes32
  public firstKey : Bytes32
  public siblingKey : Bytes32
  public inputFirstLabel : Bytes 1
  public inputFirstDigest : Bytes 33
  public inputSiblingLabel : Bytes 1
  public inputSiblingDigest : Bytes 33
  public inputOwnerBLabel : Bytes 1
  public inputOwnerBDigest : Bytes 33
  public replacementLabel : Bytes 1
  public replacementDigest : Bytes 33
end

noctium_circuit nestedFixedByteMapReadInputs where
  public ownerA : Bytes32
  public ownerB : Bytes32
  public firstKey : Bytes32
  public siblingKey : Bytes32
end

noctium_circuit nestedFixedByteMapMissingInputs where
  public owner : Bytes32
  public missingKey : Bytes32
end

noctium_contract NestedFixedByteMapRecordValues where
  tree profiles : Bytes32 => Bytes32 => struct Profile {
    label : Bytes 1
    digest : Bytes 33
  }

  entry initializeOwner uses nestedFixedByteMapOwnerInputs where
    member profiles[owner] as ownerPresent
    when eq(ownerPresent, false) insertDefault profiles[owner]
  end

  entry exercise uses nestedFixedByteMapExerciseInputs where
    member profiles[ownerA][firstKey] as hadFirst
    member profiles[ownerA][siblingKey] as hadSibling
    member profiles[ownerB][firstKey] as hadOwnerB
    insert profiles[ownerA][firstKey] := fields(inputFirstLabel, inputFirstDigest)
    insert profiles[ownerA][siblingKey] := fields(inputSiblingLabel, inputSiblingDigest)
    insert profiles[ownerB][firstKey] := fields(inputOwnerBLabel, inputOwnerBDigest)

    read profiles[ownerA][firstKey] as firstValue
    read profiles[ownerA][siblingKey] as siblingValue
    read profiles[ownerB][firstKey] as ownerBValue
    member profiles[ownerA][firstKey] as hasFirst
    member profiles[ownerA][siblingKey] as hasSibling
    member profiles[ownerB][firstKey] as hasOwnerB

    insert profiles[ownerA][firstKey] := fields(replacementLabel, replacementDigest)
    read profiles[ownerA][firstKey] as replacedValue
    remove profiles[ownerA][firstKey]
    member profiles[ownerA][firstKey] as keptFirst
    member profiles[ownerA][siblingKey] as keptSibling
    member profiles[ownerB][firstKey] as keptOwnerB

    return firstBefore : Bool := hadFirst
    return siblingBefore : Bool := hadSibling
    return ownerBBefore : Bool := hadOwnerB
    return firstPresent : Bool := hasFirst
    return siblingPresent : Bool := hasSibling
    return ownerBPresent : Bool := hasOwnerB
    return firstLabel : Bytes 1 := firstValue_label
    return firstDigest : Bytes 33 := firstValue_digest
    return siblingLabel : Bytes 1 := siblingValue_label
    return siblingDigest : Bytes 33 := siblingValue_digest
    return ownerBLabel : Bytes 1 := ownerBValue_label
    return ownerBDigest : Bytes 33 := ownerBValue_digest
    return replacedLabel : Bytes 1 := replacedValue_label
    return replacedDigest : Bytes 33 := replacedValue_digest
    return firstAfterRemove : Bool := keptFirst
    return siblingAfterRemove : Bool := keptSibling
    return ownerBAfterRemove : Bool := keptOwnerB
  end

  entry inspect uses nestedFixedByteMapReadInputs where
    read profiles[ownerA][siblingKey] as siblingValue
    read profiles[ownerB][firstKey] as ownerBValue
    member profiles[ownerA][firstKey] as hasFirst
    member profiles[ownerA][siblingKey] as hasSibling
    member profiles[ownerB][firstKey] as hasOwnerB
    return firstPresent : Bool := hasFirst
    return siblingPresent : Bool := hasSibling
    return ownerBPresent : Bool := hasOwnerB
    return siblingLabel : Bytes 1 := siblingValue_label
    return siblingDigest : Bytes 33 := siblingValue_digest
    return ownerBLabel : Bytes 1 := ownerBValue_label
    return ownerBDigest : Bytes 33 := ownerBValue_digest
  end

  entry lookupAbsent uses nestedFixedByteMapMissingInputs where
    read profiles[owner][missingKey] as missing
    return label : Bytes 1 := missing_label
  end
end

#guard (NestedFixedByteMapRecordValues.validate Capabilities.source).isOk
#guard NestedFixedByteMapRecordValues.entrypoints.all fun operation =>
  (Backend.Zkir.lowerEntrypoint NestedFixedByteMapRecordValues.state operation).isOk

private def nestedByteRecordEnvironment : Types.CompositeEnv := {
  structures := [
    {id := "Inner", fields := [{name := "byte", type := .bytes 1}]},
    {id := "Outer", fields := [{name := "inner", type := .structure "Inner"}]}]
}

#guard !(LedgerValueType.validate Capabilities.source
  (.map (.bytes 32) (.map (.bytes 32)
    (.composite nestedByteRecordEnvironment (.structure "Outer"))))).isOk
