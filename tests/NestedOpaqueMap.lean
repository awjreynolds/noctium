import Noctium.Backend.Impact
import Noctium.Backend.Zkir
import Noctium.Frontend
import Noctium.Disclosure

open scoped Noctium
open Noctium

noctium_circuit nestedOpaqueBytesStoreInputs where
  public owner : Bytes32
  public key : Bytes32
  public payload : OpaqueBytes
end

noctium_circuit nestedOpaqueBytesPathInputs where
  public owner : Bytes32
  public key : Bytes32
end

noctium_circuit nestedOpaqueStringStoreInputs where
  public owner : Bytes32
  public key : Bytes32
  public value : OpaqueString
end

noctium_circuit nestedOpaqueStringPathInputs where
  public owner : Bytes32
  public key : Bytes32
end

noctium_contract NestedOpaqueMap where
  tree byteBuckets : Bytes32 => Bytes32 => OpaqueBytes
  tree stringBuckets : Bytes32 => Bytes32 => OpaqueString

  entry storeBytes uses nestedOpaqueBytesStoreInputs where
    member byteBuckets[disclose(owner)] as ownerPresent
    if eq(ownerPresent, false) then {
      insert byteBuckets[disclose(owner)] := emptyMap
    } else {
    }
    insert byteBuckets[disclose(owner)][disclose(key)] := disclose(payload)
  end

  entry hasBytes uses nestedOpaqueBytesPathInputs where
    member byteBuckets[disclose(owner)][disclose(key)] as present
    return found : Bool := disclose(present)
  end

  entry readBytes uses nestedOpaqueBytesPathInputs where
    read byteBuckets[disclose(owner)][disclose(key)] as stored
    return payload : OpaqueBytes := disclose(stored)
  end

  entry storeString uses nestedOpaqueStringStoreInputs where
    member stringBuckets[disclose(owner)] as ownerPresent
    if eq(ownerPresent, false) then {
      insert stringBuckets[disclose(owner)] := emptyMap
    } else {
    }
    insert stringBuckets[disclose(owner)][disclose(key)] := disclose(value)
  end

  entry hasString uses nestedOpaqueStringPathInputs where
    member stringBuckets[disclose(owner)][disclose(key)] as present
    return found : Bool := disclose(present)
  end

  entry readString uses nestedOpaqueStringPathInputs where
    read stringBuckets[disclose(owner)][disclose(key)] as stored
    return value : OpaqueString := disclose(stored)
  end
end

private def nestedOpaqueEntry (name : String) : Entrypoint :=
  match NestedOpaqueMap.entrypoints.find? (·.name == name) with
  | some value => value
  | none => {name := "missing", circuit := {name := "missing"}}

#guard match NestedOpaqueMap.state with
  | [ {name := "byteBuckets", kind := .tree (.map (.bytes 32)
        (.map (.bytes 32) (.scalar .opaqueBytes))), ..},
      {name := "stringBuckets", kind := .tree (.map (.bytes 32)
        (.map (.bytes 32) (.scalar .opaqueString))), ..} ] => Bool.true
  | _ => Bool.false

#guard match NestedOpaqueMap.validate Capabilities.source with
  | .ok _ => Bool.true
  | .error _ => Bool.false

#guard match (LedgerValueType.map .native
    (.map (.bytes 32) (.scalar .opaqueString))).validate Capabilities.source with
  | .error message => message.contains "OpaqueString is only supported"
  | .ok _ => Bool.false

#guard ["storeBytes", "hasBytes", "readBytes", "storeString", "hasString", "readString"].all fun name =>
  let operation := nestedOpaqueEntry name
  match Backend.Impact.lower NestedOpaqueMap.state operation with
  | .ok _ => Bool.true
  | .error _ => Bool.false

#guard ["storeBytes", "hasBytes", "readBytes", "storeString", "hasString", "readString"].all fun name =>
  let operation := nestedOpaqueEntry name
  match Backend.Zkir.lowerPrunedEntrypoint NestedOpaqueMap.state operation with
  | .ok _ => Bool.true
  | .error _ => Bool.false

#guard NestedOpaqueMap.entrypoints.all fun operation =>
  match Disclosure.entrypoint operation with
  | .ok _ => Bool.true
  | .error _ => Bool.false

