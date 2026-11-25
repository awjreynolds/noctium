import Noctium.Backend.Impact
import Noctium.Backend.Zkir
import Noctium.Frontend

open scoped Noctium
open Noctium

noctium_circuit nestedOpaqueBytesPath where
  public owner : Bytes32
end

noctium_circuit nestedOpaqueBytesWrite where
  public owner : Bytes32
  public bytes : OpaqueBytes
end

noctium_contract NestedOpaqueBytesList where
  tree byteArrays : Bytes32 => List OpaqueBytes

  entry clear uses nestedOpaqueBytesPath where
    reset byteArrays[disclose(owner)]
  end

  entry push uses nestedOpaqueBytesWrite where
    pushFront byteArrays[disclose(owner)] := disclose(bytes)
  end

  entry inspect uses nestedOpaqueBytesPath where
    headOrDefault byteArrays[disclose(owner)] as (present, currentBytes)
    returnMaybe bytesHead as (present, currentBytes)
  end

  entry pop uses nestedOpaqueBytesPath where
    popFront byteArrays[disclose(owner)]
  end
end

private def nestedOpaqueBytesListEntry (name : String) : Entrypoint :=
  (NestedOpaqueBytesList.entrypoints.find? (·.name == name)).getD
    {name := "missing", circuit := {name := "missing"}}

#guard match NestedOpaqueBytesList.state with
  | [{name := "byteArrays", kind := .tree (.map (.bytes 32)
      (.list _ (.scalar .opaqueBytes))), ..}] => Bool.true
  | _ => Bool.false

#guard match LedgerValueType.validate Capabilities.source
    (.map (.bytes 32) (.list {} (.scalar .opaqueBytes))) with
  | .ok _ => Bool.true
  | .error _ => Bool.false

#guard match NestedOpaqueBytesList.validate Capabilities.source with
  | .ok _ => Bool.true
  | .error _ => Bool.false

#guard match nestedOpaqueBytesListEntry "inspect" with
  | {returns := [tag, value], returnViews := [head], ..} =>
      tag.ty == .native && value.ty == .opaqueBytes &&
      head.fields == ["bytesHead_is_some", "bytesHead_value"]
  | _ => Bool.false

#guard ["clear", "push", "inspect", "pop"].all fun name =>
  match Backend.Impact.lower NestedOpaqueBytesList.state
      (nestedOpaqueBytesListEntry name) with
  | .ok _ => Bool.true
  | .error _ => Bool.false

#guard ["clear", "push", "inspect", "pop"].all fun name =>
  match Backend.Zkir.lowerPrunedEntrypoint NestedOpaqueBytesList.state
      (nestedOpaqueBytesListEntry name) with
  | .ok _ => Bool.true
  | .error _ => Bool.false
