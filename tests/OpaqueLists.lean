import Noctium.Backend.Impact
import Noctium.Backend.Zkir
import Noctium.Disclosure
import Noctium.Frontend

open scoped Noctium
open Noctium

noctium_circuit opaqueListPushInputs where
  public text : OpaqueString
  public bytes : OpaqueBytes
end

noctium_circuit opaqueListNoInputs where
end

noctium_contract OpaqueLists where
  list strings : OpaqueString
  list byteArrays : OpaqueBytes

  entry push uses opaqueListPushInputs where
    pushFront strings := disclose(text)
    pushFront byteArrays := disclose(bytes)
  end

  entry inspect uses opaqueListNoInputs where
    headOrDefault strings as (stringPresent, currentString)
    headOrDefault byteArrays as (bytesPresent, currentBytes)
    return stringIsPresent : Bool := stringPresent
    return stringValue : OpaqueString := disclose(currentString)
    return bytesArePresent : Bool := bytesPresent
    return bytesValue : OpaqueBytes := disclose(currentBytes)
  end

  entry pop uses opaqueListNoInputs where
    popFront strings
    popFront byteArrays
  end
end

private def opaqueListEntry (name : String) : Entrypoint :=
  (OpaqueLists.entrypoints.find? (·.name == name)).getD
    {name := "missing", circuit := {name := "missing"}}

#guard match OpaqueLists.state with
  | [{name := "strings", kind := .tree (.list _ (.scalar .opaqueString)), ..},
     {name := "byteArrays", kind := .tree (.list _ (.scalar .opaqueBytes)), ..}] => Bool.true
  | _ => Bool.false

#guard match LedgerValueType.validate Capabilities.source
    (.map (.bytes 32) (.list {} (.scalar .opaqueString))) with
  | .error message => message == "OpaqueString is only supported as a root Bytes32 tree Map value"
  | .ok _ => Bool.false

#guard match OpaqueLists.validate Capabilities.source with
  | .ok _ => Bool.true
  | .error _ => Bool.false

#guard match Backend.Impact.lower OpaqueLists.state (opaqueListEntry "push") with
  | .ok _ => Bool.true
  | .error _ => Bool.false

#guard match Backend.Impact.lower OpaqueLists.state (opaqueListEntry "inspect") with
  | .ok _ => Bool.true
  | .error _ => Bool.false

#guard match Backend.Impact.lower OpaqueLists.state (opaqueListEntry "pop") with
  | .ok _ => Bool.true
  | .error _ => Bool.false

#guard match Backend.Zkir.lowerPrunedEntrypoint OpaqueLists.state (opaqueListEntry "push") with
  | .ok _ => Bool.true
  | .error _ => Bool.false

#guard match Backend.Zkir.lowerPrunedEntrypoint OpaqueLists.state (opaqueListEntry "inspect") with
  | .ok _ => Bool.true
  | .error _ => Bool.false

#guard match Backend.Zkir.lowerPrunedEntrypoint OpaqueLists.state (opaqueListEntry "pop") with
  | .ok _ => Bool.true
  | .error _ => Bool.false
