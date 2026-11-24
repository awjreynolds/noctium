import Noctium.Backend.Impact
import Noctium.Backend.Zkir
import Noctium.Frontend
import Noctium.Disclosure

open scoped Noctium
open Noctium

noctium_circuit byteStorageValues where
  public owner : Native
  public domain : Bytes32
  private enabled : Bool
  private empty0 : Bytes 0
  private payload1 : Bytes 1
  private payload31 : Bytes 31
  private payload32 : Bytes 32
  private payload33 : Bytes 33
  private payload1024 : Bytes 1024
end

noctium_contract BytesStorage where
  cell emptyCell : Bytes 0
  cell oneCell : Bytes 1
  cell narrowCell : Bytes 31
  cell wordCell : Bytes 32
  map values : Native => Bytes 33
  tree payloads : Bytes32 => Native => Bytes 1024
  constructor() where
    initialize emptyCell := bytes(0, "")
    initialize oneCell := bytes(1, "")
    initialize narrowCell := bytes(31, "")
    initialize wordCell := bytes(32, "")
  end
  entry update uses byteStorageValues where
    read emptyCell as previousEmpty
    read oneCell as previousOne
    read narrowCell as previousNarrow
    read wordCell as previousWord

    member values[disclose(owner)] as existedMap
    when eq(existedMap, true)
      read values[disclose(owner)] as previousMap

    member payloads[disclose(domain)] as existedDomain
    if eq(existedDomain, false) then {
      insert payloads[disclose(domain)] := emptyMap
    } else {
    }
    member payloads[disclose(domain)][disclose(owner)] as existedTree
    when eq(existedTree, true)
      read payloads[disclose(domain)][disclose(owner)] as previousTree

    write emptyCell := disclose(reverseBytes(assertThen(enabled, empty0)))
    write oneCell := disclose(payload1)
    write narrowCell := disclose(payload31)
    write wordCell := disclose(payload32)
    insert values[disclose(owner)] := disclose(payload33)
    insert payloads[disclose(domain)][disclose(owner)] := disclose(payload1024)

    read emptyCell as nextEmpty
    read oneCell as nextOne
    read narrowCell as nextNarrow
    read wordCell as nextWord
    read values[disclose(owner)] as nextMap
    read payloads[disclose(domain)][disclose(owner)] as nextTree

    return oldEmpty : Bytes 0 := disclose(previousEmpty)
    return oldOne : Bytes 1 := disclose(previousOne)
    return oldNarrow : Bytes 31 := disclose(previousNarrow)
    return oldWord : Bytes 32 := disclose(previousWord)
    return oldMap : Bytes 33 := disclose(previousMap)
    return oldTree : Bytes 1024 := disclose(previousTree)
    return newEmpty : Bytes 0 := disclose(nextEmpty)
    return newOne : Bytes 1 := disclose(nextOne)
    return newNarrow : Bytes 31 := disclose(nextNarrow)
    return newWord : Bytes 32 := disclose(nextWord)
    return newMap : Bytes 33 := disclose(nextMap)
    return newTree : Bytes 1024 := disclose(nextTree)
    return mapWasPresent : Bool := disclose(existedMap)
    return treeWasPresent : Bool := disclose(existedTree)
  end
end

private def bytesStorageEntry : Entrypoint :=
  match BytesStorage.entrypoints with
  | ep :: _ => ep
  | [] => {name := "missing", circuit := {name := "missing"}}

#guard match BytesStorage.validate Capabilities.source with
  | .ok _ => Bool.true
  | .error _ => Bool.false

#guard bytesStorageEntry.returns.map Output.name == [
  "oldEmpty", "oldOne", "oldNarrow", "oldWord", "oldMap", "oldTree",
  "newEmpty", "newOne", "newNarrow", "newWord", "newMap", "newTree",
  "mapWasPresent", "treeWasPresent"]

#guard (bytesStorageEntry.returns[0]?).map Output.nativeReturnFieldCount == some 0
#guard (bytesStorageEntry.returns[6]?).map Output.nativeReturnFieldCount == some 0

#guard match (LedgerValueType.map .native (.scalar (.bytes 33))).validate Capabilities.source with
  | .ok _ => Bool.true
  | .error _ => Bool.false

#guard match (LedgerValueType.map (.bytes 32)
    (.map .native (.scalar (.bytes 1024)))).validate Capabilities.source with
  | .ok _ => Bool.true
  | .error _ => Bool.false

#guard match ({name := "tooWideBytesCell", state := [
    {name := "value", kind := .cell (.bytes 1025)}]} : Contract).validate Capabilities.source with
  | .error diagnostic => diagnostic.message == "byte string length exceeds the maximum of 1024"
  | .ok _ => Bool.false

#guard match ({name := "tooWideBytesKey", state := [
    {name := "value", kind := .map (.bytes 1025) .native}]} : Contract).validate Capabilities.source with
  | .error diagnostic => diagnostic.message == "byte string length exceeds the maximum of 1024"
  | .ok _ => Bool.false

private def bytesStorageUndisclosedWrite : Entrypoint := {
  name := "bytesStorageUndisclosedWrite"
  circuit := byteStorageValues
  effects := [.writeCell "oneCell" (.bytes 1) (.ref "payload1")]
}

#guard match Disclosure.entrypoint bytesStorageUndisclosedWrite with
  | .error diagnostic => diagnostic.message.startsWith "undisclosed private parameter"
  | .ok _ => Bool.false
