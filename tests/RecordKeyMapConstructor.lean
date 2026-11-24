import Noctium.Backend.Impact
import Noctium.Compiler
import Noctium.Frontend

open Lean
open scoped Noctium
open Noctium

noctium_circuit recordKeyMapConstructorInspection where
  public tag : Bytes 1
  public id : Bytes 33
end

noctium_contract RecordKeyMapConstructor where
  tree entries : struct Key {
    tag : Bytes 1
    id : Bytes 33
  } => UInt 16

  constructor(tag : Bytes 1, id : Bytes 33, amount : UInt 16, enabled : Bool) where
    when enabled insert entries[fields(disclose(tag), disclose(id))] := disclose(amount)
  end

  entry inspect uses recordKeyMapConstructorInspection where
    member entries[fields(disclose(tag), disclose(id))] as memberPresent
    return present : Bool := memberPresent
  end

  entry readValue uses recordKeyMapConstructorInspection where
    read entries[fields(disclose(tag), disclose(id))] as amount
    return stored : UInt 16 := amount
  end
end

private def inspectEntry : Entrypoint :=
  (RecordKeyMapConstructor.entrypoints.find? (·.name == "inspect")).getD
    {name := "missing", circuit := {name := "missing"}}

private def constructorActionsJson (ctor : Noctium.Constructor) : Except String (Array Json) := do
  let plan ← (Backend.Impact.lower RecordKeyMapConstructor.state inspectEntry).mapError
    (·.message)
  let artifact := Compiler.nativePlanJson TargetProfile.selected321
    `RecordKeyMapConstructor RecordKeyMapConstructor.state (some ctor)
    inspectEntry plan
  let metadata ← artifact.getObjVal? "constructor"
  let actions ← metadata.getObjVal? "actions"
  actions.getArr?

#guard (RecordKeyMapConstructor.validate Capabilities.source).isOk
#guard (inspectEntry.validate Capabilities.source RecordKeyMapConstructor.state).isOk

#guard match RecordKeyMapConstructor.constructor with
  | some ctor =>
      match ctor.actions with
      | [.insertRecordKeyMap {
          state := "entries",
          fields := [
            .mk (.bytes 1) (.disclose _ (.ref "tag")),
            .mk (.bytes 33) (.disclose _ (.ref "id"))],
          valueType := .uint 65535,
          value := .disclose _ (.ref "amount"),
          guard := some (.ref "enabled")} ] => _root_.Bool.true
      | _ => _root_.Bool.false
  | none => _root_.Bool.false

#guard match RecordKeyMapConstructor.constructor with
  | some ctor =>
      match constructorActionsJson ctor with
      | .ok #[action] =>
          (action.getObjVal? "kind").toOption == some (toJson ("insertRecordKeyMap" : String)) &&
            (action.getObjVal? "state").toOption == some (toJson ("entries" : String)) &&
            (action.getObjVal? "fields").isOk &&
            (action.getObjVal? "value").isOk &&
            (action.getObjVal? "guard").isOk
      | _ => _root_.Bool.false
  | none => _root_.Bool.false
