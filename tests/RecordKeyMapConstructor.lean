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
  tree receipts : struct Key {
    tag : Bytes 1
    id : Bytes 33
  } => struct Receipt {
    accepted : Bool
    code : UInt 16
  }

  constructor(tag : Bytes 1, id : Bytes 33, amount : UInt 16,
      accepted : Bool, code : UInt 16, enabled : Bool) where
    when enabled insert entries[fields(disclose(tag), disclose(id))] := disclose(amount)
    when enabled insert receipts[fields(disclose(tag), disclose(id))] :=
      fields(disclose(accepted), disclose(code))
  end

  entry inspect uses recordKeyMapConstructorInspection where
    member entries[fields(disclose(tag), disclose(id))] as memberPresent
    return present : Bool := memberPresent
  end

  entry readValue uses recordKeyMapConstructorInspection where
    read entries[fields(disclose(tag), disclose(id))] as amount
    return stored : UInt 16 := amount
  end

  entry inspectReceipt uses recordKeyMapConstructorInspection where
    member receipts[fields(disclose(tag), disclose(id))] as receiptPresent
    read receipts[fields(disclose(tag), disclose(id))] as receipt
    return present : Bool := receiptPresent
    return accepted : Bool := receipt_accepted
    return code : UInt 16 := receipt_code
  end

  entry receiptMember uses recordKeyMapConstructorInspection where
    member receipts[fields(disclose(tag), disclose(id))] as receiptPresent
    return present : Bool := receiptPresent
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

private def badConstructorRejected
    (change : ConstructorRecordKeyMapInsert → ConstructorRecordKeyMapInsert) : _root_.Bool :=
  match RecordKeyMapConstructor.constructor with
  | some ctor =>
      match ctor.actions with
      | [.insertRecordKeyMap scalarInsert, .insertRecordKeyMap recordInsert] =>
          let invalid : Contract := {RecordKeyMapConstructor with «constructor» := some {
            ctor with actions := [
              .insertRecordKeyMap scalarInsert,
              .insertRecordKeyMap (change recordInsert)]}}
          match invalid.validate Capabilities.source with
          | .error _ => _root_.Bool.true
          | .ok _ => _root_.Bool.false
      | _ => _root_.Bool.false
  | none => _root_.Bool.false

#guard (RecordKeyMapConstructor.validate Capabilities.source).isOk
#guard (inspectEntry.validate Capabilities.source RecordKeyMapConstructor.state).isOk
#guard ((RecordKeyMapConstructor.entrypoints.find? (·.name == "inspectReceipt")).getD
  {name := "missing", circuit := {name := "missing"}}).validate
  Capabilities.source RecordKeyMapConstructor.state |>.isOk
#guard ((RecordKeyMapConstructor.entrypoints.find? (·.name == "receiptMember")).getD
  {name := "missing", circuit := {name := "missing"}}).validate
  Capabilities.source RecordKeyMapConstructor.state |>.isOk

#guard match RecordKeyMapConstructor.constructor with
  | some ctor =>
      match ctor.actions with
      | [.insertRecordKeyMap {
          state := "entries",
          fields := [
            .mk (.bytes 1) (.disclose _ (.ref "tag")),
            .mk (.bytes 33) (.disclose _ (.ref "id"))],
          value := .scalar (.uint 65535) (.disclose _ (.ref "amount")),
          guard := some (.ref "enabled")},
         .insertRecordKeyMap {
          state := "receipts",
          fields := [
            .mk (.bytes 1) (.disclose _ (.ref "tag")),
            .mk (.bytes 33) (.disclose _ (.ref "id"))],
          value := .record (.structure "RecordKeyMapConstructor.Receipt") [
            .mk .bool (.disclose _ (.ref "accepted")),
            .mk (.uint 65535) (.disclose _ (.ref "code"))],
          guard := some (.ref "enabled")} ] => _root_.Bool.true
      | _ => _root_.Bool.false
  | none => _root_.Bool.false

#guard match RecordKeyMapConstructor.constructor with
  | some ctor =>
      match constructorActionsJson ctor with
      | .ok #[scalarAction, recordAction] =>
          scalarAction.getObjValD "kind" == toJson ("insertRecordKeyMap" : String) &&
            scalarAction.getObjValD "state" == toJson ("entries" : String) &&
            (scalarAction.getObjVal? "fields").isOk &&
            (scalarAction.getObjValD "value").getObjValD "kind" == toJson ("scalar" : String) &&
            (scalarAction.getObjValD "value").getObjValD "valueType" == toJson ("UIntRange<65536>" : String) &&
            (scalarAction.getObjVal? "guard").isOk &&
            recordAction.getObjValD "kind" == toJson ("insertRecordKeyMap" : String) &&
            recordAction.getObjValD "state" == toJson ("receipts" : String) &&
            (recordAction.getObjVal? "fields").isOk &&
            (recordAction.getObjValD "value").getObjValD "kind" == toJson ("record" : String) &&
            (((recordAction.getObjValD "value").getObjValD "fields").getArr?.toOption.getD #[]).size == 2 &&
            (recordAction.getObjVal? "guard").isOk
      | _ => _root_.Bool.false
  | none => _root_.Bool.false

#guard badConstructorRejected (fun insertion => {insertion with fields := [
  .mk (.bytes 33) (.disclose ({} : SourceSpan) (.ref "tag")),
  .mk (.bytes 1) (.disclose ({} : SourceSpan) (.ref "id"))]})
#guard badConstructorRejected (fun insertion => {insertion with value :=
  (ConstructorRecordKeyMapValue.record (.structure "RecordKeyMapConstructor.Receipt") [
    .mk (.uint 65535) (.disclose ({} : SourceSpan) (.ref "code")),
    .mk .bool (.disclose ({} : SourceSpan) (.ref "accepted"))])})
#guard badConstructorRejected (fun insertion => {insertion with value :=
  (ConstructorRecordKeyMapValue.record (.structure "RecordKeyMapConstructor.Other") [
    .mk .bool (.disclose ({} : SourceSpan) (.ref "accepted")),
    .mk (.uint 65535) (.disclose ({} : SourceSpan) (.ref "code"))])})
#guard badConstructorRejected (fun insertion => {insertion with value :=
  (ConstructorRecordKeyMapValue.scalar .bool
    (.disclose ({} : SourceSpan) (.ref "accepted")))})
