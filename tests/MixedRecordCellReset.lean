import Noctium.Backend.Impact
import Noctium.Backend.Zkir
import Noctium.Frontend

open scoped Noctium
open Noctium

noctium_circuit mixedRecordCellResetInputs where
  public enabled : Bool
end

noctium_contract MixedRecordCellReset where
  cell typedMemo : struct TypedMemo {
    active : Bool
    amount : UInt 16
  }

  cell fixedBytesMemo : struct FixedBytesMemo {
    active : Bool
    payload : Bytes 4
    amount : UInt 16
  }

  constructor() where
    initialize typedMemo := fields(true, 513)
    initialize fixedBytesMemo := fields(true, bytes(4, "seed"), 1027)
  end

  entry clearMemos uses mixedRecordCellResetInputs where
    when enabled reset typedMemo
    when enabled reset fixedBytesMemo
    read typedMemo as typedObserved
    read fixedBytesMemo as fixedBytesObserved
    return typedActiveAfterReset : Bool := typedObserved_active
    return typedAmountAfterReset : UInt 16 := typedObserved_amount
    return fixedBytesActiveAfterReset : Bool := fixedBytesObserved_active
    return fixedBytesPayloadAfterReset : Bytes 4 := fixedBytesObserved_payload
    return fixedBytesAmountAfterReset : UInt 16 := fixedBytesObserved_amount
  end
end

private def mixedRecordCellResetEntry : Entrypoint :=
  match MixedRecordCellReset.entrypoints.find? (·.name == "clearMemos") with
  | some found => found
  | none => {name := "missing", circuit := {name := "missing"}}

#guard (mixedRecordCellResetEntry.validate Capabilities.source MixedRecordCellReset.state).isOk
#guard match MixedRecordCellReset.state with
  | [
      {kind := .tree (.composite environment typedType), ..},
      {kind := .tree (.composite environment' fixedBytesType), ..}] =>
      typedType == .structure "MixedRecordCellReset.TypedMemo" &&
      fixedBytesType == .structure "MixedRecordCellReset.FixedBytesMemo" &&
      (match LedgerValueType.cellRecordFields environment typedType with
      | .ok fields => fields == [("active", .bool), ("amount", .uint 65535)]
      | .error _ => Bool.false) &&
      (match LedgerValueType.cellRecordFields environment' fixedBytesType with
      | .ok fields => fields == [("active", .bool), ("payload", .bytes 4), ("amount", .uint 65535)]
      | .error _ => Bool.false)
  | _ => Bool.false

#guard match MixedRecordCellReset.constructor with
  | some ctor =>
      match ctor.actions with
      | [
          .initializeRecordCell "typedMemo" [
            .mk .bool (.bool Bool.true),
            .mk (.uint 65535) (.uint 65535 513)],
          .initializeRecordCell "fixedBytesMemo" [
            .mk .bool (.bool Bool.true),
            .mk (.bytes 4) (.bytesLiteral 4 [115, 101, 101, 100]),
            .mk (.uint 65535) (.uint 65535 1027)]] => Bool.true
      | _ => Bool.false
  | none => Bool.false

#guard match mixedRecordCellResetEntry.effects.take 2 with
  | [
      .writeCompositePath "typedMemo" [] (.structure typedId) typedValues,
      .writeCompositePath "fixedBytesMemo" [] (.structure fixedBytesId) fixedBytesValues] =>
      typedId == "MixedRecordCellReset.TypedMemo" &&
      fixedBytesId == "MixedRecordCellReset.FixedBytesMemo" &&
      (match typedValues with
      | [.mk .bool (.bool Bool.false), .mk (.uint 65535) (.uint 65535 0)] => Bool.true
      | _ => Bool.false) &&
      (match fixedBytesValues with
      | [.mk .bool (.bool Bool.false),
         .mk (.bytes 4) (.bytesLiteral 4 [0, 0, 0, 0]),
         .mk (.uint 65535) (.uint 65535 0)] => Bool.true
      | _ => Bool.false)
  | _ => Bool.false

#guard match mixedRecordCellResetEntry.effectGuards.take 2 with
  | [some (.ref "enabled"), some (.ref "enabled")] => Bool.true
  | _ => Bool.false
#guard (Backend.Impact.lower MixedRecordCellReset.state mixedRecordCellResetEntry).isOk
#guard (Backend.Zkir.lowerEntrypoint MixedRecordCellReset.state mixedRecordCellResetEntry).isOk
