import Noctium.Frontend
import Noctium.Backend.Impact
import Noctium.Backend.Zkir

open scoped Noctium
open Noctium

noctium_circuit fixedBytesRecordWriteInputs where
  private active : Bool
  private payload : Bytes 4
  private amount : UInt 16
end

noctium_circuit fixedBytesRecordNoInputs where
end

noctium_contract FixedBytesRecordCell where
  cell memo : struct Memo {
    active : Bool
    payload : Bytes 4
    amount : UInt 16
  }

  constructor() where
  end

  entry storeMemo uses fixedBytesRecordWriteInputs arguments [active, payload, amount] where
    write memo := fields(disclose(active), disclose(payload), disclose(amount))
  end

  entry inspectMemo uses fixedBytesRecordNoInputs where
    read memo as observed
    return activeResult : Bool := observed_active
    return payloadResult : Bytes 4 := observed_payload
    return amountResult : UInt 16 := observed_amount
  end

  entry clearMemo uses fixedBytesRecordNoInputs where
    reset memo
  end
end

private def fixedBytesRecordCellEntry (name : String) : Entrypoint :=
  (FixedBytesRecordCell.entrypoints.find? (·.name == name)).getD
    {name := "missing", circuit := {name := "missing"}}

private def fixedBytesRecordCellFields : List (String × Ty) :=
  [("active", .bool), ("payload", .bytes 4), ("amount", .uint 65535)]

#guard match FixedBytesRecordCell.state with
  | [{kind := .tree (.composite environment type), ..}] =>
      match LedgerValueType.cellRecordFields environment type with
      | .ok fields => fields == fixedBytesRecordCellFields
      | .error _ => _root_.Bool.false
  | _ => _root_.Bool.false

#guard FixedBytesRecordCell.constructor.isSome
#guard ((fixedBytesRecordCellEntry "storeMemo").validate Capabilities.source FixedBytesRecordCell.state).isOk
#guard ((fixedBytesRecordCellEntry "inspectMemo").validate Capabilities.source FixedBytesRecordCell.state).isOk
#guard ((fixedBytesRecordCellEntry "clearMemo").validate Capabilities.source FixedBytesRecordCell.state).isOk

#guard match Backend.Impact.lower FixedBytesRecordCell.state
    (fixedBytesRecordCellEntry "storeMemo") with
  | .ok plan =>
      match plan.operations with
      | [.push (.field (.native 0)), .pushFields schema values _root_.Bool.true, .insert 1] =>
          values.map LedgerFieldExpr.ty == [.bool, .bytes 4, .uint 65535] &&
          match FixedBytesRecordCell.state with
          | [{kind := .tree (.composite environment type), ..}] =>
              match Backend.Impact.cellRecordSchema environment type with
              | .ok expected => expected == schema
              | .error _ => _root_.Bool.false
          | _ => _root_.Bool.false
      | _ => _root_.Bool.false
  | .error _ => _root_.Bool.false

#guard match Backend.Impact.lower FixedBytesRecordCell.state
    (fixedBytesRecordCellEntry "inspectMemo") with
  | .ok plan =>
      match plan.operations with
      | [.dup, .indexPath 0 pushPath [], .popeqFields _ values] =>
          !pushPath && values.map LedgerFieldExpr.ty == fixedBytesRecordCellFields.map Prod.snd
      | _ => _root_.Bool.false
  | .error _ => _root_.Bool.false

#guard match Backend.Impact.lower FixedBytesRecordCell.state
    (fixedBytesRecordCellEntry "clearMemo") with
  | .ok plan =>
      match plan.operations with
      | [.push (.field (.native 0)), .pushFields _ values _root_.Bool.true, .insert 1] =>
          values.map LedgerFieldExpr.ty == [.bool, .bytes 4, .uint 65535] &&
          match values with
          | [.mk .bool (.bool _root_.Bool.false),
             .mk (.bytes 4) (.bytesLiteral 4 [0, 0, 0, 0]),
             .mk (.uint 65535) (.uint _ 0)] => _root_.Bool.true
          | _ => _root_.Bool.false
      | _ => _root_.Bool.false
  | .error _ => _root_.Bool.false

private def fixedByteWidthProbe : Types.CompositeEnv := {
  structures := [{
    id := "FixedBytesRecordCell.WidthProbe"
    fields := [
      {name := "empty", type := .scalar (.bytes 0)},
      {name := "wide", type := .scalar (.bytes 64)}]
  }]
}

private def fixedByteWidthProbeType : Types.CompositeType :=
  .structure "FixedBytesRecordCell.WidthProbe"

#guard match LedgerValueType.cellRecordFields fixedByteWidthProbe fixedByteWidthProbeType with
  | .ok fields => fields == [("empty", .bytes 0), ("wide", .bytes 64)]
  | .error _ => _root_.Bool.false

#guard match LedgerValueType.cellWriteRecordFields fixedByteWidthProbe fixedByteWidthProbeType with
  | .ok fields => fields == [("empty", .bytes 0), ("wide", .bytes 64)]
  | .error _ => _root_.Bool.false

#guard match LedgerValueType.ledgerRecordFields fixedByteWidthProbe fixedByteWidthProbeType with
  | .error _ => _root_.Bool.true
  | .ok _ => _root_.Bool.false

#guard match LedgerValueType.ledgerRecordWriteFields fixedByteWidthProbe fixedByteWidthProbeType with
  | .error _ => _root_.Bool.true
  | .ok _ => _root_.Bool.false

#guard match LedgerValueType.listElementFields fixedByteWidthProbe fixedByteWidthProbeType with
  | .error _ => _root_.Bool.true
  | .ok _ => _root_.Bool.false

#guard Input.byteProjectionIdentifiers "empty" 0 == []
#guard Input.byteProjectionIdentifiers "memo" 32 ==
  ["_noctium_bytes32_memo_high", "_noctium_bytes32_memo_low31"]
#guard Input.byteProjectionIdentifiers "wide" 64 ==
  ["_noctium_bytes_wide_0", "_noctium_bytes_wide_1", "_noctium_bytes_wide_2"]

#guard match FixedBytesRecordCell.state with
  | [{kind := .tree (.composite _ type), ..}] =>
      let wrongWidth : List LedgerFieldExpr := [
        .mk .bool (.bool _root_.Bool.true),
        .mk (.bytes 3) (.bytesLiteral 3 [1, 2, 3]),
        .mk (.uint 65535) (.uint 65535 513)]
      let malformed : Entrypoint := {
        (fixedBytesRecordCellEntry "storeMemo") with
        effects := [.writeCompositePath "memo" [] type wrongWidth]}
      match malformed.validate Capabilities.source FixedBytesRecordCell.state with
      | .error _ => _root_.Bool.true
      | .ok _ => _root_.Bool.false
  | _ => _root_.Bool.false

#guard (Backend.Zkir.lowerEntrypoint FixedBytesRecordCell.state
  (fixedBytesRecordCellEntry "inspectMemo")).isOk
