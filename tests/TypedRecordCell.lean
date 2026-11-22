import Noctium.Frontend
import Noctium.Backend.Impact
import Noctium.Backend.Zkir

open scoped Noctium
open Noctium

noctium_circuit typedRecordCellWriteInputs where
  private active : Bool
  private amount : UInt 16
end

noctium_circuit typedRecordCellNoInputs where
end

noctium_contract TypedRecordCell where
  cell memo : struct Memo {
    active : Bool
    amount : UInt 16
  }

  constructor() where
  end

  entry storeMemo uses typedRecordCellWriteInputs arguments [active, amount] where
    write memo := fields(disclose(active), disclose(amount))
  end

  entry inspectMemo uses typedRecordCellNoInputs where
    read memo as observed
    return activeResult : Bool := observed_active
    return amountResult : UInt 16 := observed_amount
  end

  entry clearMemo uses typedRecordCellNoInputs where
    reset memo
    read memo as afterReset
    return activeAfterReset : Bool := afterReset_active
    return amountAfterReset : UInt 16 := afterReset_amount
  end
end

private def typedRecordCellEntry (name : String) : Entrypoint :=
  (TypedRecordCell.entrypoints.find? (·.name == name)).getD
    {name := "missing", circuit := {name := "missing"}}

private def typedRecordCellFields : List (String × Ty) :=
  [("active", .bool), ("amount", .uint 65535)]

#guard match TypedRecordCell.state with
  | [{kind := .tree (.composite environment type), ..}] =>
      match LedgerValueType.cellRecordFields environment type with
      | .ok fields => fields == typedRecordCellFields
      | .error _ => _root_.Bool.false
  | _ => _root_.Bool.false

#guard TypedRecordCell.constructor.isSome
#guard ((typedRecordCellEntry "storeMemo").validate Capabilities.source TypedRecordCell.state).isOk
#guard ((typedRecordCellEntry "inspectMemo").validate Capabilities.source TypedRecordCell.state).isOk
#guard ((typedRecordCellEntry "clearMemo").validate Capabilities.source TypedRecordCell.state).isOk

#guard match Backend.Impact.lower TypedRecordCell.state (typedRecordCellEntry "storeMemo") with
  | .ok plan =>
      match plan.operations with
      | [.push (.field (.native 0)), .pushFields schema values _root_.Bool.true, .insert 1] =>
          values.map LedgerFieldExpr.ty == [.bool, .uint 65535] &&
          match TypedRecordCell.state with
          | [{kind := .tree (.composite environment type), ..}] =>
              match Backend.Impact.cellRecordSchema environment type with
              | .ok expected => expected == schema
              | .error _ => _root_.Bool.false
          | _ => _root_.Bool.false
      | _ => _root_.Bool.false
  | .error _ => _root_.Bool.false

#guard match Backend.Impact.lower TypedRecordCell.state (typedRecordCellEntry "inspectMemo") with
  | .ok plan =>
      match plan.operations, plan.reads with
      | [.dup, .indexPath 0 pushPath [], .popeqFields _ _],
        [{name := "observed", ty := .native, components := fields, ..}] =>
          !pushPath && fields.map Prod.snd == typedRecordCellFields.map Prod.snd
      | _, _ => _root_.Bool.false
  | .error _ => _root_.Bool.false

#guard match Backend.Impact.lower TypedRecordCell.state (typedRecordCellEntry "clearMemo") with
  | .ok plan =>
      match plan.operations with
      | [.push (.field (.native 0)), .pushFields _ values _root_.Bool.true, .insert 1,
         .dup, .indexPath 0 pushPath [], .popeqFields _ _] =>
          values.map LedgerFieldExpr.ty == [.bool, .uint 65535] &&
          !pushPath &&
          match values with
          | [.mk .bool (.bool _root_.Bool.false), .mk (.uint 65535) (.uint _ 0)] => _root_.Bool.true
          | _ => _root_.Bool.false
      | _ => _root_.Bool.false
  | .error _ => _root_.Bool.false

#guard match Backend.Zkir.lowerEntrypoint TypedRecordCell.state (typedRecordCellEntry "inspectMemo") with
  | .ok _ => _root_.Bool.true
  | .error _ => _root_.Bool.false
