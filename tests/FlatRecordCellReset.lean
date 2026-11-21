import Noctium.Backend.Impact
import Noctium.Frontend

open scoped Noctium
open Noctium

noctium_circuit flatCellResetNoInputs where
end

noctium_circuit flatCellResetInputs where
  public enabled : Bool
end

noctium_contract FlatRecordCellReset where
  cell marker : Native
  cell ledger : struct Ledger {
    issued : Native
    spent : Native
  }

  entry clear uses flatCellResetNoInputs where
    reset ledger
  end

  entry guardedClear uses flatCellResetInputs where
    when enabled reset ledger
  end
end

private def flatCellResetEntry (name : String) : Entrypoint :=
  match FlatRecordCellReset.entrypoints.find? (·.name == name) with
  | some found => found
  | none => {name := "missing", circuit := {name := "missing"}}

private def isZeroLedger (values : List LedgerFieldExpr) : _root_.Bool :=
  match values with
  | [.mk .native (.native 0), .mk .native (.native 0)] => Bool.true
  | _ => Bool.false

private def flatCellResetClear := flatCellResetEntry "clear"
private def flatCellResetGuarded := flatCellResetEntry "guardedClear"

#guard (flatCellResetClear.validate Capabilities.source FlatRecordCellReset.state).isOk
#guard (flatCellResetGuarded.validate Capabilities.source FlatRecordCellReset.state).isOk

#guard match FlatRecordCellReset.state with
  | [_, {kind := .tree (.composite environment (.structure typeId)), ..}] =>
      typeId == "FlatRecordCellReset.Ledger" &&
      match LedgerValueType.recordFields environment (.structure typeId) with
      | .ok fields => fields == [("issued", .native), ("spent", .native)]
      | .error _ => Bool.false
  | _ => Bool.false

#guard match flatCellResetClear.effects, flatCellResetClear.effectGuards with
  | [.writeCompositePath "ledger" [] (.structure typeId) values], [none] =>
      typeId == "FlatRecordCellReset.Ledger" && isZeroLedger values
  | _, _ => Bool.false

#guard match Backend.Impact.lower FlatRecordCellReset.state flatCellResetClear with
  | .ok plan =>
      match plan.operations, plan.activityGuards with
      | [.push (.field (.native 1)) Bool.false, .pushFields schema values Bool.true, .insert 1], [] =>
          isZeroLedger values &&
            match FlatRecordCellReset.state with
            | [_, {kind := .tree (.composite environment type), ..}] =>
                match Backend.Impact.recordSchema environment type with
                | .ok expected => expected == schema
                | .error _ => Bool.false
            | _ => Bool.false
      | _, _ => Bool.false
  | .error _ => Bool.false

#guard match Backend.Impact.lower FlatRecordCellReset.state flatCellResetGuarded with
  | .ok plan =>
      match plan.operations.drop 2, plan.activityGuards.drop 2 with
      | [.push (.field (.native 1)) Bool.false, .pushFields _ _ Bool.true, .insert 1],
        [some (.ref "enabled"), some (.ref "enabled"), some (.ref "enabled")] =>
          Bool.true
      | _, _ => Bool.false
  | .error _ => Bool.false
