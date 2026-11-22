import Noctium.Frontend
import Noctium.Backend.Impact
import Noctium.Backend.Zkir

open scoped Noctium
open Noctium

noctium_circuit typedRecordMapStoreInputs where
  public key : Native
  private active : Bool
  private amount : UInt 16
end

noctium_circuit typedRecordMapKeyInputs where
  public key : Native
end

noctium_contract TypedRecordMap where
  tree memos : Native => struct Memo {
    active : Bool
    amount : UInt 16
  }

  entry storeMemo uses typedRecordMapStoreInputs arguments [active, amount] where
    write memos[key] := fields(disclose(active), disclose(amount))
  end

  entry inspectMemo uses typedRecordMapKeyInputs where
    read memos[key] as observed
    return activeResult : Bool := observed_active
    return amountResult : UInt 16 := observed_amount
  end

  entry hasMemo uses typedRecordMapKeyInputs where
    member memos[key] as present
    return presentResult : Bool := present
  end

  entry removeMemo uses typedRecordMapKeyInputs where
    remove memos[key]
    member memos[key] as presentAfterRemoveRead
    return presentAfterRemove : Bool := presentAfterRemoveRead
  end
end

private def typedRecordMapEntry (name : String) : Entrypoint :=
  (TypedRecordMap.entrypoints.find? (·.name == name)).getD
    {name := "missing", circuit := {name := "missing"}}

private def typedRecordMapFields : List (String × Ty) :=
  [("active", .bool), ("amount", .uint 65535)]

private def qualifiedCoinMapRecordEnvironment : Types.CompositeEnv := {
  structures := [{
    id := "QualifiedCoinMapRecord"
    fields := [
      {name := "nonce", type := .bytes 32},
      {name := "color", type := .bytes 32},
      {name := "value", type := .scalar (.uint (2 ^ 128 - 1))},
      {name := "mtIndex", type := .scalar (.uint (2 ^ 64 - 1))}
    ]
  }]
}

#guard match TypedRecordMap.state with
  | [{kind := .tree (.map .native (.composite environment type)), ..}] =>
      match LedgerValueType.cellRecordFields environment type with
      | .ok fields => fields == typedRecordMapFields
      | .error _ => _root_.Bool.false
  | _ => _root_.Bool.false

#guard (TypedRecordMap.validate Capabilities.source).isOk
#guard ((typedRecordMapEntry "storeMemo").validate Capabilities.source TypedRecordMap.state).isOk
#guard ((typedRecordMapEntry "inspectMemo").validate Capabilities.source TypedRecordMap.state).isOk
#guard ((typedRecordMapEntry "hasMemo").validate Capabilities.source TypedRecordMap.state).isOk
#guard ((typedRecordMapEntry "removeMemo").validate Capabilities.source TypedRecordMap.state).isOk

#guard match LedgerValueType.ledgerRecordWriteFields qualifiedCoinMapRecordEnvironment
    (.structure "QualifiedCoinMapRecord") with
  | .error _ => _root_.Bool.true
  | .ok _ => _root_.Bool.false

#guard match TypedRecordMap.state with
  | [{kind := .tree (.map _ (.composite environment type)), ..}] =>
      match LedgerValueType.validate Capabilities.source
          (.map (.bytes 4) (.composite environment type)) with
      | .error _ => _root_.Bool.true
      | .ok _ => _root_.Bool.false
  | _ => _root_.Bool.false

#guard match Backend.Impact.lower TypedRecordMap.state (typedRecordMapEntry "storeMemo") with
  | .ok plan =>
      plan.operations.any fun operation => match operation with
      | .pushFields schema values _root_.Bool.true =>
          values.map LedgerFieldExpr.ty == [.bool, .uint 65535] &&
          match TypedRecordMap.state with
          | [{kind := .tree (.map .native (.composite environment type)), ..}] =>
              match Backend.Impact.cellRecordSchema environment type with
              | .ok expected => expected == schema
              | .error _ => _root_.Bool.false
          | _ => _root_.Bool.false
      | _ => _root_.Bool.false
  | .error _ => _root_.Bool.false

#guard match Backend.Impact.lower TypedRecordMap.state (typedRecordMapEntry "inspectMemo") with
  | .ok plan =>
      plan.reads.any fun item =>
        item.name == "observed" && item.ty == .native &&
          item.components.map Prod.snd == typedRecordMapFields.map Prod.snd
  | .error _ => _root_.Bool.false

#guard match Backend.Impact.lower TypedRecordMap.state (typedRecordMapEntry "hasMemo") with
  | .ok plan =>
      plan.reads.any fun item => item.name == "present" && item.ty == .bool
  | .error _ => _root_.Bool.false

#guard match Backend.Impact.lower TypedRecordMap.state (typedRecordMapEntry "removeMemo") with
  | .ok plan =>
      plan.operations.any (fun operation => match operation with
        | .mapRemove 0 [_] => _root_.Bool.true
        | _ => _root_.Bool.false) &&
      plan.reads.any fun item => item.name == "presentAfterRemoveRead" && item.ty == .bool
  | .error _ => _root_.Bool.false

#guard match Backend.Zkir.lowerEntrypoint TypedRecordMap.state (typedRecordMapEntry "inspectMemo") with
  | .ok _ => _root_.Bool.true
  | .error _ => _root_.Bool.false
