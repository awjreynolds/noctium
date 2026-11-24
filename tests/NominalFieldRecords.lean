import Noctium.Frontend

open scoped Noctium
open Noctium

namespace NominalFieldRecords

noctium_field_type Amount := Field
noctium_field_type Count := Field

noctium_circuit amountInput where
  private amount : Amount
end

noctium_circuit wrongAmountInput where
  private amount : Count
end

noctium_circuit mapAmountInput where
  public key : Native
  private amount : Amount
end

noctium_circuit mapKeyInput where
  public key : Native
end

noctium_circuit noInputs where
end

noctium_contract RecordStorage where
  cell memo : struct Memo {
    amount : Amount
  }

  tree memos : Native => struct Memo {
    amount : Amount
  }

  list records : struct Memo {
    amount : Amount
  }

  entry writeCell uses amountInput arguments [amount] where
    write memo := fields(disclose(amount))
  end

  entry readCell uses noInputs where
    read memo as observed
    return result : Amount := observed_amount
  end

  entry writeMap uses mapAmountInput arguments [amount] where
    write memos[key] := fields(disclose(amount))
  end

  entry readMap uses mapKeyInput where
    read memos[key] as observed
    return result : Amount := observed_amount
  end

  entry pushList uses amountInput arguments [amount] where
    pushFront records := fields(disclose(amount))
  end

  entry readList uses noInputs where
    head records as observed
    return result : Amount := observed_amount
  end
end

private def recordEntry (name : String) : Entrypoint :=
  (RecordStorage.entrypoints.find? (·.name == name)).getD
    {name := "missing", circuit := {name := "missing"}}

#guard match RecordStorage.state with
  | [{kind := .tree (.composite cellEnvironment cellType), ..},
      {kind := .tree (.map .native (.composite mapEnvironment mapType)), ..},
      {kind := .tree (.«list» listEnvironment listType), ..}] =>
      (match LedgerValueType.cellRecordFields cellEnvironment cellType with
        | .ok fields => fields == [("amount", .native)]
        | .error _ => _root_.Bool.false) &&
        (match LedgerValueType.rootMapRecordFields mapEnvironment mapType with
          | .ok fields => fields == [("amount", .native)]
          | .error _ => _root_.Bool.false) &&
        (match LedgerValueType.listElementFields listEnvironment listType with
          | .ok fields => fields == [("amount", .native)]
          | .error _ => _root_.Bool.false)
  | _ => _root_.Bool.false

#guard ((recordEntry "writeCell").validate Capabilities.source RecordStorage.state).isOk
#guard ((recordEntry "readCell").validate Capabilities.source RecordStorage.state).isOk
#guard ((recordEntry "writeMap").validate Capabilities.source RecordStorage.state).isOk
#guard ((recordEntry "readMap").validate Capabilities.source RecordStorage.state).isOk
#guard ((recordEntry "pushList").validate Capabilities.source RecordStorage.state).isOk
#guard ((recordEntry "readList").validate Capabilities.source RecordStorage.state).isOk

/-- error: nominal Field values require an explicit cast and must match the target type -/
#guard_msgs (substring := true) in
noctium_contract RejectWrongCellRecordAlias where
  cell memo : struct Memo {
    amount : Amount
  }

  entry writeCell uses wrongAmountInput arguments [amount] where
    write memo := fields(disclose(amount))
  end
end

/-- error: nominal Field effects require a direct scalar Cell write -/
#guard_msgs (substring := true) in
noctium_contract RejectAmountMapKey where
  tree memos : Native => struct Memo {
    amount : Amount
  }

  entry writeMap uses amountInput arguments [amount] where
    write memos[amount] := fields(disclose(amount))
  end
end

/-- error: nominal Field effects require a direct scalar Cell write -/
#guard_msgs (substring := true) in
noctium_contract RejectAmountListGuard where
  list records : struct Memo {
    amount : Amount
  }

  entry guardedPush uses amountInput arguments [amount] where
    when eq(amount, 0) pushFront records := fields(disclose(amount))
  end
end

end NominalFieldRecords
