import Noctium.Frontend

open scoped Noctium
open Noctium

noctium_uint_type RecordAmount := UInt 8
noctium_uint_type RecordCount := UInt 8

noctium_circuit recordConstructorOwner where
  private owner : Bytes32
end

noctium_contract RecordConstructor where
  cell position : struct Position {
    amount : RecordAmount
    count : RecordCount
    active : Bool
  }
  tree positions : Bytes32 => struct Position {
    amount : RecordAmount
    count : RecordCount
    active : Bool
  }

  constructor(owner : Bytes32, amount : RecordAmount, count : RecordCount, active : Bool) where
    initialize position := fields(disclose(amount), disclose(count), disclose(active))
    insert positions[disclose(owner)] := fields(cast(RecordAmount, 0), disclose(count), false)
    insert positions[disclose(owner)] := fields(disclose(amount), disclose(count), disclose(active))
  end

  entry inspect uses recordConstructorOwner arguments [owner] where
    read position as current
    read positions[disclose(owner)] as stored
    return cellAmount : RecordAmount := current_amount
    return cellCount : RecordCount := current_count
    return cellActive : Bool := current_active
    return mapAmount : RecordAmount := stored_amount
    return mapCount : RecordCount := stored_count
    return mapActive : Bool := stored_active
  end
end

#guard match RecordConstructor.constructor with
  | some ctor =>
    match ctor.actions with
    | [.initializeRecordCell "position" cellFields,
       .insertRecordMap "positions" _ firstFields,
       .insertRecordMap "positions" _ finalFields] =>
      [cellFields, firstFields, finalFields].all
        (fun fields => fields.map LedgerFieldExpr.ty == [.uint 255, .uint 255, .bool])
    | _ => Bool.false
  | none => Bool.false

#guard RecordConstructor.entrypoints.all fun operation =>
  (Backend.Zkir.lowerEntrypoint RecordConstructor.state operation).isOk

/- error: nominal UInt values require an explicit cast and must match the target type -/
#guard_msgs (substring := true) in
noctium_contract WrongRecordConstructorCellAlias where
  cell position : struct Position { amount : RecordAmount }
  constructor(count : RecordCount) where
    initialize position := fields(disclose(count))
  end
end

/- error: nominal UInt values require an explicit cast and must match the target type -/
#guard_msgs (substring := true) in
noctium_contract WrongRecordConstructorMapRawValue where
  tree positions : Bytes32 => struct Position { amount : RecordAmount }
  constructor(owner : Bytes32, raw : UInt 8) where
    insert positions[disclose(owner)] := fields(disclose(raw))
  end
end

/- error: duplicate constructor initializer for 'position' -/
#guard_msgs (substring := true) in
noctium_contract DuplicateRecordConstructorCell where
  cell position : struct Position { active : Bool }
  constructor() where
    initialize position := fields(false)
    initialize position := fields(true)
  end
end
