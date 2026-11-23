import Noctium.Frontend

open scoped Noctium
open Noctium

noctium_circuit vectorMapRecordValueInputs where
  private first : Native
  private second : Native
  private third : Native
end

noctium_circuit vectorMapRecordValueNoInputs where
end

noctium_contract VectorMapRecordValues where
  map receipts : Vector(2, Native) => struct Receipt {
    amount : Native
    active : Bool
  }

  entry update uses vectorMapRecordValueInputs arguments [first, second, third] where
    insert receipts[fields(disclose(first), disclose(second))] := fields(101, true)
    insert receipts[fields(disclose(first), disclose(third))] := fields(303, true)
    insert receipts[fields(disclose(first), disclose(second))] := fields(202, false)
    member receipts[fields(disclose(first), disclose(second))] as presentA
    member receipts[fields(disclose(first), disclose(third))] as presentB
    size receipts as mapSize
    return memberA : Bool := presentA
    return memberB : Bool := presentB
    return size : UInt 64 := mapSize
  end

  entry lookup uses vectorMapRecordValueInputs arguments [first, second, third] where
    member receipts[fields(disclose(first), disclose(second))] as presentA
    member receipts[fields(disclose(first), disclose(third))] as presentB
    when presentA read receipts[fields(disclose(first), disclose(second))] as storedA
    when presentB read receipts[fields(disclose(first), disclose(third))] as storedB
    return amountA : Native := storedA_amount
    return activeA : Bool := storedA_active
    return amountB : Native := storedB_amount
    return activeB : Bool := storedB_active
  end

  entry size uses vectorMapRecordValueNoInputs arguments [] where
    size receipts as mapSize
    return size : UInt 64 := mapSize
  end

  entry «remove» uses vectorMapRecordValueInputs arguments [first, second, third] where
    remove receipts[fields(disclose(first), disclose(second))]
    member receipts[fields(disclose(first), disclose(second))] as presentA
    member receipts[fields(disclose(first), disclose(third))] as presentB
    when presentB read receipts[fields(disclose(first), disclose(third))] as storedB
    size receipts as mapSize
    return memberA : Bool := presentA
    return memberB : Bool := presentB
    return amountB : Native := storedB_amount
    return activeB : Bool := storedB_active
    return size : UInt 64 := mapSize
  end
end

#guard (VectorMapRecordValues.validate Capabilities.source).isOk

/-- error: ledger record field count does not match its checked layout -/
#guard_msgs (substring := true) in
noctium_contract VectorMapRecordWrongWidth where
  map receipts : Vector(2, Native) => struct Receipt {
    amount : Native
    active : Bool
  }

  entry update uses vectorMapRecordValueInputs where
    insert receipts[fields(disclose(first))] := fields(101, true)
  end
end

/-- undisclosed private parameter 'first' -/
#guard_msgs (substring := true) in
noctium_contract VectorMapRecordPrivateKey where
  map receipts : Vector(2, Native) => struct Receipt {
    amount : Native
    active : Bool
  }

  entry update uses vectorMapRecordValueInputs where
    insert receipts[fields(first, disclose(second))] := fields(101, true)
  end
end
