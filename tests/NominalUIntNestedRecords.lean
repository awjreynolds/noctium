import Noctium.Frontend

open scoped Noctium
open Noctium

namespace NominalUIntNestedRecords

noctium_uint_type Amount := UInt 8
noctium_uint_type Count := UInt 8

noctium_circuit appendValues where
  private owner : Bytes32
  private amount : Amount
  private count : Count
end

noctium_circuit inspectValues where
  private owner : Bytes32
end

noctium_contract ThreeLevelRecordLists where
  tree positions : Bytes32 => Bytes32 => Bytes32 => struct Position {
    amount : Amount
    count : Count
  }
  tree history : Bytes32 => Bytes32 => Bytes32 => List struct Position {
    amount : Amount
    count : Count
  }

  entry append uses appendValues where
    pushFront history[disclose(owner)][disclose(owner)][disclose(owner)] :=
      fields(disclose(amount), disclose(count))
  end

  entry inspect uses inspectValues where
    read positions[disclose(owner)][disclose(owner)][disclose(owner)] as stored
    head history[disclose(owner)][disclose(owner)][disclose(owner)] as latest
    return amountResult : Amount := stored_amount
    return historyAmountResult : Amount := latest_amount
    return countResult : Count := latest_count
  end
end

#guard ThreeLevelRecordLists.entrypoints.all fun operation =>
  (Backend.Zkir.lowerEntrypoint ThreeLevelRecordLists.state operation).isOk

/- error: nominal UInt values require an explicit cast and must match the target type -/
#guard_msgs (substring := true) in
noctium_contract RejectsWrongNestedRecordWrite where
  tree history : Bytes32 => Bytes32 => Bytes32 => List struct Position {
    amount : Amount
    count : Count
  }

  entry append uses appendValues where
    pushFront history[disclose(owner)][disclose(owner)][disclose(owner)] :=
      fields(disclose(count), disclose(amount))
  end
end

/- error: nominal UInt values require an explicit cast and must match the target type -/
#guard_msgs (substring := true) in
noctium_contract RejectsWrongNestedRecordRead where
  tree positions : Bytes32 => Bytes32 => Bytes32 => struct Position {
    amount : Amount
    count : Count
  }

  entry inspect uses inspectValues where
    read positions[disclose(owner)][disclose(owner)][disclose(owner)] as stored
    return amountResult : Count := stored_amount
  end
end

end NominalUIntNestedRecords
