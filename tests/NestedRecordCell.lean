import Noctium.Frontend

open scoped Noctium

noctium_circuit nestedRecordCellInputs where
  private totalArg : Native
  private countArg : UInt 16
  private activeArg : Bool
end

noctium_circuit nestedRecordCellNoInputs where
end

noctium_contract NestedRecordCell where
  cell position : struct Position {
    total : Native
    details : struct Details {
      count : UInt 16
      active : Bool
    }
  }

  constructor(totalArg : Native, countArg : UInt 16, activeArg : Bool) where
    initialize position := fields(disclose(totalArg), disclose(countArg), disclose(activeArg))
  end

  entry replacePosition uses nestedRecordCellInputs where
    write position := fields(disclose(totalArg), disclose(countArg), disclose(activeArg))
  end

  entry inspect uses nestedRecordCellNoInputs where
    read position as observed
    return totalResult : Native := observed_total
    return countResult : UInt 16 := observed_details_count
    return activeResult : Bool := observed_details_active
  end
end

/- error: sealed state 'position' cannot be written by an entrypoint -/
#guard_msgs (substring := true) in
noctium_contract RejectSealedNestedRecordWrite where
  sealed cell position : struct Position {
    total : Native
    details : struct Details { count : UInt 16 active : Bool }
  }

  constructor() where
    initialize position := fields(241, 513, true)
  end

  entry replacePosition uses nestedRecordCellInputs where
    write position := fields(disclose(totalArg), disclose(countArg), disclose(activeArg))
  end
end
