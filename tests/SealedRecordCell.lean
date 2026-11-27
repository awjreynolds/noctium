import Noctium.Frontend

open scoped Noctium

noctium_circuit sealedRecordNoInputs where
end

noctium_contract SealedRecordCell where
  sealed cell position : struct Position {
    amount : UInt 8
    count : UInt 16
    active : Bool
  }
  cell marker : Native

  constructor(amount : UInt 8, count : UInt 16, active : Bool) where
    initialize position := fields(disclose(amount), disclose(count), disclose(active))
  end

  entry inspect uses sealedRecordNoInputs where
    read position as observed
    return amount : UInt 8 := observed_amount
    return count : UInt 16 := observed_count
    return active : Bool := observed_active
  end

  entry touch uses sealedRecordNoInputs where
    write marker := 37
  end
end

/- error: sealed state 'position' cannot be written by an entrypoint -/
#guard_msgs (substring := true) in
noctium_contract RejectSealedRecordWrite where
  sealed cell position : struct Position { active : Bool }
  constructor() where
    initialize position := fields(true)
  end
  entry overwrite uses sealedRecordNoInputs where
    write position := fields(false)
  end
end
