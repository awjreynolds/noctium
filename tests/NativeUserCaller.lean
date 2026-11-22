import Noctium.Frontend

open scoped Noctium

noctium_circuit observeUserCallerInputs where
end

noctium_contract NativeUserCaller where
  cell observedUser : Bytes32

  entry observe uses observeUserCallerInputs where
    readCaller as (present, isContract, contractId, userId)
    require eq(present, true)
    require eq(isContract, false)
    write observedUser := userId
  end
end
