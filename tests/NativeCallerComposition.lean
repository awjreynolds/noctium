import Noctium.Frontend

open scoped Noctium

noctium_circuit composedCallerLookupInputs where
  private enabled : Bool
end

noctium_contract ComposedCallerLookup where
  cell recorded : Bool

  entry lookup uses composedCallerLookupInputs arguments [enabled] where
    when disclose(enabled) readCaller as (present, isContract, contractId, userId)
    when disclose(enabled) write recorded := present
    return hasCaller : Bool := present
    return contractCaller : Bool := isContract
    return callerContract : Bytes32 := contractId
    return callerUser : Bytes32 := userId
  end
end

noctium_circuit callerReporterInputs where
  public target : Bytes32
  private opening : Native
  private expectedParent : Bytes32
end

noctium_contract CallerReporter where
  cell observedCaller : Bytes32

  entry forward uses callerReporterInputs where
    claimContractCall(target, disclose(callCommitment(ComposedCallerLookup,
      "lookup", opening, [true], [true, true, expectedParent, bytes32("")])))
    write observedCaller := disclose(expectedParent)
  end
end
