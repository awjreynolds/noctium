import Noctium.Frontend

open scoped Noctium

noctium_circuit typedRefTargetInput where
  private amount : UInt 8
end

noctium_contract TypedRefTarget where
  cell total : UInt 8
  entry update uses typedRefTargetInput arguments [amount] where
    write total := disclose(amount)
    return stored : UInt 8 := disclose(amount)
  end
end

noctium_interface TypedRefUpdate where
  entry update accepts [amount : UInt 8] yields [stored : UInt 8]
end

noctium_interface TypedRefOther where
  entry update accepts [amount : UInt 8] yields [stored : UInt 8]
end

noctium_implements TypedRefTarget implements TypedRefUpdate

noctium_circuit typedRefForwardInputs where
  private opening : Native
  private amount : UInt 8
  private expected : UInt 8
end

noctium_circuit typedRefRotateInputs where
  private replacement : ContractRef TypedRefUpdate
  output nextRoute : ContractRef TypedRefUpdate := disclose(replacement)
end

noctium_contract TypedRefCaller where
  cell route : ContractRef TypedRefUpdate
  constructor(initial : ContractRef TypedRefUpdate) where
    initialize route := initial
  end
  entry forward uses typedRefForwardInputs where
    read route as target
    claimContractCall(target, disclose(callCommitment("update", opening, [amount], [expected])))
  end
  entry rotate uses typedRefRotateInputs where
    write route := nextRoute
  end
end

noctium_contract TypedRefListCaller where
  list routes : ContractRef TypedRefUpdate
  constructor(initial : ContractRef TypedRefUpdate) where
    pushFront routes := initial
  end
  entry forward uses typedRefForwardInputs where
    head routes as target
    claimContractCall(target, disclose(callCommitment("update", opening, [amount], [expected])))
  end
  entry addRoute uses typedRefRotateInputs where
    pushFront routes := nextRoute
  end
end

noctium_contract TypedRefRecordCaller where
  cell route : struct Route {
    target : ContractRef TypedRefUpdate
    enabled : Bool
  }
  entry setRoute uses typedRefRotateInputs where
    write route := fields(nextRoute, true)
  end
  entry forward uses typedRefForwardInputs where
    read route as stored
    require stored_enabled
    claimContractCall(stored_target,
      disclose(callCommitment("update", opening, [amount], [expected])))
  end
end

noctium_contract TypedRefRecordListCaller where
  list routes : struct Route {
    target : ContractRef TypedRefUpdate
    enabled : Bool
  }
  entry addRoute uses typedRefRotateInputs where
    pushFront routes := fields(nextRoute, true)
  end
  entry forward uses typedRefForwardInputs where
    head routes as stored
    require stored_enabled
    claimContractCall(stored_target,
      disclose(callCommitment("update", opening, [amount], [expected])))
  end
end

/- error: contract reference must match the declared interface -/
#guard_msgs (substring := true) in
noctium_contract WrongTypedRefRecord where
  cell route : struct Route {
    target : ContractRef TypedRefOther
    enabled : Bool
  }
  entry setRoute uses typedRefRotateInputs where
    write route := fields(nextRoute, true)
  end
end

noctium_circuit typedRefPrivateTarget where
  private target : ContractRef TypedRefUpdate
  let destination : ContractRef TypedRefUpdate := copyValue(target)
  output route : ContractRef TypedRefUpdate := disclose(destination)
end

noctium_contract TypedRefDirectCaller where
  entry forward uses typedRefPrivateTarget where
    claimContractCall(route, callCommitment("update", 1, [7], [7]))
  end
end

/- error: undisclosed private -/
#guard_msgs (substring := true) in
noctium_contract UndisclosedTypedRefTarget where
  entry forward uses typedRefPrivateTarget where
    claimContractCall(target, callCommitment("update", 1, [7], [7]))
  end
end

/- error: contract reference must match the declared interface -/
#guard_msgs (substring := true) in
noctium_contract WrongTypedRefList where
  list routes : ContractRef TypedRefOther
  entry addRoute uses typedRefRotateInputs where
    pushFront routes := nextRoute
  end
end

/- error: contract reference must match the declared interface -/
#guard_msgs (substring := true) in
noctium_contract WrongTypedRefConstructor where
  cell route : ContractRef TypedRefUpdate
  constructor(initial : ContractRef TypedRefOther) where
    initialize route := initial
  end
end

/- error: has no entry 'close' -/
#guard_msgs (substring := true) in
noctium_contract WrongTypedRefMethod where
  cell route : ContractRef TypedRefUpdate
  entry forward uses typedRefForwardInputs where
    read route as target
    claimContractCall(target, disclose(callCommitment("close", opening, [], [])))
  end
end

/- error: typed contract references require the interface-based claimContractCall form -/
#guard_msgs (substring := true) in
noctium_contract RawSelectorForTypedRef where
  entry forward uses typedRefPrivateTarget where
    claimContractCall(route, bytes(32, ""), 1)
  end
end
