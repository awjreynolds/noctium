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

noctium_interface TypedRefEcho where
  entry echo accepts [target : ContractRef TypedRefUpdate]
    yields [result : ContractRef TypedRefUpdate]
end

noctium_interface TypedRefGroupedEcho where
  entry echo accepts [payload := fields(argument : ContractRef TypedRefUpdate, amount : UInt 8)]
    yields [reply := fields(result : ContractRef TypedRefUpdate, count : UInt 8)]
end

noctium_uint_type TypedRefAmount := UInt 8

/- error: nominal UInt values are not supported in contract interfaces -/
#guard_msgs (substring := true) in
noctium_interface NominalUIntMethodParameter where
  entry amount accepts [amount : TypedRefAmount] yields []
end

/- error: nominal UInt values are not supported in contract interfaces -/
#guard_msgs (substring := true) in
noctium_interface NominalUIntMethodView where
  entry amount accepts [payload := fields(amount : TypedRefAmount)] yields []
end

noctium_implements TypedRefTarget implements TypedRefUpdate

noctium_circuit typedRefEchoTargetInput where
  private target : ContractRef TypedRefUpdate
end

noctium_contract TypedRefEchoTarget where
  entry echo uses typedRefEchoTargetInput arguments [target] where
    return result : ContractRef TypedRefUpdate := disclose(target)
  end
end

noctium_implements TypedRefEchoTarget implements TypedRefEcho

noctium_circuit wrongInterfaceEchoInput where
  private target : ContractRef TypedRefOther
end

noctium_contract WrongInterfaceEchoTarget where
  entry echo uses wrongInterfaceEchoInput arguments [target] where
    return result : ContractRef TypedRefOther := disclose(target)
  end
end

/- error: entry 'echo' does not match interface 'TypedRefEcho' -/
#guard_msgs (substring := true) in
noctium_implements WrongInterfaceEchoTarget implements TypedRefEcho

noctium_circuit wrongInterfaceEchoResultInput where
  private target : ContractRef TypedRefUpdate
  private resultSource : ContractRef TypedRefOther
end

noctium_contract WrongInterfaceEchoResultTarget where
  entry echo uses wrongInterfaceEchoResultInput arguments [target] where
    return result : ContractRef TypedRefOther := disclose(resultSource)
  end
end

/- error: entry 'echo' does not match interface 'TypedRefEcho' -/
#guard_msgs (substring := true) in
noctium_implements WrongInterfaceEchoResultTarget implements TypedRefEcho

noctium_circuit rawBytesEchoInput where
  private target : Bytes32
end

noctium_contract RawBytesEchoTarget where
  entry echo uses rawBytesEchoInput arguments [target] where
    return result : Bytes32 := disclose(target)
  end
end

/- error: entry 'echo' does not match interface 'TypedRefEcho' -/
#guard_msgs (substring := true) in
noctium_implements RawBytesEchoTarget implements TypedRefEcho

noctium_circuit typedRefForwardInputs where
  private opening : Native
  private amount : UInt 8
  private expected : UInt 8
end

noctium_circuit typedRefEchoCallInputs where
  private opening : Native
  private target : ContractRef TypedRefEcho
  private argument : ContractRef TypedRefUpdate
  private expected : ContractRef TypedRefUpdate
end

noctium_contract TypedRefEchoCaller where
  entry forward uses typedRefEchoCallInputs where
    claimContractCall(disclose(target), disclose(callCommitment("echo", opening, [argument], [expected])))
  end
end

noctium_circuit typedRefGroupedEchoCallInputs where
  private opening : Native
  private target : ContractRef TypedRefGroupedEcho
  private argument : ContractRef TypedRefUpdate
  private amount : UInt 8
  private expected : ContractRef TypedRefUpdate
  private count : UInt 8
end

noctium_contract TypedRefGroupedEchoCaller where
  entry forward uses typedRefGroupedEchoCallInputs where
    claimContractCall(disclose(target), disclose(callCommitment("echo", opening,
      [payload := fields(argument, amount)], [reply := fields(expected, count)])))
  end
end

noctium_circuit wrongTypedEchoArgumentInputs where
  private opening : Native
  private target : ContractRef TypedRefEcho
  private argument : ContractRef TypedRefOther
  private expected : ContractRef TypedRefUpdate
end

/- error: contract reference must match the declared interface -/
#guard_msgs (substring := true) in
noctium_contract WrongTypedEchoArgumentCaller where
  entry forward uses wrongTypedEchoArgumentInputs where
    claimContractCall(disclose(target), callCommitment("echo", opening, [argument], [expected]))
  end
end

noctium_circuit wrongTypedEchoResultInputs where
  private opening : Native
  private target : ContractRef TypedRefEcho
  private argument : ContractRef TypedRefUpdate
  private expected : ContractRef TypedRefOther
end

/- error: contract reference must match the declared interface -/
#guard_msgs (substring := true) in
noctium_contract WrongTypedEchoResultCaller where
  entry forward uses wrongTypedEchoResultInputs where
    claimContractCall(disclose(target), callCommitment("echo", opening, [argument], [expected]))
  end
end

noctium_circuit rawTypedEchoArgumentInputs where
  private opening : Native
  private target : ContractRef TypedRefEcho
  private argument : Bytes32
  private expected : ContractRef TypedRefUpdate
end

/- error: contract reference must match the declared interface -/
#guard_msgs (substring := true) in
noctium_contract RawTypedEchoArgumentCaller where
  entry forward uses rawTypedEchoArgumentInputs where
    claimContractCall(disclose(target), callCommitment("echo", opening, [argument], [expected]))
  end
end

noctium_circuit rawTypedEchoResultInputs where
  private opening : Native
  private target : ContractRef TypedRefEcho
  private argument : ContractRef TypedRefUpdate
  private expected : Bytes32
end

/- error: contract reference must match the declared interface -/
#guard_msgs (substring := true) in
noctium_contract RawTypedEchoResultCaller where
  entry forward uses rawTypedEchoResultInputs where
    claimContractCall(disclose(target), callCommitment("echo", opening, [argument], [expected]))
  end
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
