import Noctium.Frontend
import Noctium.Backend.Impact
import Noctium.Backend.Zkir

open scoped Noctium
open Noctium

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
noctium_uint_type TypedRefCount := UInt 8

noctium_interface NominalUIntInterface where
  entry update accepts [amount : TypedRefAmount] yields [updated : TypedRefAmount]
end

noctium_interface NominalUIntGroupedInterface where
  entry update accepts [payload := fields(amount : TypedRefAmount)]
    yields [reply := fields(updated : TypedRefAmount)]
end

noctium_circuit nominalUIntInterfaceTargetInput where
  private amount : TypedRefAmount
end

noctium_contract NominalUIntInterfaceTarget where
  cell total : TypedRefAmount
  constructor(initial : TypedRefAmount) where
    initialize total := initial
  end
  entry update uses nominalUIntInterfaceTargetInput arguments [amount] where
    write total := disclose(amount)
    return updated : TypedRefAmount := disclose(amount)
  end
end

noctium_implements NominalUIntInterfaceTarget implements NominalUIntInterface

/- error: nominal UInt interface values require a typed contract reference -/
#guard_msgs (substring := true) in
noctium_circuit rawNominalInterfaceCommitment where
  output commitment : Native :=
    callCommitment(NominalUIntInterfaceTarget, NominalUIntInterface, "update", 1, [7], [7])
end

noctium_circuit nominalUIntInterfaceCallInputs where
  private amount : TypedRefAmount
  private expected : TypedRefAmount
end

noctium_contract NominalUIntInterfaceCaller where
  cell route : ContractRef NominalUIntInterface
  constructor(initial : ContractRef NominalUIntInterface) where
    initialize route := initial
  end
  entry call uses nominalUIntInterfaceCallInputs where
    read route as target
    claimContractCall(target, disclose(callCommitment("update", 1, [amount], [expected])))
  end
end

noctium_circuit wrongNominalInterfaceArgument where
  private amount : TypedRefCount
end

noctium_contract WrongNominalInterfaceArgument where
  entry update uses wrongNominalInterfaceArgument arguments [amount] where
    return updated : TypedRefAmount := disclose(cast(TypedRefAmount, amount))
  end
end

/- error: entry 'update' does not match interface 'NominalUIntInterface' -/
#guard_msgs (substring := true) in
noctium_implements WrongNominalInterfaceArgument implements NominalUIntInterface

noctium_circuit wrongNominalInterfaceResult where
  private amount : TypedRefAmount
  private otherResult : TypedRefCount
end

noctium_contract WrongNominalInterfaceResult where
  entry update uses wrongNominalInterfaceResult arguments [amount] where
    return updated : TypedRefCount := disclose(otherResult)
  end
end

/- error: entry 'update' does not match interface 'NominalUIntInterface' -/
#guard_msgs (substring := true) in
noctium_implements WrongNominalInterfaceResult implements NominalUIntInterface

noctium_circuit nominalInterfaceCallerInputs where
  private target : ContractRef NominalUIntInterface
  private amount : TypedRefAmount
  private expected : TypedRefAmount
end

noctium_contract NominalUIntInterfaceDirectCaller where
  entry call uses nominalInterfaceCallerInputs where
    claimContractCall(disclose(target), disclose(callCommitment("update", 1, [amount], [expected])))
  end
end

/- error: Noctium expression type mismatch -/
noctium_circuit wrongNominalInterfaceCallArgument where
  private target : ContractRef NominalUIntInterface
  private amount : TypedRefCount
  private expected : TypedRefAmount
end

#guard_msgs (substring := true) in
noctium_contract WrongNominalInterfaceCallArgument where
  entry call uses wrongNominalInterfaceCallArgument where
    claimContractCall(disclose(target), disclose(callCommitment("update", 1, [amount], [expected])))
  end
end

/- error: Noctium expression type mismatch -/
noctium_circuit wrongNominalInterfaceCallResult where
  private target : ContractRef NominalUIntInterface
  private amount : TypedRefAmount
  private expected : TypedRefCount
end

#guard_msgs (substring := true) in
noctium_contract WrongNominalInterfaceCallResult where
  entry call uses wrongNominalInterfaceCallResult where
    claimContractCall(disclose(target), disclose(callCommitment("update", 1, [amount], [expected])))
  end
end

noctium_circuit nominalGroupedInterfaceCallerInputs where
  private target : ContractRef NominalUIntGroupedInterface
  private amount : TypedRefAmount
  private expected : TypedRefAmount
end

noctium_contract NominalUIntGroupedInterfaceCaller where
  entry call uses nominalGroupedInterfaceCallerInputs where
    claimContractCall(disclose(target), disclose(callCommitment("update", 1,
      [payload := fields(amount)], [reply := fields(expected)])))
  end
end

noctium_circuit wrongNominalGroupedInterfaceCallArgument where
  private target : ContractRef NominalUIntGroupedInterface
  private amount : TypedRefCount
  private expected : TypedRefAmount
end

#guard_msgs (substring := true) in
noctium_contract WrongNominalGroupedInterfaceCallArgument where
  entry call uses wrongNominalGroupedInterfaceCallArgument where
    claimContractCall(disclose(target), disclose(callCommitment("update", 1,
      [payload := fields(amount)], [reply := fields(expected)])))
  end
end

noctium_circuit wrongNominalGroupedInterfaceCallResult where
  private target : ContractRef NominalUIntGroupedInterface
  private amount : TypedRefAmount
  private expected : TypedRefCount
end

#guard_msgs (substring := true) in
noctium_contract WrongNominalGroupedInterfaceCallResult where
  entry call uses wrongNominalGroupedInterfaceCallResult where
    claimContractCall(disclose(target), disclose(callCommitment("update", 1,
      [payload := fields(amount)], [reply := fields(expected)])))
  end
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

noctium_circuit typedRefNestedInsertInputs where
  private owner : Bytes32
  private replacement : ContractRef TypedRefUpdate
end

noctium_circuit typedRefNestedOwnerInputs where
  private owner : Bytes32
end

noctium_circuit typedRefNestedForwardInputs where
  private owner : Bytes32
  private opening : Native
  private amount : UInt 8
  private expected : UInt 8
end

noctium_circuit wrongTypedRefNestedInsertInputs where
  private owner : Bytes32
  private replacement : ContractRef TypedRefOther
end

noctium_circuit typedRefDeepMapInitializeInputs where
  private owner : Bytes32
end

noctium_circuit typedRefDeepListInitializeInputs where
  private owner : Bytes32
  private bucket : Bytes32
end

noctium_circuit typedRefDeepInsertInputs where
  private owner : Bytes32
  private bucket : Bytes32
  private replacement : ContractRef TypedRefUpdate
end

noctium_circuit typedRefDeepForwardInputs where
  private owner : Bytes32
  private bucket : Bytes32
  private opening : Native
  private amount : UInt 8
  private expected : UInt 8
end

noctium_circuit wrongTypedRefDeepInsertInputs where
  private owner : Bytes32
  private bucket : Bytes32
  private replacement : ContractRef TypedRefOther
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

noctium_contract TypedRefNestedMapCaller where
  tree routes : Bytes32 => struct Route {
    target : ContractRef TypedRefUpdate
    enabled : Bool
  }
  entry insertRoute uses typedRefNestedInsertInputs arguments [owner, replacement] where
    insert routes[disclose(owner)] := fields(disclose(replacement), true)
  end
  entry forward uses typedRefNestedForwardInputs arguments [owner, opening, amount, expected] where
    read routes[disclose(owner)] as stored
    require stored_enabled
    claimContractCall(stored_target,
      disclose(callCommitment("update", opening, [amount], [expected])))
  end
end

noctium_contract TypedRefNestedListCaller where
  tree routes : Bytes32 => List struct Route {
    target : ContractRef TypedRefUpdate
    enabled : Bool
  }
  entry initializeOwner uses typedRefNestedOwnerInputs arguments [owner] where
    member routes[disclose(owner)] as ownerPresent
    when eq(ownerPresent, false) insertDefault routes[disclose(owner)]
  end
  entry addRoute uses typedRefNestedInsertInputs arguments [owner, replacement] where
    pushFront routes[disclose(owner)] := fields(disclose(replacement), true)
  end
  entry forward uses typedRefNestedForwardInputs arguments [owner, opening, amount, expected] where
    head routes[disclose(owner)] as routeHead
    require routeHead_enabled
    claimContractCall(routeHead_target,
      disclose(callCommitment("update", opening, [amount], [expected])))
  end
  entry forwardOptional uses typedRefNestedForwardInputs arguments [owner, opening, amount, expected] where
    headOrDefault routes[disclose(owner)] as (routePresent, routeHead)
    when routePresent require routeHead_enabled
    when routePresent claimContractCall(routeHead_target,
      disclose(callCommitment("update", opening, [amount], [expected])))
  end
end

noctium_contract TypedRefDeepMapCaller where
  tree routes : Bytes32 => Bytes32 => struct Route {
    target : ContractRef TypedRefUpdate
    enabled : Bool
  }
  entry initializeOwner uses typedRefDeepMapInitializeInputs arguments [owner] where
    member routes[disclose(owner)] as ownerPresent
    if eq(ownerPresent, false) then {
      insert routes[disclose(owner)] := emptyMap
    } else {
    }
  end
  entry insertRoute uses typedRefDeepInsertInputs arguments [owner, bucket, replacement] where
    insert routes[disclose(owner)][disclose(bucket)] := fields(disclose(replacement), true)
  end
  entry forward uses typedRefDeepForwardInputs arguments [owner, bucket, opening, amount, expected] where
    read routes[disclose(owner)][disclose(bucket)] as stored
    require stored_enabled
    claimContractCall(stored_target,
      disclose(callCommitment("update", opening, [amount], [expected])))
  end
end

noctium_contract TypedRefDeepListCaller where
  tree routes : Bytes32 => Bytes32 => List struct Route {
    target : ContractRef TypedRefUpdate
    enabled : Bool
  }
  entry initializeBucket uses typedRefDeepListInitializeInputs arguments [owner, bucket] where
    member routes[disclose(owner)] as ownerPresent
    if eq(ownerPresent, false) then {
      insert routes[disclose(owner)] := emptyMap
    } else {
    }
    member routes[disclose(owner)][disclose(bucket)] as bucketPresent
    if eq(bucketPresent, false) then {
      reset routes[disclose(owner)][disclose(bucket)]
    } else {
    }
  end
  entry addRoute uses typedRefDeepInsertInputs arguments [owner, bucket, replacement] where
    pushFront routes[disclose(owner)][disclose(bucket)] := fields(disclose(replacement), true)
  end
  entry forward uses typedRefDeepForwardInputs arguments [owner, bucket, opening, amount, expected] where
    head routes[disclose(owner)][disclose(bucket)] as routeHead
    require routeHead_enabled
    claimContractCall(routeHead_target,
      disclose(callCommitment("update", opening, [amount], [expected])))
  end
  entry forwardOptional uses typedRefDeepForwardInputs arguments [owner, bucket, opening, amount, expected] where
    headOrDefault routes[disclose(owner)][disclose(bucket)] as (routePresent, routeHead)
    when routePresent require routeHead_enabled
    when routePresent claimContractCall(routeHead_target,
      disclose(callCommitment("update", opening, [amount], [expected])))
  end
end

/- error: contract reference must match the declared interface -/
#guard_msgs (substring := true) in
noctium_contract WrongTypedRefNestedMapCaller where
  tree routes : Bytes32 => struct Route {
    target : ContractRef TypedRefUpdate
    enabled : Bool
  }
  entry insertRoute uses wrongTypedRefNestedInsertInputs arguments [owner, replacement] where
    insert routes[disclose(owner)] := fields(disclose(replacement), true)
  end
end

/- error: contract reference must match the declared interface -/
#guard_msgs (substring := true) in
noctium_contract WrongTypedRefNestedListCaller where
  tree routes : Bytes32 => List struct Route {
    target : ContractRef TypedRefUpdate
    enabled : Bool
  }
  entry addRoute uses wrongTypedRefNestedInsertInputs arguments [owner, replacement] where
    pushFront routes[disclose(owner)] := fields(disclose(replacement), true)
  end
end

/- error: contract reference must match the declared interface -/
#guard_msgs (substring := true) in
noctium_contract WrongTypedRefDeepMapCaller where
  tree routes : Bytes32 => Bytes32 => struct Route {
    target : ContractRef TypedRefUpdate
    enabled : Bool
  }
  entry insertRoute uses wrongTypedRefDeepInsertInputs arguments [owner, bucket, replacement] where
    insert routes[disclose(owner)][disclose(bucket)] := fields(disclose(replacement), true)
  end
end

/- error: contract reference must match the declared interface -/
#guard_msgs (substring := true) in
noctium_contract WrongTypedRefDeepListCaller where
  tree routes : Bytes32 => Bytes32 => List struct Route {
    target : ContractRef TypedRefUpdate
    enabled : Bool
  }
  entry addRoute uses wrongTypedRefDeepInsertInputs arguments [owner, bucket, replacement] where
    pushFront routes[disclose(owner)][disclose(bucket)] := fields(disclose(replacement), true)
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

noctium_circuit typedRefRecordKeyInsertInputs where
  private keyTarget : ContractRef TypedRefUpdate
  private replacement : ContractRef TypedRefUpdate
end

noctium_circuit typedRefRecordKeyForwardInputs where
  private keyTarget : ContractRef TypedRefUpdate
  private opening : Native
  private amount : UInt 8
  private expected : UInt 8
end

noctium_circuit typedRefRecordKeyNestedInitInputs where
  private owner : Bytes32
end

noctium_circuit typedRefRecordKeyNestedInsertInputs where
  private owner : Bytes32
  private keyTarget : ContractRef TypedRefUpdate
  private replacement : ContractRef TypedRefUpdate
end

noctium_circuit typedRefRecordKeyNestedForwardInputs where
  private owner : Bytes32
  private keyTarget : ContractRef TypedRefUpdate
  private opening : Native
  private amount : UInt 8
  private expected : UInt 8
end

noctium_contract TypedRefRecordKeyCaller where
  tree routes : struct Key {
    target : ContractRef TypedRefUpdate
    enabled : Bool
  } => struct Route {
    target : ContractRef TypedRefUpdate
    enabled : Bool
  }
  tree direct : struct Key {
    target : ContractRef TypedRefUpdate
    enabled : Bool
  } => ContractRef TypedRefUpdate
  tree nested : Bytes32 => struct Key {
    target : ContractRef TypedRefUpdate
    enabled : Bool
  } => struct Route {
    target : ContractRef TypedRefUpdate
    enabled : Bool
  }

  entry insertRoute uses typedRefRecordKeyInsertInputs arguments [keyTarget, replacement] where
    insert routes[fields(disclose(keyTarget), true)] := fields(disclose(replacement), true)
    insert direct[fields(disclose(keyTarget), true)] := disclose(replacement)
  end

  entry forward uses typedRefRecordKeyForwardInputs
      arguments [keyTarget, opening, amount, expected] where
    read routes[fields(disclose(keyTarget), true)] as stored
    require stored_enabled
    claimContractCall(stored_target,
      disclose(callCommitment("update", opening, [amount], [expected])))
  end

  entry forwardDirect uses typedRefRecordKeyForwardInputs
      arguments [keyTarget, opening, amount, expected] where
    read direct[fields(disclose(keyTarget), true)] as target
    claimContractCall(target,
      disclose(callCommitment("update", opening, [amount], [expected])))
  end

  entry initializeOwner uses typedRefRecordKeyNestedInitInputs arguments [owner] where
    member nested[disclose(owner)] as ownerPresent
    when eq(ownerPresent, false) insertDefault nested[disclose(owner)]
  end

  entry insertNestedRoute uses typedRefRecordKeyNestedInsertInputs
      arguments [owner, keyTarget, replacement] where
    insert nested[disclose(owner)][fields(disclose(keyTarget), true)] :=
      fields(disclose(replacement), true)
  end

  entry forwardNested uses typedRefRecordKeyNestedForwardInputs
      arguments [owner, keyTarget, opening, amount, expected] where
    read nested[disclose(owner)][fields(disclose(keyTarget), true)] as stored
    require stored_enabled
    claimContractCall(stored_target,
      disclose(callCommitment("update", opening, [amount], [expected])))
  end
end

noctium_circuit typedRefRecordKeyWrongKeyInputs where
  private keyTarget : ContractRef TypedRefOther
  private replacement : ContractRef TypedRefUpdate
end

/- error: contract reference must match the declared interface -/
#guard_msgs (substring := true) in
noctium_contract TypedRefRecordKeyWrongInterfaceKey where
  tree routes : struct Key {
    target : ContractRef TypedRefUpdate
    enabled : Bool
  } => struct Route {
    target : ContractRef TypedRefUpdate
    enabled : Bool
  }
  entry insertRoute uses typedRefRecordKeyWrongKeyInputs arguments [keyTarget, replacement] where
    insert routes[fields(disclose(keyTarget), true)] := fields(disclose(replacement), true)
  end
end

noctium_circuit typedRefRecordKeyWrongValueInputs where
  private keyTarget : ContractRef TypedRefUpdate
  private replacement : ContractRef TypedRefOther
end

/- error: contract reference must match the declared interface -/
#guard_msgs (substring := true) in
noctium_contract TypedRefRecordKeyWrongInterfaceValue where
  tree routes : struct Key {
    target : ContractRef TypedRefUpdate
    enabled : Bool
  } => struct Route {
    target : ContractRef TypedRefUpdate
    enabled : Bool
  }
  entry insertRoute uses typedRefRecordKeyWrongValueInputs arguments [keyTarget, replacement] where
    insert routes[fields(disclose(keyTarget), true)] := fields(disclose(replacement), true)
  end
end

noctium_circuit typedRefRecordKeyRawKeyInputs where
  private rawKey : Bytes32
  private replacement : ContractRef TypedRefUpdate
end

/- error: contract reference must match the declared interface -/
#guard_msgs (substring := true) in
noctium_contract TypedRefRecordKeyRawKey where
  tree routes : struct Key {
    target : ContractRef TypedRefUpdate
    enabled : Bool
  } => struct Route {
    target : ContractRef TypedRefUpdate
    enabled : Bool
  }
  entry insertRoute uses typedRefRecordKeyRawKeyInputs arguments [rawKey, replacement] where
    insert routes[fields(disclose(rawKey), true)] := fields(disclose(replacement), true)
  end
end

private def typedRefRecordKeyEntry (name : String) : Entrypoint :=
  (TypedRefRecordKeyCaller.entrypoints.find? (·.name == name)).getD
    {name := "missing", circuit := {name := "missing"}}

#guard (TypedRefRecordKeyCaller.validate Capabilities.source).isOk
#guard TypedRefRecordKeyCaller.entrypoints.all fun operation =>
  operation.validate Capabilities.source TypedRefRecordKeyCaller.state |>.isOk
#guard (Backend.Impact.lower TypedRefRecordKeyCaller.state
  (typedRefRecordKeyEntry "insertRoute")).isOk
#guard (Backend.Impact.lower TypedRefRecordKeyCaller.state
  (typedRefRecordKeyEntry "forward")).isOk
#guard (Backend.Impact.lower TypedRefRecordKeyCaller.state
  (typedRefRecordKeyEntry "forwardDirect")).isOk
#guard (Backend.Impact.lower TypedRefRecordKeyCaller.state
  (typedRefRecordKeyEntry "initializeOwner")).isOk
#guard (Backend.Impact.lower TypedRefRecordKeyCaller.state
  (typedRefRecordKeyEntry "insertNestedRoute")).isOk
#guard (Backend.Impact.lower TypedRefRecordKeyCaller.state
  (typedRefRecordKeyEntry "forwardNested")).isOk
#guard TypedRefRecordKeyCaller.entrypoints.all fun operation =>
  (Backend.Zkir.lowerEntrypoint TypedRefRecordKeyCaller.state operation).isOk
