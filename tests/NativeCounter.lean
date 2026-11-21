import Noctium.Frontend
import Noctium.Backend.Impact
import Noctium.Backend.Zkir

open scoped Noctium

noctium_circuit counterPaths where
  private owner : Bytes32
  private spender : Bytes32
  public enabled : Bool
end

noctium_circuit counterReadPaths where
  private owner : Bytes32
  private spender : Bytes32
end

noctium_circuit counterReadTotalInputs where
end

noctium_contract NativeCounter where
  counter total
  tree epochs : Bytes32 => Bytes32 => Counter
  entry bump uses counterPaths where
    member epochs[disclose(owner)] as ownerPresent
    if eq(ownerPresent, false) then {
      insert epochs[disclose(owner)] := emptyMap
    } else {
    }
    member epochs[disclose(owner)][disclose(spender)] as recordPresent
    if eq(recordPresent, false) then {
      reset epochs[disclose(owner)][disclose(spender)]
    } else {
    }
    increment total by 3
    increment epochs[disclose(owner)][disclose(spender)] by 1
    read total as totalAfterBump
    read epochs[disclose(owner)][disclose(spender)] as epochAfterBump
  end
  entry reduce uses counterPaths where
    decrement total by 2
    decrement epochs[disclose(owner)][disclose(spender)] by 1
    read total as totalAfterDecrement
    read epochs[disclose(owner)][disclose(spender)] as epochAfterDecrement
  end
  entry resetCounters uses counterPaths where
    reset total
    reset epochs[disclose(owner)][disclose(spender)]
    read total as totalAfterReset
    read epochs[disclose(owner)][disclose(spender)] as epochAfterReset
    require eq(totalAfterReset, uint(0))
    require eq(epochAfterReset, uint(0))
  end
  entry guarded uses counterPaths where
    when enabled increment epochs[disclose(owner)][disclose(spender)] by 5
  end
  entry readCounters uses counterReadPaths where
    read total as currentTotal
    read epochs[disclose(owner)][disclose(spender)] as currentEpoch
    return totalValue : UInt 64 := currentTotal
    return epochValue : UInt 64 := currentEpoch
  end
  entry readTotal uses counterReadTotalInputs where
    read total as currentTotal
    return totalValue : UInt 64 := currentTotal
  end
end

private def nativeCounterEntry (name : String) : Noctium.Entrypoint :=
  match NativeCounter.entrypoints.find? (·.name == name) with
  | some found => found
  | none => {name := "missing", circuit := {name := "missing"}}

#guard match Noctium.Backend.Impact.lower NativeCounter.state (nativeCounterEntry "bump") with
  | .ok plan =>
      plan.operations.any (fun op => match op with
        | .addImmediate (.uint _ 3) => _root_.Bool.true
        | _ => _root_.Bool.false) &&
      plan.operations.any (fun op => match op with
        | .addImmediate (.uint _ 1) => _root_.Bool.true
        | _ => _root_.Bool.false)
  | .error _ => _root_.Bool.false

#guard match Noctium.Backend.Impact.lower NativeCounter.state (nativeCounterEntry "reduce") with
  | .ok plan => plan.operations.any (fun op => match op with
      | .subImmediate (.uint _ 2) => _root_.Bool.true
      | _ => _root_.Bool.false)
  | .error _ => _root_.Bool.false

#guard match Noctium.Backend.Impact.lower NativeCounter.state (nativeCounterEntry "resetCounters") with
  | .ok plan => plan.operations.any (fun op => match op with
      | .push (.counter (.uint _ 0)) Bool.true => _root_.Bool.true
      | _ => _root_.Bool.false)
  | .error _ => _root_.Bool.false

#guard match Noctium.Backend.Impact.lower NativeCounter.state (nativeCounterEntry "guarded") with
  | .ok plan => plan.activityGuards.any Option.isSome &&
      plan.operations.any (fun op => match op with
        | .addImmediate (.uint _ 5) => _root_.Bool.true
        | _ => _root_.Bool.false)
  | .error _ => _root_.Bool.false

#guard match Noctium.Backend.Zkir.lowerEntrypoint NativeCounter.state (nativeCounterEntry "bump") with
  | .ok _ => _root_.Bool.true
  | .error _ => _root_.Bool.false
