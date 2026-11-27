import Noctium.Frontend

open scoped Noctium

noctium_witness unitObserve(value : Native) : Unit
noctium_witness unitFinish(value : Native) : Native
noctium_witness echoUnit(emptyArg : Unit, seed : Native) : Native

noctium_witness_circuit readableUnitBindings where
  public seed : Native
  let first := witness unitObserve(seed)
  let saved := first
  let finished : Native := let second := witness unitObserve(add(seed, 1)) in
    witness unitFinish(add(seed, 2))
  output result : Native := disclose(finished)
  output presentUnit := some(witness unitObserve(add(seed, 3)))
  output absentUnit := none(Unit)
end

noctium_witness_circuit unitArgument where
  public seed : Native
  let observed : Native := witness echoUnit(default(Unit), seed)
  output result : Native := disclose(observed)
end

/- error: witness callback argument type mismatch -/
#guard_msgs (substring := true) in
noctium_witness_circuit rejectsBoolForUnitArgument where
  public seed : Native
  let observed : Native := witness echoUnit(true, seed)
  output result : Native := disclose(observed)
end

noctium_contract ReadableUnitBindings where
  entry update uses readableUnitBindings where
    return value : Native := result
    return presentUnit
    return absentUnit
  end
  entry passUnit uses unitArgument where
    return value : Native := result
  end
end
