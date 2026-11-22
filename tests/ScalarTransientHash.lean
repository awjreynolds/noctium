import Noctium.Frontend

open scoped Noctium
open Noctium

noctium_circuit scalarTransientOrdinary where
  public fieldValue : Native
  public flagValue : Bool
  public byteValue : UInt 8
  output fieldDigest : Native := transientHashValue(fieldValue)
  output flagDigest : Native := transientHashValue(flagValue)
  output byteDigest : Native := transientHashValue(byteValue)
end

noctium_witness_circuit scalarTransientReadable where
  public fieldValue : Native
  public flagValue : Bool
  public byteValue : UInt 8
  output fieldDigest : Native := transientHashValue(fieldValue)
  output flagDigest : Native := transientHashValue(flagValue)
  output byteDigest : Native := transientHashValue(byteValue)
end

/- error: transientHashValue requires Native, Bool or UInt -/
#guard_msgs (substring := true) in
noctium_circuit rejectsTransientHashBytes where
  private bytesValue : Bytes 1
  output digest : Native := transientHashValue(bytesValue)
end

/- error: undisclosed private -/
#guard_msgs (substring := true) in
noctium_circuit rejectsImplicitDisclosure where
  private value : Native
  output digest : Native := transientHashValue(value)
end

/- error: undisclosed private -/
#guard_msgs (substring := true) in
noctium_witness_circuit rejectsReadableTransientHashDisclosure where
  private value : Bool
  output digest : Native := transientHashValue(value)
end

noctium_circuit transientHashRetainsPartialOperand where
  private enabled : Bool
  let unused : Native := transientHashValue(assertThen(enabled, 7))
  output result : Native := 1
end

private def transientHashEvalContext : EvalContext := {
  modulus := Field.modulus
  poseidon2 := fun _ _ _ => pure 0
}

#guard match transientHashRetainsPartialOperand.constraints with
  | [constraint] => match constraint.eval transientHashEvalContext [("enabled", .bool Bool.false)] with
    | .error "helper assertion failed" => Bool.true
    | _ => Bool.false
  | _ => Bool.false

noctium_contract ScalarTransientHash where
  entry ordinary uses scalarTransientOrdinary where
    return fieldResult : Native := fieldDigest
    return flagResult : Native := flagDigest
    return byteResult : Native := byteDigest
  end
  entry readable uses scalarTransientReadable where
    return fieldResult : Native := fieldDigest
    return flagResult : Native := flagDigest
    return byteResult : Native := byteDigest
  end
end
