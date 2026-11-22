import Noctium.Frontend

open scoped Noctium
open Noctium
open Noctium.Helpers
open Noctium.Types

namespace ReadableLazyConditional

private def payloadWire : Helpers.Wire.Codec := {
  payload := .structure "ReadableLazyConditional.Payload"
  frameBytes := 33
  composites := {structures := [
    {id := "ReadableLazyConditional.Extra", fields := [
      {name := "enabled", type := .scalar .bool}]},
    {id := "ReadableLazyConditional.Payload", fields := [
      {name := "amount", type := .scalar .native},
      {name := "extra", type := .structure "ReadableLazyConditional.Extra"}]}
  ]}
}

noctium_witness loadLeft() : Payload payloadWire
noctium_witness loadRight() : Payload payloadWire
noctium_witness afterChoice(expected : Native) : Unit

noctium_witness_circuit choose using payloadWire where
  public choice : Bool
  public expected : Native
  let selected := if choice then
    let value := witness loadLeft() in value
  else
    let value := witness loadRight() in value
  prove ite(choice,
    assertThen(eq(expected, 7), true),
    assertThen(eq(expected, 9), true))
  output selectedAmount : Native := disclose(field(selected, amount))
  output selectedEnabled : Bool := disclose(field(field(selected, extra), enabled))
end

#guard (Noctium.Witness.compile choose.__program
  "noctium.witness-circuit.ReadableLazyConditional.choose.v1").isOk

noctium_witness_circuit shortCircuit using payloadWire where
  public choice : Bool
  public expected : Native
  let both := andThen(choice,
    let value := witness loadLeft() in field(field(value, extra), enabled))
  let either := orElse(choice,
    let value := witness loadRight() in field(field(value, extra), enabled))
  prove orElse(
    andThen(choice, assertThen(eq(expected, 7), true)),
    assertThen(eq(expected, 9), true)
  )
  output selectedAmount : Native := expected
  output selectedEnabled : Bool := disclose(ite(choice, both, either))
end

noctium_witness_circuit branchChoice using payloadWire where
  public choice : Bool
  public expected : Native
  if choice then
    let selected := witness loadLeft()
    prove eq(field(selected, amount), expected)
    prove field(field(selected, extra), enabled)
  else
    let selected := witness loadRight()
    prove eq(field(selected, amount), expected)
    prove boolNot(field(field(selected, extra), enabled))
  end
  witness afterChoice(expected)
  output selectedAmount : Native := expected
  output selectedEnabled : Bool := choice
end

/- error: readable witness expression type mismatch -/
#guard_msgs (substring := true) in
noctium_witness_circuit rejectsNonBoolBranch where
  if 1 then
    prove true
  end
end

/- error: unknown readable witness value -/
#guard_msgs (substring := true) in
noctium_witness_circuit rejectsEscapedBranchBinding where
  public choice : Bool
  if choice then
    let localValue := 7
  end
  output value : Native := localValue
end

/- error: short-circuit operands require Bool -/
#guard_msgs (substring := true) in
noctium_witness_circuit rejectsNonBoolShortCircuit where
  public choice : Bool
  output invalid : Bool := andThen(choice, 1)
end

/- error: undisclosed private -/
#guard_msgs (substring := true) in
noctium_witness_circuit rejectsUndisclosedShortCircuit where
  private choice : Bool
  output result : Bool := andThen(choice, true)
end

/- error: conditional branches require a common type -/
#guard_msgs (substring := true) in
noctium_witness_circuit rejectsIncompatibleBranches using payloadWire where
  public choice : Bool
  let selected := if choice then
    let value := witness loadLeft() in value
  else 0
  output observed : Native := field(selected, amount)
end

/- error: undisclosed private -/
#guard_msgs (substring := true) in
noctium_witness_circuit rejectsUndisclosedSelection using payloadWire where
  public choice : Bool
  let selected := if choice then
    let value := witness loadLeft() in value
  else
    let value := witness loadRight() in value
  output enabled : Bool := field(field(selected, extra), enabled)
end

/- error: undisclosed private -/
#guard_msgs (substring := true) in
noctium_witness_circuit rejectsUndisclosedChoice using payloadWire where
  private choice : Bool
  public left : Payload payloadWire
  public right : Payload payloadWire
  let selected := if choice then left else right
  output amount : Native := field(selected, amount)
end

end ReadableLazyConditional

noctium_contract ReadableLazyConditional where
  entry choose uses ReadableLazyConditional.choose where
    return observed : Native := selectedAmount
    return enabled : Bool := selectedEnabled
  end
  entry shortCircuit uses ReadableLazyConditional.shortCircuit where
    return observed : Native := selectedAmount
    return enabled : Bool := selectedEnabled
  end
  entry branchChoice uses ReadableLazyConditional.branchChoice where
    return observed : Native := selectedAmount
    return enabled : Bool := selectedEnabled
  end
end
