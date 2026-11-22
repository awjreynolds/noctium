import Noctium.Frontend

open scoped Noctium
open Noctium
open Noctium.Helpers
open Noctium.Types

namespace ReadableBindPatterns

private def packetWire : Helpers.Wire.Codec := {
  payload := .structure "ReadableBindPatterns.Packet"
  frameBytes := 67
  composites := {structures := [
    {
      id := "ReadableBindPatterns.Reading"
      fields := [
        {name := "count", type := .scalar (.uint 255)},
        {name := "active", type := .scalar .bool}
      ]
    },
    {
      id := "ReadableBindPatterns.Packet"
      fields := [
        {name := "reading", type := .structure "ReadableBindPatterns.Reading"},
        {name := "measures", type := .tuple [.scalar .native, .scalar .bool]},
        {name := "omitted", type := .scalar .native}
      ]
    }
  ]}
}

noctium_witness load(seed : Native) : Payload packetWire

noctium_witness_circuit unpack using packetWire where
  public seed : Native
  let {measures := [measured, _], reading := {count := amount}} := witness load(seed)
  output total : Native := disclose(add(measured, amount))
end

noctium_witness_circuit unpackViews using packetWire where
  public seed : Native
  let {measures := [measured, _], reading := {count := amount, active := enabled}} :=
    witness load(seed)
  output total : Native := disclose(add(measured, amount))
  output flag : Bool := disclose(enabled)
end

#guard (Noctium.Witness.compile unpack.__program
  "noctium.witness-circuit.ReadableBindPatterns.unpack.v1").isOk
#guard (Noctium.Witness.compile unpackViews.__program
  "noctium.witness-circuit.ReadableBindPatterns.unpackViews.v1").isOk

/- error: positional pattern requires -/
#guard_msgs (substring := true) in
noctium_witness_circuit rejectsTupleArity using packetWire where
  public seed : Native
  let {measures := [measured], reading := {count := amount}} :=
    witness load(seed)
  output total : Native := disclose(add(measured, amount))
end

/- error: unknown aggregate struct field -/
#guard_msgs (substring := true) in
noctium_witness_circuit rejectsUnknownField using packetWire where
  public seed : Native
  let {unknown := _} := witness load(seed)
  output total : Native := disclose(seed)
end

/- error: duplicate record pattern field -/
#guard_msgs (substring := true) in
noctium_witness_circuit rejectsDuplicateField using packetWire where
  public seed : Native
  let {measures := _, measures := _} := witness load(seed)
  output total : Native := disclose(seed)
end

/- error: duplicate readable witness value -/
#guard_msgs (substring := true) in
noctium_witness_circuit rejectsDuplicateBinding using packetWire where
  public seed : Native
  let {measures := [duplicate, duplicate]} := witness load(seed)
  output total : Native := disclose(seed)
end

/- error: undisclosed private -/
#guard_msgs (substring := true) in
noctium_witness_circuit rejectsUndisclosedPrivate using packetWire where
  public seed : Native
  let {measures := [measured, _], reading := {count := amount}} :=
    witness load(seed)
  output total : Native := add(measured, amount)
end

end ReadableBindPatterns

private def vectorWire : Helpers.Wire.Codec := {
  payload := .vector 2 (.scalar .native)
  frameBytes := 64
  composites := {}
}

noctium_witness_circuit sequenceBindings using vectorWire where
  public pair : Payload vectorWire
  public bytes : Bytes 2
  let [first, _] := pair
  let [_, second] := bytes
  output result : Native := add(first, second)
end

noctium_contract ReadableBindPatterns where
  entry unpack uses ReadableBindPatterns.unpack where
    return totalResult : Native := total
  end
  entry unpackViews uses ReadableBindPatterns.unpackViews where
    return totalResult : Native := total
    return activeResult : Bool := flag
  end
end
