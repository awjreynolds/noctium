import Noctium.Frontend

open scoped Noctium

noctium_witness iterationSeed() : Native
noctium_witness iterationBytes() : Bytes 2
noctium_witness iterationVisit(item : UInt 8) : Native

noctium_witness_circuit readableIteration where
  public offset : Native
  let sum : Native := fold(witness iterationSeed(),
    [map([witness iterationBytes()], fun item => witness iterationVisit(item))],
    fun acc value => add(add(acc, value), offset))
  output result : Native := disclose(sum)
end

#guard
  let compiled := Noctium.Witness.compile readableIteration.__program
    "noctium.witness-circuit.readableIteration.v1"
  (compiled.toOption.map (fun source => source.calls.map (·.name))) ==
    some ["iterationSeed", "iterationBytes", "iterationVisit", "iterationVisit"]

noctium_contract ReadableIteration where
  cell total : Native
  entry update uses readableIteration where
    write total := result
    return updated : Native := result
  end
end

/-- public output -/
#guard_msgs (substring := true) in
noctium_witness_circuit uncheckedIteration where
  private data : Bytes 2
  output leaked : Native := fold(0, [data], fun acc value => add(acc, value))
end

private def bytePair : Noctium.Helpers.Wire.Codec := {
  payload := .vector 2 (.scalar (.uint 255))
  frameBytes := 2
}

noctium_witness_circuit decodedIteration using bytePair where
  public frame : Bytes 2
  let values := decode(bytePair, frame)
  let bumped := let offset := 1 in map([values], fun value => add(value, offset))
  output mapped := bumped
  output sum : Native := fold(0, [bumped], fun acc value => add(acc, value))
end

noctium_witness blockItems(seed : Native) : Payload bytePair
noctium_witness blockOffset(seed : Native) : Native

noctium_witness_circuit blockIteration using bytePair where
  public seed : Native
  let items := witness blockItems(seed)
  let offset := witness blockOffset(add(seed, 1))
  let mapped := map([items], fun item => do
    let widened := cast(Native, item)
    let adjusted := add(widened, offset)
    prove boolNot(eq(adjusted, 999))
    return adjusted
  end)
  let sum : Native := fold(0, [mapped], fun acc value => do
    let next := add(acc, value)
    prove boolNot(eq(next, 85))
    return next
  end)
  output first : Native := disclose(elementAt(mapped, 0))
  output second : Native := disclose(elementAt(mapped, 1))
  output total : Native := disclose(sum)
end

noctium_contract ReadableIterationBlock where
  entry run uses blockIteration where
    return mappedFirst : Native := first
    return mappedSecond : Native := second
    return sum : Native := total
  end
end

/- error: readable witness expression type mismatch -/
#guard_msgs (substring := true) in
noctium_witness_circuit rejectsNonBooleanStep where
  output mapped := map([vector(1)], fun item => do
    prove item
    return item
  end)
end
