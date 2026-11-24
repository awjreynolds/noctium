import Noctium.Frontend

open scoped Noctium

private def readablePlanBody (plan : Lean.Json) : String := Id.run do
  let .ok functions := plan.getObjValAs? (Array Lean.Json) "functions" | return ""
  let bodies := functions.toList.flatMap fun function =>
    match function.getObjValAs? (Array Lean.Json) "body" with
    | .ok body => body.toList
    | .error _ => []
  return String.intercalate "" (bodies.map Lean.Json.compress)

private def readableFragmentsInOrder (source : String) : List String → _root_.Bool
  | [] => _root_.Bool.true
  | fragment :: rest =>
    match source.splitOn fragment with
    | _ :: first :: following =>
      readableFragmentsInOrder (String.intercalate fragment (first :: following)) rest
    | _ => _root_.Bool.false

noctium_private_state ContainerWallet where
  cell last : Native
end

noctium_witness containerBytes() : Bytes 2
noctium_witness containerBytesFromOuter(seed : Native) : Bytes 2
noctium_witness emptyContainer() : Bytes 0
noctium_witness containerStep(item : UInt 8, previous : Native) : Native
noctium_witness containerObserve(item : Native) : Unit

noctium_witness_circuit readableContainerLoop where
  public expected : Native
  for item in witness containerBytes() do
    read private ContainerWallet.last as previous
    let next : Native := witness containerStep(item, previous)
    prove eq(next, add(previous, item))
    stage ContainerWallet.last := next
  end
  for item in witness emptyContainer() do
    let next : Native := witness containerStep(item, 0)
    prove eq(next, item)
  end
  read private ContainerWallet.last as finalValue
  prove eq(finalValue, expected)
  output result : Native := expected
end

noctium_witness_circuit readableContainerItemShadow where
  let item : Native := 7
  let previous : Native := 11
  for item in witness containerBytesFromOuter(item) do
    let visited : Native := witness containerStep(item, previous)
  end
  prove eq(item, 7)
  witness containerObserve(item)
end

#guard
  let compiled := Noctium.Witness.compile readableContainerItemShadow.__program
    "noctium.witness-circuit.readableContainerItemShadow.v1"
  compiled.toOption.map (fun source =>
    let body := readablePlanBody source.plan
    source.calls.map (·.name) == ["containerBytesFromOuter", "containerStep", "containerStep", "containerObserve"] &&
      body.contains "\"name\":\"containerBytesFromOuter\"" &&
      body.contains "\"value\":\"7\"" &&
      body.contains "\"arguments\":[{\"name\":\"item\"" &&
      body.contains "\"arguments\":[{\"name\":\"__noctium:branch-shadow:1\"" &&
      body.contains "\"name\":\"previous\"" &&
      readableFragmentsInOrder body [
        "\"arguments\":[{\"name\":\"__noctium:branch-shadow:1\"",
        "\"name\":\"previous\""] &&
      body.contains "\"name\":\"containerObserve\"" &&
      body.contains "\"arguments\":[{\"name\":\"item\"") == some _root_.Bool.true



/- error: duplicate readable witness value -/
#guard_msgs (substring := true) in
noctium_witness_circuit duplicateContainerItemShadow where
  let item : Native := 7
  for item in witness containerBytes() do
    let item : Native := 1
  end
end

#guard
  let compiled := Noctium.Witness.compile readableContainerLoop.__program
    "noctium.witness-circuit.readableContainerLoop.v1"
  compiled.toOption.map (fun source => source.calls.map (·.name)) ==
    some ["containerBytes", "private_state.read.ContainerWallet.last.v1", "containerStep",
      "private_state.read.ContainerWallet.last.v1", "containerStep", "emptyContainer",
      "private_state.read.ContainerWallet.last.v1"]

noctium_control readableContainerLoopHost from readableContainerLoop.__program
  entry "noctium.witness-circuit.readableContainerLoop.v1"

noctium_contract ReadableContainerLoop where
  cell total : Native
  entry update uses readableContainerLoop where
    write total := result
    return updated : Native := result
  end
end

noctium_witness_circuit nestedOperatorReturn where
  public bytes : Bytes 1
  for item in bytes do
    let values := map([bytes], fun value => add(value, item))
    prove eq(elementAt(values, 0), add(item, item))
  end
end

private def emptyTupleWire : Noctium.Helpers.Wire.Codec := {
  payload := .tuple []
  frameBytes := 0
}

noctium_witness_circuit emptyTupleLoops using emptyTupleWire where
  let items := decode(emptyTupleWire, witness emptyContainer())
  for unused in items do
    prove false
  end
  for item : UInt 8 in items do
    let next : Native := witness containerStep(item, 0)
    prove eq(next, item)
  end
  for inferred in items do
    let next := witness containerStep(inferred, 0)
    let widened : Native := inferred
    prove eq(next, widened)
  end
  for inferred in items do
    let flag : Bool := inferred
    prove flag
  end
end

#guard
  let compiled := Noctium.Witness.compile emptyTupleLoops.__program
    "noctium.witness-circuit.emptyTupleLoops.v1"
  compiled.toOption.map (fun source => source.calls.map (·.name)) == some ["emptyContainer"]

noctium_witness emptyTupleSeed() : Native
noctium_witness emptyTupleFlag(item : Bool) : Native

noctium_witness_circuit emptyTupleOperators using emptyTupleWire where
  let items := decode(emptyTupleWire, witness emptyContainer())
  let mapped := map([items],
    fun item => add(witness containerStep(item, 0), witness emptyTupleFlag(item)))
  let sum := fold(witness emptyTupleSeed(), [items, mapped],
    fun acc item value => add(value,
      add(witness containerStep(item, acc), witness emptyTupleFlag(item))))
  output result : Native := disclose(sum)
end

#guard
  let compiled := Noctium.Witness.compile emptyTupleOperators.__program
    "noctium.witness-circuit.emptyTupleOperators.v1"
  compiled.toOption.map (fun source => source.calls.map (·.name)) ==
    some ["emptyContainer", "emptyTupleSeed"]

noctium_control emptyTupleOperatorsHost from emptyTupleOperators.__program
  entry "noctium.witness-circuit.emptyTupleOperators.v1"

noctium_witness_circuit mixedEmptyItemTypes using emptyTupleWire where
  public bytes : Bytes 1
  let items := decode(emptyTupleWire, witness emptyContainer())
  for item in items do
    let flag : Bool := item
    let byte : UInt 8 := item
    for inner in bytes do
      let next := witness containerStep(item, inner)
      prove eq(next, byte)
    end
    for index in 0 ..< 1 do
      let next := witness emptyTupleFlag(item)
      prove eq(next, index)
    end
    prove flag
  end
end

#guard
  let compiled := Noctium.Witness.compile mixedEmptyItemTypes.__program
    "noctium.witness-circuit.mixedEmptyItemTypes.v1"
  compiled.toOption.map (fun source => source.calls.map (·.name)) == some ["emptyContainer"]

/-- error: readable witness expression type mismatch -/
#guard_msgs in
noctium_witness_circuit invalidNonemptyItemType where
  public bytes : Bytes 1
  for item in bytes do
    let flag : Bool := item
    prove flag
  end
end

/-- error: unknown readable witness value 'item' -/
#guard_msgs in
noctium_witness_circuit escapedContainerItem where
  public bytes : Bytes 1
  for item in bytes do
    prove eq(item, item)
  end
  output escaped : UInt 8 := item
end
