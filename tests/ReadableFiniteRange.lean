import Noctium.Frontend

open scoped Noctium

noctium_private_state RangeWallet where
  cell last : Native
end

noctium_witness rangeStep(index : Native, previous : Native) : Native
noctium_witness rangeObserve(index : Native) : Unit
noctium_witness rangeShadowObserve(index : Native, previous : Native) : Unit

syntax "rangeFixture" ident "using" ident "from" "(" term ")" "..<" "(" term ")" : command

macro_rules
  | `(rangeFixture $name:ident using $observer:ident from ($start:term) ..< ($stop:term)) =>
    `(noctium_witness_circuit $name where
      for i in ($start) ..< ($stop) do
        witness $observer(i)
      end
      output result : Native := 0
    end)

private def fragmentsInOrder (source : String) : List String → _root_.Bool
  | [] => _root_.Bool.true
  | fragment :: rest =>
    match source.splitOn fragment with
    | _ :: first :: following => fragmentsInOrder (String.intercalate fragment (first :: following)) rest
    | _ => _root_.Bool.false

private def planBody (plan : Lean.Json) : String := Id.run do
  let .ok functions := plan.getObjValAs? (Array Lean.Json) "functions" | return ""
  let .ok body := functions[0]!.getObjValAs? (Array Lean.Json) "body" | return ""
  return String.intercalate "" (body.toList.map Lean.Json.compress)

rangeFixture closedRangeFromTerms using rangeObserve from (Nat.succ 0) ..< (Nat.succ (Nat.succ 1))
rangeFixture emptyRangeFromTerms using rangeObserve from (Nat.succ (Nat.succ 0)) ..< (Nat.succ (Nat.succ 0))

noctium_witness_circuit readableRangeShadow where
  let index : Native := 1
  let previous : Native := 7
  for index in (1) ..< (3) do
    witness rangeShadowObserve(index, previous)
  end
  prove eq(index, 1)
  witness rangeShadowObserve(index, previous)
end

#guard
  let compiled := Noctium.Witness.compile readableRangeShadow.__program
    "noctium.witness-circuit.readableRangeShadow.v1"
  compiled.toOption.map (fun source =>
    source.calls.map (·.name) == ["rangeShadowObserve", "rangeShadowObserve", "rangeShadowObserve"] &&
      (let plan := planBody source.plan
      plan.contains "\"value\":\"1\"" && plan.contains "\"value\":\"2\"" &&
        plan.contains "\"name\":\"__noctium:branch-shadow:0\"" &&
        plan.contains "\"name\":\"previous\"" &&
        fragmentsInOrder plan [
          "\"arguments\":[{\"name\":\"__noctium:branch-shadow:0\"",
          "\"name\":\"previous\""] &&
        plan.contains "\"arguments\":[{\"name\":\"index\"")) ==
    some _root_.Bool.true

/- error: duplicate readable witness value -/
#guard_msgs (substring := true) in
noctium_witness_circuit duplicateRangeShadow where
  for index in 0 ..< 2 do
    let index : Native := 1
  end
end

#guard
  let compiled := Noctium.Witness.compile closedRangeFromTerms.__program
    "noctium.witness-circuit.closedRangeFromTerms.v1"
  compiled.toOption.map (fun source =>
    source.calls.map (·.name) == ["rangeObserve", "rangeObserve"] &&
      fragmentsInOrder source.plan.compress [
        "\"value\":\"1\"", "\"name\":\"rangeObserve\"",
        "\"value\":\"2\"", "\"name\":\"rangeObserve\""]) == some _root_.Bool.true

#guard
  let compiled := Noctium.Witness.compile emptyRangeFromTerms.__program
    "noctium.witness-circuit.emptyRangeFromTerms.v1"
  compiled.toOption.map (fun source =>
    source.calls.isEmpty &&
      (source.plan.compress.splitOn "\"tag\":\"witnessCall\"").length == 1) ==
    some _root_.Bool.true

/- error: Unknown identifier `runtimeCount` -/
#guard_msgs (substring := true) in
noctium_witness_circuit rejectsRuntimeRangeBound where
  private runtimeCount : Native
  for i in (runtimeCount) ..< (3) do
    witness rangeObserve(i)
  end
  output result : Native := 0
end

noctium_witness_circuit readableRange where
  public expected : Native
  for i in 1 ..< 3 do
    read private RangeWallet.last as previous
    let next : Native := witness rangeStep(i, previous)
    prove eq(next, add(previous, i))
    stage RangeWallet.last := next
    for j in 0 ..< 1 do
      witness rangeObserve(add(i, j))
    end
  end
  for skipped in 0 ..< 0 do
    witness rangeObserve(skipped)
  end
  read private RangeWallet.last as finalValue
  prove eq(finalValue, expected)
  output checked : Native := expected
end

noctium_contract ReadableFiniteRange where
  cell total : Native
  entry update uses readableRange where
    write total := checked
    return result : Native := checked
  end
end

/-- error: unknown readable witness value 'i' -/
#guard_msgs in
noctium_witness_circuit escapedIndex where
  for i in 0 ..< 1 do
    prove eq(i, 0)
  end
  output escaped : Native := i
end
