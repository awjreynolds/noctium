import Noctium.Frontend

open scoped Noctium
open Noctium
open Noctium.Helpers
open Noctium.Types

namespace CompositeMaybe

private def limitsWire : Helpers.Wire.Codec := {
  payload := .structure "CompositeMaybe.Limits"
  frameBytes := 6
  composites := {structures := [{
    id := "CompositeMaybe.Limits"
    fields := [
      {name := "count", type := .scalar (.uint 255)},
      {name := "enabled", type := .scalar .bool},
      {name := "memo", type := .bytes 4}
    ]
  }]}
}

noctium_witness_circuit options using limitsWire where
  public value : Payload limitsWire
  output presentValue := some(value)
  output absentValue := none(Payload limitsWire)
end

private def compiledOptions := Noctium.Witness.compile options.__program
  "noctium.witness-circuit.CompositeMaybe.options.v1"

#guard match compiledOptions with
  | .ok compiled =>
      compiled.circuit.inputs.map (·.name) == [
        "value.count", "value.enabled", "value.memo.0", "value.memo.1",
        "value.memo.2", "value.memo.3"] &&
      compiled.circuit.outputs.map (·.name) == [
        "result.presentValue.is_some", "result.presentValue.value.count",
        "result.presentValue.value.enabled", "result.presentValue.value.memo.0",
        "result.presentValue.value.memo.1", "result.presentValue.value.memo.2",
        "result.presentValue.value.memo.3", "result.absentValue.is_some",
        "result.absentValue.value.count", "result.absentValue.value.enabled",
        "result.absentValue.value.memo.0", "result.absentValue.value.memo.1",
        "result.absentValue.value.memo.2", "result.absentValue.value.memo.3"]
  | .error _ => Bool.false

#guard (options.__program.composites.structures.filter
  (·.id.startsWith "CompositeMaybe.options.MaybeComposite") |>.map (·.id)) ==
    ["CompositeMaybe.options.MaybeComposite12049812722228462552"]

#guard options.__program.composites.structures.any fun declaration =>
  declaration.id == "CompositeMaybe.options.MaybeComposite12049812722228462552" &&
  declaration.fields.map (fun field => (field.name, field.type)) == [
    ("is_some", .scalar .bool), ("value", .structure "CompositeMaybe.Limits")]

private def optionsContext : EvalContext := {
  modulus := Field.modulus
  poseidon2 := fun _ _ _ => .error "unused by composite Maybe fixture"
}

#guard match options.run optionsContext [
    ("value.count", .native 17), ("value.enabled", .native 1),
    ("value.memo.0", .native 0), ("value.memo.1", .native 1),
    ("value.memo.2", .native 2), ("value.memo.3", .native 255)] with
  | .ok outputs => outputs == [
      ("result.presentValue.is_some", .native 1),
      ("result.presentValue.value.count", .native 17),
      ("result.presentValue.value.enabled", .native 1),
      ("result.presentValue.value.memo.0", .native 0),
      ("result.presentValue.value.memo.1", .native 1),
      ("result.presentValue.value.memo.2", .native 2),
      ("result.presentValue.value.memo.3", .native 255),
      ("result.absentValue.is_some", .native 0),
      ("result.absentValue.value.count", .native 0),
      ("result.absentValue.value.enabled", .native 0),
      ("result.absentValue.value.memo.0", .native 0),
      ("result.absentValue.value.memo.1", .native 0),
      ("result.absentValue.value.memo.2", .native 0),
      ("result.absentValue.value.memo.3", .native 0)]
  | .error _ => Bool.false

private def privateOptionsProgram : Helpers.Program := {
  options.__program with
  exports := options.__program.exports.map fun exported =>
    {exported with compositeInputs := exported.compositeInputs.map fun input =>
      {input with visibility := Noctium.Visibility.private}}
}

#guard match Noctium.Witness.compile privateOptionsProgram
    "noctium.witness-circuit.CompositeMaybe.options.v1" with
  | .error diagnostic => diagnostic.message.contains "undisclosed private parameter 'value.count'"
  | .ok _ => Bool.false

end CompositeMaybe

noctium_contract CompositeMaybe where
  entry options uses CompositeMaybe.options where
    return presentValue
    return absentValue
  end
end
