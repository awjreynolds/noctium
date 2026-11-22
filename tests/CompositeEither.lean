import Noctium.Frontend

open scoped Noctium
open Noctium
open Noctium.Helpers
open Noctium.Types

namespace CompositeEither

private def limitsWire : Helpers.Wire.Codec := {
  payload := .structure "CompositeEither.Limits"
  frameBytes := 6
  composites := {structures := [{
    id := "CompositeEither.Limits"
    fields := [
      {name := "count", type := .scalar (.uint 255)},
      {name := "enabled", type := .scalar .bool},
      {name := "memo", type := .bytes 4}
    ]
  }]}
}

private def boolVectorWire : Helpers.Wire.Codec := {
  payload := .vector 2 (.scalar .bool)
  frameBytes := 2
}

noctium_witness_circuit choose using limitsWire, boolVectorWire where
  public isLeft : Bool
  public leftValue : Payload limitsWire
  public rightValue : Payload boolVectorWire
  output eitherValue := either(isLeft, leftValue, rightValue)
end

private def compiledChoose := Noctium.Witness.compile choose.__program
  "noctium.witness-circuit.CompositeEither.choose.v1"

#guard match compiledChoose with
  | .ok compiled =>
      compiled.circuit.inputs.map (·.name) == [
        "isLeft", "leftValue.count", "leftValue.enabled", "leftValue.memo.0",
        "leftValue.memo.1", "leftValue.memo.2", "leftValue.memo.3",
        "rightValue.0", "rightValue.1"] &&
      compiled.circuit.outputs.map (·.name) == [
        "result.eitherValue.is_left", "result.eitherValue.left.count",
        "result.eitherValue.left.enabled", "result.eitherValue.left.memo.0",
        "result.eitherValue.left.memo.1", "result.eitherValue.left.memo.2",
        "result.eitherValue.left.memo.3", "result.eitherValue.right.0",
        "result.eitherValue.right.1"]
  | .error _ => Bool.false

#guard (choose.__program.composites.structures.filter
  (·.id.startsWith "CompositeEither.choose.EitherComposite") |>.map (·.id)).length == 1

#guard choose.__program.composites.structures.any fun declaration =>
  declaration.id.startsWith "CompositeEither.choose.EitherComposite" &&
  declaration.fields.map (fun field => (field.name, field.type)) == [
    ("is_left", .scalar .bool),
    ("left", .structure "CompositeEither.Limits"),
    ("right", .vector 2 (.scalar .bool))]

private def chooseContext : EvalContext := {
  modulus := Field.modulus
  poseidon2 := fun _ _ _ => .error "unused by composite Either fixture"
}

#guard match choose.run chooseContext [
    ("isLeft", .native 1), ("leftValue.count", .native 17),
    ("leftValue.enabled", .native 1), ("leftValue.memo.0", .native 0),
    ("leftValue.memo.1", .native 1), ("leftValue.memo.2", .native 2),
    ("leftValue.memo.3", .native 255), ("rightValue.0", .native 1),
    ("rightValue.1", .native 0)] with
  | .ok outputs => outputs == [
      ("result.eitherValue.is_left", .native 1),
      ("result.eitherValue.left.count", .native 17),
      ("result.eitherValue.left.enabled", .native 1),
      ("result.eitherValue.left.memo.0", .native 0),
      ("result.eitherValue.left.memo.1", .native 1),
      ("result.eitherValue.left.memo.2", .native 2),
      ("result.eitherValue.left.memo.3", .native 255),
      ("result.eitherValue.right.0", .native 0),
      ("result.eitherValue.right.1", .native 0)]
  | .error _ => Bool.false

#guard match choose.run chooseContext [
    ("isLeft", .native 0), ("leftValue.count", .native 17),
    ("leftValue.enabled", .native 1), ("leftValue.memo.0", .native 0),
    ("leftValue.memo.1", .native 1), ("leftValue.memo.2", .native 2),
    ("leftValue.memo.3", .native 255), ("rightValue.0", .native 1),
    ("rightValue.1", .native 0)] with
  | .ok outputs => outputs == [
      ("result.eitherValue.is_left", .native 0),
      ("result.eitherValue.left.count", .native 0),
      ("result.eitherValue.left.enabled", .native 0),
      ("result.eitherValue.left.memo.0", .native 0),
      ("result.eitherValue.left.memo.1", .native 0),
      ("result.eitherValue.left.memo.2", .native 0),
      ("result.eitherValue.left.memo.3", .native 0),
      ("result.eitherValue.right.0", .native 1),
      ("result.eitherValue.right.1", .native 0)]
  | .error _ => Bool.false

private def privateChooseProgram : Helpers.Program := {
  choose.__program with
  exports := choose.__program.exports.map fun exported =>
    {exported with compositeInputs := exported.compositeInputs.map fun input =>
      {input with visibility := Noctium.Visibility.private}}
}

#guard match Noctium.Witness.compile privateChooseProgram
    "noctium.witness-circuit.CompositeEither.choose.v1" with
  | .error diagnostic =>
      diagnostic.message.contains "undisclosed private parameter 'leftValue.count'"
  | .ok _ => Bool.false

end CompositeEither

noctium_contract CompositeEither where
  entry choose uses CompositeEither.choose where
    return eitherValue
  end
end
