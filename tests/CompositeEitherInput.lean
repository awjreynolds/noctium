import Noctium.Frontend

open scoped Noctium
open Noctium
open Noctium.Helpers
open Noctium.Types

namespace CompositeEitherInput

private def limitsWire : Helpers.Wire.Codec := {
  payload := .structure "CompositeEitherInput.Limits"
  frameBytes := 6
  composites := {structures := [{
    id := "CompositeEitherInput.Limits"
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

private def eitherWire : Helpers.Wire.Codec := Helpers.Wire.either
  "CompositeEitherInput.LimitsOrBoolPair" limitsWire boolVectorWire

#guard eitherWire.payload == .structure "CompositeEitherInput.LimitsOrBoolPair"
#guard eitherWire.frameBytes == 9
#guard match eitherWire.composites.structures.find?
    (·.id == "CompositeEitherInput.LimitsOrBoolPair") with
  | some declaration => declaration.fields.map (fun field => (field.name, field.type)) == [
      ("is_left", .scalar .bool),
      ("left", .structure "CompositeEitherInput.Limits"),
      ("right", .vector 2 (.scalar .bool))]
  | none => Bool.false
#guard eitherWire.composites.structures.any
  (·.id == "CompositeEitherInput.Limits")

private def codecDeclarations (codec : Helpers.Wire.Codec) :
    Except String (List Helpers.Declaration) := do
  let composites := Helpers.Wire.compositeEnv {} [codec]
  let compiled ← match Types.compileType composites codec.payload with
    | .ok value => pure value
    | .error diagnostic => throw diagnostic.message
  Helpers.Wire.declarations compiled "checked" codec.frameBytes ⟨0, 1⟩ ⟨0, 2⟩

#guard match codecDeclarations (Helpers.Wire.either
    "CompositeEitherInput.Limits" limitsWire boolVectorWire) with
  | .error message => message.contains "duplicate declaration identity"
  | .ok _ => Bool.false

#guard match codecDeclarations (Helpers.Wire.either "CompositeEitherInput.TooNarrow"
    {limitsWire with frameBytes := 5} boolVectorWire) with
  | .error message => message.contains "requires at least 9 bytes"
  | .ok _ => Bool.false

#guard match codecDeclarations (Helpers.Wire.either "CompositeEitherInput.TooWide"
    {limitsWire with frameBytes := Noctium.maxBytesLength} boolVectorWire) with
  | .error message => message.contains "aggregate wire width exceeds the source limit"
  | .ok _ => Bool.false

noctium_witness_circuit echo using limitsWire, boolVectorWire, eitherWire where
  public value : Payload eitherWire
  output echoed := value
end

private def compiledEcho := Noctium.Witness.compile echo.__program
  "noctium.witness-circuit.CompositeEitherInput.echo.v1"

#guard match compiledEcho with
  | .ok compiled =>
      compiled.circuit.inputs.map (·.name) == [
        "value.is_left", "value.left.count", "value.left.enabled",
        "value.left.memo.0", "value.left.memo.1", "value.left.memo.2",
        "value.left.memo.3", "value.right.0", "value.right.1"] &&
      compiled.circuit.outputs.map (·.name) == [
        "result.is_left", "result.left.count", "result.left.enabled",
        "result.left.memo.0", "result.left.memo.1", "result.left.memo.2",
        "result.left.memo.3", "result.right.0", "result.right.1"]
  | .error _ => Bool.false

#guard echo.__program.composites.structures.any fun declaration =>
  declaration.id == "CompositeEitherInput.LimitsOrBoolPair" &&
  declaration.fields.map (fun field => (field.name, field.type)) == [
    ("is_left", .scalar .bool),
    ("left", .structure "CompositeEitherInput.Limits"),
    ("right", .vector 2 (.scalar .bool))]

private def echoContext : EvalContext := {
  modulus := Field.modulus
  poseidon2 := fun _ _ _ => .error "unused by composite Either input fixture"
}

private def echoInputs (isLeft : Nat) : List (String × Value) := [
  ("value.is_left", .native isLeft),
  ("value.left.count", .native 17), ("value.left.enabled", .native 1),
  ("value.left.memo.0", .native 0), ("value.left.memo.1", .native 1),
  ("value.left.memo.2", .native 2), ("value.left.memo.3", .native 255),
  ("value.right.0", .native 1), ("value.right.1", .native 1)]

private def echoOutputs (isLeft : Nat) : List (String × Value) := [
  ("result.is_left", .native isLeft),
  ("result.left.count", .native 17), ("result.left.enabled", .native 1),
  ("result.left.memo.0", .native 0), ("result.left.memo.1", .native 1),
  ("result.left.memo.2", .native 2), ("result.left.memo.3", .native 255),
  ("result.right.0", .native 1), ("result.right.1", .native 1)]

#guard match echo.run echoContext (echoInputs 1) with
  | .ok outputs => outputs == echoOutputs 1
  | .error _ => Bool.false

#guard match echo.run echoContext (echoInputs 0) with
  | .ok outputs => outputs == echoOutputs 0
  | .error _ => Bool.false

end CompositeEitherInput

noctium_contract CompositeEitherInput where
  cell seen : Bool
  entry echo uses CompositeEitherInput.echo where
    write seen := disclose(eq(result.is_left, 1))
    return echoed
  end
end
