import Noctium.Frontend

open scoped Noctium
open Noctium
open Noctium.Helpers
open Noctium.Types

namespace CompositeMaybeInput

private def limitsWire : Helpers.Wire.Codec := {
  payload := .structure "CompositeMaybeInput.Limits"
  frameBytes := 6
  composites := {structures := [{
    id := "CompositeMaybeInput.Limits"
    fields := [
      {name := "count", type := .scalar (.uint 255)},
      {name := "enabled", type := .scalar .bool},
      {name := "memo", type := .bytes 4}
    ]
  }]}
}

private def maybeWire : Helpers.Wire.Codec := Helpers.Wire.maybe
  "CompositeMaybeInput.MaybeLimits" limitsWire

#guard maybeWire.payload == .structure "CompositeMaybeInput.MaybeLimits"
#guard maybeWire.frameBytes == 7
#guard match maybeWire.composites.structures.find? (·.id == "CompositeMaybeInput.MaybeLimits") with
  | some declaration => declaration.fields.map (fun field => (field.name, field.type)) == [
      ("is_some", .scalar .bool), ("value", .structure "CompositeMaybeInput.Limits")]
  | none => Bool.false

private def collidingPayload : Helpers.Wire.Codec := {
  payload := .structure "CompositeMaybeInput.MaybeLimits"
  frameBytes := 1
  composites := {structures := [{
    id := "CompositeMaybeInput.MaybeLimits"
    fields := [{name := "present", type := .scalar .bool}]
  }]}
}

private def codecDeclarations (codec : Helpers.Wire.Codec) :
    Except String (List Helpers.Declaration) := do
  let compiled ← match Types.compileType codec.composites codec.payload with
    | .ok value => pure value
    | .error diagnostic => throw diagnostic.message
  Helpers.Wire.declarations compiled "checked" codec.frameBytes ⟨0, 1⟩ ⟨0, 2⟩

#guard match codecDeclarations (Helpers.Wire.maybe
    "CompositeMaybeInput.MaybeLimits" collidingPayload) with
  | .error message => message.contains "duplicate declaration identity"
  | .ok _ => Bool.false

#guard match codecDeclarations (Helpers.Wire.maybe "CompositeMaybeInput.TooNarrow"
    {limitsWire with frameBytes := 5}) with
  | .error message => message.contains "requires at least 7 bytes"
  | .ok _ => Bool.false

#guard match codecDeclarations (Helpers.Wire.maybe "CompositeMaybeInput.TooWide" {
    limitsWire with frameBytes := Noctium.maxByteOperationLength + 1
  }) with
  | .error message => message.contains "aggregate wire width exceeds the source limit"
  | .ok _ => Bool.false

noctium_witness_circuit echo using maybeWire where
  public value : Payload maybeWire
  output echoed := value
end

private def compiledEcho := Noctium.Witness.compile echo.__program
  "noctium.witness-circuit.CompositeMaybeInput.echo.v1"

#guard match compiledEcho with
  | .ok compiled =>
      compiled.circuit.inputs.map (·.name) == [
        "value.is_some", "value.value.count", "value.value.enabled",
        "value.value.memo.0", "value.value.memo.1", "value.value.memo.2", "value.value.memo.3"] &&
      compiled.circuit.outputs.map (·.name) == [
        "result.is_some", "result.value.count", "result.value.enabled",
        "result.value.memo.0", "result.value.memo.1", "result.value.memo.2", "result.value.memo.3"]
  | .error _ => Bool.false

private def echoContext : EvalContext := {
  modulus := Field.modulus
  poseidon2 := fun _ _ _ => .error "unused by aggregate Maybe echo fixture"
}

#guard match echo.run echoContext [
    ("value.is_some", .native 1), ("value.value.count", .native 17),
    ("value.value.enabled", .native 1), ("value.value.memo.0", .native 0),
    ("value.value.memo.1", .native 1), ("value.value.memo.2", .native 2),
    ("value.value.memo.3", .native 255)] with
  | .ok outputs => outputs == [
      ("result.is_some", .native 1), ("result.value.count", .native 17),
      ("result.value.enabled", .native 1), ("result.value.memo.0", .native 0),
      ("result.value.memo.1", .native 1), ("result.value.memo.2", .native 2),
      ("result.value.memo.3", .native 255)]
  | .error _ => Bool.false

#guard match echo.run echoContext [
    ("value.is_some", .native 0), ("value.value.count", .native 0),
    ("value.value.enabled", .native 0), ("value.value.memo.0", .native 0),
    ("value.value.memo.1", .native 0), ("value.value.memo.2", .native 0),
    ("value.value.memo.3", .native 0)] with
  | .ok outputs => outputs == [
      ("result.is_some", .native 0), ("result.value.count", .native 0),
      ("result.value.enabled", .native 0), ("result.value.memo.0", .native 0),
      ("result.value.memo.1", .native 0), ("result.value.memo.2", .native 0),
      ("result.value.memo.3", .native 0)]
  | .error _ => Bool.false

#guard match echo.run echoContext [
    ("value.is_some", .native 0), ("value.value.count", .native 17),
    ("value.value.enabled", .native 1), ("value.value.memo.0", .native 0),
    ("value.value.memo.1", .native 1), ("value.value.memo.2", .native 2),
    ("value.value.memo.3", .native 255)] with
  | .ok outputs => outputs == [
      ("result.is_some", .native 0), ("result.value.count", .native 17),
      ("result.value.enabled", .native 1), ("result.value.memo.0", .native 0),
      ("result.value.memo.1", .native 1), ("result.value.memo.2", .native 2),
      ("result.value.memo.3", .native 255)]
  | .error _ => Bool.false

end CompositeMaybeInput

noctium_contract CompositeMaybeInput where
  cell seen : Bool
  entry echo uses CompositeMaybeInput.echo where
    write seen := disclose(eq(result.is_some, 1))
    return echoed
  end
end
