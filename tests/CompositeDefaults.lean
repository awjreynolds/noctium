import Noctium.Frontend
import Noctium.Types.Either

open scoped Noctium
open Noctium
open Noctium.Helpers
open Noctium.Types

namespace CompositeDefaults

private def limitsId : Types.DeclId := "CompositeDefaults.Limits"
private def maybeLimitsId : Types.DeclId := "CompositeDefaults.MaybeLimits"
private def eitherId : Types.DeclId :=
  (Either.scalarTypeId "CompositeDefaults" (.uint 255) .bool).toOption.getD ""

private def limitsDeclaration : Types.StructDecl := {
  id := limitsId
  fields := [
    {name := "count", type := .scalar (.uint 255)},
    {name := "enabled", type := .scalar .bool},
    {name := "memo", type := .bytes 4}
  ]
}

private def limitsWire : Helpers.Wire.Codec := {
  payload := .structure limitsId
  frameBytes := 6
  composites := {structures := [limitsDeclaration]}
}

private def limitsVectorWire : Helpers.Wire.Codec := {
  payload := .vector 2 (.structure limitsId)
  frameBytes := 12
  composites := {structures := [limitsDeclaration]}
}

private def maybeLimitsWire : Helpers.Wire.Codec := {
  payload := .structure maybeLimitsId
  frameBytes := 7
  composites := {structures := [limitsDeclaration, {
    id := maybeLimitsId
    fields := [
      {name := "is_some", type := .scalar .bool},
      {name := "value", type := .structure limitsId}
    ]
  }]}
}

private def eitherWire : Helpers.Wire.Codec := {
  payload := .structure eitherId
  frameBytes := 3
  composites := (Either.scalarEnvironment eitherId (.uint 255) .bool).toOption.getD {}
}

noctium_witness_circuit defaults using limitsWire, limitsVectorWire, maybeLimitsWire, eitherWire where
  output recordValue := default(Payload limitsWire)
  output vectorValue := default(Payload limitsVectorWire)
  output maybeValue := default(Payload maybeLimitsWire)
  output eitherValue := default(Payload eitherWire)
end

private def outputTerm? (binding : String) : Option Helpers.Term := do
  let declaration ← defaults.__program.declarations.find? (·.name == "CompositeDefaults.defaults")
  match declaration.body.find? fun statement =>
      match statement with
      | .bind name _ _ => name == binding
      | _ => _root_.Bool.false with
  | some (.bind _ _ (.at _ value)) => some value
  | some (.bind _ _ value) => some value
  | _ => none

#guard maybeLimitsId == "CompositeDefaults.MaybeLimits"
#guard eitherId == "CompositeDefaults.EitherLeftUInt8RightBool"
#guard (Noctium.Witness.compile defaults.__program
  "noctium.witness-circuit.CompositeDefaults.defaults.v1").isOk

#guard match outputTerm? "__noctium_output_0_recordValue" with
  | some (.composite (.structure "CompositeDefaults.Limits") [
      .uint 255 0, .bool Bool.false, .native 0, .native 0, .native 0, .native 0]) => Bool.true
  | _ => Bool.false

#guard match outputTerm? "__noctium_output_1_vectorValue" with
  | some (.composite (.vector 2 (.structure "CompositeDefaults.Limits")) [
      .uint 255 0, .bool Bool.false, .native 0, .native 0, .native 0, .native 0,
      .uint 255 0, .bool Bool.false, .native 0, .native 0, .native 0, .native 0]) => Bool.true
  | _ => Bool.false

#guard match outputTerm? "__noctium_output_2_maybeValue" with
  | some (.composite (.structure "CompositeDefaults.MaybeLimits") [
      .bool Bool.false, .uint 255 0, .bool Bool.false, .native 0, .native 0, .native 0, .native 0]) => Bool.true
  | _ => Bool.false

#guard match outputTerm? "__noctium_output_3_eitherValue" with
  | some (.composite (.structure "CompositeDefaults.EitherLeftUInt8RightBool")
      [.bool Bool.false, .uint 255 0, .bool Bool.false]) => Bool.true
  | _ => Bool.false

/-- error: add codec 'limitsWire' to the circuit's using clause -/
#guard_msgs (substring := true) in
noctium_witness_circuit unselectedCodec where
  output value := default(Payload limitsWire)
end

end CompositeDefaults

noctium_contract CompositeDefaults where
  entry defaults uses CompositeDefaults.defaults where
    return recordValue
    return vectorValue
    return maybeValue
    return eitherValue
  end
end
