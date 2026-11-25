import Noctium.Frontend
import Noctium.Backend.Impact
import Noctium.Backend.Zkir

open scoped Noctium
open Lean
open Noctium
open Noctium.Helpers
open Noctium.Types

namespace NestedMaybeUInt

private def uint8Wire : Helpers.Wire.Codec := {
  payload := .scalar (.uint 255)
  frameBytes := 1
}

private def maybeUInt8Wire : Helpers.Wire.Codec := Helpers.Wire.maybe
  "NestedMaybeUInt.inspect.MaybeUInt8" uint8Wire

noctium_witness_circuit inspect using maybeUInt8Wire where
  public outer : Bool
  public inner : Bool
  public value : UInt 8
  output result := if outer then
    some(if inner then some(value) else none(UInt 8))
  else none(Payload maybeUInt8Wire)
end

end NestedMaybeUInt

noctium_contract NestedMaybeUInt where
  entry inspect uses NestedMaybeUInt.inspect where
    return result
  end
end

private def compiledInspect := Noctium.Witness.compile NestedMaybeUInt.inspect.__program
  "noctium.witness-circuit.NestedMaybeUInt.inspect.v1"

#guard match compiledInspect with
  | .ok compiled => compiled.circuit.inputs.map (·.name) == ["outer", "inner", "value"] &&
      compiled.circuit.outputs.map (·.name) == [
        "result.is_some", "result.value.is_some", "result.value.value"]
  | .error _ => Bool.false

private def inspectEntry : Entrypoint :=
  (NestedMaybeUInt.entrypoints.find? (·.name == "inspect")).getD
    {name := "missing", circuit := {name := "missing"}}

private def structureFields? (environment : CompositeEnv) (id : String) :
    Option (List (String × CompositeType)) := do
  let declaration ← environment.structures.find? (·.id == id)
  pure (declaration.fields.map fun field => (field.name, field.type))

#guard match inspectEntry.returnViews with
  | [view] =>
      view.name == "result" &&
      match view.type with
      | .structure outerId =>
          match structureFields? view.environment outerId with
          | some [
              ("is_some", .scalar .bool),
              ("value", .structure innerId)] =>
                structureFields? view.environment innerId == some [
                  ("is_some", .scalar .bool),
                  ("value", .scalar (.uint 255))]
          | _ => Bool.false
      | _ => Bool.false
  | _ => Bool.false

#guard match Backend.Impact.lower NestedMaybeUInt.state inspectEntry with
  | .ok _ => Bool.true
  | .error _ => Bool.false

#guard (Backend.Zkir.lowerEntrypoint NestedMaybeUInt.state inspectEntry).isOk

private def maybeContext : EvalContext := {
  modulus := Field.modulus
  poseidon2 := fun _ _ _ => .error "unused by nested Maybe UInt fixture"
}

private def runInspect (outer inner : _root_.Bool) (value : Nat) :=
  inspectEntry.run maybeContext [
    ("outer", .bool outer),
    ("inner", .bool inner),
    ("value", .uint 255 value)
  ] {trees := []}

#guard match runInspect Bool.false Bool.true 255 with
  | .ok (outputs, _) =>
      outputs.lookup "result.is_some" == some (.native 0) &&
      outputs.lookup "result.value.is_some" == some (.native 0) &&
      outputs.lookup "result.value.value" == some (.native 0)
  | .error _ => Bool.false

#guard match runInspect Bool.true Bool.false 255 with
  | .ok (outputs, _) =>
      outputs.lookup "result.is_some" == some (.native 1) &&
      outputs.lookup "result.value.is_some" == some (.native 0) &&
      outputs.lookup "result.value.value" == some (.native 0)
  | .error _ => Bool.false

#guard match runInspect Bool.true Bool.true 0 with
  | .ok (outputs, _) =>
      outputs.lookup "result.is_some" == some (.native 1) &&
      outputs.lookup "result.value.is_some" == some (.native 1) &&
      outputs.lookup "result.value.value" == some (.native 0)
  | .error _ => Bool.false

#guard match runInspect Bool.true Bool.true 255 with
  | .ok (outputs, _) =>
      outputs.lookup "result.is_some" == some (.native 1) &&
      outputs.lookup "result.value.is_some" == some (.native 1) &&
      outputs.lookup "result.value.value" == some (.native 255)
  | .error _ => Bool.false
