import Noctium.Frontend

open scoped Noctium
open Noctium
open Noctium.Helpers
open Noctium.Types

namespace NestedAggregateEquality

private def sampleWire : Helpers.Wire.Codec := {
  payload := .structure "NestedAggregateEquality.Sample"
  frameBytes := 135
  composites := {
    structures := [
      {id := "NestedAggregateEquality.Inner", fields := [
        {name := "octets", type := .bytes 2},
        {name := "enabled", type := .scalar .bool},
        {name := "amount", type := .scalar (.uint 255)}]},
      {id := "NestedAggregateEquality.Sample", fields := [
        {name := "head", type := .scalar .native},
        {name := "inner", type := .structure "NestedAggregateEquality.Inner"},
        {name := "pair", type := .tuple [
          .scalar .native, .vector 2 (.scalar .native)]},
        {name := "bytes", type := .bytes 2},
        {name := "kind", type := .enumeration "NestedAggregateEquality.Kind"}]}]
    enumerations := [{id := "NestedAggregateEquality.Kind", variants := [
      {name := "A"}, {name := "B"}, {name := "C"}]}]
  }
}

private def otherSampleWire : Helpers.Wire.Codec := {
  sampleWire with
  payload := .structure "NestedAggregateEquality.OtherSample"
  composites := {
    sampleWire.composites with
    structures := sampleWire.composites.structures.map fun declaration =>
      if declaration.id == "NestedAggregateEquality.Sample" then
        {declaration with id := "NestedAggregateEquality.OtherSample"}
      else declaration
  }
}

noctium_witness_circuit compareSample using sampleWire where
  public left : Payload sampleWire
  private right : Payload sampleWire
  output equalValue : Bool := disclose(eq(left, right))
end

#guard compareSample.__program.exports.any fun exported =>
  exported.compositeInputs.map (fun input => (input.name, input.type, input.visibility)) == [
    ("left", .structure "NestedAggregateEquality.Sample", .public),
    ("right", .structure "NestedAggregateEquality.Sample", .private)]

#guard (Noctium.Witness.compile compareSample.__program
  "noctium.witness-circuit.NestedAggregateEquality.compareSample.v1").isOk

private def equalityContext : EvalContext := {
  modulus := Field.modulus
  poseidon2 := fun _ _ _ => .error "unused by nested aggregate equality fixture"
}

private def sampleInputs (inputRoot : String) (head : Nat) : List (String × Value) := [
  (inputRoot ++ ".head", .native head),
  (inputRoot ++ ".inner.octets.0", .native 1),
  (inputRoot ++ ".inner.octets.1", .native 2),
  (inputRoot ++ ".inner.enabled", .native 1),
  (inputRoot ++ ".inner.amount", .native 5),
  (inputRoot ++ ".pair.0", .native 31),
  (inputRoot ++ ".pair.1.0", .native 41),
  (inputRoot ++ ".pair.1.1", .native 42),
  (inputRoot ++ ".bytes.0", .native 9),
  (inputRoot ++ ".bytes.1", .native 8),
  (inputRoot ++ ".kind.$tag", .native 2)]

private def compares (rightHead : Nat) (expected : _root_.Bool) : _root_.Bool :=
  match compareSample.run equalityContext
      (sampleInputs "left" 11 ++ sampleInputs "right" rightHead) with
  | .ok [(_, .bool actual)] => actual == expected
  | _ => Bool.false

#guard compares 11 Bool.true
#guard compares 12 Bool.false

/- error: undisclosed private -/
#guard_msgs (substring := true) in
noctium_witness_circuit rejectsUndisclosedPrivateSample using sampleWire where
  public left : Payload sampleWire
  private right : Payload sampleWire
  output equalValue : Bool := eq(left, right)
end

/- error: eq record operands must have the same nominal type -/
#guard_msgs (substring := true) in
noctium_witness_circuit rejectsMixedIdentity using sampleWire, otherSampleWire where
  public left : Payload sampleWire
  public right : Payload otherSampleWire
  output equalValue : Bool := disclose(eq(left, right))
end

end NestedAggregateEquality

noctium_contract NestedAggregateEquality where
  entry compare uses NestedAggregateEquality.compareSample where
    return same : Bool := equalValue
  end
end
