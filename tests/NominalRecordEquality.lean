import Noctium.Frontend

open scoped Noctium
open Noctium
open Noctium.Helpers
open Noctium.Types

namespace NominalRecordEqualityFixture

private def pairedReadingWire : Helpers.Wire.Codec := {
  payload := .structure "NominalRecordEquality.PairedReading"
  frameBytes := 34
  composites := {structures := [{
    id := "NominalRecordEquality.PairedReading"
    fields := [
      {name := "reading", type := .scalar .native},
      {name := "count", type := .scalar (.uint 255)},
      {name := "active", type := .scalar .bool}
    ]
  }]}
}

private def otherReadingWire : Helpers.Wire.Codec := {
  payload := .structure "NominalRecordEquality.OtherReading"
  frameBytes := 34
  composites := {structures := [{
    id := "NominalRecordEquality.OtherReading"
    fields := [
      {name := "reading", type := .scalar .native},
      {name := "count", type := .scalar (.uint 255)},
      {name := "active", type := .scalar .bool}
    ]
  }]}
}

noctium_witness_circuit compare using pairedReadingWire where
  public left : Payload pairedReadingWire
  public right : Payload pairedReadingWire
  output comparison : Bool := eq(left, right)
end

#guard compare.__program.composites.structures.any fun declaration =>
  declaration.id == "NominalRecordEquality.PairedReading" &&
  declaration.fields.map (fun field => (field.name, field.type)) == [
    ("reading", .scalar .native), ("count", .scalar (.uint 255)),
    ("active", .scalar .bool)]

#guard compare.__program.exports.any fun exported =>
  exported.compositeInputs.map (fun input => (input.name, input.type, input.visibility)) == [
    ("left", .structure "NominalRecordEquality.PairedReading", .public),
    ("right", .structure "NominalRecordEquality.PairedReading", .public)]

#guard compare.__program.declarations.any fun declaration =>
  declaration.name == "NominalRecordEqualityFixture.compare" &&
  declaration.body.any fun statement =>
    match statement with
    | .return (some (.at _ (.eq (.ref "left") (.ref "right")))) => Bool.true
    | _ => Bool.false

private def equalityContext : EvalContext := {
  modulus := Field.modulus
  poseidon2 := fun _ _ _ => .error "unused by nominal record equality fixture"
}

private def comparisonInputs (leftReading leftCount : Nat) (leftActive : _root_.Bool)
    (rightReading rightCount : Nat) (rightActive : _root_.Bool) : List (String × Value) := [
  ("left.reading", .native leftReading), ("left.count", .native leftCount),
  ("left.active", .native (if leftActive then 1 else 0)),
  ("right.reading", .native rightReading), ("right.count", .native rightCount),
  ("right.active", .native (if rightActive then 1 else 0))]

private def compares (inputs : List (String × Value)) (expected : Nat) : _root_.Bool :=
  match compare.run equalityContext inputs with
  | .ok outputs => outputs == [("comparison", .bool (expected != 0))]
  | .error _ => Bool.false

#guard compares (comparisonInputs 9 17 Bool.true 9 17 Bool.true) 1
#guard compares (comparisonInputs 9 17 Bool.true 10 17 Bool.true) 0
#guard compares (comparisonInputs 9 17 Bool.true 9 18 Bool.true) 0
#guard compares (comparisonInputs 9 17 Bool.true 9 17 Bool.false) 0

/- error: eq record operands must have the same nominal type -/
#guard_msgs (substring := true) in
noctium_witness_circuit rejectsMixedIdentity using pairedReadingWire, otherReadingWire where
  public left : Payload pairedReadingWire
  public right : Payload otherReadingWire
  output comparison : Bool := eq(left, right)
end

/- error: undisclosed private -/
#guard_msgs (substring := true) in
noctium_witness_circuit rejectsPrivateEquality using pairedReadingWire where
  private left : Payload pairedReadingWire
  public right : Payload pairedReadingWire
  output comparison : Bool := eq(left, right)
end

end NominalRecordEqualityFixture

noctium_contract NominalRecordEqualityFixture where
  entry compare uses NominalRecordEqualityFixture.compare where
    return same : Bool := comparison
  end
end
