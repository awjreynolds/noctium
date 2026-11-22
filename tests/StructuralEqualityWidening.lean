import Noctium.Frontend

open scoped Noctium
open Noctium
open Noctium.Helpers
open Noctium.Types

namespace StructuralEqualityWidening

private def vector8Wire : Helpers.Wire.Codec := {
  payload := .vector 2 (.scalar (.uint 255))
  frameBytes := 2
}

private def vector16Wire : Helpers.Wire.Codec := {
  payload := .vector 2 (.scalar (.uint 65535))
  frameBytes := 4
}

private def vector3Wire : Helpers.Wire.Codec := {
  payload := .vector 3 (.scalar (.uint 255))
  frameBytes := 3
}

private def tuple8Wire : Helpers.Wire.Codec := {
  payload := .tuple [.scalar (.uint 255), .scalar .native]
  frameBytes := 33
}

private def tuple16Wire : Helpers.Wire.Codec := {
  payload := .tuple [.scalar (.uint 65535), .scalar .native]
  frameBytes := 34
}

noctium_witness_circuit compareVectors using vector8Wire, vector16Wire where
  public left : Payload vector8Wire
  private right : Payload vector16Wire
  output vectorEqual : Bool := disclose(eq(left, right))
end

noctium_witness_circuit compareTuples using tuple8Wire, tuple16Wire where
  public left : Payload tuple8Wire
  private right : Payload tuple16Wire
  output tupleEqual : Bool := disclose(eq(left, right))
end

#guard (Noctium.Witness.compile compareVectors.__program
  "noctium.witness-circuit.StructuralEqualityWidening.compareVectors.v1").isOk
#guard (Noctium.Witness.compile compareTuples.__program
  "noctium.witness-circuit.StructuralEqualityWidening.compareTuples.v1").isOk

/- error: eq aggregate operands must have compatible checked types -/
#guard_msgs (substring := true) in
noctium_witness_circuit rejectsVectorLengthMismatch using vector8Wire, vector3Wire where
  public left : Payload vector8Wire
  public right : Payload vector3Wire
  output same : Bool := disclose(eq(left, right))
end

/- error: undisclosed private -/
#guard_msgs (substring := true) in
noctium_witness_circuit rejectsUndisclosedPrivateComparison using vector8Wire, vector16Wire where
  public left : Payload vector8Wire
  private right : Payload vector16Wire
  output same : Bool := eq(left, right)
end

end StructuralEqualityWidening

noctium_contract StructuralEqualityWidening where
  entry compareVectors uses StructuralEqualityWidening.compareVectors where
    return same : Bool := vectorEqual
  end
  entry compareTuples uses StructuralEqualityWidening.compareTuples where
    return same : Bool := tupleEqual
  end
end
