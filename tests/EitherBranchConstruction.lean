import Noctium.Frontend

open scoped Noctium
open Noctium

namespace EitherBranchConstruction

private def limitsWire : Helpers.Wire.Codec := {
  payload := .structure "EitherBranchConstruction.Limits"
  frameBytes := 6
  composites := {structures := [{
    id := "EitherBranchConstruction.Limits"
    fields := [
      {name := "count", type := .scalar (.uint 255)},
      {name := "enabled", type := .scalar .bool},
      {name := "memo", type := .bytes 4}
    ]
  }]}
}

private def flagsWire : Helpers.Wire.Codec := {
  payload := .vector 2 (.scalar .bool)
  frameBytes := 2
}

private def eitherWire : Helpers.Wire.Codec :=
  Helpers.Wire.either "EitherBranchConstruction.LimitsOrFlags" limitsWire flagsWire

noctium_witness fetchLimits(marker : Native) : Payload limitsWire

noctium_witness_circuit makeLeft using limitsWire, eitherWire where
  private value : Payload limitsWire
  output selected := disclose(left(Payload eitherWire, value))
end

noctium_witness_circuit makeRight using flagsWire, eitherWire where
  private value : Payload flagsWire
  output selected := disclose(right(Payload eitherWire, value))
end

noctium_witness_circuit fetchLeft using limitsWire, eitherWire where
  public marker : Native
  output selected := disclose(left(Payload eitherWire, witness fetchLimits(marker)))
end

private def otherLimitsWire : Helpers.Wire.Codec := {
  limitsWire with
  payload := .structure "EitherBranchConstruction.OtherLimits"
  composites := {structures := limitsWire.composites.structures.map fun declaration =>
    {declaration with id := "EitherBranchConstruction.OtherLimits"}}
}

/- error: Either branch does not match the declared arm type -/
#guard_msgs (substring := true) in
noctium_witness_circuit rejectsWrongNominalArm using otherLimitsWire, eitherWire where
  private value : Payload otherLimitsWire
  output selected := disclose(left(Payload eitherWire, value))
end

/- error: undisclosed private -/
#guard_msgs (substring := true) in
noctium_witness_circuit rejectsImplicitRelease using limitsWire, eitherWire where
  private value : Payload limitsWire
  output selected := left(Payload eitherWire, value)
end

private def context : EvalContext := {
  modulus := Field.modulus
  poseidon2 := fun _ _ _ => .error "unused by Either branch fixture"
}

private def leftLeaves := [
  ("count", 17), ("enabled", 1), ("memo.0", 0), ("memo.1", 1),
  ("memo.2", 2), ("memo.3", 255)]

private def rightLeaves := [("0", 1), ("1", 0)]

private def inputLeaves (pathPrefix : String) (active : _root_.Bool) (leaves : List (String × Nat)) :
    List (String × Value) :=
  leaves.map fun (name, value) => (pathPrefix ++ name, .native (if active then value else 0))

private def expected (isLeft : _root_.Bool) : List (String × Value) :=
  ("result.is_left", .native (if isLeft then 1 else 0)) ::
    inputLeaves "result.left." isLeft leftLeaves ++ inputLeaves "result.right." (!isLeft) rightLeaves

#guard (makeLeft.run context (inputLeaves "value." Bool.true leftLeaves)).toOption ==
  some (expected Bool.true)
#guard (makeRight.run context (inputLeaves "value." Bool.true rightLeaves)).toOption ==
  some (expected Bool.false)

#guard match Witness.compile fetchLeft.__program
    "noctium.witness-circuit.EitherBranchConstruction.fetchLeft.v1" with
  | .ok compiled => compiled.calls.length == 1
  | .error _ => Bool.false

noctium_contract Codec where
  entry makeLeft uses makeLeft arguments [value] where
    return selected
  end
  entry makeRight uses makeRight arguments [value] where
    return selected
  end
  entry fetchLeft uses fetchLeft where
    return selected
  end
end

end EitherBranchConstruction
