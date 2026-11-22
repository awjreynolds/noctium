import Noctium.Frontend

open scoped Noctium
open Noctium
open Noctium.Helpers
open Noctium.Types

namespace CheckedEnumCasts

private def statusWire : Wire.Codec := {
  payload := .enumeration "CheckedEnumCasts.Status"
  frameBytes := 1
  composites := {enumerations := [{
    id := "CheckedEnumCasts.Status"
    variants := [
      {name := "Pending"},
      {name := "Review"},
      {name := "Done"}
    ]
  }]}
}

noctium_witness_circuit convert using statusWire where
  public fieldOrdinal : Native
  public uintOrdinal : UInt 2
  output fromField := disclose(cast(Payload statusWire, fieldOrdinal))
  output fromUInt := disclose(cast(Payload statusWire, uintOrdinal))
  output first := disclose(default(Payload statusWire))
end

noctium_witness_circuit extract using statusWire where
  public choice : Payload statusWire
  output asField : Native := disclose(cast(Native, choice))
  output asUInt : UInt 2 := disclose(cast(UInt 2, choice))
end

noctium_witness_circuit narrow using statusWire where
  public choice : Payload statusWire
  output narrowed : UInt 1 := disclose(cast(UInt 1, choice))
end

/- error: undisclosed private -/
#guard_msgs (substring := true) in
noctium_witness_circuit rejectsPrivateEnumCast using statusWire where
  private ordinal : Native
  output choice := cast(Payload statusWire, ordinal)
end

#guard (Noctium.Witness.compile convert.__program
  "noctium.witness-circuit.CheckedEnumCasts.convert.v1").isOk
#guard (Noctium.Witness.compile extract.__program
  "noctium.witness-circuit.CheckedEnumCasts.extract.v1").isOk
#guard (Noctium.Witness.compile narrow.__program
  "noctium.witness-circuit.CheckedEnumCasts.narrow.v1").isOk

private def enumCastEvalContext : EvalContext := {
  modulus := Field.modulus
  poseidon2 := fun _ _ _ => .error "unused by checked enum casts"
}

#guard match convert.run enumCastEvalContext [
    ("fieldOrdinal", .native 0), ("uintOrdinal", .uint 3 2)] with
  | .ok outputs =>
    outputs.lookup "result.fromField.$tag" == some (.native 0) &&
    outputs.lookup "result.fromUInt.$tag" == some (.native 2) &&
    outputs.lookup "result.first.$tag" == some (.native 0)
  | .error _ => Bool.false

#guard match convert.run enumCastEvalContext [
    ("fieldOrdinal", .native 3), ("uintOrdinal", .uint 3 0)] with
  | .error _ => _root_.Bool.true
  | .ok _ => Bool.false

#guard match convert.run enumCastEvalContext [
    ("fieldOrdinal", .native 0), ("uintOrdinal", .uint 3 3)] with
  | .error _ => _root_.Bool.true
  | .ok _ => Bool.false

#guard match extract.run enumCastEvalContext [("choice.$tag", .native 2)] with
  | .ok outputs =>
    outputs.lookup "result.asField" == some (.native 2) &&
    outputs.lookup "result.asUInt" == some (.native 2)
  | .error _ => Bool.false

#guard match narrow.run enumCastEvalContext [("choice.$tag", .native 2)] with
  | .error _ => _root_.Bool.true
  | .ok _ => Bool.false

noctium_contract CheckedEnumCasts where
  entry convert uses CheckedEnumCasts.convert where
    return fromField
    return fromUInt
    return first
  end
  entry extract uses CheckedEnumCasts.extract where
    return fieldValue : Native := asField
    return unsignedValue : UInt 2 := asUInt
  end
  entry narrow uses CheckedEnumCasts.narrow where
    return narrowValue : UInt 1 := narrowed
  end
end

end CheckedEnumCasts
