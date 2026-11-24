import Noctium.Authoring
import Noctium.Backend.Zkir

open scoped Noctium
open Noctium
open Noctium.Helpers

namespace DirectFieldlessEnumCodec

private def statusWire : Wire.Codec := {
  payload := .enumeration "DirectFieldlessEnumCodec.Status"
  frameBytes := 2
  composites := {enumerations := [{
    id := "DirectFieldlessEnumCodec.Status"
    variants := [{name := "Pending"}, {name := "Done"}]
  }]}
}

noctium_witness_circuit transcode using statusWire where
  public wire : Bytes 2
  let decoded := deserialize(Payload statusWire, wire)
  output encoded : Bytes 2 := disclose(serialize(enumMember(statusWire, Done), 2))
  output isDone : Bool := disclose(eq(decoded, enumMember(statusWire, Done)))
end

#guard (Noctium.Witness.compile transcode.__program
  "noctium.witness-circuit.DirectFieldlessEnumCodec.transcode.v1").isOk

private def enumCodecContext : EvalContext := {
  modulus := Field.modulus
  poseidon2 := fun _ _ _ => .error "unused by direct enum codec"
}

#guard match transcode.run enumCodecContext [("wire", .bytes 2 [1, 0])] with
  | .ok outputs =>
    outputs.lookup "result.encoded.0" == some (.native 1) &&
    outputs.lookup "result.encoded.1" == some (.native 0) &&
    outputs.lookup "result.isDone" == some (.native 1)
  | .error _ => Bool.false

#guard match transcode.run enumCodecContext [("wire", .bytes 2 [2, 0])] with
  | .error _ => _root_.Bool.true
  | .ok _ => Bool.false

#guard match transcode.run enumCodecContext [("wire", .bytes 2 [1, 9])] with
  | .ok outputs => outputs.lookup "result.isDone" == some (.native 1)
  | .error _ => Bool.false

private def onlyWire : Wire.Codec := {
  payload := .enumeration "DirectFieldlessEnumCodec.Only"
  frameBytes := 1
  composites := {enumerations := [{
    id := "DirectFieldlessEnumCodec.Only"
    variants := [{name := "Only"}]
  }]}
}

noctium_witness_circuit singleVariant using onlyWire where
  output encoded : Bytes 1 := disclose(serialize(enumMember(onlyWire, Only), 1))
end

#guard match singleVariant.run enumCodecContext [] with
  | .ok [("encoded", .bytes 1 [0])] => Bool.true
  | _ => Bool.false

private def otherStatusWire : Wire.Codec := {
  payload := .enumeration "OtherModule.Status"
  frameBytes := 2
  composites := {enumerations := [{
    id := "OtherModule.Status"
    variants := [{name := "Pending"}, {name := "Done"}]
  }]}
}

/- error: eq enum operands must have the same nominal type -/
#guard_msgs (substring := true) in
noctium_witness_circuit rejectsWrongIdentity using statusWire, otherStatusWire where
  public wire : Bytes 2
  let decoded := deserialize(Payload statusWire, wire)
  output mismatch : Bool := eq(decoded, enumMember(otherStatusWire, Done))
end

/- error: undisclosed private -/
#guard_msgs (substring := true) in
noctium_witness_circuit rejectsPrivateDecodeOutput using statusWire where
  private wire : Bytes 2
  output decoded := deserialize(Payload statusWire, wire)
end

noctium_contract Codec where
  entry transcode uses transcode where
    return serialized : Bytes 2 := encoded
    return matchesDone : Bool := isDone
  end
end

#guard Codec.entrypoints.all fun entrypoint =>
  match Backend.Zkir.lowerEntrypoint Codec.state entrypoint with
  | .ok _ => Bool.true
  | .error _ => Bool.false

end DirectFieldlessEnumCodec
