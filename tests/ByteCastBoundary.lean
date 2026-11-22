import Noctium.Frontend
import Noctium.Backend.Zkir
import Noctium.Semantics

open scoped Noctium
open Noctium
open Noctium.Helpers

noctium_circuit ordinaryByteProjectionCast where
  private payload : Bytes 1
  output decoded : UInt 8 := disclose(deserialize(UInt 8, payload))
  output widened : Native := disclose(cast(Native, byteAt(payload, 0)))
end

noctium_witness_circuit readableByteProjectionCast where
  private payload : Bytes 1
  output decoded : UInt 8 := disclose(deserialize(UInt 8, payload))
  output widened : Native := disclose(cast(Native, byteAt(payload, 0)))
end

#guard (Noctium.Backend.Zkir.lowerCircuit ordinaryByteProjectionCast).isOk
#guard (Noctium.Witness.compile readableByteProjectionCast.__program
  "noctium.witness-circuit.readableByteProjectionCast.v1").isOk

#guard match ordinaryByteProjectionCast.run
    {modulus := Noctium.Field.modulus, poseidon2 := fun _ _ _ => .error "unused"}
    [("payload", .bytes 1 [255])] with
  | .ok [("decoded", .uint 255 255), ("widened", .native 255)] => _root_.Bool.true
  | _ => _root_.Bool.false

private def helperCastRejected (target : Ty) (source : Term) : _root_.Bool :=
  match Noctium.Helpers.infer {} 0 [] {} (.cast target source) with
  | .error diagnostic => diagnostic.message == "byte strings do not support scalar casts"
  | .ok _ => _root_.Bool.false

#guard (Noctium.Helpers.infer {} 0 [] {} (.cast .native (.uint 255 42))).isOk
#guard helperCastRejected .native (.bytes (.bytesLiteral 1 [42]) [])
#guard helperCastRejected (.bytes 1) (.native 42)

/- error: byte strings do not support scalar casts -/
#guard_msgs (substring := true) in
noctium_circuit rejectsBytesToNative where
  private payload : Bytes 1
  output widened : Native := cast(Native, payload)
end

/- error: byte strings do not support scalar casts -/
#guard_msgs (substring := true) in
noctium_circuit rejectsNativeToBytes where
  private value : Native
  output encoded : Bytes 1 := cast(Bytes 1, value)
end

/- error: byte strings do not support scalar casts -/
#guard_msgs (substring := true) in
noctium_witness_circuit rejectsReadableBytesToNative where
  private payload : Bytes 1
  output widened : Native := cast(Native, payload)
end

/- error: byte strings do not support scalar casts -/
#guard_msgs (substring := true) in
noctium_witness_circuit rejectsReadableNativeToBytes where
  private value : Native
  output encoded : Bytes 1 := cast(Bytes 1, value)
end
