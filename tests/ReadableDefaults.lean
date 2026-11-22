import Noctium.Frontend
import Noctium.Backend.Zkir

open scoped Noctium
open Noctium
open Noctium.Helpers

namespace ReadableDefaults

private def byteVectorWire : Wire.Codec := {
  payload := .vector 2 (.scalar (.uint 255))
  frameBytes := 2
}

private def emptyByteVectorWire : Wire.Codec := {
  payload := .vector 0 (.scalar (.uint 255))
  frameBytes := 0
}

noctium_witness_circuit defaults using byteVectorWire, emptyByteVectorWire where
  output nativeValue : Native := default(Native)
  output boolValue : Bool := default(Bool)
  output uintValue : UInt 8 := default(UInt 8)
  output emptyBytes : Bytes 0 := default(Bytes 0)
  output shortBytes : Bytes 3 := default(Bytes 3)
  output wordBytes : Bytes32 := default(Bytes32)
  output vectorValue := default(Payload byteVectorWire)
  output emptyVectorValue := default(Payload emptyByteVectorWire)
end

noctium_witness_circuit curveDefaults where
  let jubjubScalarValue : JubjubScalar := default(JubjubScalar)
  prove eq(jubjubScalarToNative(jubjubScalarValue),
    jubjubScalarToNative(jubjubScalarFromNative(0)))
  let jubjubPointValue : JubjubPoint := default(JubjubPoint)
  let jubjubIdentity := jubjubFromCoordinates(0, 1)
  prove boolAnd(
    eq(jubjubX(jubjubPointValue), jubjubX(jubjubIdentity)),
    eq(jubjubY(jubjubPointValue), jubjubY(jubjubIdentity)))

  let secp256k1BaseValue : Secp256k1Base := default(Secp256k1Base)
  prove eq(secp256k1BaseValue, secp256k1Base(0))
  let secp256k1ScalarValue : Secp256k1Scalar := default(Secp256k1Scalar)
  prove eq(secp256k1ScalarValue, secp256k1Scalar(0))
  let secp256k1PointValue : Secp256k1Point := default(Secp256k1Point)
  prove eq(secp256k1PointValue, secp256k1Identity())

  let secp256r1BaseValue : Secp256r1Base := default(Secp256r1Base)
  prove eq(secp256r1BaseValue, secp256r1Base(0))
  let secp256r1ScalarValue : Secp256r1Scalar := default(Secp256r1Scalar)
  prove eq(secp256r1ScalarValue, secp256r1Scalar(0))
  let secp256r1PointValue : Secp256r1Point := default(Secp256r1Point)
  prove eq(secp256r1PointValue, secp256r1Identity())

  let curve25519BaseValue : Curve25519Base := default(Curve25519Base)
  prove eq(curve25519BaseValue, curve25519Base(0))
  let curve25519ScalarValue : Curve25519Scalar := default(Curve25519Scalar)
  prove eq(curve25519ScalarValue, curve25519Scalar(0))
  let curve25519PointValue : Curve25519Point := default(Curve25519Point)
  prove eq(curve25519PointValue, curve25519Identity())

  output verified : Bool := disclose(true)
end

private def outputTerms? : Option (List (ResultType × Term)) := do
  let declaration ← defaults.__program.declarations.find? (·.name == "ReadableDefaults.defaults")
  some (declaration.body.filterMap fun statement =>
    match statement with
    | .bind name type (.at _ value) =>
      if name.startsWith "__noctium_output_" then some (type, value) else none
    | .bind name type value =>
      if name.startsWith "__noctium_output_" then some (type, value) else none
    | _ => none)

#guard (Noctium.Witness.compile defaults.__program
  "noctium.witness-circuit.ReadableDefaults.defaults.v1").isOk

#guard match outputTerms? with
  | some [
      (.scalar .native, .native 0),
      (.scalar .bool, .bool Bool.false),
      (.scalar (.uint 255), .uint 255 0),
      (.scalar (.bytes 0), .bytes (.bytesLiteral 0 []) []),
      (.scalar (.bytes 3), .bytes (.bytesLiteral 3 [0, 0, 0]) []),
      (.scalar (.bytes 32), .bytes32Literal bytes),
      (.composite (.vector 2 (.scalar (.uint 255))), .composite
        (.vector 2 (.scalar (.uint 255))) [.uint 255 0, .uint 255 0]),
      (.composite (.vector 0 (.scalar (.uint 255))), .composite
        (.vector 0 (.scalar (.uint 255))) [])] => bytes == List.replicate 32 0
  | _ => Bool.false

#guard (Noctium.Witness.compile curveDefaults.__program
  "noctium.witness-circuit.ReadableDefaults.curveDefaults.v1").isOk

/- error: byte string length exceeds the maximum of 1024 -/
#guard_msgs (substring := true) in
noctium_witness_circuit oversizedBytesDefault where
  output value := default(Bytes 1025)
end

end ReadableDefaults

noctium_contract ReadableCurveDefaults where
  entry inspect uses ReadableDefaults.curveDefaults where
    return result : Bool := verified
  end
end
