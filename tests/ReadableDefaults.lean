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

/- error: Jubjub values have no generic default expression -/
#guard_msgs (substring := true) in
noctium_witness_circuit unsupportedCurveDefault where
  output value := default(JubjubScalar)
end

/- error: byte string length exceeds the maximum of 1024 -/
#guard_msgs (substring := true) in
noctium_witness_circuit oversizedBytesDefault where
  output value := default(Bytes 1025)
end

end ReadableDefaults
