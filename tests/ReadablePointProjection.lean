import Noctium.Frontend
import Noctium.Disclosure

open scoped Noctium
open Noctium

private abbrev schnorrWire := Crypto.JubjubSchnorrSignature.codec
private abbrev ed25519Wire := Crypto.Ed25519Signature.codec

noctium_witness schnorrSignature() : Payload schnorrWire

noctium_witness_circuit readablePointProjection using schnorrWire where
  private signature : Payload schnorrWire
  output point : JubjubPoint := disclose(field(signature, announcement))
end

noctium_witness_circuit readablePointGroupedProjection using schnorrWire where
  private signature : Payload schnorrWire
  output point : JubjubPoint := disclose(field(signature, announcement))
  output responseValue : Native := disclose(field(signature, response))
end

noctium_witness_circuit readablePointPatternControl using schnorrWire where
  private signature : Payload schnorrWire as { announcement, response := signedResponse }
  output point : JubjubPoint := disclose(announcement)
  output responseValue : Native := disclose(signedResponse)
end

noctium_witness_circuit readablePointWitnessCall using schnorrWire where
  let signature := witness schnorrSignature()
  output point : JubjubPoint := disclose(field(signature, announcement))
  output responseValue : Native := disclose(field(signature, response))
end

noctium_witness_circuit readableForeignPointProjection using ed25519Wire where
  private signature : Payload ed25519Wire
  output point : Curve25519Point := disclose(field(signature, r))
  output scalarValue : Curve25519Scalar := disclose(field(signature, s))
end

noctium_witness_circuit readableForeignPointPatternControl using ed25519Wire where
  private signature : Payload ed25519Wire as { r := signedPoint, s := signedScalar }
  output point : Curve25519Point := disclose(signedPoint)
  output scalarValue : Curve25519Scalar := disclose(signedScalar)
end

noctium_contract ReadablePointProjection where
  entry direct uses readablePointProjection where
    return outPoint : JubjubPoint := point
  end
  entry projected uses readablePointGroupedProjection where
    return outPoint : JubjubPoint := point
    return outResponse : Native := responseValue
  end
  entry structured uses readablePointPatternControl where
    return outPoint : JubjubPoint := point
    return outResponse : Native := responseValue
  end
  entry witnessCall uses readablePointWitnessCall where
    return outPoint : JubjubPoint := point
    return outResponse : Native := responseValue
  end
  entry foreignPoint uses readableForeignPointProjection where
    return outPoint : Curve25519Point := point
    return outScalar : Curve25519Scalar := scalarValue
  end
  entry foreignPointStructured uses readableForeignPointPatternControl where
    return outPoint : Curve25519Point := point
    return outScalar : Curve25519Scalar := scalarValue
  end
end

#guard readablePointProjection.outputs.map (·.ty) == [.jubjubPoint]
#guard readablePointGroupedProjection.outputs.map (·.ty) == List.replicate 3 .native
#guard match Disclosure.circuit readablePointProjection with
  | .ok _ => Bool.true
  | .error _ => Bool.false
#guard match Disclosure.circuit readablePointGroupedProjection with
  | .ok _ => Bool.true
  | .error _ => Bool.false
#guard readableForeignPointProjection.outputs.map (·.ty) == List.replicate 6 .native
#guard match Disclosure.circuit readableForeignPointProjection with
  | .ok _ => Bool.true
  | .error _ => Bool.false

/- error: tests/ReadablePointProjection.lean -/
#guard_msgs (substring := true) in
noctium_witness_circuit rejectsUndisclosedPointProjection using schnorrWire where
  private signature : Payload schnorrWire
  output point : JubjubPoint := field(signature, announcement)
end
