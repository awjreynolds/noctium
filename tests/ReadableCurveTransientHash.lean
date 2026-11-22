import Noctium.Frontend

open scoped Noctium
open Noctium
open Noctium.Helpers

namespace ReadableCurveTransientHash

private def curveFabWire : Helpers.Wire.Codec := {
  payload := .structure "CurveFabHashes.CurvePayload"
  frameBytes := 194
  composites := {structures := [
    {id := "CurveFabHashes.Inner", fields := [
      {name := "scalar", type := .scalar .jubjubScalar},
      {name := "point", type := .scalar .jubjubPoint}
    ]},
    {id := "CurveFabHashes.CurvePayload", fields := [
      {name := "inner", type := .structure "CurveFabHashes.Inner"},
      {name := "secpBase", type := .scalar (.foreign (.base .secp256k1))},
      {name := "secpPoint", type := .scalar (.foreign (.point .secp256k1))},
      {name := "pair", type := .tuple [
        .scalar .jubjubPoint,
        .scalar (.foreign (.point .secp256k1))
      ]}
    ]}
  ]}
}

noctium_witness_circuit hashCurvePayload using curveFabWire where
  private payload : Payload curveFabWire
  output digest : Native := disclose(transientHashValue(payload))
end

private def compiledCurvePayload := Noctium.Witness.compile hashCurvePayload.__program
  "noctium.witness-circuit.ReadableCurveTransientHash.hashCurvePayload.v1"

#guard curveFabWire.frameBytes == 194
#guard match compiledCurvePayload with
  | .ok compiled =>
    (compiled.plan.compress.splitOn "\"tag\":\"foreignEncodedField\"").length == 13
  | .error _ => _root_.Bool.false

/- error: undisclosed private -/
#guard_msgs (substring := true) in
noctium_witness_circuit rejectUndisclosedCurveDigest using curveFabWire where
  private payload : Payload curveFabWire
  output digest : Native := transientHashValue(payload)
end

end ReadableCurveTransientHash

noctium_contract ReadableCurveTransientHash where
  entry hash uses ReadableCurveTransientHash.hashCurvePayload where
    return digestResult : Native := digest
  end
end
