import Noctium.Frontend

open scoped Noctium
open Noctium
open Noctium.Helpers
open Noctium.Types

namespace CurveAggregateContract

private def curveAggregateWire : Wire.Codec := {
  payload := .structure "CurveAggregateContract.Payload"
  frameBytes := 194
  composites := {structures := [
    {id := "CurveAggregateContract.Payload", fields := [
      {name := "jubjubScalar", type := .scalar .jubjubScalar},
      {name := "jubjubPoint", type := .scalar .jubjubPoint},
      {name := "secp256k1Base", type := .scalar (.foreign (.base .secp256k1))},
      {name := "secp256k1Point", type := .scalar (.foreign (.point .secp256k1))},
      {name := "pair", type := .tuple [
        .scalar .jubjubScalar,
        .scalar (.foreign (.point .secp256k1))]}
    ]}
  ]}
}

noctium_witness_circuit inspect using curveAggregateWire where
  public payload : Payload curveAggregateWire
  output echoedPayload := disclose(payload)
  output jubjubScalarValue : Native :=
    disclose(jubjubScalarToNative(field(payload, jubjubScalar)))
  output baseValue : Secp256k1Base := disclose(field(payload, secp256k1Base))
end

#guard curveAggregateWire.frameBytes == 194
#guard (Noctium.Witness.compile inspect.__program
  "noctium.witness-circuit.CurveAggregateContract.inspect.v1").isOk

/- error: undisclosed private -/
#guard_msgs (substring := true) in
noctium_witness_circuit rejectPrivateEcho using curveAggregateWire where
  private payload : Payload curveAggregateWire
  output echoedPayload := payload
end

end CurveAggregateContract

noctium_contract CurveAggregateContract where
  entry inspect uses CurveAggregateContract.inspect where
    return jubjubScalar : Native := jubjubScalarValue
    return echoedPayload
    return base : Secp256k1Base := baseValue
  end
end
