import Noctium.Frontend

open scoped Noctium
open Noctium
open Noctium.Helpers

namespace ReadableFabHash

private def nestedPayloadWire : Helpers.Wire.Codec := {
  payload := .structure "ReadableFabHash.Payload"
  frameBytes := 165
  composites := {
    structures := [
      {id := "ReadableFabHash.Inner", fields := [
        {name := "tag", type := .bytes 2},
        {name := "enabled", type := .scalar .bool},
        {name := "amount", type := .scalar (.uint 65535)}]},
      {id := "ReadableFabHash.Payload", fields := [
        {name := "head", type := .scalar .native},
        {name := "inner", type := .structure "ReadableFabHash.Inner"},
        {name := "pair", type := .tuple [
          .scalar .native, .vector 2 (.scalar .native)]},
        {name := "empty", type := .vector 0 (.scalar .native)},
        {name := "tail", type := .scalar .native}]}]
  }
}

private def emptyPayloadWire : Helpers.Wire.Codec := {
  payload := .structure "ReadableFabHash.EmptyPayload"
  frameBytes := 0
  composites := {structures := [
    {id := "ReadableFabHash.EmptyPayload", fields := []}]}
}

noctium_witness_circuit hashReadablePayload using nestedPayloadWire, emptyPayloadWire where
  private payload : Payload nestedPayloadWire
  output payloadDigest : Native := disclose(transientHashValue(payload))
  output emptyPayloadDigest : Native := disclose(
    transientHashValue(default(Payload emptyPayloadWire)))
end

#guard (Noctium.Witness.compile hashReadablePayload.__program
  "noctium.witness-circuit.ReadableFabHash.hashReadablePayload.v1").isOk

/- error: undisclosed private -/
#guard_msgs (substring := true) in
noctium_witness_circuit rejectsUndisclosedReadableHash using nestedPayloadWire where
  private payload : Payload nestedPayloadWire
  output digest : Native := transientHashValue(payload)
end

end ReadableFabHash

noctium_contract ReadableFabHash where
  entry digest uses ReadableFabHash.hashReadablePayload where
    return digest : Native := payloadDigest
    return emptyDigest : Native := emptyPayloadDigest
  end
end
