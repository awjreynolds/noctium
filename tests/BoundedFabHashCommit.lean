import Noctium.Frontend
import Noctium.Helpers

open scoped Noctium
open Noctium
open Noctium.Types

private def boundedFabHashEnvironment : CompositeEnv := {
  structures := [{id := "BoundedFabHashCommit.Payload", fields := [
    {name := "count", type := .scalar (.uint 6)}
  ]}]
}

private def boundedFabHashPayloadType : CompositeType :=
  .structure "BoundedFabHashCommit.Payload"

noctium_circuit boundedFabHashInputs where
  private count : UIntRange 7
  private persistentOpening : Bytes32
  private transientOpening : Native
  output persistentDigest : Bytes32 := disclose(persistentHashFab(
    boundedFabHashEnvironment, boundedFabHashPayloadType, [count]))
  output persistentCommitDigest : Bytes32 := disclose(persistentCommitFab(
    boundedFabHashEnvironment, boundedFabHashPayloadType, persistentOpening, [count]))
  output transientDigest : Native := disclose(transientHashFab(
    boundedFabHashEnvironment, boundedFabHashPayloadType, [count]))
  output transientCommitDigest : Native := disclose(transientCommitFab(
    boundedFabHashEnvironment, boundedFabHashPayloadType, transientOpening, [count]))
end

namespace BoundedFabHashCommit

private def payloadWire : Helpers.Wire.Codec := {
  payload := .structure "BoundedFabHashCommit.Payload"
  frameBytes := 1
  composites := boundedFabHashEnvironment
}

noctium_witness_circuit hashPayload using payloadWire where
  private payload : Payload payloadWire
  output digest : Native := disclose(transientHashValue(payload))
end

end BoundedFabHashCommit

noctium_contract BoundedFabHashCommit where
  entry commit uses boundedFabHashInputs where
    return persistentResult : Bytes32 := persistentDigest
    return persistentCommitResult : Bytes32 := persistentCommitDigest
    return transientResult : Native := transientDigest
    return transientCommitResult : Native := transientCommitDigest
  end
  entry readable uses BoundedFabHashCommit.hashPayload where
    return readableDigest : Native := digest
  end
end
