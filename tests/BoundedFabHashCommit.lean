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

private def scalarFabCommitEnvironment : CompositeEnv := {}
private def scalarFabCommitType : CompositeType := .scalar .native
private def scalarFabCommitPayload : Sigma Expr := ⟨.native, .native 41⟩
private def emptyFabCommitType : CompositeType := .vector 0 (.scalar .native)

#guard (validateFabCommitLayout scalarFabCommitEnvironment (.scalar .bool)
  [⟨.bool, .bool Bool.true⟩]).isOk == Bool.false
#guard (validateFabCommitLayout scalarFabCommitEnvironment scalarFabCommitType
  [scalarFabCommitPayload, scalarFabCommitPayload]).isOk == Bool.false
#guard (validateFabHashLayout scalarFabCommitEnvironment scalarFabCommitType
  [scalarFabCommitPayload]).isOk == Bool.false
#guard (validateFabCommitLayout scalarFabCommitEnvironment
  (.vector 1 (.scalar .native)) []).isOk == Bool.false

noctium_circuit scalarFabCommitInputs where
  private payload : Native
  private persistentOpening : Bytes32
  private transientOpening : Native
  output persistentCommitDigest : Bytes32 := disclose(persistentCommitFab(
    scalarFabCommitEnvironment, scalarFabCommitType, persistentOpening, [payload]))
  output transientCommitDigest : Native := disclose(transientCommitFab(
    scalarFabCommitEnvironment, scalarFabCommitType, transientOpening, [payload]))
end

noctium_circuit emptyFabCommitInputs where
  private persistentOpening : Bytes32
  private transientOpening : Native
  output persistentCommitDigest : Bytes32 := disclose(persistentCommitFab(
    scalarFabCommitEnvironment, emptyFabCommitType, persistentOpening, []))
  output transientCommitDigest : Native := disclose(transientCommitFab(
    scalarFabCommitEnvironment, emptyFabCommitType, transientOpening, []))
end

/- error: undisclosed private -/
#guard_msgs (substring := true) in
noctium_circuit rejectsScalarCommitDisclosure where
  private payload : Native
  public opening : Native
  output digest : Native := transientCommitFab(
    scalarFabCommitEnvironment, scalarFabCommitType, opening, [payload])
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
  entry scalarCommit uses scalarFabCommitInputs where
    return persistentCommitResult : Bytes32 := persistentCommitDigest
    return transientCommitResult : Native := transientCommitDigest
  end
  entry emptyCommit uses emptyFabCommitInputs where
    return persistentCommitResult : Bytes32 := persistentCommitDigest
    return transientCommitResult : Native := transientCommitDigest
  end
  entry readable uses BoundedFabHashCommit.hashPayload where
    return readableDigest : Native := digest
  end
end
