import Noctium.Frontend
import Noctium.Backend.NativeExpected
import Noctium.Backend.Zkir

open scoped Noctium
open Noctium
open Noctium.Types

private def mixedFabCommitmentsEnvironment : CompositeEnv := {
  enumerations := [{id := "MixedFabCommitments.LeafMarker", variants := [
    {name := "Only"}
  ]}],
  structures := [{id := "MixedFabCommitments.FabPayload", fields := [
    {name := "octets", type := .bytes 32},
    {name := "flag", type := .scalar .bool},
    {name := "counter", type := .scalar (.uint 65535)},
    {name := "marker", type := .enumeration "MixedFabCommitments.LeafMarker"},
    {name := "anchor", type := .scalar .native}
  ]}]
}

private def mixedFabCommitmentsPayloadType : CompositeType :=
  .structure "MixedFabCommitments.FabPayload"

noctium_circuit mixedFabCommitmentsInputs where
  private octets : Bytes32
  private flag : Bool
  private counterInput : UInt 16
  private persistentOpening : Bytes32
  private transientOpening : Native
  private anchor : Native
  output persistentCommitment : Bytes32 := disclose(persistentCommitFab(
    mixedFabCommitmentsEnvironment, mixedFabCommitmentsPayloadType, persistentOpening,
    [octets, flag, counterInput, uint(0), anchor]))
  output transientCommitment : Native := disclose(transientCommitFab(
    mixedFabCommitmentsEnvironment, mixedFabCommitmentsPayloadType, transientOpening,
    [octets, flag, counterInput, uint(0), anchor]))
  output transientDigest : Native := disclose(transientHashFab(
    mixedFabCommitmentsEnvironment, mixedFabCommitmentsPayloadType,
    [octets, flag, counterInput, uint(0), anchor]))
end

noctium_contract MixedFabCommitments where
  entry commit uses mixedFabCommitmentsInputs where
    return persistentResult : Bytes32 := persistentCommitment
    return transientResult : Native := transientCommitment
    return transientHashResult : Native := transientDigest
  end
end

private def mixedFabCommitmentsEntry : Entrypoint :=
  match MixedFabCommitments.entrypoints with
  | ep :: _ => ep
  | _ => {name := "missing", circuit := {name := "missing"}}

#guard match Backend.Native.expectedEntrypoint MixedFabCommitments.state mixedFabCommitmentsEntry with
  | .ok _ => Bool.true
  | .error _ => Bool.false

#guard match Backend.Zkir.lowerEntrypoint MixedFabCommitments.state mixedFabCommitmentsEntry with
  | .ok _ => Bool.true
  | .error _ => Bool.false

#guard
  Backend.Native.persistentHashFabTerm ["field", "field"]
    [.input "left", .input "right"] ==
      Backend.Native.persistentHashNativeVectorTerm [.input "left", .input "right"] &&
  Backend.Native.persistentHashFabTerm ["bytes:32"]
    [.input "high", .input "low"] ==
      Backend.Native.persistentHash32Term (.input "high") (.input "low") &&
  Backend.Native.persistentHashFabTerm ["bytes:32", "bytes:32"]
    [.input "high0", .input "low0", .input "high1", .input "low1"] ==
      Backend.Native.persistentHashVector32Term
        [(.input "high0", .input "low0"), (.input "high1", .input "low1")] &&
  Backend.Native.persistentHashFabTerm ["bytes:1"] [.input "byte"] ==
    Backend.Native.fixedByteHashTerm "persistent_hash" 1 [.input "byte"]
