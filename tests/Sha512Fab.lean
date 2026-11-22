import Noctium.Frontend
import Noctium.Backend.NativeExpected
import Noctium.Backend.Zkir

open scoped Noctium
open Noctium
open Noctium.Types

private def sha512FabEnvironment : CompositeEnv := {
  structures := [{id := "Sha512Fab.Payload", fields := [
    {name := "octets", type := .bytes 32},
    {name := "flag", type := .scalar .bool},
    {name := "counter", type := .scalar (.uint 65535)},
    {name := "anchor", type := .scalar .native}
  ]}]
}

private def sha512FabPayloadType : CompositeType := .structure "Sha512Fab.Payload"

private def digestWire : Helpers.Wire.Codec := {
  payload := sha512FabPayloadType
  frameBytes := 67
  composites := sha512FabEnvironment
}

noctium_witness payloadForDigest() : Payload digestWire

noctium_witness_circuit hostedFabDigests using digestWire where
  public expectedSha : Bytes 64
  public expectedKeccak : Bytes32
  let payload := witness payloadForDigest()
  let sha := sha512(payload)
  let keccak := keccak256(payload)
  prove eq(sha, expectedSha)
  prove eq(keccak, expectedKeccak)
  output checkedSha : Bytes 64 := disclose(sha)
  output checkedKeccak : Bytes32 := disclose(keccak)
end

/- error: undisclosed private -/
#guard_msgs (substring := true) in
noctium_witness_circuit rejectedPrivateDigest using digestWire where
  private payload : Payload digestWire
  output digest : Bytes32 := keccak256(payload)
end

noctium_circuit sha512FabInputs where
  private octets : Bytes32
  private flag : Bool
  private counterInput : UInt 16
  private anchor : Native
  output digest : Bytes 64 := disclose(sha512Fab(
    sha512FabEnvironment, sha512FabPayloadType, [octets, flag, counterInput, anchor]))
  output keccakDigest : Bytes32 := disclose(keccak256Fab(
    sha512FabEnvironment, sha512FabPayloadType, [octets, flag, counterInput, anchor]))
end

noctium_contract Sha512Fab where
  entry hash uses sha512FabInputs where
    return resultDigest : Bytes 64 := digest
    return keccakResult : Bytes32 := keccakDigest
  end
  entry hashHosted uses hostedFabDigests where
    return shaDigest : Bytes 64 := checkedSha
    return keccakDigest : Bytes32 := checkedKeccak
  end
end

private def sha512FabEntry : Entrypoint :=
  match Sha512Fab.entrypoints with
  | ep :: _ => ep
  | _ => {name := "missing", circuit := {name := "missing"}}

#guard match Backend.Native.expectedEntrypoint Sha512Fab.state sha512FabEntry with
  | .ok _ => Bool.true
  | .error _ => Bool.false

#guard match Backend.Zkir.lowerEntrypoint Sha512Fab.state sha512FabEntry with
  | .ok _ => Bool.true
  | .error _ => Bool.false
