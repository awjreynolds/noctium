import Noctium.Frontend
import Noctium.Backend.NativeExpected
import Noctium.Backend.Zkir

open scoped Noctium
open Noctium
open Noctium.Types

private def mixedFabHashToCurveEnvironment : CompositeEnv := {
  enumerations := [{id := "MixedFabHashToCurve.LeafMarker", variants := [
    {name := "Only"}
  ]}],
  structures := [{id := "MixedFabHashToCurve.FabPayload", fields := [
    {name := "octets", type := .bytes 32},
    {name := "flag", type := .scalar .bool},
    {name := "counter", type := .scalar (.uint 65535)},
    {name := "marker", type := .enumeration "MixedFabHashToCurve.LeafMarker"},
    {name := "anchor", type := .scalar .native}
  ]}]
}

private def mixedFabHashToCurvePayloadType : CompositeType :=
  .structure "MixedFabHashToCurve.FabPayload"

private def mixedFabPayloadWire : Helpers.Wire.Codec := {
  payload := mixedFabHashToCurvePayloadType
  frameBytes := 68
  composites := mixedFabHashToCurveEnvironment
}

noctium_witness loadMixedFabPayload(counterArg : UInt 16) : Payload mixedFabPayloadWire

noctium_witness_circuit readableMixedFabHashToCurve using mixedFabPayloadWire where
  public counterArg : UInt 16
  let payload := witness loadMixedFabPayload(counterArg)
  output resultPoint : JubjubPoint := disclose(hashToCurveValue(payload))
end

#guard
  let compiled := Noctium.Witness.compile readableMixedFabHashToCurve.__program
    "noctium.witness-circuit.readableMixedFabHashToCurve.v1"
  compiled.toOption.map (fun source => source.calls.map (·.name)) == some ["loadMixedFabPayload"]

/- error: undisclosed private -/
#guard_msgs (substring := true) in
noctium_witness_circuit rejectsUnreleasedFabCurvePoint using mixedFabPayloadWire where
  public counterArg : UInt 16
  let payload := witness loadMixedFabPayload(counterArg)
  output resultPoint : JubjubPoint := hashToCurveValue(payload)
end

noctium_circuit mixedFabHashToCurveInputs where
  private octets : Bytes32
  private flag : Bool
  private counterInput : UInt 16
  private anchor : Native
  output resultPoint : JubjubPoint := disclose(hashToCurveFab(
    mixedFabHashToCurveEnvironment, mixedFabHashToCurvePayloadType,
    [octets, flag, counterInput, uint(0), anchor]))
end

noctium_contract MixedFabHashToCurve where
  entry hash uses mixedFabHashToCurveInputs where
    return pointResult : JubjubPoint := resultPoint
  end
  entry hashFromWitness uses readableMixedFabHashToCurve where
    return pointResult : JubjubPoint := resultPoint
  end
end

private def mixedFabHashToCurveEntry : Entrypoint :=
  match MixedFabHashToCurve.entrypoints with
  | ep :: _ => ep
  | _ => {name := "missing", circuit := {name := "missing"}}

#guard match Backend.Native.expectedEntrypoint MixedFabHashToCurve.state mixedFabHashToCurveEntry with
  | .ok _ => Bool.true
  | .error _ => Bool.false

#guard match Backend.Zkir.lowerEntrypoint MixedFabHashToCurve.state mixedFabHashToCurveEntry with
  | .ok _ => Bool.true
  | .error _ => Bool.false
