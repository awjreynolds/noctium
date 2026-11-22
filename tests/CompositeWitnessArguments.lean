import Noctium.Frontend

open scoped Noctium
open Noctium
open Noctium.Helpers
open Noctium.Types

namespace CompositeWitnessArguments

private def limitsWire : Helpers.Wire.Codec := {
  payload := .structure "CompositeWitnessArguments.Limits"
  frameBytes := 6
  composites := {structures := [{
    id := "CompositeWitnessArguments.Limits"
    fields := [
      {name := "count", type := .scalar (.uint 255)},
      {name := "enabled", type := .scalar .bool},
      {name := "memo", type := .bytes 4}
    ]
  }]}
}

-- The same payload under a different codec name must not silently replace the
-- callback's declared ABI.
private def aliasLimitsWire : Helpers.Wire.Codec := limitsWire

-- Same nominal source type, but a different frame ABI.
private def conflictingLimitsWire : Helpers.Wire.Codec := {
  limitsWire with frameBytes := 7
}

private def otherWire : Helpers.Wire.Codec := {
  payload := .structure "CompositeWitnessArguments.Other"
  frameBytes := 6
  composites := {structures := [{
    id := "CompositeWitnessArguments.Other"
    fields := [
      {name := "count", type := .scalar (.uint 255)},
      {name := "enabled", type := .scalar .bool},
      {name := "memo", type := .bytes 4}
    ]
  }]}
}

noctium_witness inspect(payload : Payload limitsWire, amount : UInt 8) : Bool

noctium_witness_circuit inspectLimits using limitsWire where
  public payload : Payload limitsWire
  public amount : UInt 8
  output accepted : Bool := disclose(witness inspect(payload, amount))
end

#guard inspect.__witnessSignature.parameters.map (fun parameter =>
  (parameter.name, parameter.type)) == [
    ("payload", .composite (.structure "CompositeWitnessArguments.Limits")),
    ("amount", .scalar (.uint 255))]

private def inspectCallArguments? : Option (List Helpers.Term) := do
  let declaration ← inspectLimits.__program.declarations.find?
    (·.name == "CompositeWitnessArguments.inspectLimits")
  match declaration.body.getLast? with
  | some (.return (some result)) =>
      match result with
      | .at _ (.disclose _ (.witnessCall _ "CompositeWitnessArguments.inspect" arguments)) =>
          some arguments
      | _ => none
  | _ => none

#guard match inspectCallArguments? with
  | some [.ref "payload", .ref "amount"] => Bool.true
  | _ => Bool.false

private def compiledInspect := Noctium.Witness.compile inspectLimits.__program
  "noctium.witness-circuit.CompositeWitnessArguments.inspectLimits.v1"

#guard match compiledInspect with
  | .ok compiled =>
      (compiled.circuit.inputs.take 7).map (fun (input : Input) => input.name) == [
        "amount", "payload.count", "payload.enabled", "payload.memo.0", "payload.memo.1",
        "payload.memo.2", "payload.memo.3"] &&
      compiled.circuit.outputs.map (fun (resultOutput : Output) => resultOutput.name) == ["result"] &&
      compiled.calls.length == 1 &&
      compiled.calls.head?.map (fun (call : Helpers.WitnessCallBinding) => call.name) ==
        some "CompositeWitnessArguments.inspect" &&
      compiled.circuit.privateOrigins.any (fun origin => origin.2 == .provider)
  | .error _ => Bool.false

/- error: witness parameter 'CompositeWitnessArguments.inspect.payload' requires codec -/
#guard_msgs (substring := true) in
noctium_witness_circuit requiresDeclaredCodec using aliasLimitsWire where
  public payload : Payload aliasLimitsWire
  public amount : UInt 8
  output accepted : Bool := disclose(witness inspect(payload, amount))
end

/- error: witness callback aggregate argument must use the declared Payload codec -/
#guard_msgs (substring := true) in
noctium_witness_circuit rejectsOtherPayload using limitsWire, otherWire where
  public payload : Payload otherWire
  public amount : UInt 8
  output accepted : Bool := disclose(witness inspect(payload, amount))
end

/- error: witness parameter 'CompositeWitnessArguments.inspect.payload' has conflicting codecs -/
#guard_msgs (substring := true) in
noctium_witness_circuit rejectsConflictingCodec using limitsWire, conflictingLimitsWire where
  public payload : Payload limitsWire
  public amount : UInt 8
  output accepted : Bool := disclose(witness inspect(payload, amount))
end

end CompositeWitnessArguments

noctium_contract CompositeWitnessArguments where
  entry inspectLimits uses CompositeWitnessArguments.inspectLimits where
    return acceptedResult : Bool := accepted
  end
end
