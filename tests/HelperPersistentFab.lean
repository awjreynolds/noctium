import Noctium.Frontend
import Noctium.Backend.NativeExpected
import Noctium.Backend.Zkir

open scoped Noctium
open Noctium
open Noctium.Types

namespace HelperPersistentFab

private def payloadEnvironment : CompositeEnv := {
  structures := [
    {id := "HelperPersistentFab.Inner", fields := [
      {name := "label", type := .bytes 2},
      {name := "active", type := .scalar .bool},
      {name := "amount", type := .scalar (.uint 65535)}]},
    {id := "HelperPersistentFab.Payload", fields := [
      {name := "inner", type := .structure "HelperPersistentFab.Inner"},
      {name := "anchor", type := .scalar .native}]}]
}

private def payloadType : CompositeType := .structure "HelperPersistentFab.Payload"

private def payloadWire : Helpers.Wire.Codec := {
  payload := payloadType
  frameBytes := 37
  composites := payloadEnvironment
}

private def buildHashHelper : Except String Helpers.Program := do
  let compiled ← (Types.compileType payloadEnvironment payloadType).mapError (·.message)
  let operands ← Helpers.Wire.fabDigestOperands compiled (.ref "payload")
  pure {
    composites := payloadEnvironment
    declarations := [{
      id := ⟨0, 0⟩
      name := "hashPayload"
      parameters := [{name := "payload", ty := .native}]
      compositeParameters := [("payload", payloadType)]
      result := .scalar (.bytes 32)
      body := [.return (some (.bytes
        (.fabDigest .persistentHash payloadType (operands.map Prod.fst))
        (operands.map Prod.snd)))]
    }]
    exports := [{
      name := "hashPayload"
      target := ⟨0, 0⟩
      compositeInputs := [{name := "payload", type := payloadType, visibility := .public}]
    }]
  }

private def hashHelper : Helpers.Program :=
  match buildHashHelper with
  | .ok program => program
  | .error _ => {composites := payloadEnvironment, declarations := []}

noctium_witness nestedPayload() : Payload payloadWire

noctium_witness_circuit compareNamedAndDirectFab using payloadWire with hashHelper where
  let payload := witness nestedPayload()
  let helperDigest := invoke(hashPayload, [payload])
  output helperResult : Bytes32 := disclose(helperDigest)
end

/- error: undisclosed private -/
#guard_msgs (substring := true) in
noctium_witness_circuit rejectsUndisclosedHelperDigest using payloadWire with hashHelper where
  let payload := witness nestedPayload()
  output digest : Bytes32 := invoke(hashPayload, [payload])
end

noctium_contract PersistentFabHelper where
  entry hash uses compareNamedAndDirectFab where
    return result : Bytes32 := helperResult
  end
end

private def hashEntry : Entrypoint :=
  match PersistentFabHelper.entrypoints with
  | ep :: _ => ep
  | _ => {name := "missing", circuit := {name := "missing"}}

private def hashContext : EvalContext := {
  modulus := Field.modulus
  poseidon2 := fun _ _ _ => .error "unused"
  persistentHash32 := fun preimage => pure
    ((preimage.length % 251) :: preimage.take 31 ++ List.replicate (31 - (preimage.take 31).length) 0)
}

private def directDigest : Expr (.bytes 32) :=
  .persistentHashFab payloadEnvironment payloadType [
    ⟨.bytes 2, .bytesLiteral 2 [10, 11]⟩,
    ⟨.bool, .bool Bool.true⟩,
    ⟨.uint 65535, .uint 65535 258⟩,
    ⟨.native, .native 77⟩
  ]

private def helperInputs : List (String × Value) := [
  ("payload.inner.label.0", .native 10),
  ("payload.inner.label.1", .native 11),
  ("payload.inner.active", .native 1),
  ("payload.inner.amount", .native 258),
  ("payload.anchor", .native 77)
]

private def helperMatchesDirect : Except String _root_.Bool := do
  let circuit ← (Helpers.compile hashHelper "hashPayload").mapError (·.message)
  let outputs ← circuit.run hashContext helperInputs
  let direct ← directDigest.eval hashContext []
  pure (outputs.lookup "result" == some (.bytes 32 direct))

#guard helperMatchesDirect.toOption == some _root_.Bool.true

#guard match Backend.Native.expectedEntrypoint PersistentFabHelper.state hashEntry with
  | .ok _ => Bool.true
  | .error _ => Bool.false

#guard match Backend.Zkir.lowerEntrypoint PersistentFabHelper.state hashEntry with
  | .ok _ => Bool.true
  | .error _ => Bool.false

end HelperPersistentFab
