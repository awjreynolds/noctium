import Noctium.Frontend
import Noctium.Backend.NativeExpected
import Noctium.Backend.Zkir

open scoped Noctium
open Noctium
open Noctium.Types

private def nestedTransientHashEnvironment : CompositeEnv := {
  structures := [
    {id := "NestedTransientHash.Inner", fields := [
      {name := "tag", type := .bytes 2},
      {name := "enabled", type := .scalar .bool},
      {name := "amount", type := .scalar (.uint 65535)}
    ]},
    {id := "NestedTransientHash.Payload", fields := [
      {name := "head", type := .scalar .native},
      {name := "inner", type := .structure "NestedTransientHash.Inner"},
      {name := "pair", type := .tuple [
        .scalar .native,
        .vector 2 (.scalar .native)
      ]},
      {name := "empty", type := .vector 0 (.scalar .native)},
      {name := "tail", type := .scalar .native}
    ]}
  ]
}

private def nestedTransientHashType : CompositeType :=
  .structure "NestedTransientHash.Payload"

private def emptyTransientHashType : CompositeType := .tuple []

noctium_circuit nestedTransientHashInputs where
  private head : Native
  private tag : Bytes 2
  private enabled : Bool
  private amount : UInt 16
  private pairHead : Native
  private firstItem : Native
  private secondItem : Native
  private tail : Native
  output computedDigest : Native := disclose(transientHashFab(
    nestedTransientHashEnvironment, nestedTransientHashType,
    [head, tag, enabled, amount, pairHead, firstItem, secondItem, tail]))
  output computedEmptyDigest : Native := disclose(transientHashFab(
    nestedTransientHashEnvironment, emptyTransientHashType, []))
end

noctium_contract NestedTransientHash where
  entry digest uses nestedTransientHashInputs where
    return digest : Native := computedDigest
    return emptyDigest : Native := computedEmptyDigest
  end
end

private def nestedTransientHashEntry : Entrypoint :=
  match NestedTransientHash.entrypoints with
  | ep :: _ => ep
  | _ => {name := "missing", circuit := {name := "missing"}}

#guard match Backend.Native.expectedEntrypoint NestedTransientHash.state nestedTransientHashEntry with
  | .ok _ => Bool.true
  | .error _ => Bool.false

#guard match Backend.Zkir.lowerEntrypoint NestedTransientHash.state nestedTransientHashEntry with
  | .ok _ => Bool.true
  | .error _ => Bool.false

#guard match validateTransientFabHashFields nestedTransientHashEnvironment nestedTransientHashType
    [⟨.native, .native 11⟩] with
  | .error message => message == "transient FAB value count differs from its layout"
  | .ok _ => Bool.false
