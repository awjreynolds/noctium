import Noctium.Frontend
import Noctium.Modules

open Noctium Noctium.Helpers.Specialization
open scoped Noctium

def foreignCurveGenericIdentityProgram : Program := {
  declarations := [{
    id := ⟨0, 0⟩
    name := "identity"
    parameters := [⟨"T", .type⟩]
    values := [("value", .parameter "T")]
    result := .parameter "T"
    body := [.return (some (.ref "value"))]}]
  exports := [{
    name := "identity"
    target := ⟨0, 0⟩
    inputs := [{name := "value", type := .parameter "T", visibility := .public}]}]}

private def foreignKindViewName : Foreign.Kind → String
  | .base .secp256k1 => "secp256k1Base"
  | .scalar .secp256k1 => "secp256k1Scalar"
  | .point .secp256k1 => "secp256k1Point"
  | .base .secp256r1 => "secp256r1Base"
  | .scalar .secp256r1 => "secp256r1Scalar"
  | .point .secp256r1 => "secp256r1Point"
  | .base .curve25519 => "curve25519Base"
  | .scalar .curve25519 => "curve25519Scalar"
  | .point .curve25519 => "curve25519Point"

private def foreignEntryName (kind : Foreign.Kind) : String :=
  foreignKindViewName kind ++ "Identity"

def foreignIdentityModule : Modules.Definition := {
  parameters := [⟨"T", .type⟩]
  members := [{
    id := 0
    name := "identity"
    kind := .circuit
    visibility := .«public»
    sourceExport? := some {
      program := `foreignCurveGenericIdentityProgram
      exportName := "identity"
      arguments := [.typeParameter "T"]}}]
  exports := [{name := "identity", target := .localMember 0}]}

noctium_module from foreignIdentityModule

private def foreignIdentityImport (kind : Foreign.Kind) : Modules.Import := {
  viewName := foreignKindViewName kind
  target := `foreignIdentityModule
  arguments := [.typeValue (.scalar (.foreign kind))]
  selections := [{sourceName := "identity", localName := "identity"}]}

private def foreignEntryMember (kind : Foreign.Kind) (index : Nat) : Modules.Member := {
  id := index
  name := foreignEntryName kind
  kind := .entrypoint
  visibility := .«public»}

private def foreignScalarResultMember : Modules.Member := {
  id := Foreign.kinds.length
  name := "secp256k1ScalarResult"
  kind := .state
  visibility := .«public»
  stateKind? := some (.cell (.foreign (.scalar .secp256k1)))}

private def foreignIdentityEntrypoint (kind : Foreign.Kind) (index : Nat) :
    Modules.ModuleEntrypoint := Id.run do
  let effects := match kind with
    | .scalar .secp256k1 =>
      [{effect := .writeCellOutput (.localMember Foreign.kinds.length) "result"}]
    | _ => []
  return {
    «member» := index
    name := foreignEntryName kind
    circuit := .importedMember (foreignKindViewName kind) "identity"
    effects
    span := {}}

private def foreignIdentityExport (kind : Foreign.Kind) (index : Nat) : Modules.Export := {
  name := foreignEntryName kind
  target := .localMember index}

def foreignCurveGenericIdentityRoot : Modules.Definition := {
  imports := Foreign.kinds.map foreignIdentityImport
  members := (Foreign.kinds.zipIdx.map fun (kind, index) =>
    foreignEntryMember kind index) ++ [foreignScalarResultMember]
  entrypoints := Foreign.kinds.zipIdx.map fun (kind, index) =>
    foreignIdentityEntrypoint kind index
  exports := (Foreign.kinds.zipIdx.map fun (kind, index) =>
    foreignIdentityExport kind index) ++ [
    {name := "secp256k1ScalarResult", target := .localMember Foreign.kinds.length}]}

noctium_module from foreignCurveGenericIdentityRoot

def foreignCurveGenericIdentityRequest : Modules.Request := {
  sourceName := `foreignCurveGenericIdentityRoot
  arguments := []}

noctium_module_contract ForeignCurveGenericIdentity from foreignCurveGenericIdentityRequest
