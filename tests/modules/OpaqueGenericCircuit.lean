import Noctium.Frontend
import Noctium.Modules

open Noctium
open Noctium.Helpers.Specialization
open Noctium.Modules
open scoped Noctium

def opaqueGenericIdentityProgram : Noctium.Helpers.Specialization.Program := {
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

def opaqueGenericIdentityModule : Modules.Definition := {
  parameters := [⟨"T", .type⟩]
  members := [{
    id := 0
    name := "identity"
    kind := .circuit
    visibility := .«public»
    sourceExport? := some {
      program := `opaqueGenericIdentityProgram
      exportName := "identity"
      arguments := [.typeParameter "T"]}}]
  exports := [{name := "identity", target := .localMember 0}]}

noctium_module from opaqueGenericIdentityModule

def opaqueGenericIdentityRoot : Modules.Definition := {
  imports := [
    {viewName := "string", target := `opaqueGenericIdentityModule,
      arguments := [.typeValue (.scalar .opaqueString)], selections := [
        {sourceName := "identity", localName := "identity"}]},
    {viewName := "bytes", target := `opaqueGenericIdentityModule,
      arguments := [.typeValue (.scalar .opaqueBytes)], selections := [
        {sourceName := "identity", localName := "identity"}]}]
  members := [
    {id := 0, name := "echoString", kind := .entrypoint, visibility := .«public»},
    {id := 1, name := "echoBytes", kind := .entrypoint, visibility := .«public»}]
  entrypoints := [
    {«member» := 0, name := "echoString", circuit := .importedMember "string" "identity",
      returns := [{name := "echoString", ty := .opaqueString, value := .ref "result"}]},
    {«member» := 1, name := "echoBytes", circuit := .importedMember "bytes" "identity",
      returns := [{name := "echoBytes", ty := .opaqueBytes, value := .ref "result"}]}]
  exports := [
    {name := "echoString", target := .localMember 0},
    {name := "echoBytes", target := .localMember 1}]}

noctium_module from opaqueGenericIdentityRoot

def opaqueGenericCircuitRequest : Modules.Request := {
  sourceName := `opaqueGenericIdentityRoot
  arguments := []}

noctium_module_contract OpaqueGenericCircuit from opaqueGenericCircuitRequest

private def moduleEntry (name : String) : Option Entrypoint :=
  OpaqueGenericCircuit.entrypoints.find? (·.name == name)

private def typedOpaqueIdentity (name : String) (ty : Ty) : _root_.Bool :=
  match moduleEntry name with
  | none => _root_.Bool.false
  | some compiledEntrypoint =>
    let inputOk := compiledEntrypoint.circuit.inputs.any fun input =>
      input.name == "value" && input.ty == ty && input.visibility == .public
    let circuitOutputOk := match compiledEntrypoint.circuit.outputs with
      | [circuitResult] => circuitResult.name == "result" && circuitResult.ty == ty
      | _ => _root_.Bool.false
    let returnOk := match compiledEntrypoint.returns with
      | [returned] => returned.name == name && returned.ty == ty &&
          returned.nativeReturnFieldCount == 1 && returned.nativeReturnFields.isOk
      | _ => _root_.Bool.false
    inputOk && circuitOutputOk && returnOk

#guard typedOpaqueIdentity "echoString" .opaqueString
#guard typedOpaqueIdentity "echoBytes" .opaqueBytes
