import Noctium.Frontend
import Noctium.Modules

open Noctium
open Noctium.Helpers.Specialization
open Noctium.Modules
open scoped Noctium

def opaqueModuleCellProgram : Program := {
  declarations := [{
    id := ⟨0, 0⟩
    name := "unit"
    result := .unit
    body := [.return]
  }]
  exports := [{name := "hash", target := ⟨0, 0⟩}]
}

def genericOpaqueCellModule : Definition := {
  parameters := [⟨"T", .type⟩]
  members := [
    {id := 0, name := "value", kind := .state, visibility := .«public»,
      stateSchema? := some (.cell (.parameter "T"))},
    {id := 1, name := "hashCircuit", kind := .circuit, sourceExport? := some {
      program := `opaqueModuleCellProgram
      exportName := "hash"}},
    {id := 2, name := "hash", kind := .entrypoint, visibility := .«public»}]
  entrypoints := [{
    «member» := 2
    name := "hash"
    circuit := .localMember 1
    opaqueCellHashReturns := [{name := "digest", state := .localMember 0}]
  }]
  exports := [
    {name := "value", target := .localMember 0},
    {name := "hash", target := .localMember 2}]
}

noctium_module from genericOpaqueCellModule

def opaqueModuleCellsRoot : Definition := {
  imports := [
    {viewName := "text", target := `genericOpaqueCellModule,
      arguments := [.typeValue (.scalar .opaqueString)], selections := [
        {sourceName := "value", localName := "value"},
        {sourceName := "hash", localName := "hash"}]},
    {viewName := "bytes", target := `genericOpaqueCellModule,
      arguments := [.typeValue (.scalar .opaqueBytes)], selections := [
        {sourceName := "value", localName := "value"},
        {sourceName := "hash", localName := "hash"}]}]
  exports := [
    {name := "textValue", target := .importedMember "text" "value"},
    {name := "bytesValue", target := .importedMember "bytes" "value"},
    {name := "hashString", target := .importedMember "text" "hash"},
    {name := "hashBytes", target := .importedMember "bytes" "hash"}]
}

noctium_module from opaqueModuleCellsRoot

def opaqueModuleCellsRequest : Request := {
  sourceName := `opaqueModuleCellsRoot
  arguments := []
  constructorInputs := [
    {state := .importedMember "text" "value", parameterName := "initialString"},
    {state := .importedMember "bytes" "value", parameterName := "initialBytes"}]
}

noctium_module_contract OpaqueModuleCells from opaqueModuleCellsRequest

#guard (OpaqueModuleCells.state.map (·.name)).eraseDups.length == 2
#guard OpaqueModuleCells.state.any (fun state => state.kind == .cell .opaqueString)
#guard OpaqueModuleCells.state.any (fun state => state.kind == .cell .opaqueBytes)
#guard match OpaqueModuleCells.constructor with
  | some constr => constr.parameters.map (fun parameter =>
      (parameter.name, parameter.type)) == [
        ("initialString", .opaqueString),
        ("initialBytes", .scalar .opaqueBytes)] &&
    constr.initializers.length == 2
  | none => Bool.false
#guard match OpaqueModuleCells.entrypoints.find? (·.name == "hashString"),
    OpaqueModuleCells.entrypoints.find? (·.name == "hashBytes") with
  | some text, some bytes =>
    text.effects.length == 1 && bytes.effects.length == 1 &&
    text.returns.length == 1 && bytes.returns.length == 1 &&
    text.returns[0]?.map (·.ty) == some .native &&
    bytes.returns[0]?.map (·.ty) == some .native
  | _, _ => Bool.false
