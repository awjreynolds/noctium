import Noctium.Frontend
import Noctium.Modules

open scoped Noctium
open Noctium.Helpers.Specialization

def moduleIdentityProgram : Program := {
  declarations := [{
    id := ⟨0, 0⟩
    name := "identity"
    parameters := [⟨"T", .type⟩, ⟨"N", .natural⟩]
    values := [("value", .parameter "T")]
    result := .parameter "T"
    body := [.return (some (.ref "value"))]}]
  exports := [{
    name := "update"
    target := ⟨0, 0⟩
    arguments := [.type .native, .natural (.literal 2)]
    inputs := [{name := "value", type := .parameter "T", visibility := .public}]}]
}

private def moduleBalance : Noctium.Modules.Member := {
  id := 0
  name := "balance"
  kind := .state
  visibility := .«public»
  stateSchema? := some (.cell (.parameter "T"))}

private def moduleUpdateCircuit : Noctium.Modules.Member := {
  id := 1
  name := "updateCircuit"
  kind := .circuit
  visibility := .«private»
  sourceExport? := some {
    program := `moduleIdentityProgram
    exportName := "update"
    arguments := [.typeParameter "T", .naturalParameter "N"]}}

private def moduleUpdateEntry : Noctium.Modules.Member := {
  id := 2
  name := "update"
  kind := .entrypoint
  visibility := .«public»}

def genericLedgerModule : Noctium.Modules.Definition := {
  parameters := [⟨"N", .natural⟩, ⟨"T", .type⟩]
  members := [moduleBalance, moduleUpdateCircuit, moduleUpdateEntry]
  entrypoints := [{
    «member» := 2
    name := "update"
    circuit := .localMember 1
    effects := [{effect := .writeCellOutput (.localMember 0) "result"}]}]
  exports := [
    {name := "balance", target := .localMember 0},
    {name := "update", target := .localMember 2}]
}

noctium_module from genericLedgerModule

def moduleContractRoot : Noctium.Modules.Definition := {
  members := [
    {id := 0, name := "readCheck", kind := .circuit, sourceExport? := some {
      program := `moduleIdentityProgram
      exportName := "update"
      arguments := [.typeValue (.scalar .native), .naturalValue 2]}},
    {id := 1, name := "againRead", kind := .entrypoint, visibility := .«public»}]
  imports := [
    {viewName := "first", target := `genericLedgerModule,
      arguments := [.naturalValue 2, .typeValue (.scalar .native)], selections := [
        {sourceName := "balance", localName := "balance"},
        {sourceName := "update", localName := "update"}]},
    {viewName := "again", target := `genericLedgerModule,
      arguments := [.naturalValue 2, .typeValue (.scalar .native)], selections := [
        {sourceName := "balance", localName := "mirror"},
        {sourceName := "update", localName := "update"}]},
    {viewName := "different", target := `genericLedgerModule,
      arguments := [.naturalValue 3, .typeValue (.scalar (.uint 255))], selections := [
        {sourceName := "balance", localName := "balance"},
        {sourceName := "update", localName := "update"}]}]
  entrypoints := [{
    «member» := 1
    name := "againRead"
    circuit := .localMember 0
    effects := [
      {effect := .readCell (.importedMember "again" "mirror") "observed" .native},
      {effect := .require (.eq (.ref "observed" : Noctium.Expr .native) (.ref "value"))}]}]
  exports := [
    {name := "firstBalance", target := .importedMember "first" "balance"},
    {name := "againBalance", target := .importedMember "again" "mirror"},
    {name := "differentBalance", target := .importedMember "different" "balance"},
    {name := "firstUpdate", target := .importedMember "first" "update"},
    {name := "againUpdate", target := .importedMember "again" "update"},
    {name := "differentUpdate", target := .importedMember "different" "update"},
    {name := "againRead", target := .localMember 1}]
}

noctium_module from moduleContractRoot

def moduleContractRequest : Noctium.Modules.Request := {
  sourceName := `moduleContractRoot
  arguments := []}

noctium_module_contract ModuleLedger from moduleContractRequest
