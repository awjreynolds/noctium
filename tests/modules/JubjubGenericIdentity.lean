import Noctium.Frontend
import Noctium.Modules

open Noctium Noctium.Helpers.Specialization
open scoped Noctium

def jubjubGenericIdentityProgram : Noctium.Helpers.Specialization.Program := {
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

def jubjubGenericIdentityModule : Noctium.Modules.Definition := {
  parameters := [⟨"T", .type⟩]
  members := [{
    id := 0
    name := "identity"
    kind := .circuit
    visibility := .«public»
    sourceExport? := some {
      program := `jubjubGenericIdentityProgram
      exportName := "identity"
      arguments := [.typeParameter "T"]}}]
  exports := [{name := "identity", target := .localMember 0}]}

noctium_module from jubjubGenericIdentityModule

def jubjubGenericIdentityRoot : Noctium.Modules.Definition := {
  imports := [
    {viewName := "scalar", target := `jubjubGenericIdentityModule,
      arguments := [.typeValue (.scalar .jubjubScalar)],
      selections := [{sourceName := "identity", localName := "identity"}]},
    {viewName := "point", target := `jubjubGenericIdentityModule,
      arguments := [.typeValue (.scalar .jubjubPoint)],
      selections := [{sourceName := "identity", localName := "identity"}]}]
  members := [
    {id := 0, name := "scalarResult", kind := .state, visibility := .«public»,
      stateKind? := some (.cell .jubjubScalar)},
    {id := 1, name := "pointResult", kind := .state, visibility := .«public»,
      stateKind? := some (.cell .jubjubPoint)},
    {id := 2, name := "scalarIdentity", kind := .entrypoint, visibility := .«public»},
    {id := 3, name := "pointIdentity", kind := .entrypoint, visibility := .«public»}]
  entrypoints := [
    {«member» := 2, name := "scalarIdentity",
      circuit := .importedMember "scalar" "identity",
      effects := [⟨.writeCellOutput (.localMember 0) "result", {}⟩]},
    {«member» := 3, name := "pointIdentity",
      circuit := .importedMember "point" "identity",
      effects := [⟨.writeCellOutput (.localMember 1) "result", {}⟩]}]
  exports := [
    {name := "scalarResult", target := .localMember 0},
    {name := "pointResult", target := .localMember 1},
    {name := "scalarIdentity", target := .localMember 2},
    {name := "pointIdentity", target := .localMember 3}]}

noctium_module from jubjubGenericIdentityRoot

def jubjubGenericIdentityRequest : Noctium.Modules.Request := {
  sourceName := `jubjubGenericIdentityRoot
  arguments := []}

noctium_module_contract JubjubGenericIdentity from jubjubGenericIdentityRequest
