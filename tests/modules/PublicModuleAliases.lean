import Noctium.Frontend

open Lean Noctium
open scoped Noctium

private def publicAliasTypesSource : Helpers.Specialization.Program := {
  structures := [{
    id := "PublicAlias.Packet"
    parameters := [⟨"Element", .type⟩]
    fields := [("value", .parameter "Element"), ("valid", .bool)]}]
}

def publicAliasInner : Modules.Definition := {
  parameters := [⟨"T", .type⟩]
  members := [
    {id := 0, name := "Packet", kind := .type, visibility := .public,
      typeTemplate? := some {
        source := publicAliasTypesSource
        value := .structure "PublicAlias.Packet" [.type (.parameter "T")]}},
    {id := 1, name := "Count", kind := .type, visibility := .public,
      typeTemplate? := some {
        source := {}
        value := .uint (.literal 255)
        nominalUInt? := some {name := "PublicAlias.Count", maximum := 255}}}]
  exports := [
    {name := "Packet", target := .localMember 0},
    {name := "Count", target := .localMember 1}]
}

noctium_module from publicAliasInner

def publicAliasOuter : Modules.Definition := {
  members := [{
    id := 0
    name := "Inner"
    kind := .module
    visibility := .public
    moduleTarget? := some `publicAliasInner}]
  exports := [{name := "Inner", target := .localMember 0}]
}

noctium_module from publicAliasOuter

def publicAliasBridge : Modules.Definition := {
  imports := [{
    viewName := "outer"
    target := `publicAliasOuter
    selections := [{sourceName := "Inner", localName := "Inner"}]}]
  exports := [{name := "Inner", target := .importedMember "outer" "Inner"}]
}

noctium_module from publicAliasBridge

def publicAliasConsumer : Modules.Definition := {
  imports := [
    {
      viewName := "bridge"
      target := `publicAliasBridge
      selections := [{sourceName := "Inner", localName := "Inner"}]},
    {
      viewName := "specialized"
      target := .moduleMember "bridge" "Inner"
      arguments := [.typeValue (.scalar .native)]
      selections := [
        {sourceName := "Packet", localName := "Packet"},
        {sourceName := "Count", localName := "Count"}]}]
}

noctium_module from publicAliasConsumer

def publicAliasRequest : Modules.Request := {
  sourceName := `publicAliasConsumer
  arguments := []}

noctium_module_type LocalPacket from publicAliasRequest with "specialized", "Packet"
noctium_module_type LocalCount from publicAliasRequest with "specialized", "Count"

private def publicAliasRegistry : Modules.Registry := {
  modules := [
    {sourceName := `publicAliasInner, definition := publicAliasInner},
    {sourceName := `publicAliasOuter, definition := publicAliasOuter},
    {sourceName := `publicAliasBridge, definition := publicAliasBridge},
    {sourceName := `publicAliasConsumer, definition := publicAliasConsumer}]
}

private def publicAliasExpansion : Except Diagnostic Modules.Expansion :=
  Modules.expand publicAliasRegistry `publicAliasConsumer []

/-- The bridge export keeps Outer.Inner's identity. Consumer resolves that
identity to the registered generic module and specializes it at Native. -/
private def publicAliasIdentityCheck (expansion : Modules.Expansion) : Option _root_.Bool := do
  let outer ← expansion.instances.find? (fun candidate : Modules.ModuleInstance =>
    candidate.key.sourceName == `publicAliasOuter)
  let bridge ← expansion.instances.find? (fun candidate : Modules.ModuleInstance =>
    candidate.key.sourceName == `publicAliasBridge)
  let consumer ← expansion.findInstance expansion.root
  let outerExport ← outer.exports.find? (fun exported : Modules.ExportedMember =>
    exported.name == "Inner")
  let bridgeExport ← bridge.exports.find? (fun exported : Modules.ExportedMember =>
    exported.name == "Inner")
  let bridgeView ← consumer.imports.find? (fun view : Modules.ImportedView =>
    view.name == "bridge")
  let binding ← bridgeView.members.find? (fun binding : Modules.ViewBinding =>
    binding.name == "Inner")
  let inner := expansion.instances.find? (fun candidate : Modules.ModuleInstance =>
    candidate.key.sourceName == `publicAliasInner &&
      candidate.key.arguments == [.type (.scalar .native)])
  pure (outerExport.identity == bridgeExport.identity &&
    bridgeExport.identity == binding.identity && inner.isSome)

private def publicAliasPacketTypeCheck : _root_.Bool :=
  match Modules.importedType publicAliasRegistry publicAliasRequest "specialized" "Packet" with
  | .ok info =>
    match info.value with
    | .structure id =>
      match info.environment.structures.find? (·.id == id) with
      | some packet => packet.fields.map (fun field => (field.name, field.type)) == [
          ("value", .scalar .native), ("valid", .scalar .bool)] &&
          info.environment.structures.length == 1
      | none => _root_.Bool.false
    | _ => _root_.Bool.false
  | .error _ => _root_.Bool.false

private def publicAliasCountTypeCheck : _root_.Bool :=
  match Modules.importedType publicAliasRegistry publicAliasRequest "specialized" "Count" with
  | .ok info => info.nominalUInt? ==
      some {name := "PublicAlias.Count", maximum := 255}
  | .error _ => _root_.Bool.false

private def publicAliasChecks : _root_.Bool :=
  match publicAliasExpansion with
  | .error _ => _root_.Bool.false
  | .ok expansion =>
    (publicAliasIdentityCheck expansion).getD _root_.Bool.false &&
      publicAliasPacketTypeCheck && publicAliasCountTypeCheck

#guard publicAliasChecks

private def forwardViewConsumer : Modules.Definition := {
  imports := [
    {
      viewName := "specialized"
      target := .moduleMember "bridge" "Inner"
      arguments := [.typeValue (.scalar .native)]},
    {
      viewName := "bridge"
      target := `publicAliasBridge
      selections := [{sourceName := "Inner", localName := "Inner"}]}]
}

private def forwardViewRegistry : Modules.Registry := {
  modules := [
    {sourceName := `publicAliasInner, definition := publicAliasInner},
    {sourceName := `publicAliasOuter, definition := publicAliasOuter},
    {sourceName := `publicAliasBridge, definition := publicAliasBridge},
    {sourceName := `forwardViewConsumer, definition := forwardViewConsumer}]
}

#guard match Modules.expand forwardViewRegistry `forwardViewConsumer [] with
  | .error diagnostic =>
    (diagnostic.message.splitOn "unknown module import view 'bridge'").length > 1
  | .ok _ => _root_.Bool.false

private def privateModuleAliasOwner : Modules.Definition := {
  members := [{
    id := 0
    name := "Hidden"
    kind := .module
    visibility := .«private»
    moduleTarget? := some `publicAliasInner}]
}

private def privateModuleAliasConsumer : Modules.Definition := {
  imports := [{
    viewName := "owner"
    target := `privateModuleAliasOwner
    selections := [{sourceName := "Hidden", localName := "Hidden"}]}]
}

private def privateModuleAliasRegistry : Modules.Registry := {
  modules := [
    {sourceName := `publicAliasInner, definition := publicAliasInner},
    {sourceName := `privateModuleAliasOwner, definition := privateModuleAliasOwner},
    {sourceName := `privateModuleAliasConsumer, definition := privateModuleAliasConsumer}]
}

#guard match Modules.expand privateModuleAliasRegistry `privateModuleAliasConsumer [] with
  | .error diagnostic =>
    (diagnostic.message.splitOn "does not export 'Hidden'").length > 1
  | .ok _ => _root_.Bool.false

private def packetWire : Helpers.Wire.Codec := {
  payload := LocalPacket.value
  composites := LocalPacket.environment
  frameBytes := 33}

noctium_witness_circuit publicAliasPacketCheck using packetWire where
  public packet : Payload packetWire
  output valid : Bool := field(packet, valid)
end

noctium_circuit publicAliasCountCheck where
  private count : LocalCount
  output echoed : LocalCount := disclose(count)
end
