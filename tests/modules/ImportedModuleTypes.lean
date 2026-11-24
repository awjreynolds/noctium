import Noctium.Frontend

open Noctium
open scoped Noctium

namespace ModuleTypes

noctium_field_type Amount := Field

end ModuleTypes

private def exportedTypeSource : Helpers.Specialization.Program := {
  structures := [{
    id := "ModuleTypes.Packet"
    parameters := [⟨"Element", .type⟩]
    fields := [("value", .parameter "Element"), ("valid", .bool)]}]
  base := {composites := {enumerations := [{
    id := "ModuleTypes.Flag"
    variants := [{name := "inactive"}, {name := "active"}]}]}}}

private def exportedKeyTypeSource : Helpers.Specialization.Program := {
  structures := [{
    id := "ModuleTypes.Key"
    fields := [("amount", .native)]}]}

private def keyTypeModule (memberType : Helpers.Specialization.GenericType)
    (nominalFields : List (List String × String)) : Modules.Definition := {
  members := [{
    id := 0
    name := "Key"
    kind := .type
    visibility := .public
    typeTemplate? := some {
      source := {structures := [{
        id := "ModuleTypes.Key"
        fields := [("amount", memberType)]}]}
      value := .structure "ModuleTypes.Key" []
      nominalFieldPaths := nominalFields}}]}

private def keyTypeIsRejected (memberType : Helpers.Specialization.GenericType)
    (nominalFields : List (List String × String)) (expectedMessage : String) : _root_.Bool :=
  match Modules.expand
      {modules := [{sourceName := `keyTypeValidation, definition := keyTypeModule memberType nominalFields}]}
      `keyTypeValidation [] with
  | .error diagnostic => diagnostic.message == expectedMessage
  | .ok _ => _root_.Bool.false

def exportedModuleTypes : Modules.Definition := {
  parameters := [⟨"T", .type⟩]
  members := [
    {id := 0, name := "Packet", kind := .type, visibility := .public,
      typeTemplate? := some {
        source := exportedTypeSource
        value := .structure "ModuleTypes.Packet" [.type (.parameter "T")]}},
    {id := 1, name := "Count", kind := .type, visibility := .public,
      typeTemplate? := some {
        source := {}
        value := .uint (.literal 255)
        nominalUInt? := some {name := "ModuleTypes.Count", maximum := 255}}},
    {id := 2, name := "Flag", kind := .type, visibility := .public,
      typeTemplate? := some {
        source := exportedTypeSource
        value := .enumeration "ModuleTypes.Flag"}},
    {id := 3, name := "Secret", kind := .type,
      typeTemplate? := some {source := {}, value := .native}},
    {id := 4, name := "Key", kind := .type, visibility := .public,
      typeTemplate? := some {
        source := exportedKeyTypeSource
        value := .structure "ModuleTypes.Key" []
        nominalFieldPaths := [(["amount"], "ModuleTypes.Amount")]}}]
  exports := [
    {name := "Packet", target := .localMember 0},
    {name := "Count", target := .localMember 1},
    {name := "Flag", target := .localMember 2},
    {name := "Key", target := .localMember 4}]}

noctium_module from exportedModuleTypes

def reexportedModuleTypes : Modules.Definition := {
  imports := [{
    viewName := "source"
    target := `exportedModuleTypes
    arguments := [.typeValue (.scalar .native)]
    selections := [
      {sourceName := "Packet", localName := "Packet"},
      {sourceName := "Key", localName := "Key"},
      {sourceName := "Count", localName := "Count"},
      {sourceName := "Flag", localName := "Flag"}]}]
  exports := [
    {name := "Packet", target := .importedMember "source" "Packet"},
    {name := "Key", target := .importedMember "source" "Key"},
    {name := "Count", target := .importedMember "source" "Count"},
    {name := "Flag", target := .importedMember "source" "Flag"}]}

noctium_module from reexportedModuleTypes

def consumingModuleTypes : Modules.Definition := {
  imports := [
    {
      viewName := "selected"
      target := `reexportedModuleTypes
      selections := [
        {sourceName := "Packet", localName := "LocalPacket"},
        {sourceName := "Packet", localName := "AlsoPacket"},
        {sourceName := "Count", localName := "LocalCount"},
        {sourceName := "Count", localName := "AlsoCount"},
        {sourceName := "Flag", localName := "LocalFlag"},
        {sourceName := "Key", localName := "LocalKey"}]},
    {
      viewName := "other"
      target := `exportedModuleTypes
      arguments := [.typeValue (.scalar (.uint 255))]
      selections := [{sourceName := "Packet", localName := "LocalPacket"}]}]}

noctium_module from consumingModuleTypes

def importedModuleTypesRequest : Modules.Request := {
  sourceName := `consumingModuleTypes
  arguments := []}

noctium_module_type LocalPacket from importedModuleTypesRequest with "selected", "LocalPacket"
noctium_module_type AlsoPacket from importedModuleTypesRequest with "selected", "AlsoPacket"
noctium_module_type OtherPacket from importedModuleTypesRequest with "other", "LocalPacket"
noctium_module_type LocalCount from importedModuleTypesRequest with "selected", "LocalCount"
noctium_module_type AlsoCount from importedModuleTypesRequest with "selected", "AlsoCount"
noctium_module_type LocalFlag from importedModuleTypesRequest with "selected", "LocalFlag"
noctium_module_type LocalKey from importedModuleTypesRequest with "selected", "LocalKey"

/- error: module view 'selected' does not expose 'Secret' -/
#guard_msgs (substring := true) in
noctium_module_type Hidden from importedModuleTypesRequest with "selected", "Secret"

#guard LocalPacket.value == AlsoPacket.value && LocalPacket.value != OtherPacket.value
#guard LocalCount.nominalUInt? == AlsoCount.nominalUInt?
#guard match LocalKey.value with
  | .structure id =>
    LocalKey.environment.structures.any (fun declaration =>
      declaration.id == id &&
      declaration.fields.map (fun field => (field.name, field.type)) ==
        [("amount", .scalar .native)]) &&
    LocalKey.nominalFieldPaths == [(["amount"], "ModuleTypes.Amount")]
  | _ => _root_.Bool.false

#guard keyTypeIsRejected .native [(["missing"], "ModuleTypes.Amount")]
  "module nominal Field path 'missing' does not exist"
#guard keyTypeIsRejected .bool [(["amount"], "ModuleTypes.Amount")]
  "module nominal Field path 'amount' must have Native physical type"

private def packetWire : Helpers.Wire.Codec := {
  payload := LocalPacket.value
  composites := LocalPacket.environment
  frameBytes := 33}

private def flagWire : Helpers.Wire.Codec := {
  payload := LocalFlag.value
  composites := LocalFlag.environment
  frameBytes := 1}

noctium_witness_circuit importedPacketInput using packetWire where
  public packet : Payload packetWire
  output valid : Bool := field(packet, valid)
end

noctium_witness_circuit importedFlagInput using flagWire where
  public flag : Payload flagWire
  output ordinal : Native := cast(Native, flag)
end

noctium_witness_circuit importedCountInput where
  private count : LocalCount
  output echoed : AlsoCount := disclose(count)
end

noctium_uint_type UnrelatedCount := UInt 8

/- error: nominal UInt values require an explicit cast and must match the target type -/
#guard_msgs (substring := true) in
noctium_circuit rejectsUnrelatedCount where
  private count : UnrelatedCount
  output echoed : LocalCount := disclose(count)
end

noctium_contract ImportedModuleTypes where
  entry inspect uses importedPacketInput where
    return accepted : Bool := valid
  end
  entry flagOrdinal uses importedFlagInput where
    return flagTag : Native := ordinal
  end
  entry echoCount uses importedCountInput arguments [count] where
    return result : LocalCount := echoed
  end
end
