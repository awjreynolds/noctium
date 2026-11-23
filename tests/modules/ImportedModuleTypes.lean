import Noctium.Frontend

open Noctium
open scoped Noctium

private def exportedTypeSource : Helpers.Specialization.Program := {
  structures := [{
    id := "ModuleTypes.Packet"
    parameters := [⟨"Element", .type⟩]
    fields := [("value", .parameter "Element"), ("valid", .bool)]}]
  base := {composites := {enumerations := [{
    id := "ModuleTypes.Flag"
    variants := [{name := "inactive"}, {name := "active"}]}]}}}

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
      typeTemplate? := some {source := {}, value := .native}}]
  exports := [
    {name := "Packet", target := .localMember 0},
    {name := "Count", target := .localMember 1},
    {name := "Flag", target := .localMember 2}]}

noctium_module from exportedModuleTypes

def reexportedModuleTypes : Modules.Definition := {
  imports := [{
    viewName := "source"
    target := `exportedModuleTypes
    arguments := [.typeValue (.scalar .native)]
    selections := [
      {sourceName := "Packet", localName := "Packet"},
      {sourceName := "Count", localName := "Count"},
      {sourceName := "Flag", localName := "Flag"}]}]
  exports := [
    {name := "Packet", target := .importedMember "source" "Packet"},
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
        {sourceName := "Flag", localName := "LocalFlag"}]},
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

/- error: module view 'selected' does not expose 'Secret' -/
#guard_msgs (substring := true) in
noctium_module_type Hidden from importedModuleTypesRequest with "selected", "Secret"

#guard LocalPacket.value == AlsoPacket.value && LocalPacket.value != OtherPacket.value
#guard LocalCount.nominalUInt? == AlsoCount.nominalUInt?

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
