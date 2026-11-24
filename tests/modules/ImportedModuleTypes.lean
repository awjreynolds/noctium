import Noctium.Frontend

open Noctium
open scoped Noctium

namespace ModuleTypes

noctium_field_type Amount := Field
noctium_field_type Count := Field

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

namespace ModuleTypes

noctium_module_type ImportedKey from importedModuleTypesRequest with "selected", "LocalKey"

noctium_circuit importedKeySetInputs where
  private amount : Amount
  public adding : Bool
  public removing : Bool
end

noctium_circuit wrongImportedKeySetInputs where
  private amount : Count
  public adding : Bool
  public removing : Bool
end

noctium_circuit nestedKeySetInitializeInputs where
  public owner : Bytes32
end

noctium_circuit nestedKeySetInputs where
  public owner : Bytes32
  private amount : Amount
  public adding : Bool
  public removing : Bool
end

noctium_circuit wrongNestedKeySetInputs where
  public owner : Bytes32
  private amount : Count
end

noctium_contract ImportedKeySet where
  set members : ImportedKey

  entry update uses importedKeySetInputs where
    member members[fields(disclose(amount))] as presentBefore
    when adding insert members[fields(disclose(amount))]
    member members[fields(disclose(amount))] as presentAfterInsert
    when removing remove members[fields(disclose(amount))]
    member members[fields(disclose(amount))] as presentAfterRemove
    return before : Bool := presentBefore
    return afterInsert : Bool := presentAfterInsert
    return afterRemove : Bool := presentAfterRemove
  end
end

noctium_contract NestedImportedKeySet where
  tree buckets : Bytes32 => Set ImportedKey

  entry initializeOwner uses nestedKeySetInitializeInputs where
    insert buckets[owner] := emptyMap
  end

  entry update uses nestedKeySetInputs where
    member buckets[owner][fields(disclose(amount))] as presentBefore
    when adding insert buckets[owner][fields(disclose(amount))]
    when removing remove buckets[owner][fields(disclose(amount))]
    member buckets[owner][fields(disclose(amount))] as presentAfter
    return before : Bool := presentBefore
    return after : Bool := presentAfter
  end
end

#guard match NestedImportedKeySet.state with
  | [{name := "buckets", kind := .tree (.map (.bytes 32) (.recordSet environment type)), ..}] =>
    match LedgerValueType.recordSetKeyFields environment type with
    | .ok [("amount", .native)] => _root_.Bool.true
    | _ => _root_.Bool.false
  | _ => _root_.Bool.false

private def nestedKeySetEntry (name : String) : Entrypoint :=
  (NestedImportedKeySet.entrypoints.find? (·.name == name)).getD
    {name := "missing", circuit := {name := "missing"}}

private def nestedKeySetContext : EvalContext := {
  modulus := Field.modulus
  poseidon2 := fun _ _ _ => .error "unused by nested imported record Set fixture"
}

private def nestedKeySetInitial : LedgerState := {trees := [("buckets", .map [])]}
private def nestedKeySetOwner : List Nat := List.replicate 32 9

private def nestedKeySetInitialize (state : LedgerState) :=
  (nestedKeySetEntry "initializeOwner").run nestedKeySetContext
    [("owner", .bytes 32 nestedKeySetOwner)] state

private def nestedKeySetUpdate (amount : Nat) (adding removing : _root_.Bool) (state : LedgerState) :=
  (nestedKeySetEntry "update").run nestedKeySetContext [
    ("owner", .bytes 32 nestedKeySetOwner), ("amount", .native amount),
    ("adding", .bool adding), ("removing", .bool removing)] state

#guard !(nestedKeySetUpdate 17 _root_.Bool.true _root_.Bool.false nestedKeySetInitial).isOk

#guard match nestedKeySetInitialize nestedKeySetInitial with
  | .ok (_, state) =>
    match nestedKeySetUpdate 17 _root_.Bool.true _root_.Bool.false state with
    | .ok (outputs, insertedState) =>
      outputs.lookup "before" == some (.bool _root_.Bool.false) &&
      outputs.lookup "after" == some (.bool _root_.Bool.true) &&
      match nestedKeySetUpdate 17 _root_.Bool.false _root_.Bool.true insertedState with
      | .ok (removed, finalState) =>
        removed.lookup "before" == some (.bool _root_.Bool.true) &&
        removed.lookup "after" == some (.bool _root_.Bool.false) &&
        finalState.trees.lookup "buckets" == state.trees.lookup "buckets"
      | .error _ => _root_.Bool.false
    | .error _ => _root_.Bool.false
  | .error _ => _root_.Bool.false

#guard match ImportedKeySet.state with
  | [{name := "members", kind := .tree (.recordSet environment type), ..}] =>
    match LedgerValueType.recordSetKeyFields environment type with
    | .ok [("amount", .native)] => _root_.Bool.true
    | _ => _root_.Bool.false
  | _ => _root_.Bool.false

/- error: nominal Field values require an explicit cast and must match the target type -/
#guard_msgs (substring := true) in
noctium_contract RejectWrongImportedKeySet where
  set members : ImportedKey

  entry update uses wrongImportedKeySetInputs where
    member members[fields(disclose(amount))] as present
    when adding insert members[fields(disclose(amount))]
    when removing remove members[fields(disclose(amount))]
  end
end

/- error: nominal Field values require an explicit cast and must match the target type -/
#guard_msgs (substring := true) in
noctium_contract RejectWrongNestedImportedKeySet where
  tree buckets : Bytes32 => Set ImportedKey
  entry update uses wrongNestedKeySetInputs where
    member buckets[owner][fields(disclose(amount))] as present
  end
end

noctium_uint_type ImportedSetOwner := UInt 8
noctium_uint_type UnrelatedSetOwner := UInt 8

noctium_circuit wrongNamedSetOwnerInputs where
  public owner : UnrelatedSetOwner
  private amount : Amount
end

/- error: nominal UInt values require an explicit cast and must match the target type -/
#guard_msgs (substring := true) in
noctium_contract RejectWrongNamedSetOwner where
  tree buckets : ImportedSetOwner => Set ImportedKey
  entry inspect uses wrongNamedSetOwnerInputs where
    member buckets[owner][fields(disclose(amount))] as present
  end
end

end ModuleTypes

namespace ImportedTypeConsumer

noctium_circuit inspectInputs where
  public amount : ModuleTypes.Amount
end

noctium_contract SealedKeySet where
  sealed set members : ModuleTypes.ImportedKey

  constructor(seed : ModuleTypes.Amount) where
    insert members[fields(seed)]
  end

  entry inspect uses inspectInputs where
    member members[fields(amount)] as present
    return isPresent : Bool := present
  end
end

#guard (SealedKeySet.validate Capabilities.source).isOk
#guard match SealedKeySet.state with
  | [{kind := .tree (.recordSet ..), «sealed» := isSealed, ..}] => isSealed
  | _ => _root_.Bool.false

end ImportedTypeConsumer

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
