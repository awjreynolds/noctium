import Noctium.Modules

namespace Noctium.ModulesTests

open Lean Noctium Noctium.Modules Noctium.Helpers.Specialization

private def sourceName (parts : List String) : Name :=
  parts.foldl Name.str .anonymous

private def moduleMember (id : Nat) (name : String) (kind : MemberKind)
    (visibility : MemberVisibility := .«public») : Member :=
  {id, name, kind, visibility, span := {file := "modules.noct", line := id + 1}}

private def registerAll (definitions : List (Name × Definition)) :
    Except Diagnostic Registry := do
  let mut registry : Registry := {}
  for (name, definition) in definitions do
    registry ← registry.register name definition
  pure registry

private def messageContains (result : Except Diagnostic α) (fragment : String) : Bool :=
  match result with
  | .error diagnostic => (diagnostic.message.splitOn fragment).length > 1
  | .ok _ => false

private def genericIdentity : Noctium.Helpers.Specialization.Declaration := {
  id := ⟨0, 0⟩
  name := "identity"
  parameters := [⟨"T", .type⟩]
  values := [("value", .parameter "T")]
  result := .parameter "T"
  body := [.return (some (.ref "value"))]
}

private def genericIdentitySource : Noctium.Helpers.Specialization.Program := {
  declarations := [genericIdentity]
  exports := [
    {name := "nativeA", target := ⟨0, 0⟩, arguments := [.type .native],
      inputs := [{name := "value", type := .native, visibility := .public}]},
    {name := "nativeB", target := ⟨0, 0⟩, arguments := [.type .native],
      inputs := [{name := "value", type := .native, visibility := .public}]},
    {name := "wide", target := ⟨0, 0⟩, arguments := [.type (.uint (.literal 255))],
      inputs := [{name := "value", type := .uint (.literal 255), visibility := .public}]}]
}

private def genericRequestSource : Noctium.Helpers.Specialization.Program := {
  declarations := [genericIdentity]
  exports := [{
    name := "identity"
    target := ⟨0, 0⟩
    arguments := [.type .native]
    inputs := [{name := "value", type := .parameter "T", visibility := .public}]}]
}

private def baseModule : Definition := {
  members := [
    moduleMember 0 "balance" .state,
    moduleMember 1 "add" .helper,
    moduleMember 2 "secret" .state .«private»]
  exports := [
    {name := "balance", target := .localMember 0},
    {name := "add", target := .localMember 1}]
}

private def genericModule : Definition := {
  parameters := [⟨"T", .type⟩, ⟨"N", .natural⟩]
  members := [
    moduleMember 0 "value" .state,
    { (moduleMember 1 "compute" .circuit) with sourceExport? := some {
      program := sourceName ["Demo", "Program"]
      exportName := "compute"
      arguments := [.typeParameter "T", .naturalParameter "N"]}}]
  exports := [
    {name := "value", target := .localMember 0},
    {name := "compute", target := .localMember 1}]
}

private def genericImport (viewName : String) (type : Types.CompositeType) (size : Nat) :
    Noctium.Modules.Import := {
  viewName
  target := sourceName ["Demo", "Generic"]
  arguments := [.typeValue type, .naturalValue size]
  selections := [
    {sourceName := "value", localName := "state"},
    {sourceName := "compute", localName := "compute"}]
}

private def aliasDefinition : Definition := {
  imports := [
    {viewName := "first", target := sourceName ["Demo", "Shared"],
      selections := [{sourceName := "balance", localName := "ledger"}]},
    {viewName := "second", target := sourceName ["Demo", "Shared"],
      selections := [{sourceName := "balance", localName := "renamed"}]}]
  exports := [
    {name := "left", target := .importedMember "first" "ledger"},
    {name := "right", target := .importedMember "second" "renamed"}]
}

private def rootWithTwoGenericImports : Definition := {
  imports := [
    genericImport "nativeA" (.scalar .native) 8,
    genericImport "nativeB" (.scalar .native) 8,
    genericImport "bool" (.scalar .bool) 8]
  exports := [
    {name := "a", target := .importedMember "nativeA" "state"},
    {name := "b", target := .importedMember "nativeB" "state"},
    {name := "c", target := .importedMember "bool" "state"},
    {name := "circuitA", target := .importedMember "nativeA" "compute"},
    {name := "circuitB", target := .importedMember "nativeB" "compute"},
    {name := "circuitC", target := .importedMember "bool" "compute"}]
}

private def ledgerStateMember : Member := {
  id := 0
  name := "balance"
  kind := .state
  visibility := .«public»
  stateSchema? := some (.cell (.parameter "T"))}

private def ledgerCircuitMember : Member := {
  id := 1
  name := "updateCircuit"
  kind := .circuit
  visibility := .«private»
  sourceExport? := some {
    program := sourceName ["Demo", "Program"]
    exportName := "update"
    arguments := [.naturalParameter "N"]}}

private def ledgerEntrypointMember : Member := {
  id := 2
  name := "update"
  kind := .entrypoint
  visibility := .«public»}

private def genericLedgerModule : Definition := {
  parameters := [⟨"N", .natural⟩, ⟨"T", .type⟩]
  members := [ledgerStateMember, ledgerCircuitMember, ledgerEntrypointMember]
  entrypoints := [{
    member := 2
    name := "update"
    circuit := .localMember 1
    effects := [⟨.writeCellOutput (.localMember 0) "result", {}⟩]}]
  exports := [
    {name := "balance", target := .localMember 0},
    {name := "update", target := .localMember 2}]
}

private def moduleContractRoot : Definition := {
  imports := [
    {viewName := "first", target := sourceName ["Demo", "Ledger"],
      arguments := [.naturalValue 2, .typeValue (.scalar .native)], selections := [
        {sourceName := "balance", localName := "balance"},
        {sourceName := "update", localName := "update"}]},
    {viewName := "again", target := sourceName ["Demo", "Ledger"],
      arguments := [.naturalValue 2, .typeValue (.scalar .native)], selections := [
        {sourceName := "balance", localName := "balance"},
        {sourceName := "update", localName := "update"}]},
    {viewName := "different", target := sourceName ["Demo", "Ledger"],
      arguments := [.naturalValue 3, .typeValue (.scalar .native)], selections := [
        {sourceName := "balance", localName := "balance"},
        {sourceName := "update", localName := "update"}]}]
  exports := [
    {name := "firstBalance", target := .importedMember "first" "balance"},
    {name := "againBalance", target := .importedMember "again" "balance"},
    {name := "differentBalance", target := .importedMember "different" "balance"},
    {name := "firstUpdate", target := .importedMember "first" "update"},
    {name := "againUpdate", target := .importedMember "again" "update"},
    {name := "differentUpdate", target := .importedMember "different" "update"}]
}

private def genericTypeStateModule : Definition := {
  parameters := [⟨"T", .type⟩]
  members := [{
    id := 0
    name := "value"
    kind := .state
    visibility := .«public»
    stateSchema? := some (.cell (.parameter "T"))}]
  exports := [{name := "value", target := .localMember 0}]}

private def genericNaturalStateModule : Definition := {
  parameters := [⟨"N", .natural⟩]
  members := [{
    id := 0
    name := "value"
    kind := .state
    visibility := .«public»
    stateSchema? := some (.cell (.uint (.parameter "N")))}]
  exports := [{name := "value", target := .localMember 0}]}

private def exportIdentity (expansion : Expansion) (module : Name) (name : String) :
    Option MemberIdentity := do
  let moduleInstance ← expansion.instances.find? (·.key.sourceName == module)
  let exported ← moduleInstance.exports.find? (·.name == name)
  pure exported.identity

private def sourceExportFor (expansion : Expansion) (module : Name) (name : String) :
    Option ResolvedSourceExport := do
  let identity ← exportIdentity expansion module name
  expansion.sourceExport identity

-- Declaration identity comes from the full structural Lean name.
#guard match registerAll [
    (sourceName ["Demo", "Shared"], baseModule),
    (sourceName ["Demo", "Facade"], baseModule)] with
  | .ok registry =>
    match expand registry (sourceName ["Demo", "Shared"]) [] with
    | .ok shared =>
      match expand registry (sourceName ["Demo", "Facade"]) [] with
      | .ok facade =>
        match exportIdentity shared (sourceName ["Demo", "Shared"]) "balance",
            exportIdentity facade (sourceName ["Demo", "Facade"]) "balance" with
        | some first, some second => first != second
        | _, _ => false
      | .error _ => false
    | .error _ => false
  | .error _ => false

-- Module contract plans share aliased state, split distinct specializations,
-- and preserve source helper arguments under the original declaration name.
#guard match registerAll [
    (sourceName ["Demo", "Ledger"], genericLedgerModule),
    (sourceName ["Demo", "Contract"], moduleContractRoot)] with
  | .ok registry =>
    match expand registry (sourceName ["Demo", "Contract"]) [] with
    | .ok expansion =>
      match expansion.contractPlan expansion.root with
      | .ok plan =>
        let groupResult := plan.specializationGroups
        let fakeCircuits := plan.circuits.map fun source =>
          {name := source.outputName : Circuit}
        let contractResult := plan.assembleContract "Demo.Contract" fakeCircuits
        match groupResult with
        | .ok [group] =>
          match plan.entrypoints.find? (·.name == "firstUpdate"),
              plan.entrypoints.find? (·.name == "againUpdate"),
              plan.entrypoints.find? (·.name == "differentUpdate") with
          | some entryA, some entryB, some entryC =>
            match entryA.effects, entryB.effects, entryC.effects with
            | [.writeCell stateNameA .native _], [.writeCell stateNameB .native _],
                [.writeCell stateNameC .native _] =>
              plan.state.length == 2 && plan.state[0]?.map (·.name) !=
                plan.state[1]?.map (·.name) && plan.circuits.length == 2 &&
              plan.circuits[0]?.map (·.outputName) != plan.circuits[1]?.map (·.outputName) &&
              group.requests.length == 2 && stateNameA == stateNameB &&
              stateNameA != stateNameC &&
              (match contractResult with
                | .ok contract => contract.name == "Demo.Contract" &&
                    contract.state.length == 2 && contract.entrypoints.length == 3 &&
                    contract.entrypoints.all (fun entry =>
                      (fakeCircuits.map (·.name)).contains entry.circuit.name)
                | .error _ => false) &&
              group.requests.all fun request =>
                request.sourceExport == "update" && request.arguments.length == 1 &&
                (request.arguments == [.natural (.literal 2)] ||
                  request.arguments == [.natural (.literal 3)])
            | _, _, _ => false
          | _, _, _ => false
        | _ => false
      | .error _ => false
    | .error _ => false
  | .error _ => false

-- A batch shares one cache and assigns generated IDs in canonical export order.
#guard match Noctium.Helpers.Specialization.specializeBatch genericIdentitySource
      ["wide", "nativeB", "nativeA"],
    Noctium.Helpers.Specialization.specializeBatch genericIdentitySource
      ["nativeA", "wide", "nativeB"] with
  | .ok first, .ok second =>
    first.instances == second.instances &&
    first.program.declarations.map (·.id) == second.program.declarations.map (·.id) &&
    first.program.exports.map (fun entry => (entry.name, entry.target)) ==
      second.program.exports.map (fun entry => (entry.name, entry.target)) &&
    first.instances.length == 2 &&
    (first.program.exports.find? (·.name == "nativeA")).map (·.target) ==
      (first.program.exports.find? (·.name == "nativeB")).map (·.target)
  | _, _ => false

#guard messageContains
  (Noctium.Helpers.Specialization.specializeBatchWithLimits
    {maxSpecializations := 1} genericIdentitySource ["nativeA", "wide"])
  "batch export count"

private def moduleRequests : List ExportRequest := [
  {sourceExport := "identity", outputName := "nlm_10", arguments :=
    [.type (.uint (.literal 31))]},
  {sourceExport := "identity", outputName := "nlm_11", arguments :=
    [.type (.uint (.literal 31))]},
  {sourceExport := "identity", outputName := "nlm_12", arguments :=
    [.type (.uint (.literal 63))]}]

#guard match
    Noctium.Helpers.Specialization.specializeRequestsWithLimits {}
      genericRequestSource moduleRequests,
    Noctium.Helpers.Specialization.specializeRequestsWithLimits {}
      genericRequestSource moduleRequests.reverse with
  | .ok first, .ok second =>
    first.instances == second.instances &&
    first.program.exports.map (·.name) == second.program.exports.map (·.name) &&
    first.instances.length == 2 &&
    (first.program.exports.find? (·.name == "nlm_10")).map (·.target) ==
      (first.program.exports.find? (·.name == "nlm_11")).map (·.target) &&
    (first.program.exports.find? (·.name == "nlm_12")).bind
      (fun entry => entry.inputs.head?.map (·.ty)) ==
      some (.uint 63)
  | _, _ => false

-- Two view aliases preserve the original declaration identity and state field.
#guard match registerAll [
    (sourceName ["Demo", "Shared"], baseModule),
    (sourceName ["Demo", "Alias"], aliasDefinition)] with
  | .ok registry =>
    match expand registry (sourceName ["Demo", "Alias"]) [] with
    | .ok expansion =>
      match exportIdentity expansion (sourceName ["Demo", "Alias"]) "left",
          exportIdentity expansion (sourceName ["Demo", "Alias"]) "right" with
      | some left, some right =>
        left == right &&
        (expansion.stateFieldName left) == (expansion.stateFieldName right) &&
        left.module.sourceName == sourceName ["Demo", "Shared"]
      | _, _ => false
    | .error _ => false
  | .error _ => false

-- Equal ordered normalized arguments reuse one module instance. A different
-- type argument gets a separate identity even though the module source matches.
#guard match registerAll [
    (sourceName ["Demo", "Generic"], genericModule),
    (sourceName ["Demo", "Root"], rootWithTwoGenericImports)] with
  | .ok registry =>
    match expand registry (sourceName ["Demo", "Root"]) [] with
    | .ok expansion =>
      let genericInstances := expansion.instances.filter
        (·.key.sourceName == sourceName ["Demo", "Generic"])
      match exportIdentity expansion (sourceName ["Demo", "Root"]) "a",
          exportIdentity expansion (sourceName ["Demo", "Root"]) "b",
          exportIdentity expansion (sourceName ["Demo", "Root"]) "c" with
      | some a, some b, some c =>
        let sourceA := sourceExportFor expansion (sourceName ["Demo", "Root"]) "circuitA"
        let sourceB := sourceExportFor expansion (sourceName ["Demo", "Root"]) "circuitB"
        let sourceC := sourceExportFor expansion (sourceName ["Demo", "Root"]) "circuitC"
        genericInstances.length == 2 && a == b && a != c &&
        expansion.stateFieldName a == expansion.stateFieldName b &&
        expansion.stateFieldName a != expansion.stateFieldName c &&
        sourceA == sourceB && sourceA != sourceC &&
        sourceA.map (·.arguments) == some [.type (.scalar .native), .natural 8] &&
        sourceC.map (·.arguments) == some [.type (.scalar .bool), .natural 8] &&
        sourceA.map (·.program) == some (sourceName ["Demo", "Program"])
      | _, _, _ => false
    | .error _ => false
  | .error _ => false

-- A nested generic module forwards only names from its own declared scope.
private def forwardingModule : Definition := {
  parameters := [⟨"U", .type⟩, ⟨"M", .natural⟩]
  imports := [⟨"child", sourceName ["Demo", "Generic"],
    [.typeParameter "U", .naturalParameter "M"],
    [{sourceName := "value", localName := "value"}], {}⟩]
  exports := [{name := "value", target := .importedMember "child" "value"}]
}

#guard match registerAll [
    (sourceName ["Demo", "Generic"], genericModule),
    (sourceName ["Demo", "Forward"], forwardingModule)] with
  | .ok registry =>
    match expand registry (sourceName ["Demo", "Forward"])
        [.type (.scalar .native), .natural 11] with
    | .ok expansion =>
      expansion.instances.any fun moduleInstance =>
        moduleInstance.key.sourceName == sourceName ["Demo", "Generic"] &&
        moduleInstance.key.arguments == [.type (.scalar .native), .natural 11]
    | .error _ => false
  | .error _ => false

-- GEN-ARITY and GEN-KINDS fail before any instance is emitted.
#guard match registerAll [(sourceName ["Demo", "Generic"], genericModule)] with
  | .ok registry =>
    messageContains (expand registry (sourceName ["Demo", "Generic"])
      [.type (.scalar .native)]) "arity mismatch" &&
    messageContains (expand registry (sourceName ["Demo", "Generic"])
      [.natural 1, .type (.scalar .native)]) "kind mismatch"
  | .error _ => false

-- Private members cannot export or cross a selective-import boundary.
private def privateExport : Definition := {
  members := [moduleMember 0 "hidden" .state .«private»]
  exports := [{name := "hidden", target := .localMember 0}]
}

private def privateMemberOnly : Definition := {
  members := [moduleMember 0 "hidden" .state .«private»]
}

private def privateSelection : Definition := {
  imports := [⟨"private", sourceName ["Demo", "Private"], [],
    [{sourceName := "hidden", localName := "hidden"}], {}⟩]
}

#guard match registerAll [
    (sourceName ["Demo", "Private"], privateExport),
    (sourceName ["Demo", "Root"], privateSelection)] with
  | .ok registry =>
    messageContains (expand registry (sourceName ["Demo", "Private"]) [])
      "cannot be exported" &&
    match registerAll [
      (sourceName ["Demo", "Private"], privateMemberOnly),
      (sourceName ["Demo", "Root"], privateSelection)] with
    | .ok privateRegistry => messageContains
        (expand privateRegistry (sourceName ["Demo", "Root"]) [])
        "does not export 'hidden'"
    | .error _ => false
  | .error _ => false

-- Import cycles report a bounded source diagnostic.
private def cycleA : Definition := {
  imports := [{viewName := "b", target := sourceName ["Demo", "CycleB"]}]
}

private def cycleB : Definition := {
  imports := [{viewName := "a", target := sourceName ["Demo", "CycleA"]}]
}

#guard match registerAll [
    (sourceName ["Demo", "CycleA"], cycleA),
    (sourceName ["Demo", "CycleB"], cycleB)] with
  | .ok registry => messageContains
      (expand registry (sourceName ["Demo", "CycleA"]) []) "module import cycle"
  | .error _ => false

-- Generic ledger schemas resolve type and natural arguments per module key.
#guard match registerAll [
    (sourceName ["Demo", "TypeState"], genericTypeStateModule),
    (sourceName ["Demo", "NaturalState"], genericNaturalStateModule)] with
  | .ok registry =>
    let typeResult := expand registry (sourceName ["Demo", "TypeState"])
      [.type (.scalar (.uint 31))]
    let typeNativeResult := expand registry (sourceName ["Demo", "TypeState"])
      [.type (.scalar .native)]
    let naturalResult := expand registry (sourceName ["Demo", "NaturalState"])
      [.natural 63]
    let typeResolved := match typeResult with
      | .ok expansion =>
        match expansion.findInstance expansion.root with
        | some moduleInstance => moduleInstance.members.any fun member =>
          member.stateKind? == some (.cell (.uint 31))
        | none => false
      | .error _ => false
    let naturalResolved := match naturalResult with
      | .ok expansion =>
        match expansion.findInstance expansion.root with
        | some moduleInstance => moduleInstance.members.any fun member =>
          member.stateKind? == some (.cell (.uint 63))
        | none => false
      | .error _ => false
    let typeIdentityDistinct := match typeNativeResult, typeResult with
      | .ok nativeExpansion, .ok uintExpansion =>
        let nativeIdentity := exportIdentity nativeExpansion
          (sourceName ["Demo", "TypeState"]) "value"
        let uintIdentity := exportIdentity uintExpansion
          (sourceName ["Demo", "TypeState"]) "value"
        nativeIdentity.isSome && uintIdentity.isSome && nativeIdentity != uintIdentity &&
          nativeIdentity.bind nativeExpansion.stateFieldName !=
            uintIdentity.bind uintExpansion.stateFieldName
      | _, _ => false
    typeResolved && naturalResolved && typeIdentityDistinct && messageContains
      (expand registry (sourceName ["Demo", "TypeState"])
        [.type (.tuple [.scalar .native])])
      "aggregate ledger state is not supported" &&
      messageContains (expand registry (sourceName ["Demo", "TypeState"])
        [.type (.scalar .jubjubScalar)])
        "Jubjub state parameters are not supported by module specialization"
  | .error _ => false

-- Instance and normalized-type budgets stop before expansion or key encoding.
#guard match registerAll [
    (sourceName ["Demo", "Generic"], genericModule),
    (sourceName ["Demo", "Root"], rootWithTwoGenericImports)] with
  | .ok registry =>
    messageContains (expandWithLimits {maxModuleInstances := 1} registry
      (sourceName ["Demo", "Root"]) []) "module instance count before expansion" &&
    messageContains (expandWithLimits {maxExpandedNodes := 1} registry
      (sourceName ["Demo", "Generic"])
      [.type (.vector 4 (.scalar .native)), .natural 1]) "normalized type nodes"
  | .error _ => false

end Noctium.ModulesTests
