import Noctium.Frontend
import Noctium.Modules

open Noctium
open Noctium.Helpers.Specialization
open Noctium.Modules
open scoped Noctium

private def genericRecordCellLedgerEnvironment : Types.CompositeEnv := {
  structures := [{
    id := "GenericRecordCell.Ledger"
    fields := [
      {name := "issued", type := .scalar .native},
      {name := "spent", type := .scalar .native},
      {name := "tag", type := .bytes 4}
    ]
  }]
}

def genericRecordCellInspectProgram : Program := {
  declarations := [{
    id := ⟨0, 0⟩
    name := "unit"
    parameters := [⟨"T", .type⟩]
    result := .unit
    body := [.return]
  }]
  exports := [{name := "inspect", target := ⟨0, 0⟩}]
}

def genericRecordCellUpdateProgram : Program := {
  declarations := [{
    id := ⟨0, 0⟩
    name := "unit"
    parameters := [⟨"T", .type⟩]
    values := [
      ("enabled", .bool),
      ("next", .parameter "T")
    ]
    result := .unit
    body := [.return]
  }]
  exports := [{
    name := "update"
    target := ⟨0, 0⟩
    inputs := [
      {name := "enabled", type := .bool, visibility := .private},
      {name := "next", type := .parameter "T", visibility := .private}
    ]
  }]
}

private def genericRecordCellState : Member := {
  id := 0
  name := "ledger"
  kind := .state
  visibility := .«public»
  stateSchema? := some (.cell (.parameter "T"))
}

private def genericRecordCellEntrypointMember (id : Nat) (name : String) : Member := {
  id
  name
  kind := .entrypoint
  visibility := .«public»
}

def genericRecordCellModule : Definition := {
  parameters := [⟨"T", .type⟩]
  members := [
    genericRecordCellState,
    {id := 1, name := "inspectCircuit", kind := .circuit,
      sourceExport? := some {
        program := `genericRecordCellInspectProgram
        exportName := "inspect"
        arguments := [.typeParameter "T"]
      }},
    {id := 2, name := "updateCircuit", kind := .circuit,
      sourceExport? := some {
        program := `genericRecordCellUpdateProgram
        exportName := "update"
        arguments := [.typeParameter "T"]
      }},
    genericRecordCellEntrypointMember 3 "inspect",
    genericRecordCellEntrypointMember 4 "update"
  ]
  entrypoints := [
    {
      «member» := 3
      name := "inspect"
      circuit := .localMember 1
      cellReturns := [{name := "result", state := .localMember 0}]
    },
    {
      «member» := 4
      name := "update"
      circuit := .localMember 2
      callInputs := ["enabled"]
      effects := [{
        effect := .writeRecordCellInput (.localMember 0) "next" (disclosed := Bool.true)
        guard := some (.disclose {} (.ref "enabled" : Expr .bool))
      }]
      cellReturns := [{name := "result", state := .localMember 0}]
    }
  ]
  exports := [
    {name := "ledger", target := .localMember 0},
    {name := "inspect", target := .localMember 3},
    {name := "update", target := .localMember 4}
  ]
}

noctium_module from genericRecordCellModule

def genericRecordCellRoot : Definition := {
  imports := [{
    viewName := "record"
    target := `genericRecordCellModule
    arguments := [
      .checkedTypeValue (.structure "GenericRecordCell.Ledger")
        genericRecordCellLedgerEnvironment
    ]
    selections := [
      {sourceName := "ledger", localName := "ledger"},
      {sourceName := "inspect", localName := "inspect"},
      {sourceName := "update", localName := "update"}
    ]
  }]
  exports := [
    {name := "ledger", target := .importedMember "record" "ledger"},
    {name := "inspect", target := .importedMember "record" "inspect"},
    {name := "update", target := .importedMember "record" "update"}
  ]
}

noctium_module from genericRecordCellRoot

def genericRecordCellRequest : Request := {
  sourceName := `genericRecordCellRoot
  arguments := []
  constructorInputs := [{
    state := .importedMember "record" "ledger"
    recordFields := [("issued", "issued"), ("spent", "spent"), ("tag", "initialTag")]
  }]
}

noctium_module_contract GenericRecordCell from genericRecordCellRequest

private def genericRecordCellRegistry : Registry := {
  modules := [
    {sourceName := `genericRecordCellModule, definition := genericRecordCellModule},
    {sourceName := `genericRecordCellRoot, definition := genericRecordCellRoot}
  ]
}

private def genericRecordCellPlanFor (request : Request) : Except Diagnostic ModuleContractPlan := do
  let expansion ← Modules.expand genericRecordCellRegistry request.sourceName request.arguments
  expansion.contractPlan expansion.root request.constructorInputs

private def genericRecordCellWrongFieldsRequest : Request := {
  genericRecordCellRequest with
  constructorInputs := [{
    state := .importedMember "record" "ledger"
    recordFields := [("issued", "issued"), ("missing", "spent"), ("tag", "initialTag")]
  }]
}

private def genericRecordCellWrongInputEnvironment : Types.CompositeEnv := {
  structures := [{
    id := "GenericRecordCell.OtherLedger"
    fields := [
      {name := "issued", type := .scalar .native},
      {name := "spent", type := .scalar .native},
      {name := "tag", type := .bytes 4}
    ]
  }]
}

def genericRecordCellWrongUpdateProgram : Program := genericRecordCellUpdateProgram

def genericRecordCellWrongInputModule : Definition := {
  genericRecordCellModule with
  members := genericRecordCellModule.members.map fun item =>
    if item.id == 2 then
      {item with sourceExport? := some {
        program := `genericRecordCellWrongUpdateProgram
        exportName := "update"
        arguments := [.checkedTypeValue (.structure "GenericRecordCell.OtherLedger")
          genericRecordCellWrongInputEnvironment]
      }}
    else item
}

noctium_module from genericRecordCellWrongInputModule

def genericRecordCellWrongInputRoot : Definition := {
  genericRecordCellRoot with
  imports := genericRecordCellRoot.imports.map fun item =>
    {item with target := `genericRecordCellWrongInputModule}
}

noctium_module from genericRecordCellWrongInputRoot

private def genericRecordCellWrongInputRegistry : Registry := {
  modules := genericRecordCellRegistry.modules ++ [
    {sourceName := `genericRecordCellWrongInputModule,
      definition := genericRecordCellWrongInputModule},
    {sourceName := `genericRecordCellWrongInputRoot,
      definition := genericRecordCellWrongInputRoot}
  ]
}

private def genericRecordCellWrongInputRequest : Request := {
  genericRecordCellRequest with sourceName := `genericRecordCellWrongInputRoot
}

private def genericRecordCellWrongInputSpecialization : Except Diagnostic SpecializedModule := do
  let expansion ← Modules.expand genericRecordCellWrongInputRegistry
    genericRecordCellWrongInputRequest.sourceName genericRecordCellWrongInputRequest.arguments
  let plan ← expansion.contractPlan expansion.root
    genericRecordCellWrongInputRequest.constructorInputs
  plan.specializeWithSources {} [
    (`genericRecordCellInspectProgram, genericRecordCellInspectProgram),
    (`genericRecordCellWrongUpdateProgram, genericRecordCellWrongUpdateProgram)
  ]

#guard match LedgerValueType.cellRecordFields genericRecordCellLedgerEnvironment
    (.structure "GenericRecordCell.Ledger") with
  | .ok [
      ("issued", .native),
      ("spent", .native),
      ("tag", .bytes 4)
    ] => Bool.true
  | _ => Bool.false

#guard match genericRecordCellPlanFor genericRecordCellRequest with
  | .ok plan =>
    match plan.constructor? with
    | some constr =>
      constr.parameters.map (fun parameter => (parameter.name, parameter.type)) == [
          ("issued", .scalar .native),
          ("spent", .scalar .native),
          ("initialTag", .scalar (.bytes 4))
        ]
    | none => Bool.false
  | .error _ => Bool.false

#guard match GenericRecordCell.entrypoints.find? (·.name == "update") with
  | some update =>
    let viewMatches := match update.callInputViews with
      | [view] =>
        view.name == "next" && view.fields == [
          ("next.issued", .native),
          ("next.spent", .native),
          ("next.tag.0", .uint 255),
          ("next.tag.1", .uint 255),
          ("next.tag.2", .uint 255),
          ("next.tag.3", .uint 255)
        ]
      | _ => Bool.false
    update.callInputs == [
      "enabled",
      "next.issued",
      "next.spent",
      "next.tag.0",
      "next.tag.1",
      "next.tag.2",
      "next.tag.3"
    ] && viewMatches
  | none => Bool.false

#guard match genericRecordCellPlanFor genericRecordCellWrongFieldsRequest with
  | .error diagnostic => diagnostic.message.contains "module record Cell is missing field 'spent'"
  | .ok _ => Bool.false

#guard match genericRecordCellWrongInputSpecialization with
  | .error diagnostic =>
    diagnostic.message.contains "module record Cell input 'next' does not match the checked Cell layout"
  | .ok _ => Bool.false

-- Making an input a call argument does not authorize its use as a public write guard.
#guard
  let hiddenGuard := {GenericRecordCell with
    entrypoints := GenericRecordCell.entrypoints.map fun operation =>
      if operation.name == "update" then
        {operation with effectGuards := [some (.ref "enabled"), none]}
      else operation}
  match Disclosure.contract hiddenGuard with
  | .error diagnostic =>
    diagnostic.message.contains "undisclosed private control from parameter 'enabled'"
  | .ok _ => Bool.false
