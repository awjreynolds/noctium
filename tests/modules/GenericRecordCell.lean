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
      {name := "spent", type := .scalar .native}
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
    values := [
      ("enabled", .bool),
      ("nextIssued", .native),
      ("nextSpent", .native)
    ]
    result := .unit
    body := [.return]
  }]
  exports := [{
    name := "update"
    target := ⟨0, 0⟩
    inputs := [
      {name := "enabled", type := .bool, visibility := .private},
      {name := "nextIssued", type := .native, visibility := .private},
      {name := "nextSpent", type := .native, visibility := .private}
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
      }},
    genericRecordCellEntrypointMember 3 "inspect",
    genericRecordCellEntrypointMember 4 "update"
  ]
  entrypoints := [
    {
      «member» := 3
      name := "inspect"
      circuit := .localMember 1
      recordCellReturns := [{name := "result", state := .localMember 0}]
    },
    {
      «member» := 4
      name := "update"
      circuit := .localMember 2
      callInputs := ["enabled", "nextIssued", "nextSpent"]
      effects := [{
        effect := .writeRecordCell (.localMember 0) [
          ("issued", .mk .native (.disclose {} (.ref "nextIssued" : Expr .native))),
          ("spent", .mk .native (.disclose {} (.ref "nextSpent" : Expr .native)))
        ]
        guard := some (.disclose {} (.ref "enabled" : Expr .bool))
      }]
      recordCellReturns := [{name := "result", state := .localMember 0}]
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
    recordFields := [("issued", "issued"), ("spent", "spent")]
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
    recordFields := [("issued", "issued"), ("missing", "spent")]
  }]
}

private def genericRecordCellWrongTypeEnvironment : Types.CompositeEnv := {
  structures := [{
    id := "GenericRecordCell.Ledger"
    fields := [
      {name := "issued", type := .scalar .native},
      {name := "spent", type := .scalar .bool}
    ]
  }]
}

def genericRecordCellWrongLayoutRoot : Definition := {
  genericRecordCellRoot with
  imports := genericRecordCellRoot.imports.map fun item =>
    {item with arguments := [
      .checkedTypeValue (.structure "GenericRecordCell.Ledger")
        genericRecordCellWrongTypeEnvironment
    ]}
}

private def genericRecordCellWrongLayoutRegistry : Registry := {
  modules := genericRecordCellRegistry.modules ++ [
    {sourceName := `genericRecordCellWrongLayoutRoot,
      definition := genericRecordCellWrongLayoutRoot}
  ]
}

private def genericRecordCellWrongLayoutRequest : Request := {
  genericRecordCellRequest with sourceName := `genericRecordCellWrongLayoutRoot
}

private def genericRecordCellWrongLayoutPlan : Except Diagnostic ModuleContractPlan := do
  let expansion ← Modules.expand genericRecordCellWrongLayoutRegistry
    genericRecordCellWrongLayoutRequest.sourceName genericRecordCellWrongLayoutRequest.arguments
  expansion.contractPlan expansion.root genericRecordCellWrongLayoutRequest.constructorInputs

#guard match Types.layout Types.defaultLimits genericRecordCellLedgerEnvironment
    (.structure "GenericRecordCell.Ledger") with
  | .ok (.structure "GenericRecordCell.Ledger" [
      ("issued", .scalar .nativeField),
      ("spent", .scalar .nativeField)
    ]) => Bool.true
  | _ => Bool.false

#guard match genericRecordCellPlanFor genericRecordCellRequest with
  | .ok plan =>
    match plan.constructor? with
    | some constr =>
      constr.parameters.map (fun parameter => (parameter.name, parameter.type)) == [
          ("issued", .scalar .native),
          ("spent", .scalar .native)
        ]
    | none => Bool.false
  | .error _ => Bool.false

#guard match genericRecordCellPlanFor genericRecordCellWrongFieldsRequest with
  | .error diagnostic => diagnostic.message.contains "module record Cell is missing field 'spent'"
  | .ok _ => Bool.false

#guard match genericRecordCellWrongLayoutPlan with
  | .error diagnostic => diagnostic.message.contains "module record Cell write field type mismatch"
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
