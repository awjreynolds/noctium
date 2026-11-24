import Noctium.Frontend
import Noctium.Modules

open Noctium
open Noctium.Helpers.Specialization
open Noctium.Modules
open scoped Noctium

def genericScalarCellReadProgram : Program := {
  declarations := [{
    id := ⟨0, 0⟩
    name := "unit"
    result := .unit
    body := [.return]
  }]
  exports := [{name := "read", target := ⟨0, 0⟩}]
}

def genericScalarCellUpdateProgram : Program := {
  declarations := [{
    id := ⟨0, 0⟩
    name := "update"
    parameters := [⟨"T", .type⟩]
    values := [("enabled", .bool), ("next", .parameter "T")]
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

def genericScalarCellModule : Definition := {
  parameters := [⟨"T", .type⟩]
  members := [
    {
      id := 0
      name := "cell"
      kind := .state
      visibility := .«public»
      stateSchema? := some (.cell (.parameter "T"))
    },
    {id := 1, name := "readCircuit", kind := .circuit, sourceExport? := some {
      program := `genericScalarCellReadProgram
      exportName := "read"
    }},
    {id := 2, name := "read", kind := .entrypoint, visibility := .«public»},
    {id := 3, name := "updateCircuit", kind := .circuit, sourceExport? := some {
      program := `genericScalarCellUpdateProgram
      exportName := "update"
      arguments := [.typeParameter "T"]
    }},
    {id := 4, name := "update", kind := .entrypoint, visibility := .«public»}
  ]
  entrypoints := [
    {
      «member» := 2
      name := "read"
      circuit := .localMember 1
      cellReturns := [{name := "result", state := .localMember 0}]
    },
    {
      «member» := 4
      name := "update"
      circuit := .localMember 3
      callInputs := ["enabled"]
      effects := [{
        effect := .writeCellInput (.localMember 0) "next" (disclosed := Bool.true)
        guard := some (.disclose {} (.ref "enabled" : Expr .bool))
      }]
      cellReturns := [{name := "result", state := .localMember 0}]
    }
  ]
  exports := [
    {name := "cell", target := .localMember 0},
    {name := "read", target := .localMember 2},
    {name := "update", target := .localMember 4}
  ]
}

noctium_module from genericScalarCellModule

def genericScalarCellRoot : Definition := {
  imports := [
    {
      viewName := "field"
      target := `genericScalarCellModule
      arguments := [.typeValue (.scalar .native)]
      selections := [
        {sourceName := "cell", localName := "cell"},
        {sourceName := "read", localName := "read"},
        {sourceName := "update", localName := "update"}
      ]
    },
    {
      viewName := "flag"
      target := `genericScalarCellModule
      arguments := [.typeValue (.scalar .bool)]
      selections := [
        {sourceName := "cell", localName := "cell"},
        {sourceName := "read", localName := "read"},
        {sourceName := "update", localName := "update"}
      ]
    },
    {
      viewName := "count"
      target := `genericScalarCellModule
      arguments := [.typeValue (.scalar (.uint 65535))]
      selections := [
        {sourceName := "cell", localName := "cell"},
        {sourceName := "read", localName := "read"},
        {sourceName := "update", localName := "update"}
      ]
    }
  ]
  exports := [
    {name := "fieldCell", target := .importedMember "field" "cell"},
    {name := "flagCell", target := .importedMember "flag" "cell"},
    {name := "countCell", target := .importedMember "count" "cell"},
    {name := "readField", target := .importedMember "field" "read"},
    {name := "readFlag", target := .importedMember "flag" "read"},
    {name := "readCount", target := .importedMember "count" "read"},
    {name := "updateField", target := .importedMember "field" "update"},
    {name := "updateFlag", target := .importedMember "flag" "update"},
    {name := "updateCount", target := .importedMember "count" "update"}
  ]
}

noctium_module from genericScalarCellRoot

def genericScalarCellRequest : Request := {
  sourceName := `genericScalarCellRoot
  arguments := []
  constructorInputs := [
    {state := .importedMember "field" "cell", parameterName := "initialField"},
    {state := .importedMember "flag" "cell", parameterName := "initialFlag"},
    {state := .importedMember "count" "cell", parameterName := "initialCount"}
  ]
}

noctium_module_contract GenericScalarCellConstructor from genericScalarCellRequest

#guard match GenericScalarCellConstructor.constructor with
  | some constr =>
    constr.parameters.map (fun parameter => (parameter.name, parameter.type)) == [
      ("initialField", .scalar .native),
      ("initialFlag", .scalar .bool),
      ("initialCount", .scalar (.uint 65535))
    ] &&
    constr.initializers.map (fun initializer => initializer.type) == [
      .scalar .native,
      .scalar .bool,
      .scalar (.uint 65535)
    ]
  | none => Bool.false

private def genericScalarCellReturnType (entryName : String) (ty : Ty) : _root_.Bool :=
  match GenericScalarCellConstructor.entrypoints.find? (·.name == entryName) with
  | some operation =>
    match operation.returns with
    | [returned] => returned.name == "result" && returned.ty == ty
    | _ => Bool.false
  | none => Bool.false

#guard genericScalarCellReturnType "readField" .native &&
  genericScalarCellReturnType "readFlag" .bool &&
  genericScalarCellReturnType "readCount" (.uint 65535) &&
  genericScalarCellReturnType "updateField" .native &&
  genericScalarCellReturnType "updateFlag" .bool &&
  genericScalarCellReturnType "updateCount" (.uint 65535)

private def genericScalarCellUpdateHeader (entryName : String) (ty : Ty) : _root_.Bool :=
  match GenericScalarCellConstructor.entrypoints.find? (·.name == entryName) with
  | some operation =>
    operation.callInputViews.isEmpty &&
      operation.callArguments.map (fun argument => (argument.name, argument.ty)) ==
        [("enabled", .bool), ("next", ty)]
  | none => Bool.false

#guard genericScalarCellUpdateHeader "updateField" .native &&
  genericScalarCellUpdateHeader "updateFlag" .bool &&
  genericScalarCellUpdateHeader "updateCount" (.uint 65535)

private def genericScalarCellRegistry : Registry := {
  modules := [
    {sourceName := `genericScalarCellModule, definition := genericScalarCellModule},
    {sourceName := `genericScalarCellRoot, definition := genericScalarCellRoot}
  ]
}

private def genericScalarCellDuplicateRequest : Request := {
  genericScalarCellRequest with
  constructorInputs := genericScalarCellRequest.constructorInputs ++ [
    {state := .importedMember "field" "cell", parameterName := "duplicateField"}
  ]
}

private def genericScalarCellPlanFor (request : Request) : Except Diagnostic ModuleContractPlan := do
  let expansion ← Modules.expand genericScalarCellRegistry request.sourceName request.arguments
  expansion.contractPlan expansion.root request.constructorInputs

#guard match genericScalarCellPlanFor genericScalarCellDuplicateRequest with
  | .error diagnostic =>
    diagnostic.message.contains "duplicate module constructor initializer"
  | .ok _ => Bool.false

private def wrongScalarCellSetterRegistry : Registry := {
  modules := genericScalarCellRegistry.modules.map fun registered =>
    if registered.sourceName == `genericScalarCellModule then
      let members := registered.definition.members.map fun item =>
        if item.id == 3 then
          {item with sourceExport? := item.sourceExport?.map fun source =>
            {source with arguments := [.typeValue (.scalar (.uint 255))]}}
        else item
      {registered with definition := {registered.definition with members}}
    else registered
}

#guard match Modules.specializeRequestWithSources {} {} wrongScalarCellSetterRegistry
    genericScalarCellRequest [
      (`genericScalarCellReadProgram, genericScalarCellReadProgram),
      (`genericScalarCellUpdateProgram, genericScalarCellUpdateProgram)
    ] with
  | .error diagnostic =>
    diagnostic.message.contains "module scalar Cell input 'next' does not match the checked Cell type"
  | .ok _ => Bool.false
