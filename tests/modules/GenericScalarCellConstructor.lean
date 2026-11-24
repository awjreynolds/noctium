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

def genericScalarCellModule : Definition := {
  parameters := [⟨"T", .type⟩]
  members := [{
    id := 0
    name := "cell"
    kind := .state
    visibility := .«public»
    stateSchema? := some (.cell (.parameter "T"))
  }]
  exports := [{name := "cell", target := .localMember 0}]
}

noctium_module from genericScalarCellModule

def genericScalarCellRoot : Definition := {
  imports := [
    {
      viewName := "field"
      target := `genericScalarCellModule
      arguments := [.typeValue (.scalar .native)]
      selections := [{sourceName := "cell", localName := "cell"}]
    },
    {
      viewName := "flag"
      target := `genericScalarCellModule
      arguments := [.typeValue (.scalar .bool)]
      selections := [{sourceName := "cell", localName := "cell"}]
    },
    {
      viewName := "count"
      target := `genericScalarCellModule
      arguments := [.typeValue (.scalar (.uint 65535))]
      selections := [{sourceName := "cell", localName := "cell"}]
    }
  ]
  members := [
    {id := 0, name := "readCircuit", kind := .circuit, sourceExport? := some {
      program := `genericScalarCellReadProgram
      exportName := "read"
    }},
    {id := 1, name := "readField", kind := .entrypoint, visibility := .«public»},
    {id := 2, name := "readFlag", kind := .entrypoint, visibility := .«public»},
    {id := 3, name := "readCount", kind := .entrypoint, visibility := .«public»}
  ]
  entrypoints := [
    {
      «member» := 1
      name := "readField"
      circuit := .localMember 0
      effects := [{effect := .readCell (.importedMember "field" "cell") "fieldValue" .native}]
      returns := [{name := "result", ty := .native, value := .ref "fieldValue"}]
    },
    {
      «member» := 2
      name := "readFlag"
      circuit := .localMember 0
      effects := [{effect := .readCell (.importedMember "flag" "cell") "flagValue" .bool}]
      returns := [{name := "result", ty := .bool, value := .ref "flagValue"}]
    },
    {
      «member» := 3
      name := "readCount"
      circuit := .localMember 0
      effects := [{effect := .readCell (.importedMember "count" "cell") "countValue" (.uint 65535)}]
      returns := [{name := "result", ty := .uint 65535, value := .ref "countValue"}]
    }
  ]
  exports := [
    {name := "fieldCell", target := .importedMember "field" "cell"},
    {name := "flagCell", target := .importedMember "flag" "cell"},
    {name := "countCell", target := .importedMember "count" "cell"},
    {name := "readField", target := .localMember 1},
    {name := "readFlag", target := .localMember 2},
    {name := "readCount", target := .localMember 3}
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
