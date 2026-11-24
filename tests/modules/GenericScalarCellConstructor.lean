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
    {id := 2, name := "read", kind := .entrypoint, visibility := .«public»}
  ]
  entrypoints := [{
    «member» := 2
    name := "read"
    circuit := .localMember 1
    cellReturns := [{name := "result", state := .localMember 0}]
  }]
  exports := [
    {name := "cell", target := .localMember 0},
    {name := "read", target := .localMember 2}
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
        {sourceName := "read", localName := "read"}
      ]
    },
    {
      viewName := "flag"
      target := `genericScalarCellModule
      arguments := [.typeValue (.scalar .bool)]
      selections := [
        {sourceName := "cell", localName := "cell"},
        {sourceName := "read", localName := "read"}
      ]
    },
    {
      viewName := "count"
      target := `genericScalarCellModule
      arguments := [.typeValue (.scalar (.uint 65535))]
      selections := [
        {sourceName := "cell", localName := "cell"},
        {sourceName := "read", localName := "read"}
      ]
    }
  ]
  exports := [
    {name := "fieldCell", target := .importedMember "field" "cell"},
    {name := "flagCell", target := .importedMember "flag" "cell"},
    {name := "countCell", target := .importedMember "count" "cell"},
    {name := "readField", target := .importedMember "field" "read"},
    {name := "readFlag", target := .importedMember "flag" "read"},
    {name := "readCount", target := .importedMember "count" "read"}
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
  genericScalarCellReturnType "readCount" (.uint 65535)

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
