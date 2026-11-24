import Noctium.Frontend
import Noctium.Modules

open Noctium
open Noctium.Helpers.Specialization
open Noctium.Modules
open scoped Noctium

def genericJubjubScalarReadProgram : Program := {
  declarations := [{
    id := ⟨0, 0⟩
    name := "unit"
    result := .unit
    body := [.return]
  }]
  exports := [{name := "read", target := ⟨0, 0⟩}]
}

def genericJubjubScalarUpdateProgram : Program := {
  declarations := [{
    id := ⟨0, 0⟩
    name := "update"
    parameters := [⟨"T", .type⟩]
    values := [("next", .parameter "T")]
    result := .unit
    body := [.return]
  }]
  exports := [{
    name := "update"
    target := ⟨0, 0⟩
    inputs := [{name := "next", type := .parameter "T", visibility := .private}]
  }]
}

def genericJubjubScalarCellModule : Definition := {
  parameters := [⟨"T", .type⟩]
  members := [
    {
      id := 0
      name := "value"
      kind := .state
      visibility := .«public»
      stateSchema? := some (.cell (.parameter "T"))
    },
    {id := 1, name := "readCircuit", kind := .circuit, sourceExport? := some {
      program := `genericJubjubScalarReadProgram, exportName := "read"}},
    {id := 2, name := "read", kind := .entrypoint, visibility := .«public»},
    {id := 3, name := "updateCircuit", kind := .circuit, sourceExport? := some {
      program := `genericJubjubScalarUpdateProgram, exportName := "update",
      arguments := [.typeParameter "T"]}},
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
      effects := [{
        effect := .writeCellInput (.localMember 0) "next" (disclosed := Bool.true)
      }]
      cellReturns := [{name := "result", state := .localMember 0}]
    }
  ]
  exports := [
    {name := "value", target := .localMember 0},
    {name := "read", target := .localMember 2},
    {name := "update", target := .localMember 4}
  ]
}

noctium_module from genericJubjubScalarCellModule

def genericJubjubScalarCellRoot : Definition := {
  imports := [{
    viewName := "scalar"
    target := `genericJubjubScalarCellModule
    arguments := [.typeValue (.scalar .jubjubScalar)]
    selections := [
      {sourceName := "value", localName := "value"},
      {sourceName := "read", localName := "read"},
      {sourceName := "update", localName := "update"}
    ]
  }]
  exports := [
    {name := "value", target := .importedMember "scalar" "value"},
    {name := "read", target := .importedMember "scalar" "read"},
    {name := "update", target := .importedMember "scalar" "update"}
  ]
}

noctium_module from genericJubjubScalarCellRoot

def genericJubjubScalarCellRequest : Request := {
  sourceName := `genericJubjubScalarCellRoot
  arguments := []
  constructorInputs := [{
    state := .importedMember "scalar" "value"
    parameterName := "initial"
  }]
}

noctium_module_contract GenericJubjubScalarCell from genericJubjubScalarCellRequest

#guard match GenericJubjubScalarCell.constructor with
  | some constr =>
    constr.parameters.map (fun parameter => (parameter.name, parameter.type)) ==
      [("initial", .scalar .jubjubScalar)] &&
    constr.initializers.map (fun initializer => initializer.type) ==
      [.scalar .jubjubScalar]
  | none => Bool.false

private def genericJubjubScalarCellReturnType (entryName : String) : _root_.Bool :=
  match GenericJubjubScalarCell.entrypoints.find? (·.name == entryName) with
  | some operation =>
    match operation.returns with
    | [returned] => returned.name == "result" && returned.ty == .jubjubScalar
    | _ => Bool.false
  | none => Bool.false

#guard genericJubjubScalarCellReturnType "read" &&
  genericJubjubScalarCellReturnType "update"

private def genericJubjubScalarCellRegistry : Registry := {
  modules := [
    {sourceName := `genericJubjubScalarCellModule, definition := genericJubjubScalarCellModule},
    {sourceName := `genericJubjubScalarCellRoot, definition := genericJubjubScalarCellRoot}
  ]
}

private def genericJubjubScalarDefaultRegistry : Registry := {
  modules := [{
    sourceName := `genericJubjubScalarCellModule
    definition := genericJubjubScalarCellModule
  }]
}

private def genericJubjubScalarDefaultRequest : Request := {
  sourceName := `genericJubjubScalarCellModule
  arguments := [.type (.scalar .jubjubScalar)]
}

#guard match Modules.expand genericJubjubScalarDefaultRegistry
    `genericJubjubScalarCellModule [.type (.scalar .jubjubScalar)] with
  | .ok expansion =>
    match expansion.findInstance expansion.root with
    | some moduleInstance => moduleInstance.members.any fun item =>
      item.stateKind? == some (.cell .jubjubScalar)
    | none => Bool.false
  | .error _ => Bool.false

#guard match Modules.expand genericJubjubScalarCellRegistry
    `genericJubjubScalarCellRoot [] with
  | .ok expansion =>
    match expansion.contractPlan expansion.root genericJubjubScalarCellRequest.constructorInputs with
    | .ok _ => Bool.true
    | .error _ => Bool.false
  | .error _ => Bool.false

def genericJubjubPointCellRoot : Definition := {
  imports := [{
    viewName := "point"
    target := `genericJubjubScalarCellModule
    arguments := [.typeValue (.scalar .jubjubPoint)]
    selections := [
      {sourceName := "value", localName := "value"},
      {sourceName := "read", localName := "read"},
      {sourceName := "update", localName := "update"}
    ]
  }]
  exports := [
    {name := "value", target := .importedMember "point" "value"},
    {name := "read", target := .importedMember "point" "read"},
    {name := "update", target := .importedMember "point" "update"}
  ]
}

noctium_module from genericJubjubPointCellRoot

def genericJubjubPointCellRequest : Request := {
  sourceName := `genericJubjubPointCellRoot
  arguments := []
  constructorInputs := [{
    state := .importedMember "point" "value"
    parameterName := "initial"
  }]
}

noctium_module_contract GenericJubjubPointCell from genericJubjubPointCellRequest

#guard match GenericJubjubPointCell.constructor with
  | some constr =>
    constr.parameters.map (fun parameter => (parameter.name, parameter.type)) ==
      [("initial", .scalar .jubjubPoint)] &&
    constr.initializers.map (fun initializer => initializer.type) ==
      [.scalar .jubjubPoint]
  | none => Bool.false

private def genericJubjubPointCellReturnType (entryName : String) : _root_.Bool :=
  match GenericJubjubPointCell.entrypoints.find? (·.name == entryName) with
  | some operation =>
    match operation.returns with
    | [returned] => returned.name == "result" && returned.ty == .jubjubPoint
    | _ => Bool.false
  | none => Bool.false

#guard genericJubjubPointCellReturnType "read" &&
  genericJubjubPointCellReturnType "update"

private def genericJubjubPointCellRegistry : Registry := {
  modules := [
    {sourceName := `genericJubjubScalarCellModule, definition := genericJubjubScalarCellModule},
    {sourceName := `genericJubjubPointCellRoot, definition := genericJubjubPointCellRoot}
  ]
}

#guard match Modules.expand genericJubjubPointCellRegistry
    `genericJubjubPointCellRoot [] with
  | .ok expansion =>
    match expansion.contractPlan expansion.root genericJubjubPointCellRequest.constructorInputs with
    | .ok _ => Bool.true
    | .error _ => Bool.false
  | .error _ => Bool.false

#guard match Modules.expand genericJubjubScalarDefaultRegistry
    `genericJubjubScalarCellModule [.type (.scalar .jubjubScalar)] with
  | .ok expansion =>
    match expansion.contractPlan expansion.root
        genericJubjubScalarDefaultRequest.constructorInputs with
    | .ok plan => plan.constructor?.isNone
    | .error _ => Bool.false
  | .error _ => Bool.false
