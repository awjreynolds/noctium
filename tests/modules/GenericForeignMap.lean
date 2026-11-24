import Noctium.Frontend
import Noctium.Modules

open Noctium
open Noctium.Helpers.Specialization
open Noctium.Modules
open scoped Noctium

def genericForeignMapInsertProgram : Program := {
  declarations := [{
    id := ⟨0, 0⟩
    name := "insert"
    parameters := [⟨"K", .type⟩, ⟨"V", .type⟩]
    values := [("key", .parameter "K"), ("next", .parameter "V")]
    result := .unit
    body := [.return]
  }]
  exports := [{
    name := "insert"
    target := ⟨0, 0⟩
    inputs := [
      {name := "key", type := .parameter "K", visibility := .private},
      {name := "next", type := .parameter "V", visibility := .private}
    ]
  }]
}

def genericForeignMapReadProgram : Program := {
  declarations := [{
    id := ⟨0, 0⟩
    name := "read"
    parameters := [⟨"K", .type⟩, ⟨"V", .type⟩]
    values := [("key", .parameter "K")]
    result := .unit
    body := [.return]
  }]
  exports := [{
    name := "read"
    target := ⟨0, 0⟩
    inputs := [{name := "key", type := .parameter "K", visibility := .private}]
  }]
}

def genericForeignMapModule : Definition := {
  parameters := [⟨"K", .type⟩, ⟨"V", .type⟩]
  members := [
    {
      id := 0
      name := "values"
      kind := .state
      visibility := .«public»
      stateSchema? := some (.map (.parameter "K") (.parameter "V"))
    },
    {id := 1, name := "insertCircuit", kind := .circuit, sourceExport? := some {
      program := `genericForeignMapInsertProgram
      exportName := "insert"
      arguments := [.typeParameter "K", .typeParameter "V"]
    }},
    {id := 2, name := "readCircuit", kind := .circuit, sourceExport? := some {
      program := `genericForeignMapReadProgram
      exportName := "read"
      arguments := [.typeParameter "K", .typeParameter "V"]
    }},
    {id := 3, name := "insert", kind := .entrypoint, visibility := .«public»},
    {id := 4, name := "read", kind := .entrypoint, visibility := .«public»}
  ]
  entrypoints := [
    {
      «member» := 3
      name := "insert"
      circuit := .localMember 1
      effects := [{
        effect := .writeMapInput (.localMember 0)
          (.argument "key" (disclosed := Bool.true)) "next" (disclosed := Bool.true)
      }]
    },
    {
      «member» := 4
      name := "read"
      circuit := .localMember 2
      mapReturns := [{
        name := "result"
        state := .localMember 0
        key := .argument "key" (disclosed := Bool.true)
      }]
    }
  ]
  exports := [
    {name := "values", target := .localMember 0},
    {name := "insert", target := .localMember 3},
    {name := "read", target := .localMember 4}
  ]
}

noctium_module from genericForeignMapModule

def genericForeignMapRoot : Definition := {
  imports := [
    {
      viewName := "secp"
      target := `genericForeignMapModule
      arguments := [
        .typeValue (.scalar (.foreign (.point .secp256k1))),
        .typeValue (.scalar (.foreign (.base .secp256r1)))
      ]
      selections := [
        {sourceName := "values", localName := "secpValues"},
        {sourceName := "insert", localName := "insertSecpPointToR1Base"},
        {sourceName := "read", localName := "readSecpPointToR1Base"}
      ]
    },
    {
      viewName := "curve"
      target := `genericForeignMapModule
      arguments := [
        .typeValue (.scalar (.foreign (.scalar .curve25519))),
        .typeValue (.scalar (.foreign (.point .curve25519)))
      ]
      selections := [
        {sourceName := "values", localName := "curveValues"},
        {sourceName := "insert", localName := "insertC255ScalarToC255Point"},
        {sourceName := "read", localName := "readC255ScalarToC255Point"}
      ]
    }
  ]
  exports := [
    {name := "secpValues", target := .importedMember "secp" "secpValues"},
    {name := "curveValues", target := .importedMember "curve" "curveValues"},
    {name := "insertSecpPointToR1Base", target := .importedMember "secp" "insertSecpPointToR1Base"},
    {name := "readSecpPointToR1Base", target := .importedMember "secp" "readSecpPointToR1Base"},
    {name := "insertC255ScalarToC255Point", target := .importedMember "curve" "insertC255ScalarToC255Point"},
    {name := "readC255ScalarToC255Point", target := .importedMember "curve" "readC255ScalarToC255Point"}
  ]
}

noctium_module from genericForeignMapRoot

def genericForeignMapRequest : Request := {
  sourceName := `genericForeignMapRoot
  arguments := []
}

noctium_module_contract GenericForeignMap from genericForeignMapRequest

private def genericForeignMapEntry (name : String) : Option Entrypoint :=
  GenericForeignMap.entrypoints.find? (·.name == name)

#guard GenericForeignMap.state.any fun declaration =>
  declaration.kind == .map (.foreign (.point .secp256k1)) (.foreign (.base .secp256r1))

#guard GenericForeignMap.state.any fun declaration =>
  declaration.kind == .map (.foreign (.scalar .curve25519)) (.foreign (.point .curve25519))

#guard match genericForeignMapEntry "insertSecpPointToR1Base" with
  | some operation =>
    operation.callInputs == ["key", "next"] &&
      operation.callInputViews.isEmpty && operation.returns.isEmpty
  | none => Bool.false

#guard match genericForeignMapEntry "readSecpPointToR1Base" with
  | some operation =>
    operation.callInputs == ["key"] && operation.callInputViews.isEmpty &&
      operation.returns.map (fun returned => (returned.name, returned.ty)) ==
        [("result", .foreign (.base .secp256r1))]
  | none => Bool.false

#guard match genericForeignMapEntry "insertC255ScalarToC255Point" with
  | some operation =>
    operation.callInputs == ["key", "next"] &&
      operation.callInputViews.isEmpty && operation.returns.isEmpty
  | none => Bool.false

#guard match genericForeignMapEntry "readC255ScalarToC255Point" with
  | some operation =>
    operation.callInputs == ["key"] && operation.callInputViews.isEmpty &&
      operation.returns.map (fun returned => (returned.name, returned.ty)) ==
        [("result", .foreign (.point .curve25519))]
  | none => Bool.false
