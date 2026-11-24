import Noctium.Frontend
import Noctium.Modules

open Noctium
open Noctium.Helpers.Specialization
open Noctium.Modules
open scoped Noctium

private def genericRecordMapReceiptEnvironment : Types.CompositeEnv := {
  structures := [{
    id := "GenericRecordMap.Receipt"
    fields := [
      {name := "amount", type := .scalar .native},
      {name := "active", type := .scalar .bool}
    ]
  }]
}

def genericRecordMapPutProgram : Program := {
  declarations := [{
    id := ⟨0, 0⟩
    name := "put"
    parameters := [⟨"K", .type⟩, ⟨"V", .type⟩]
    values := [
      ("enabled", .bool),
      ("key", .parameter "K"),
      ("next", .parameter "V")
    ]
    result := .unit
    body := [.return]
  }]
  exports := [{
    name := "put"
    target := ⟨0, 0⟩
    inputs := [
      {name := "enabled", type := .bool, visibility := .private},
      {name := "key", type := .parameter "K", visibility := .private},
      {name := "next", type := .parameter "V", visibility := .private}
    ]
  }]
}

def genericRecordMapLookupProgram : Program := {
  declarations := [{
    id := ⟨0, 0⟩
    name := "lookup"
    parameters := [⟨"K", .type⟩, ⟨"V", .type⟩]
    values := [("key", .parameter "K")]
    result := .unit
    body := [.return]
  }]
  exports := [{
    name := "lookup"
    target := ⟨0, 0⟩
    inputs := [{name := "key", type := .parameter "K", visibility := .private}]
  }]
}

def genericRecordMapModule : Definition := {
  parameters := [⟨"K", .type⟩, ⟨"V", .type⟩]
  members := [
    {
      id := 0
      name := "receipts"
      kind := .state
      visibility := .«public»
      stateSchema? := some (.map (.parameter "K") (.parameter "V"))
    },
    {id := 1, name := "putCircuit", kind := .circuit, sourceExport? := some {
      program := `genericRecordMapPutProgram
      exportName := "put"
      arguments := [.typeParameter "K", .typeParameter "V"]
    }},
    {id := 2, name := "lookupCircuit", kind := .circuit, sourceExport? := some {
      program := `genericRecordMapLookupProgram
      exportName := "lookup"
      arguments := [.typeParameter "K", .typeParameter "V"]
    }},
    {id := 3, name := "put", kind := .entrypoint, visibility := .«public»},
    {id := 4, name := "lookup", kind := .entrypoint, visibility := .«public»}
  ]
  entrypoints := [
    {
      «member» := 3
      name := "put"
      circuit := .localMember 1
      callInputs := ["enabled", "key"]
      effects := [{
        effect := .writeMapInput (.localMember 0)
          (.mk .native (.disclose {} (.ref "key" : Expr .native))) "next"
          (disclosed := Bool.true)
        guard := some (.disclose {} (.ref "enabled" : Expr .bool))
      }]
    },
    {
      «member» := 4
      name := "lookup"
      circuit := .localMember 2
      callInputs := ["key"]
      mapReturns := [{
        name := "result"
        state := .localMember 0
        key := .mk .native (.disclose {} (.ref "key" : Expr .native))
      }]
    }
  ]
  exports := [
    {name := "receipts", target := .localMember 0},
    {name := "put", target := .localMember 3},
    {name := "lookup", target := .localMember 4}
  ]
}

noctium_module from genericRecordMapModule

def genericRecordMapRoot : Definition := {
  imports := [{
    viewName := "receiptMap"
    target := `genericRecordMapModule
    arguments := [
      .typeValue (.scalar .native),
      .checkedTypeValue (.structure "GenericRecordMap.Receipt")
        genericRecordMapReceiptEnvironment
    ]
    selections := [
      {sourceName := "receipts", localName := "receipts"},
      {sourceName := "put", localName := "put"},
      {sourceName := "lookup", localName := "lookup"}
    ]
  }]
  exports := [
    {name := "receipts", target := .importedMember "receiptMap" "receipts"},
    {name := "put", target := .importedMember "receiptMap" "put"},
    {name := "lookup", target := .importedMember "receiptMap" "lookup"}
  ]
}

noctium_module from genericRecordMapRoot

def genericRecordMapRequest : Request := {
  sourceName := `genericRecordMapRoot
  arguments := []
}

noctium_module_contract GenericRecordMap from genericRecordMapRequest
