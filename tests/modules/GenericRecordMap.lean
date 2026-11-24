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

private def genericRecordMapOtherReceiptEnvironment : Types.CompositeEnv := {
  structures := [{
    id := "GenericRecordMap.OtherReceipt"
    fields := [
      {name := "amount", type := .scalar .native},
      {name := "active", type := .scalar .bool}
    ]
  }]
}

private def genericRecordMapKeyEnvironment : Types.CompositeEnv := {
  structures := [{
    id := "GenericRecordMap.Key"
    fields := [
      {name := "active", type := .scalar .bool},
      {name := "epoch", type := .scalar (.uint 65535)}
    ]
  }]
}

private def genericRecordMapOtherKeyEnvironment : Types.CompositeEnv := {
  structures := [{
    id := "GenericRecordMap.OtherKey"
    fields := [
      {name := "active", type := .scalar .bool},
      {name := "epoch", type := .scalar (.uint 65535)}
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
      callInputs := ["enabled"]
      effects := [{
        effect := .writeMapInput (.localMember 0)
          (.argument "key" (disclosed := Bool.true)) "next"
          (disclosed := Bool.true)
        guard := some (.disclose {} (.ref "enabled" : Expr .bool))
      }]
    },
    {
      «member» := 4
      name := "lookup"
      circuit := .localMember 2
      mapReturns := [{
        name := "result"
        state := .localMember 0
        key := .argument "key" (disclosed := Bool.true)
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
  imports := [
    {
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
    },
    {
      viewName := "receiptBytesMap"
      target := `genericRecordMapModule
      arguments := [
        .typeValue (.bytes 32),
        .checkedTypeValue (.structure "GenericRecordMap.Receipt")
          genericRecordMapReceiptEnvironment
      ]
      selections := [
        {sourceName := "receipts", localName := "receipts"},
        {sourceName := "put", localName := "putBytes"},
        {sourceName := "lookup", localName := "lookupBytes"}
      ]
    },
    {
      viewName := "recordKeyMap"
      target := `genericRecordMapModule
      arguments := [
        .checkedTypeValue (.structure "GenericRecordMap.Key")
          genericRecordMapKeyEnvironment,
        .typeValue (.scalar (.uint 65535))
      ]
      selections := [
        {sourceName := "receipts", localName := "recordKeyValues"},
        {sourceName := "put", localName := "putRecordKey"},
        {sourceName := "lookup", localName := "lookupRecordKey"}
      ]
    },
    {
      viewName := "recordKeyReceiptMap"
      target := `genericRecordMapModule
      arguments := [
        .checkedTypeValue (.structure "GenericRecordMap.Key")
          genericRecordMapKeyEnvironment,
        .checkedTypeValue (.structure "GenericRecordMap.Receipt")
          genericRecordMapReceiptEnvironment
      ]
      selections := [
        {sourceName := "receipts", localName := "recordKeyReceipts"},
        {sourceName := "put", localName := "putRecordKeyReceipt"},
        {sourceName := "lookup", localName := "lookupRecordKeyReceipt"}
      ]
    }
  ]
  exports := [
    {name := "receipts", target := .importedMember "receiptMap" "receipts"},
    {name := "receiptsBytes", target := .importedMember "receiptBytesMap" "receipts"},
    {name := "put", target := .importedMember "receiptMap" "put"},
    {name := "lookup", target := .importedMember "receiptMap" "lookup"},
    {name := "putBytes", target := .importedMember "receiptBytesMap" "putBytes"},
    {name := "lookupBytes", target := .importedMember "receiptBytesMap" "lookupBytes"},
    {name := "recordKeyValues", target := .importedMember "recordKeyMap" "recordKeyValues"},
    {name := "putRecordKey", target := .importedMember "recordKeyMap" "putRecordKey"},
    {name := "lookupRecordKey", target := .importedMember "recordKeyMap" "lookupRecordKey"},
    {name := "recordKeyReceipts", target := .importedMember "recordKeyReceiptMap" "recordKeyReceipts"},
    {name := "putRecordKeyReceipt", target := .importedMember "recordKeyReceiptMap" "putRecordKeyReceipt"},
    {name := "lookupRecordKeyReceipt", target := .importedMember "recordKeyReceiptMap" "lookupRecordKeyReceipt"}
  ]
}

noctium_module from genericRecordMapRoot

def genericRecordMapWrongKeyModule : Definition := {
  genericRecordMapModule with
  members := genericRecordMapModule.members.map fun item =>
    if item.id == 1 then
      {item with sourceExport? := some {
        program := `genericRecordMapPutProgram
        exportName := "put"
        arguments := [
          .checkedTypeValue (.structure "GenericRecordMap.OtherKey")
            genericRecordMapOtherKeyEnvironment,
          .checkedTypeValue (.structure "GenericRecordMap.Receipt")
            genericRecordMapReceiptEnvironment
        ]
      }}
    else item
}

noctium_module from genericRecordMapWrongKeyModule

def genericRecordMapWrongKeyRoot : Definition := {
  genericRecordMapRoot with
  imports := genericRecordMapRoot.imports.map fun item =>
    if item.viewName == "recordKeyReceiptMap" then
      {item with target := `genericRecordMapWrongKeyModule}
    else item
}

noctium_module from genericRecordMapWrongKeyRoot

def genericRecordMapWrongValueModule : Definition := {
  genericRecordMapModule with
  members := genericRecordMapModule.members.map fun item =>
    if item.id == 1 then
      {item with sourceExport? := some {
        program := `genericRecordMapPutProgram
        exportName := "put"
        arguments := [
          .checkedTypeValue (.structure "GenericRecordMap.Key")
            genericRecordMapKeyEnvironment,
          .checkedTypeValue (.structure "GenericRecordMap.OtherReceipt")
            genericRecordMapOtherReceiptEnvironment
        ]
      }}
    else item
}

noctium_module from genericRecordMapWrongValueModule

def genericRecordMapWrongValueRoot : Definition := {
  genericRecordMapRoot with
  imports := genericRecordMapRoot.imports.map fun item =>
    if item.viewName == "recordKeyReceiptMap" then
      {item with target := `genericRecordMapWrongValueModule}
    else item
}

noctium_module from genericRecordMapWrongValueRoot

def genericRecordMapRequest : Request := {
  sourceName := `genericRecordMapRoot
  arguments := []
}

noctium_module_contract GenericRecordMap from genericRecordMapRequest

private def genericRecordMapStateHasKeyType (keyType : Ty) : _root_.Bool :=
  GenericRecordMap.state.any fun declared =>
    match declared.kind with
    | .tree (.map actualKey (.composite environment type)) =>
      actualKey == keyType && environment == genericRecordMapReceiptEnvironment &&
        type == .structure "GenericRecordMap.Receipt"
    | _ => _root_.Bool.false

private def genericRecordMapEntry (name : String) : Option Entrypoint :=
  GenericRecordMap.entrypoints.find? (·.name == name)

private def genericRecordMapHasHeader (name : String) (expected : List String) : _root_.Bool :=
  match genericRecordMapEntry name with
  | some operation => operation.callInputs == expected
  | none => _root_.Bool.false

private def genericRecordMapHasInputView (entryName viewName : String)
    (fields : List (String × Ty)) : _root_.Bool :=
  match genericRecordMapEntry entryName with
  | some operation => operation.callInputViews.any fun view =>
      view.name == viewName && view.fields == fields
  | none => _root_.Bool.false

private def genericRecordMapBytesKeyFields : List (String × Ty) :=
  (List.range 32).map fun index => (s!"key.{index}", .uint 255)

private def genericRecordMapReceiptInputFields : List (String × Ty) := [
  ("next.amount", .native), ("next.active", .bool)
]

private def genericRecordMapKeyInputFields : List (String × Ty) := [
  ("key.active", .bool), ("key.epoch", .uint 65535)
]

private def genericRecordMapRegistry : Registry := {
  modules := [
    {sourceName := `genericRecordMapModule, definition := genericRecordMapModule},
    {sourceName := `genericRecordMapRoot, definition := genericRecordMapRoot}
  ]
}

private def genericRecordMapWrongKeySpecialization : Except Diagnostic SpecializedModule := do
  let request : Request := {sourceName := `genericRecordMapWrongKeyRoot, arguments := []}
  let registry : Registry := {
    modules := genericRecordMapRegistry.modules ++ [
      {sourceName := `genericRecordMapWrongKeyModule,
        definition := genericRecordMapWrongKeyModule},
      {sourceName := `genericRecordMapWrongKeyRoot,
        definition := genericRecordMapWrongKeyRoot}
    ]
  }
  let expansion ← Modules.expand registry request.sourceName request.arguments
  let plan ← expansion.contractPlan expansion.root request.constructorInputs
  plan.specializeWithSources {} [
    (`genericRecordMapPutProgram, genericRecordMapPutProgram),
    (`genericRecordMapLookupProgram, genericRecordMapLookupProgram)
  ]

private def genericRecordMapHasRecordKeyState : _root_.Bool :=
  GenericRecordMap.state.any fun declared =>
    match declared.kind with
    | .tree (.recordMapKey environment type (.uint 65535)) =>
      environment == genericRecordMapKeyEnvironment &&
        type == .structure "GenericRecordMap.Key"
    | _ => _root_.Bool.false

private def genericRecordMapHasRecordKeyReceiptState : _root_.Bool :=
  GenericRecordMap.state.any fun declared =>
    match declared.kind with
    | .tree (.recordMapComposite keyEnvironment keyType valueEnvironment valueType) =>
      keyEnvironment == genericRecordMapKeyEnvironment &&
        keyType == .structure "GenericRecordMap.Key" &&
        valueEnvironment == genericRecordMapReceiptEnvironment &&
        valueType == .structure "GenericRecordMap.Receipt"
    | _ => _root_.Bool.false

private def genericRecordMapWrongValueSpecialization : Except Diagnostic SpecializedModule := do
  let request : Request := {sourceName := `genericRecordMapWrongValueRoot, arguments := []}
  let registry : Registry := {
    modules := genericRecordMapRegistry.modules ++ [
      {sourceName := `genericRecordMapWrongValueModule,
        definition := genericRecordMapWrongValueModule},
      {sourceName := `genericRecordMapWrongValueRoot,
        definition := genericRecordMapWrongValueRoot}
    ]
  }
  let expansion ← Modules.expand registry request.sourceName request.arguments
  let plan ← expansion.contractPlan expansion.root request.constructorInputs
  plan.specializeWithSources {} [
    (`genericRecordMapPutProgram, genericRecordMapPutProgram),
    (`genericRecordMapLookupProgram, genericRecordMapLookupProgram)
  ]

#guard genericRecordMapStateHasKeyType .native &&
  genericRecordMapStateHasKeyType (.bytes 32) &&
  genericRecordMapHasRecordKeyState &&
  genericRecordMapHasRecordKeyReceiptState

#guard genericRecordMapHasHeader "put" ["enabled", "key", "next.amount", "next.active"] &&
  genericRecordMapHasHeader "lookup" ["key"] &&
  genericRecordMapHasHeader "putBytes"
    (["enabled"] ++ genericRecordMapBytesKeyFields.map Prod.fst ++
      genericRecordMapReceiptInputFields.map Prod.fst) &&
  genericRecordMapHasHeader "lookupBytes" (genericRecordMapBytesKeyFields.map Prod.fst) &&
  genericRecordMapHasHeader "putRecordKey"
    (["enabled"] ++ genericRecordMapKeyInputFields.map Prod.fst ++ ["next"]) &&
  genericRecordMapHasHeader "lookupRecordKey" (genericRecordMapKeyInputFields.map Prod.fst) &&
  genericRecordMapHasHeader "putRecordKeyReceipt"
    (["enabled"] ++ genericRecordMapKeyInputFields.map Prod.fst ++
      genericRecordMapReceiptInputFields.map Prod.fst) &&
  genericRecordMapHasHeader "lookupRecordKeyReceipt"
    (genericRecordMapKeyInputFields.map Prod.fst)

#guard genericRecordMapHasInputView "put" "next" genericRecordMapReceiptInputFields &&
  genericRecordMapHasInputView "putBytes" "next" genericRecordMapReceiptInputFields &&
  genericRecordMapHasInputView "putBytes" "key" genericRecordMapBytesKeyFields &&
  genericRecordMapHasInputView "lookupBytes" "key" genericRecordMapBytesKeyFields &&
  genericRecordMapHasInputView "putRecordKey" "key" genericRecordMapKeyInputFields &&
  genericRecordMapHasInputView "lookupRecordKey" "key" genericRecordMapKeyInputFields &&
  genericRecordMapHasInputView "putRecordKeyReceipt" "key" genericRecordMapKeyInputFields &&
  genericRecordMapHasInputView "putRecordKeyReceipt" "next" genericRecordMapReceiptInputFields &&
  genericRecordMapHasInputView "lookupRecordKeyReceipt" "key" genericRecordMapKeyInputFields

#guard match genericRecordMapEntry "lookupRecordKey" with
  | some operation => operation.returns.map (fun returned => (returned.name, returned.ty)) ==
      [("result", .uint 65535)]
  | none => _root_.Bool.false

#guard match genericRecordMapEntry "putRecordKey" with
  | some operation =>
    operation.effects.length == 1 &&
      (match operation.effectGuards with | [some _] => _root_.Bool.true | _ => _root_.Bool.false)
  | none => _root_.Bool.false

#guard match genericRecordMapEntry "lookupRecordKeyReceipt" with
  | some operation => operation.returnViews.any fun view =>
      view.name == "result" && view.environment == genericRecordMapReceiptEnvironment &&
        view.type == .structure "GenericRecordMap.Receipt" && view.fields.length == 2
  | none => _root_.Bool.false

#guard match genericRecordMapWrongKeySpecialization with
  | .error diagnostic =>
    diagnostic.message.contains "module record Map key input 'key' does not match the checked Map key layout"
  | .ok _ => _root_.Bool.false

#guard match genericRecordMapWrongValueSpecialization with
  | .error diagnostic =>
    diagnostic.message.contains "module record Map input 'next' does not match the checked Map layout"
  | .ok _ => _root_.Bool.false
