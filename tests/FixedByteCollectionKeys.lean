import Noctium.Frontend
import Noctium.Backend.Impact
import Noctium.Backend.Zkir
import Noctium.Modules

open scoped Noctium
open Noctium
open Noctium.Modules
open Noctium.Helpers.Specialization

noctium_circuit fixedByteCollectionInputs where
  private emptyKey : Bytes 0
  private shortKey : Bytes 1
  private longKey : Bytes 33
  private value : Native
end

noctium_contract FixedByteCollectionKeys where
  map zeroValues : Bytes 0 => Native
  map oneValues : Bytes 1 => Native
  map wideValues : Bytes 33 => Native
  tree nestedGroups : Bytes 0 => Set Bytes 1

  entry exerciseDirect uses fixedByteCollectionInputs where
    insert zeroValues[disclose(emptyKey)] := disclose(value)
    insert oneValues[disclose(shortKey)] := disclose(value)
    insert wideValues[disclose(longKey)] := disclose(value)
    read zeroValues[disclose(emptyKey)] as zeroValue
    read oneValues[disclose(shortKey)] as oneValue
    read wideValues[disclose(longKey)] as wideValue
    member nestedGroups[disclose(emptyKey)] as initialized
    when eq(initialized, false) insertDefault nestedGroups[disclose(emptyKey)]
    insert nestedGroups[disclose(emptyKey)][disclose(shortKey)]
    member nestedGroups[disclose(emptyKey)][disclose(shortKey)] as nestedPresent
    return zeroResult : Native := zeroValue
    return oneResult : Native := oneValue
    return wideResult : Native := wideValue
    return nestedResult : Bool := nestedPresent
  end
end

private def fixedByteCollectionEntry : Entrypoint :=
  (FixedByteCollectionKeys.entrypoints.find? (·.name == "exerciseDirect")).getD
    {name := "missing", circuit := {name := "missing"}}

private def fixedByteCollectionContext : EvalContext :=
  {modulus := Field.modulus, poseidon2 := fun _ _ _ => .error "unused by this fixture"}

private def fixedByteCollectionLongKey : Value :=
  .bytes 33 ((List.range 33).map (· + 1))

#guard (FixedByteCollectionKeys.validate Capabilities.source).isOk
#guard (fixedByteCollectionEntry.validate Capabilities.source FixedByteCollectionKeys.state).isOk
#guard (Backend.Impact.lower FixedByteCollectionKeys.state fixedByteCollectionEntry).isOk
#guard (Backend.Zkir.lowerEntrypoint FixedByteCollectionKeys.state fixedByteCollectionEntry).isOk

#guard match fixedByteCollectionEntry.run fixedByteCollectionContext [
    ("emptyKey", .bytes 0 []), ("shortKey", .bytes 1 [167]),
    ("longKey", fixedByteCollectionLongKey), ("value", .native 71)]
    {maps := [("zeroValues", []), ("oneValues", []), ("wideValues", [])],
      trees := [("nestedGroups", .map [])]} with
  | .ok (outputs, after) =>
    outputs.lookup "zeroResult" == some (.native 71) &&
    outputs.lookup "oneResult" == some (.native 71) &&
    outputs.lookup "wideResult" == some (.native 71) &&
    outputs.lookup "nestedResult" == some (.bool Bool.true) &&
    after.maps.lookup "zeroValues" == some [(.bytes 0 [], .native 71)] &&
    after.maps.lookup "oneValues" == some [(.bytes 1 [167], .native 71)] &&
    after.maps.lookup "wideValues" == some [(fixedByteCollectionLongKey, .native 71)] &&
    after.trees.lookup "nestedGroups" == some
      (.map [(.bytes 0 [], .map [(.bytes 1 [167], .null)])])
  | .error _ => Bool.false

def fixedByteGenericPutProgram : Program := {
  declarations := [{
    id := ⟨0, 0⟩
    name := "put"
    parameters := [⟨"K", .type⟩]
    values := [("enabled", .bool), ("key", .parameter "K"), ("next", .native)]
    result := .unit
    body := [.return]
  }]
  exports := [{
    name := "put"
    target := ⟨0, 0⟩
    inputs := [
      {name := "enabled", type := .bool, visibility := .private},
      {name := "key", type := .parameter "K", visibility := .private},
      {name := "next", type := .native, visibility := .private}
    ]
  }]
}

def fixedByteGenericLookupProgram : Program := {
  declarations := [{
    id := ⟨0, 0⟩
    name := "lookup"
    parameters := [⟨"K", .type⟩]
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

def fixedByteGenericMapModule : Definition := {
  parameters := [⟨"K", .type⟩]
  members := [
    {
      id := 0
      name := "values"
      kind := .state
      visibility := .«public»
      stateSchema? := some (.map (.parameter "K") .native)
    },
    {id := 1, name := "putCircuit", kind := .circuit, sourceExport? := some {
      program := `fixedByteGenericPutProgram
      exportName := "put"
      arguments := [.typeParameter "K"]
    }},
    {id := 2, name := "lookupCircuit", kind := .circuit, sourceExport? := some {
      program := `fixedByteGenericLookupProgram
      exportName := "lookup"
      arguments := [.typeParameter "K"]
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
    {name := "values", target := .localMember 0},
    {name := "put", target := .localMember 3},
    {name := "lookup", target := .localMember 4}
  ]
}

noctium_module from fixedByteGenericMapModule

def fixedByteGenericMapRoot : Definition := {
  imports := [
    {
      viewName := "emptyMap"
      target := `fixedByteGenericMapModule
      arguments := [.typeValue (.bytes 0)]
      selections := [
        {sourceName := "values", localName := "zeroValues"},
        {sourceName := "put", localName := "putZero"},
        {sourceName := "lookup", localName := "lookupZero"}
      ]
    },
    {
      viewName := "shortMap"
      target := `fixedByteGenericMapModule
      arguments := [.typeValue (.bytes 1)]
      selections := [
        {sourceName := "values", localName := "oneValues"},
        {sourceName := "put", localName := "putOne"},
        {sourceName := "lookup", localName := "lookupOne"}
      ]
    },
    {
      viewName := "wideMap"
      target := `fixedByteGenericMapModule
      arguments := [.typeValue (.bytes 33)]
      selections := [
        {sourceName := "values", localName := "wideValues"},
        {sourceName := "put", localName := "putWide"},
        {sourceName := "lookup", localName := "lookupWide"}
      ]
    }
  ]
  exports := [
    {name := "zeroValues", target := .importedMember "emptyMap" "zeroValues"},
    {name := "oneValues", target := .importedMember "shortMap" "oneValues"},
    {name := "wideValues", target := .importedMember "wideMap" "wideValues"},
    {name := "putZero", target := .importedMember "emptyMap" "putZero"},
    {name := "lookupZero", target := .importedMember "emptyMap" "lookupZero"},
    {name := "putOne", target := .importedMember "shortMap" "putOne"},
    {name := "lookupOne", target := .importedMember "shortMap" "lookupOne"},
    {name := "putWide", target := .importedMember "wideMap" "putWide"},
    {name := "lookupWide", target := .importedMember "wideMap" "lookupWide"}
  ]
}

noctium_module from fixedByteGenericMapRoot

def fixedByteGenericMapRequest : Request := {
  sourceName := `fixedByteGenericMapRoot
  arguments := []
}

noctium_module_contract FixedByteGenericCollectionKeys from fixedByteGenericMapRequest

private def fixedByteGenericMapHasKeyType (keyType : Ty) : _root_.Bool :=
  FixedByteGenericCollectionKeys.state.any fun declared =>
    declared.kind == .map keyType .native

private def fixedByteGenericMapInputFields (length : Nat) : List (String × Ty) :=
  (List.range length).map fun index => (s!"key.{index}", .uint 255)

private def fixedByteGenericMapHasView (entryName : String) (length : Nat) : _root_.Bool :=
  match FixedByteGenericCollectionKeys.entrypoints.find? (·.name == entryName) with
  | some operation => operation.callInputViews.any fun view =>
      view.name == "key" && view.fields == fixedByteGenericMapInputFields length
  | none => Bool.false

#guard fixedByteGenericMapHasKeyType (.bytes 0) &&
  fixedByteGenericMapHasKeyType (.bytes 1) &&
  fixedByteGenericMapHasKeyType (.bytes 33)

#guard fixedByteGenericMapHasView "putZero" 0 &&
  fixedByteGenericMapHasView "lookupZero" 0 &&
  fixedByteGenericMapHasView "putOne" 1 &&
  fixedByteGenericMapHasView "lookupOne" 1 &&
  fixedByteGenericMapHasView "putWide" 33 &&
  fixedByteGenericMapHasView "lookupWide" 33

#guard (Backend.Impact.lower FixedByteGenericCollectionKeys.state
    ((FixedByteGenericCollectionKeys.entrypoints.find? (·.name == "putZero")).getD
      {name := "missing", circuit := {name := "missing"}})).isOk
#guard (Backend.Zkir.lowerEntrypoint FixedByteGenericCollectionKeys.state
    ((FixedByteGenericCollectionKeys.entrypoints.find? (·.name == "lookupWide")).getD
      {name := "missing", circuit := {name := "missing"}})).isOk
