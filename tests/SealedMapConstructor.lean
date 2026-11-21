import Noctium.Backend.Impact
import Noctium.Compiler
import Noctium.Frontend
import Noctium.Helpers

open Lean
open scoped Noctium
open Noctium

noctium_circuit sealedMapGetInputs where
  public key : Native
end

noctium_circuit sealedMapTouchInputs where
end

noctium_contract SealedMapConstructor where
  sealed map entries : Native => UInt 64
  sealed map emptyEntries : Native => UInt 64
  cell marker : Native

  constructor(key : Native, value : UInt 64) where
    insert entries[disclose(key)] := disclose(value)
  end

  entry get uses sealedMapGetInputs where
    member entries[key] as present
    read entries[key] as stored
    require eq(present, true)
    return storedValue : UInt 64 := stored
  end

  entry touch uses sealedMapTouchInputs where
    write marker := 37
  end
end

noctium_contract EmptySealedMapConstructor where
  sealed map emptyEntries : Native => UInt 64
  constructor() where
  end

  entry hasEntry uses sealedMapGetInputs where
    member emptyEntries[key] as present
    return hasEntry : Bool := present
  end
end

noctium_contract DefaultOnlySealedMap where
  sealed map emptyEntries : Native => UInt 64
end

noctium_contract OrdinaryMapConstructor where
  map entries : Native => UInt 64
  constructor(key : Native, value : UInt 64) where
    insert entries[disclose(key)] := disclose(value)
  end
end

private def sealedMapGet : Entrypoint :=
  (SealedMapConstructor.entrypoints.find? (·.name == "get")).getD
    {name := "missing", circuit := {name := "missing"}}

private def sealedMapTouch : Entrypoint :=
  (SealedMapConstructor.entrypoints.find? (·.name == "touch")).getD
    {name := "missing", circuit := {name := "missing"}}

private def sealedMapPlanJson (name : String) : Except String Json := do
  let some ep := SealedMapConstructor.entrypoints.find? (·.name == name)
    | throw s!"unknown test entrypoint '{name}'"
  let plan ← (Backend.Impact.lower SealedMapConstructor.state ep).mapError (·.message)
  pure (Compiler.nativePlanJson TargetProfile.selected321 `SealedMapConstructor
    SealedMapConstructor.state SealedMapConstructor.constructor ep plan)

private def emptyMapPlanJson : Except String Json := do
  let some ep := EmptySealedMapConstructor.entrypoints.head?
    | throw "missing empty Map test entrypoint"
  let plan ← (Backend.Impact.lower EmptySealedMapConstructor.state ep).mapError (·.message)
  pure (Compiler.nativePlanJson TargetProfile.selected321 `EmptySealedMapConstructor
    EmptySealedMapConstructor.state EmptySealedMapConstructor.constructor ep plan)

#guard (SealedMapConstructor.validate Capabilities.source).isOk
#guard (EmptySealedMapConstructor.validate Capabilities.source).isOk
#guard (DefaultOnlySealedMap.validate Capabilities.source).isOk
#guard (OrdinaryMapConstructor.validate Capabilities.source).isOk

#guard match SealedMapConstructor.state with
  | [entryState, emptyState, markerState] =>
      let valueMaximum := match entryState.kind with | .map .native (.uint maximum) => maximum | _ => 0
      let emptyMaximum := match emptyState.kind with | .map .native (.uint maximum) => maximum | _ => 0
      valueMaximum == 2 ^ 64 - 1 && emptyMaximum == valueMaximum &&
        entryState.sealed && emptyState.sealed && !markerState.sealed &&
        entryState.name == "entries" && emptyState.name == "emptyEntries" && markerState.name == "marker"
  | _ => _root_.Bool.false

#guard match SealedMapConstructor.constructor with
  | some ctor =>
      match ctor.mapInserts with
      | [{state := "entries", key := .mk .native (.disclose _ (.ref "key")),
          valueType := .uint valueMaximum, value := .disclose _ (.ref "value")}] =>
            valueMaximum == 2 ^ 64 - 1
      | _ => Bool.false
  | none => Bool.false

#guard sealedMapGet.effects.any (fun effect => match effect with
  | .readMap "entries" .. | .readMember "entries" .. => Bool.true
  | _ => Bool.false)
#guard (sealedMapGet.validate Capabilities.source SealedMapConstructor.state).isOk
#guard (sealedMapTouch.validate Capabilities.source SealedMapConstructor.state).isOk

private def rejectSealedMapWrite (effect : Effect) : _root_.Bool :=
  let candidate := {sealedMapGet with effects := [effect], effectGuards := [none]}
  match candidate.validate Capabilities.source SealedMapConstructor.state with
  | .error diagnostic =>
      diagnostic.message == "sealed state 'entries' cannot be written by an entrypoint"
  | .ok _ => Bool.false

private def mapKey : PathKey := .mk .native (.native 1)
private def mapValue : Expr (.uint (2 ^ 64 - 1)) := .uint (2 ^ 64 - 1) 2

#guard [
  Effect.writeMap "entries" .native (.uint (2 ^ 64 - 1)) (.native 1) mapValue,
  Effect.insertPath "entries" [mapKey] (.uint (2 ^ 64 - 1)) mapValue,
  Effect.writePath "entries" [mapKey] (.uint (2 ^ 64 - 1)) mapValue,
  Effect.emptyMapPath "entries" [],
  Effect.removePath "entries" [mapKey]
].all rejectSealedMapWrite

private def sealedMapHelperRead : Helpers.Program := {
  ledger := SealedMapConstructor.state
  declarations := [{
    id := ⟨0, 0⟩,
    name := "get",
    parameters := [⟨"key", .native⟩],
    result := .scalar (.uint (2 ^ 64 - 1)),
    body := [
      .readMember "entries" "present" .native (.uint (2 ^ 64 - 1)) (.ref "key"),
      .readMap "entries" "stored" .native (.uint (2 ^ 64 - 1)) (.ref "key"),
      .return (some (.ref "stored"))]
  }]
  exports := [{name := "get", target := ⟨0, 0⟩, inputs := [
    {name := "key", ty := .native, visibility := .public}]}]
}

private def sealedMapHelperWrite : Helpers.Program := {
  sealedMapHelperRead with
    declarations := [{
      id := ⟨0, 0⟩,
      name := "put",
      parameters := [⟨"key", .native⟩, ⟨"value", .uint (2 ^ 64 - 1)⟩],
      body := [
        .writeMap "entries" .native (.uint (2 ^ 64 - 1)) (.ref "key") (.ref "value"),
        .return none]
    }]
    exports := [{name := "put", target := ⟨0, 0⟩, inputs := [
      {name := "key", ty := .native, visibility := .public},
      {name := "value", ty := .uint (2 ^ 64 - 1), visibility := .public}]}]
}

#guard (Helpers.compileEntrypointFor sealedMapHelperRead "get" SealedMapConstructor.state).isOk
#guard match Helpers.compileEntrypointFor sealedMapHelperWrite "put" SealedMapConstructor.state with
  | .error diagnostic => diagnostic.message == "sealed state 'entries' cannot be written"
  | .ok _ => Bool.false

#guard match sealedMapPlanJson "get" with
  | .ok plan =>
      match plan.getObjVal? "constructor" with
      | .ok ctor =>
          match ctor.getObjVal? "mapInserts" with
          | .ok (.arr #[insertion]) =>
              (insertion.getObjVal? "state" >>= Json.getStr?).toOption == some "entries" &&
                (insertion.getObjVal? "key").isOk && (insertion.getObjVal? "value").isOk
          | _ => Bool.false
      | .error _ => Bool.false
  | .error _ => Bool.false

#guard match emptyMapPlanJson with
  | .ok plan =>
      match plan.getObjVal? "constructor" with
      | .ok ctor => !(ctor.getObjVal? "mapInserts").isOk
      | .error _ => Bool.false
  | .error _ => Bool.false
