import Noctium.Backend.Impact
import Noctium.Compiler
import Noctium.Frontend

open Lean
open scoped Noctium
open Noctium

noctium_circuit setInspectionInputs where
  public key : Native
end

noctium_contract SealedRootSetConstructor where
  sealed set registered : Native
  sealed set emptySet : Native

  constructor(key : Native) where
    insert registered[disclose(key)]
    insert registered[disclose(key)]
  end

  entry inspect uses setInspectionInputs where
    member registered[key] as presentValue
    size registered as setSize
    isEmpty emptySet as neighborIsEmpty
    return present : Bool := presentValue
    return size : UInt 64 := setSize
    return neighborEmpty : Bool := neighborIsEmpty
  end
end

noctium_contract OrdinaryRootSetConstructor where
  set registered : Native

  constructor(key : Native) where
    insert registered[key]
  end
end

noctium_contract EmptySealedRootSet where
  sealed set registered : Native
end

private def inspectEntry : Entrypoint :=
  (SealedRootSetConstructor.entrypoints.find? (·.name == "inspect")).getD
    {name := "missing", circuit := {name := "missing"}}

private def constructorPlan : Except String Json := do
  let plan ← (Backend.Impact.lower SealedRootSetConstructor.state inspectEntry).mapError
    (·.message)
  let artifact := Compiler.nativePlanJson TargetProfile.selected321
    `SealedRootSetConstructor SealedRootSetConstructor.state
    SealedRootSetConstructor.constructor inspectEntry plan
  artifact.getObjVal? "constructor"

private def jsonSetName (value : Json) : String :=
  ((value.getObjVal? "name").toOption.bind fun field => field.getStr?.toOption).getD ""

private def hasIndexedJsonField (values : Array Json) (index : Nat) (field : String) : _root_.Bool :=
  match values[index]? with
  | some value => (value.getObjVal? field).isOk
  | none => _root_.Bool.false

#guard (SealedRootSetConstructor.validate Capabilities.source).isOk
#guard (OrdinaryRootSetConstructor.validate Capabilities.source).isOk
#guard (EmptySealedRootSet.validate Capabilities.source).isOk
#guard (inspectEntry.validate Capabilities.source SealedRootSetConstructor.state).isOk

#guard match SealedRootSetConstructor.state with
  | [registered, emptySet] =>
      registered.kind == .tree (.set .native) && registered.sealed &&
      emptySet.kind == .tree (.set .native) && emptySet.sealed
  | _ => _root_.Bool.false

#guard match SealedRootSetConstructor.constructor with
  | some ctor =>
      match ctor.setInserts with
      | [{name := "registered", key := .mk .native (.disclose _ (.ref "key"))},
         {name := "registered", key := .mk .native (.disclose _ (.ref "key"))}] => _root_.Bool.true
      | _ => _root_.Bool.false
  | none => _root_.Bool.false

#guard match constructorPlan with
  | .ok ctor =>
      let inserts := (ctor.getObjValD "setInserts").getArr?.toOption.getD #[]
      inserts.size == 2 && inserts.toList.map jsonSetName == ["registered", "registered"] &&
        hasIndexedJsonField inserts 0 "key" && hasIndexedJsonField inserts 1 "key"
  | .error _ => _root_.Bool.false

private def sealedSetWriteRejected : _root_.Bool :=
  let candidate := {inspectEntry with
    effects := [.setInsert "registered" [.mk .native (.ref "key")]]
    effectGuards := [none]}
  match candidate.validate Capabilities.source SealedRootSetConstructor.state with
  | .error diagnostic =>
      diagnostic.message == "sealed state 'registered' cannot be written by an entrypoint"
  | .ok _ => _root_.Bool.false

#guard sealedSetWriteRejected

private def wrongSetKey : Noctium.Constructor := {
  setInserts := [{name := "registered", key := .mk .bool (.bool _root_.Bool.true)}]
}

private def wrongSetKeyContract : Noctium.Contract := {
  name := "WrongSetKey",
  state := SealedRootSetConstructor.state,
  «constructor» := some wrongSetKey
}

private def wrongSetKeyRejected : _root_.Bool :=
  match wrongSetKeyContract.validate Capabilities.source with
  | .error diagnostic => diagnostic.message == "constructor Set key type mismatch for 'registered'"
  | .ok _ => _root_.Bool.false

#guard wrongSetKeyRejected

private def tooManyConstructorActions : Noctium.Constructor := {
  mapInserts := List.replicate 16 {
    state := "unused",
    key := .mk .native (.native 0),
    valueType := .native,
    value := .native 0
  },
  counterIncrements := List.replicate 16 {
    state := "unused",
    amount := .uint (2 ^ 32 - 1) 1
  },
  listPushes := List.replicate 16 {
    state := "unused",
    valueType := .native,
    value := .native 0
  },
  setInserts := List.replicate 17 {
    name := "unused",
    key := .mk .native (.native 0)
  }
}

private def tooManyActionsContract : Noctium.Contract := {
  name := "TooManySetActions",
  «constructor» := some tooManyConstructorActions
}

#guard match tooManyActionsContract.validate Capabilities.source with
  | .error diagnostic =>
      diagnostic.message == "constructor collection action limit exceeded"
  | .ok _ => _root_.Bool.false
