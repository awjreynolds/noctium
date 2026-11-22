import Noctium.Backend.Impact
import Noctium.Compiler
import Noctium.Frontend

open Lean
open scoped Noctium
open Noctium

noctium_circuit sealedCollectionReads where
end

noctium_contract SealedCounterListConstructor where
  sealed counter total
  sealed list items : Native

  constructor(amount : UInt 16, first : Native) where
    increment total by 70000
    increment total by amount
    pushFront items := first
    pushFront items := 42
  end

  entry inspect uses sealedCollectionReads where
    read total as currentAmount
    length items as currentLength
    head items as currentHead
    return amountRead : UInt 64 := currentAmount
    return lengthRead : UInt 64 := currentLength
    return headRead : Native := currentHead
  end
end

noctium_contract DefaultSealedCollections where
  sealed counter emptyCounter
  sealed list emptyItems : Native
end

private def inspectedEntry : Entrypoint :=
  (SealedCounterListConstructor.entrypoints.find? (·.name == "inspect")).getD
    {name := "missing", circuit := {name := "missing"}}

private def constructorPlan : Except String Json := do
  let plan ← (Backend.Impact.lower SealedCounterListConstructor.state inspectedEntry).mapError
    (·.message)
  let artifact := Compiler.nativePlanJson TargetProfile.selected321
    `SealedCounterListConstructor SealedCounterListConstructor.state
    SealedCounterListConstructor.constructor inspectedEntry plan
  artifact.getObjVal? "constructor"

private def jsonStateName (value : Json) : String :=
  ((value.getObjVal? "state").toOption.bind fun field => field.getStr?.toOption).getD ""

private def hasIndexedJsonField (values : Array Json) (index : Nat) (field : String) : _root_.Bool :=
  match values[index]? with
  | some value => (value.getObjVal? field).isOk
  | none => _root_.Bool.false

#guard (SealedCounterListConstructor.validate Capabilities.source).isOk
#guard (DefaultSealedCollections.validate Capabilities.source).isOk
#guard (inspectedEntry.validate Capabilities.source SealedCounterListConstructor.state).isOk
#guard inspectedEntry.effects.any (fun effect => match effect with
  | .counterRead "total" .. => _root_.Bool.true
  | _ => _root_.Bool.false)
#guard inspectedEntry.effects.any (fun effect => match effect with
  | .listHead "items" .. => _root_.Bool.true
  | _ => _root_.Bool.false)
#guard inspectedEntry.effects.any (fun effect => match effect with
  | .listLength "items" .. => _root_.Bool.true
  | _ => _root_.Bool.false)

#guard match SealedCounterListConstructor.constructor with
  | some ctor =>
      let countersInOrder := match ctor.counterIncrements with
        | [{state := "total", amount := first}, {state := "total", amount := second}] =>
            let immediate := match first with
              | .uint _ 70000 => _root_.Bool.true
              | _ => _root_.Bool.false
            let parameter := match second with
              | .cast _ (.ref "amount") => _root_.Bool.true
              | _ => _root_.Bool.false
            immediate && parameter
        | _ => _root_.Bool.false
      let listsInOrder := match ctor.listPushes with
        | [{state := "items", valueType := .native, value := .ref "first"},
           {state := "items", value := .native 42, ..}] => _root_.Bool.true
        | _ => _root_.Bool.false
      countersInOrder && listsInOrder
  | none => _root_.Bool.false

#guard match constructorPlan with
  | .ok ctor =>
      let counters := (ctor.getObjValD "counterIncrements").getArr?.toOption.getD #[]
      let lists := (ctor.getObjValD "listPushes").getArr?.toOption.getD #[]
      counters.size == 2 && lists.size == 2 &&
        counters.toList.map jsonStateName == ["total", "total"] &&
        lists.toList.map jsonStateName == ["items", "items"] &&
        hasIndexedJsonField counters 0 "amount" && hasIndexedJsonField lists 0 "value"
  | .error _ => _root_.Bool.false

private def sealedWriteRejected (effect : Effect) : _root_.Bool :=
  let candidate := {inspectedEntry with effects := [effect], effectGuards := [none]}
  match candidate.validate Capabilities.source SealedCounterListConstructor.state with
  | .error diagnostic =>
      diagnostic.message.startsWith "sealed state '" &&
        diagnostic.message.endsWith "cannot be written by an entrypoint"
  | .ok _ => _root_.Bool.false

#guard [
  Effect.counterAdjust "total" [] _root_.Bool.false (.uint (2 ^ 32 - 1) 1),
  Effect.counterReset "total" [],
  Effect.listPushFront "items" [] (.scalar .native) [.mk .native (.native 1)],
  Effect.listReset "items" []
].all sealedWriteRejected

private def tooManyConstructorActions : Noctium.Constructor := {
  mapInserts := List.replicate 20 {
    state := "unused",
    key := .mk .native (.native 0),
    valueType := .native,
    value := .native 0
  },
  counterIncrements := List.replicate 20 {
    state := "unused",
    amount := .uint (2 ^ 32 - 1) 1
  },
  listPushes := List.replicate 25 {
    state := "unused",
    valueType := .native,
    value := .native 0
  }
}

private def tooManyActionsContract : Noctium.Contract := {
  name := "TooManyActions",
  «constructor» := some tooManyConstructorActions
}

#guard match tooManyActionsContract.validate Capabilities.source with
  | .error diagnostic =>
      diagnostic.message == "constructor collection action limit exceeded"
  | .ok _ => _root_.Bool.false
