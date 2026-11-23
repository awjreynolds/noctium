import Noctium.Backend.Impact
import Noctium.Compiler
import Noctium.Frontend

open Lean
open scoped Noctium
open Noctium

noctium_circuit guardedConstructorListCounterRead where
end

noctium_contract GuardedConstructorListCounter where
  sealed counter total
  sealed list items : Native

  constructor(enabled : Bool, amount : UInt 16, first : Native) where
    when enabled increment total by amount
    when enabled pushFront items := first
  end

  entry readBack uses guardedConstructorListCounterRead where
    read total as currentAmount
    length items as currentLength
    headOrDefault items as (headPresent, headValue)
    return amountRead : UInt 64 := currentAmount
    return lengthRead : UInt 64 := currentLength
    returnMaybe head as (headPresent, headValue)
  end
end

private def readBackEntry : Entrypoint :=
  (GuardedConstructorListCounter.entrypoints.find? (·.name == "readBack")).getD
    {name := "missing", circuit := {name := "missing"}}

private def constructorMetadata (ctor : Noctium.Constructor) : Except String Json := do
  let plan ← (Backend.Impact.lower GuardedConstructorListCounter.state readBackEntry).mapError
    (·.message)
  let artifact := Compiler.nativePlanJson TargetProfile.selected321
    `GuardedConstructorListCounter GuardedConstructorListCounter.state (some ctor)
    readBackEntry plan
  artifact.getObjVal? "constructor"

private def constructorActions (metadata : Json) (name : String) : Array Json :=
  ((metadata.getObjVal? name).toOption.getD Json.null).getArr?.toOption.getD #[]

#guard (GuardedConstructorListCounter.validate Capabilities.source).isOk
#guard (readBackEntry.validate Capabilities.source GuardedConstructorListCounter.state).isOk

#guard match GuardedConstructorListCounter.constructor with
  | some ctor =>
      let counterCheck := match ctor.counterIncrements with
        | [{state := "total", amount := .cast _ (.ref "amount"),
            guard := some (.ref "enabled")}] => _root_.Bool.true
        | _ => _root_.Bool.false
      let listCheck := match ctor.listPushes with
        | [{state := "items", valueType := .native, value := .ref "first",
            guard := some (.ref "enabled")}] => _root_.Bool.true
        | _ => _root_.Bool.false
      counterCheck && listCheck
  | none => _root_.Bool.false

#guard match GuardedConstructorListCounter.constructor with
  | some ctor =>
      match constructorMetadata ctor with
      | .ok metadata =>
          let counters := constructorActions metadata "counterIncrements"
          let lists := constructorActions metadata "listPushes"
          counters.size == 1 && lists.size == 1 &&
            (counters[0]?.getD Json.null).getObjValD "guard" ==
              NativeExpression.toJson (.ref "enabled" : Expr .bool) &&
            (lists[0]?.getD Json.null).getObjValD "guard" ==
              NativeExpression.toJson (.ref "enabled" : Expr .bool)
      | .error _ => _root_.Bool.false
  | none => _root_.Bool.false

#guard match GuardedConstructorListCounter.constructor with
  | some ctor =>
      let unguarded := {ctor with
        counterIncrements := ctor.counterIncrements.map fun action =>
          {action with guard := none}
        listPushes := ctor.listPushes.map fun listPush => {listPush with guard := none}}
      match constructorMetadata unguarded with
      | .ok metadata =>
          let counters := constructorActions metadata "counterIncrements"
          let lists := constructorActions metadata "listPushes"
          counters.size == 1 && lists.size == 1 &&
            !((counters[0]?.getD Json.null).getObjVal? "guard").isOk &&
            !((lists[0]?.getD Json.null).getObjVal? "guard").isOk
      | .error _ => _root_.Bool.false
  | none => _root_.Bool.false
