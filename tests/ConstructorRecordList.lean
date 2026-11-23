import Noctium.Backend.Impact
import Noctium.Compiler
import Noctium.Frontend

open Lean
open scoped Noctium
open Noctium

noctium_circuit constructorRecordListNoInputs where
end

noctium_contract ConstructorRecordList where
  list history : struct Position {
    owner : Native
    active : Bool
  }

  constructor(firstOwner : Native, secondOwner : Native, includeThird : Bool) where
    pushFront history := fields(disclose(firstOwner), false)
    pushFront history := fields(disclose(secondOwner), true)
    when includeThird pushFront history := fields(99, false)
  end

  entry head uses constructorRecordListNoInputs arguments [] where
    headOrDefault history as (present, position)
    returnMaybe head as (present, position)
  end

  entry pop uses constructorRecordListNoInputs arguments [] where
    popFront history
  end
end

private def headEntry : Entrypoint :=
  (ConstructorRecordList.entrypoints.find? (·.name == "head")).getD
    {name := "missing", circuit := {name := "missing"}}

private def constructorPlan (ctor : Noctium.Constructor) : Except String Json := do
  let plan ← (Backend.Impact.lower ConstructorRecordList.state headEntry).mapError (·.message)
  let artifact := Compiler.nativePlanJson TargetProfile.selected321
    `ConstructorRecordList ConstructorRecordList.state (some ctor) headEntry plan
  artifact.getObjVal? "constructor"

private def constructorActions (metadata : Json) : Array Json :=
  ((metadata.getObjVal? "actions").toOption.getD Json.null).getArr?.toOption.getD #[]

#guard (ConstructorRecordList.validate Capabilities.source).isOk
#guard (headEntry.validate Capabilities.source ConstructorRecordList.state).isOk

#guard match ConstructorRecordList.constructor with
  | some ctor =>
      match ctor.actions with
      | [.pushRecordList "history" firstFields none,
         .pushRecordList "history" secondFields none,
         .pushRecordList "history" thirdFields (some (.ref "includeThird"))] =>
          [firstFields, secondFields, thirdFields].all
            (fun fields => fields.map LedgerFieldExpr.ty == [.native, .bool])
      | _ => _root_.Bool.false
  | none => _root_.Bool.false

#guard match ConstructorRecordList.constructor with
  | some ctor =>
      match constructorPlan ctor with
      | .ok metadata =>
          let actions := constructorActions metadata
          let guard := NativeExpression.toJson (.ref "includeThird" : Expr .bool)
          actions.size == 3 && actions.toList.all (fun action =>
            action.getObjValD "kind" == toJson ("pushRecordList" : String) &&
              action.getObjValD "state" == toJson ("history" : String) &&
              (action.getObjVal? "fields").isOk &&
              !(action.getObjVal? "schema").isOk) &&
            !(actions[0]!.getObjVal? "guard").isOk &&
            !(actions[1]!.getObjVal? "guard").isOk &&
            actions[2]!.getObjValD "guard" == guard
      | .error _ => _root_.Bool.false
  | none => _root_.Bool.false

/- error: ledger record field count does not match its checked layout -/
#guard_msgs (substring := true) in
noctium_contract ConstructorRecordListWrongWidth where
  list history : struct Position {
    owner : Native
    active : Bool
  }

  constructor(owner : Native) where
    pushFront history := fields(disclose(owner))
  end
end
