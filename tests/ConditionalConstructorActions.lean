import Noctium.Backend.Impact
import Noctium.Compiler
import Noctium.Frontend

open Lean
open scoped Noctium
open Noctium

noctium_circuit conditionalConstructorInspection where
  public key : Native
end

noctium_contract ConditionalConstructorActions where
  sealed map seeded : Native => Native
  sealed cell present : Bool

  constructor(key : Native, enabled : Bool) where
    when enabled insert seeded[key] := 41
    initializeMember present from seeded[key]
  end

  entry inspect uses conditionalConstructorInspection where
    member seeded[key] as mapMember
    read present as sealedPresent
    return hasKey : Bool := mapMember
    return isPresent : Bool := sealedPresent
  end
end

private def inspectEntry : Entrypoint :=
  (ConditionalConstructorActions.entrypoints.find? (·.name == "inspect")).getD
    {name := "missing", circuit := {name := "missing"}}

private def fullPlanJson : Except String Json := do
  let plan ← (Backend.Impact.lower ConditionalConstructorActions.state inspectEntry).mapError
    (·.message)
  pure (Compiler.nativePlanJson TargetProfile.selected321
    `ConditionalConstructorActions ConditionalConstructorActions.state
    ConditionalConstructorActions.constructor inspectEntry plan)

private def constructorPlan : Except String Json := do
  (← fullPlanJson).getObjVal? "constructor"

private def jsonStringField (value : Json) (field : String) : String :=
  ((value.getObjVal? field).toOption.bind fun item => item.getStr?.toOption).getD ""

private def actionKind (value : Json) : String := jsonStringField value "kind"

private def actionState (value : Json) : String := jsonStringField value "state"

#guard (ConditionalConstructorActions.validate Capabilities.source).isOk
#guard (inspectEntry.validate Capabilities.source ConditionalConstructorActions.state).isOk

#guard match ConditionalConstructorActions.constructor with
  | some ctor =>
      ctor.mapInserts.isEmpty &&
      match ctor.actions with
      | [.mapInsert insertion, .initializeCellFromMapMember memberInit] =>
          insertion.state == "seeded" && insertion.valueType == .native &&
          (match insertion.key with | .mk .native (.ref "key") => _root_.Bool.true | _ => _root_.Bool.false) &&
          (match insertion.guard with
            | some (.ref "enabled") => _root_.Bool.true
            | _ => _root_.Bool.false) &&
          memberInit.state == "present" && memberInit.map == "seeded" &&
          (match memberInit.key with | .mk .native (.ref "key") => _root_.Bool.true | _ => _root_.Bool.false)
      | _ => _root_.Bool.false
  | none => _root_.Bool.false

#guard match constructorPlan with
  | .ok ctor =>
      let actions := match ctor.getObjVal? "actions" with
        | .ok value => value.getArr?.toOption.getD #[]
        | .error _ => #[]
      let legacyInserts := ctor.getObjVal? "mapInserts"
      actions.size == 2 && actionKind (actions[0]!) == "mapInsert" &&
        actionState (actions[0]!) == "seeded" &&
        (actions[0]!.getObjVal? "key").isOk &&
        (actions[0]!.getObjVal? "value").isOk &&
        (actions[0]!.getObjVal? "guard").isOk &&
        actionKind (actions[1]!) == "initializeCellFromMapMember" &&
        actionState (actions[1]!) == "present" &&
        jsonStringField (actions[1]!) "map" == "seeded" &&
        (actions[1]!.getObjVal? "key").isOk && !legacyInserts.isOk
  | .error _ => _root_.Bool.false

private def nonBoolTargetRejected : _root_.Bool :=
  match ConditionalConstructorActions.constructor with
  | none => _root_.Bool.false
  | some ctor =>
      let invalid := {ConditionalConstructorActions with
        state := ConditionalConstructorActions.state.map fun state : StateDecl =>
          if state.name == "present" then {state with kind := .cell .native} else state,
        «constructor» := some ctor}
      match invalid.validate Capabilities.source with
      | .error diagnostic => diagnostic.message.contains "requires a sealed Bool cell"
      | .ok _ => _root_.Bool.false

#guard nonBoolTargetRejected

private def unsealedTargetRejected : _root_.Bool :=
  match ConditionalConstructorActions.constructor with
  | none => _root_.Bool.false
  | some ctor =>
      let invalid := {ConditionalConstructorActions with
        state := ConditionalConstructorActions.state.map fun state : StateDecl =>
          if state.name == "present" then {state with
            «sealed» := _root_.Bool.false} else state,
        «constructor» := some ctor}
      match invalid.validate Capabilities.source with
      | .error diagnostic => diagnostic.message.contains "requires a sealed Bool cell"
      | .ok _ => _root_.Bool.false

#guard unsealedTargetRejected

private def duplicateTargetRejected : _root_.Bool :=
  match ConditionalConstructorActions.constructor with
  | none => _root_.Bool.false
  | some ctor =>
      let duplicate := {ctor with initializers := [{
        state := "present",
        type := .scalar .bool,
        value := .scalar (.bool _root_.Bool.false)
      }]}
      let invalid := {ConditionalConstructorActions with «constructor» := some duplicate}
      match invalid.validate Capabilities.source with
      | .error diagnostic => diagnostic.message.contains "duplicate constructor state initializer"
      | .ok _ => _root_.Bool.false

#guard duplicateTargetRejected

