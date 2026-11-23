import Noctium.Backend.Impact
import Noctium.Compiler
import Noctium.Frontend

open Lean
open scoped Noctium
open Noctium

noctium_uint_type CounterReadNominal64 := UInt 64

noctium_circuit orderedConstructorCounterRead where
end

noctium_contract OrderedConstructorCounterRead where
  sealed counter total
  sealed cell before : UInt 64
  sealed cell after : UInt 64

  constructor(enabled : Bool, amount : UInt 16) where
    initializeCounter before from total
    when enabled increment total by amount
    initializeCounter after from total
  end

  entry readBack uses orderedConstructorCounterRead where
    read total as totalValue
    read before as beforeValue
    read after as afterValue
    return totalRead : UInt 64 := totalValue
    return beforeRead : UInt 64 := beforeValue
    return afterRead : UInt 64 := afterValue
  end
end

private def readBackEntry : Entrypoint :=
  (OrderedConstructorCounterRead.entrypoints.find? (·.name == "readBack")).getD
    {name := "missing", circuit := {name := "missing"}}

private def constructorMetadata (ctor : Noctium.Constructor) : Except String Json := do
  let plan ← (Backend.Impact.lower OrderedConstructorCounterRead.state readBackEntry).mapError
    (·.message)
  (Compiler.nativePlanJson TargetProfile.selected321
    `OrderedConstructorCounterRead OrderedConstructorCounterRead.state (some ctor)
    readBackEntry plan).getObjVal? "constructor"

private def jsonStringField (value : Json) (field : String) : String :=
  ((value.getObjVal? field).toOption.bind fun item => item.getStr?.toOption).getD ""

private def constructorActions (metadata : Json) : Array Json :=
  ((metadata.getObjVal? "actions").toOption.getD Json.null).getArr?.toOption.getD #[]

private def actionKind (value : Json) : String := jsonStringField value "kind"

private def actionState (value : Json) : String := jsonStringField value "state"

#guard (OrderedConstructorCounterRead.validate Capabilities.source).isOk
#guard (readBackEntry.validate Capabilities.source OrderedConstructorCounterRead.state).isOk

#guard match OrderedConstructorCounterRead.constructor with
  | some ctor =>
      ctor.counterIncrements.isEmpty &&
      match ctor.actions with
      | [.initializeCellFromCounter "before" "total",
         .counterIncrement orderedAction,
         .initializeCellFromCounter "after" "total"] =>
          orderedAction.state == "total" &&
          (match orderedAction.amount with
            | .cast _ (.ref "amount") => _root_.Bool.true
            | _ => _root_.Bool.false) &&
          (match orderedAction.guard with
            | some (.ref "enabled") => _root_.Bool.true
            | _ => _root_.Bool.false)
      | _ => _root_.Bool.false
  | none => _root_.Bool.false

#guard match OrderedConstructorCounterRead.constructor with
  | some ctor =>
      match constructorMetadata ctor with
      | .ok metadata =>
          let actions := constructorActions metadata
          actions.size == 3 &&
            actionKind (actions[0]!) == "initializeCellFromCounter" &&
            actionState (actions[0]!) == "before" &&
            jsonStringField (actions[0]!) "counter" == "total" &&
            actionKind (actions[1]!) == "counterIncrement" &&
            actionState (actions[1]!) == "total" &&
            (actions[1]!.getObjVal? "amount").isOk &&
            (actions[1]!.getObjVal? "guard").toOption.getD Json.null ==
              NativeExpression.toJson (.ref "enabled" : Expr .bool) &&
            actionKind (actions[2]!) == "initializeCellFromCounter" &&
            actionState (actions[2]!) == "after" &&
            jsonStringField (actions[2]!) "counter" == "total" &&
            !(metadata.getObjVal? "counterIncrements").isOk
      | .error _ => _root_.Bool.false
  | none => _root_.Bool.false

private def orderedAndBatchCountersRejected : _root_.Bool :=
  match OrderedConstructorCounterRead.constructor with
  | none => _root_.Bool.false
  | some ctor =>
      let counterChange : ConstructorCounterIncrement := {
        state := "total",
        amount := .uint (2 ^ 32 - 1) 1
      }
      let invalid := {OrderedConstructorCounterRead with
        «constructor» := some {ctor with counterIncrements := [counterChange]}}
      match invalid.validate Capabilities.source with
      | .error diagnostic => diagnostic.message.contains "ordered constructor Counter actions"
      | .ok _ => _root_.Bool.false

#guard orderedAndBatchCountersRejected

private def wrongSnapshotCellRejected : _root_.Bool :=
  match OrderedConstructorCounterRead.constructor with
  | none => _root_.Bool.false
  | some ctor =>
      let invalid := {OrderedConstructorCounterRead with
        state := OrderedConstructorCounterRead.state.map fun state : StateDecl =>
          if state.name == "before" then {state with kind := .cell .native} else state,
        «constructor» := some ctor}
      match invalid.validate Capabilities.source with
      | .error diagnostic => diagnostic.message.contains "counter snapshot requires a UInt64 Cell"
      | .ok _ => _root_.Bool.false

#guard wrongSnapshotCellRejected

private def nestedCounterRejected : _root_.Bool :=
  match OrderedConstructorCounterRead.constructor with
  | none => _root_.Bool.false
  | some ctor =>
      let invalid := {OrderedConstructorCounterRead with
        state := OrderedConstructorCounterRead.state.map fun state : StateDecl =>
          if state.name == "total" then
            {state with kind := .tree (.map .native .counter), «sealed» := _root_.Bool.false}
          else state,
        «constructor» := some ctor}
      match invalid.validate Capabilities.source with
      | .error diagnostic => diagnostic.message.contains "requires a root Counter"
      | .ok _ => _root_.Bool.false

#guard nestedCounterRejected

private def duplicateSnapshotRejected : _root_.Bool :=
  match OrderedConstructorCounterRead.constructor with
  | none => _root_.Bool.false
  | some ctor =>
      let duplicate : ConstructorInitializer := {
        state := "before",
        type := .scalar (.uint (2 ^ 64 - 1)),
        value := .scalar (.uint (2 ^ 64 - 1) 0)
      }
      let invalid := {OrderedConstructorCounterRead with
        «constructor» := some {ctor with initializers := [duplicate]}}
      match invalid.validate Capabilities.source with
      | .error diagnostic => diagnostic.message.contains "duplicate constructor state initializer"
      | .ok _ => _root_.Bool.false

#guard duplicateSnapshotRejected

/- error: counter snapshot requires a plain UInt64 Cell -/
#guard_msgs (substring := true) in
noctium_contract NominalUInt64CounterSnapshotRejected where
  counter total
  cell snapshot : CounterReadNominal64
  constructor() where
    initializeCounter snapshot from total
  end
end
