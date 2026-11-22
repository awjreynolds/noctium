import Noctium.Frontend
import Noctium.Backend.Impact
import Noctium.Backend.Zkir
import Noctium.Compiler

open scoped Noctium
open Lean
open Noctium

noctium_circuit recordMapUpdateInputs where
  public active : Bool
  public amount : UInt 16
  public value : UInt 16
end

noctium_circuit recordMapKeyInputs where
  public active : Bool
  public amount : UInt 16
end

noctium_contract RecordMapKeys where
  tree memos : struct Memo {
    active : Bool
    amount : UInt 16
  } => UInt 16

  entry update uses recordMapUpdateInputs where
    member memos[fields(active, amount)] as beforeMember
    insert memos[fields(active, amount)] := disclose(value)
    member memos[fields(active, amount)] as afterMember
    return presentBefore : Bool := beforeMember
    return presentAfter : Bool := afterMember
  end

  entry removeMemo uses recordMapKeyInputs where
    member memos[fields(active, amount)] as beforeMember
    remove memos[fields(active, amount)]
    member memos[fields(active, amount)] as afterMember
    return presentBefore : Bool := beforeMember
    return presentAfter : Bool := afterMember
  end

  entry lookup uses recordMapKeyInputs where
    read memos[fields(active, amount)] as foundValue
    return storedValue : UInt 16 := foundValue
  end
end

private def recordMapEntry (name : String) : Entrypoint :=
  (RecordMapKeys.entrypoints.find? (·.name == name)).getD
    {name := "missing", circuit := {name := "missing"}}

private def recordMapContext : EvalContext := {
  modulus := Field.modulus
  poseidon2 := fun _ _ _ => .error "unused by record Map key fixture"
}

private def recordMapInitialState : LedgerState := {trees := [("memos", .map [])]}

private def recordMapUpdateRun (active : _root_.Bool) (amount value : Nat) (state : LedgerState) :=
  (recordMapEntry "update").run recordMapContext [
    ("active", .bool active), ("amount", .uint 65535 amount),
    ("value", .uint 65535 value)] state

private def recordMapRemoveRun (active : _root_.Bool) (amount : Nat) (state : LedgerState) :=
  (recordMapEntry "removeMemo").run recordMapContext [
    ("active", .bool active), ("amount", .uint 65535 amount)] state

private def recordMapLookupRun (active : _root_.Bool) (amount : Nat) (state : LedgerState) :=
  (recordMapEntry "lookup").run recordMapContext [
    ("active", .bool active), ("amount", .uint 65535 amount)] state

private def validateGuardedRecordMapEffect (effect : Effect) : Except Diagnostic Unit := do
  let base := recordMapEntry "update"
  let guarded := {base with
    effects := [effect]
    effectSpans := [{}]
    effectGuards := [some (.bool _root_.Bool.true)]
    returns := []}
  guarded.validate Capabilities.source RecordMapKeys.state

#guard (RecordMapKeys.validate Capabilities.source).isOk
#guard ((recordMapEntry "update").validate Capabilities.source RecordMapKeys.state).isOk
#guard ((recordMapEntry "removeMemo").validate Capabilities.source RecordMapKeys.state).isOk
#guard ((recordMapEntry "lookup").validate Capabilities.source RecordMapKeys.state).isOk
#guard (validateGuardedRecordMapEffect (.writeRecordMap "memos" [
  .mk .bool (.ref "active"), .mk (.uint 65535) (.ref "amount")]
  (.uint 65535) (.ref "value"))).isOk
#guard (validateGuardedRecordMapEffect (.removeRecordMap "memos" [
  .mk .bool (.ref "active"), .mk (.uint 65535) (.ref "amount")])).isOk

#guard match RecordMapKeys.state with
  | [{kind := .tree (.recordMapKey environment type (.uint 65535)), ..}] =>
      match LedgerValueType.ledgerRecordWriteFields environment type with
      | .ok fields => fields == [("active", .bool), ("amount", .uint 65535)]
      | .error _ => _root_.Bool.false
  | _ => _root_.Bool.false

#guard match Backend.Impact.lower RecordMapKeys.state (recordMapEntry "lookup") with
  | .ok plan =>
      plan.operations.any (fun operation => match operation with
        | .indexRecordPath 0 schema values =>
            values.map LedgerFieldExpr.ty == [.bool, .uint 65535] &&
            schema != Lean.Json.null
        | _ => _root_.Bool.false) &&
      plan.reads.any (fun binding => binding.ty == .uint 65535)
  | .error _ => _root_.Bool.false

#guard match Backend.Zkir.lowerEntrypoint RecordMapKeys.state (recordMapEntry "lookup") with
  | .ok _ => _root_.Bool.true
  | .error _ => _root_.Bool.false

#guard match recordMapUpdateRun _root_.Bool.true 513 7 recordMapInitialState with
  | .ok (outputs, state) =>
      outputs.lookup "presentBefore" == some (.bool _root_.Bool.false) &&
      outputs.lookup "presentAfter" == some (.bool _root_.Bool.true) &&
      state.trees.lookup "memos" == some (.map [
        (.record [(.bool, [1]), (.uint 65535, [513])], .scalar (.uint 65535 7))])
  | .error _ => _root_.Bool.false

#guard match recordMapUpdateRun _root_.Bool.false 513 9
    (match recordMapUpdateRun _root_.Bool.true 513 7 recordMapInitialState with
      | .ok (_, state) => state
      | .error _ => recordMapInitialState) with
  | .ok (_, state) => match state.trees.lookup "memos" with
      | some (.map entries) => entries.length == 2 && entries.contains
          (.record [(.bool, [0]), (.uint 65535, [513])], .scalar (.uint 65535 9))
      | _ => _root_.Bool.false
  | .error _ => _root_.Bool.false

#guard match recordMapLookupRun _root_.Bool.true 513
    (match recordMapUpdateRun _root_.Bool.true 513 7 recordMapInitialState with
      | .ok (_, state) => state
      | .error _ => recordMapInitialState) with
  | .ok (outputs, _) => outputs.lookup "storedValue" == some (.uint 65535 7)
  | .error _ => _root_.Bool.false

#guard match recordMapRemoveRun _root_.Bool.true 513
    (match recordMapUpdateRun _root_.Bool.false 513 9
      (match recordMapUpdateRun _root_.Bool.true 513 7 recordMapInitialState with
        | .ok (_, state) => state
        | .error _ => recordMapInitialState) with
      | .ok (_, state) => state
      | .error _ => recordMapInitialState) with
  | .ok (outputs, state) =>
      outputs.lookup "presentBefore" == some (.bool _root_.Bool.true) &&
      outputs.lookup "presentAfter" == some (.bool _root_.Bool.false) &&
      match state.trees.lookup "memos" with
      | some (.map entries) => entries.length == 1 && !entries.contains
          (.record [(.bool, [1]), (.uint 65535, [513])], .scalar (.uint 65535 7))
      | _ => _root_.Bool.false
  | .error _ => _root_.Bool.false

#guard match recordMapLookupRun _root_.Bool.true 513 recordMapInitialState with
  | .error _ => _root_.Bool.true
  | .ok _ => _root_.Bool.false

private def undisclosedRecordMapMember : Entrypoint := {
  name := "privateProbe"
  circuit := {name := "privateProbe", inputs := [
    {name := "active", ty := .bool, visibility := .«private»},
    {name := "amount", ty := .uint 65535, visibility := .«private»}]}
  effects := [.memberRecordMap "memos" "present" [
    .mk .bool (.ref "active"), .mk (.uint 65535) (.ref "amount")]]
  effectSpans := [{}]
}

#guard match Disclosure.entrypoint undisclosedRecordMapMember with
  | .error diagnostic => diagnostic.message.contains "undisclosed private parameter" &&
      diagnostic.message.contains "public record Map membership key 'memos'"
  | .ok _ => _root_.Bool.false
