import Noctium.Frontend
import Noctium.Backend.Impact
import Noctium.Backend.Zkir
import Noctium.Compiler

open scoped Noctium
open Lean
open Noctium

noctium_circuit typedSetKeyInputs where
  public active : Bool
  public amount : UInt 16
  public adding : Bool
  public removing : Bool
end

noctium_contract TypedSetKey where
  set memoSet : struct Memo {
    active : Bool
    amount : UInt 16
  }

  entry update uses typedSetKeyInputs where
    member memoSet[fields(active, amount)] as presentBefore
    when adding insert memoSet[fields(active, amount)]
    when removing remove memoSet[fields(active, amount)]
    return wasPresent : Bool := presentBefore
  end
end

private def typedSetKeyEntry : Entrypoint :=
  (TypedSetKey.entrypoints.find? (·.name == "update")).getD
    {name := "missing", circuit := {name := "missing"}}

#guard (TypedSetKey.validate Capabilities.source).isOk
#guard (typedSetKeyEntry.validate Capabilities.source TypedSetKey.state).isOk

#guard match TypedSetKey.state with
  | [{kind := .tree (.recordSet environment type), ..}] =>
      match LedgerValueType.ledgerRecordWriteFields environment type with
      | .ok fields => fields == [("active", .bool), ("amount", .uint 65535)]
      | .error _ => _root_.Bool.false
  | _ => _root_.Bool.false

#guard match Backend.Impact.lower TypedSetKey.state typedSetKeyEntry with
  | .ok plan =>
      match plan.operations.drop (plan.operations.length - 11) with
      | [.dup, .indexPath 0 _root_.Bool.false [],
         .pushFields _ memberValues _root_.Bool.false, .member,
         .popeq (.bitExpr (.ref _)),
         .indexPath 0 _root_.Bool.true [], .pushFields _ insertValues _root_.Bool.false,
         .push (.field (.native 1)) _root_.Bool.false, .newMap, .insert 2,
         .mapRemoveRecord 0 _ removeValues] =>
          memberValues.length == 2 && insertValues.length == 2 && removeValues.length == 2 &&
          memberValues.map LedgerFieldExpr.ty == [.bool, .uint 65535] &&
          insertValues.map LedgerFieldExpr.ty == [.bool, .uint 65535] &&
          removeValues.map LedgerFieldExpr.ty == [.bool, .uint 65535] &&
          plan.activityGuards.length == plan.operations.length &&
          (plan.fieldGroups.drop (plan.fieldGroups.length - 14)).map List.length ==
            [1, 4, 7, 1, 4, 4, 7, 5, 1, 1, 4, 7, 1, 1]
      | _ => _root_.Bool.false
  | .error _ => _root_.Bool.false

#guard match Backend.Zkir.lowerEntrypoint TypedSetKey.state typedSetKeyEntry with
  | .ok _ => _root_.Bool.true
  | .error _ => _root_.Bool.false

private def typedSetKeyContext : EvalContext := {
  modulus := Field.modulus
  poseidon2 := fun _ _ _ => .error "unused by record Set key fixture"
}

private def typedSetKeyState : LedgerState := {trees := [("memoSet", .map [])]}

private def typedSetKeyRun (active : _root_.Bool) (amount : Nat)
    (adding removing : _root_.Bool)
    (state : LedgerState) :=
  typedSetKeyEntry.run typedSetKeyContext [
    ("active", .bool active), ("amount", .uint 65535 amount),
    ("adding", .bool adding), ("removing", .bool removing)] state

#guard match typedSetKeyRun _root_.Bool.true 513 _root_.Bool.true _root_.Bool.false typedSetKeyState with
  | .ok (outputs, state) =>
      outputs.lookup "wasPresent" == some (.bool _root_.Bool.false) &&
      state.trees.lookup "memoSet" == some (.map [
        (.record [(.bool, [1]), (.uint 65535, [513])], .null)])
  | .error _ => _root_.Bool.false

#guard match typedSetKeyRun _root_.Bool.false 513 _root_.Bool.true _root_.Bool.false
    (match typedSetKeyRun _root_.Bool.true 513 _root_.Bool.true _root_.Bool.false typedSetKeyState with
      | .ok (_, state) => state
      | .error _ => typedSetKeyState) with
  | .ok (outputs, state) =>
      outputs.lookup "wasPresent" == some (.bool _root_.Bool.false) &&
      match state.trees.lookup "memoSet" with
      | some (.map entries) => entries.length == 2 && entries.contains
          (.record [(.bool, [1]), (.uint 65535, [513])], .null) && entries.contains
          (.record [(.bool, [0]), (.uint 65535, [513])], .null)
      | _ => _root_.Bool.false
  | .error _ => _root_.Bool.false

#guard match typedSetKeyRun _root_.Bool.true 514 _root_.Bool.true _root_.Bool.false
    (match typedSetKeyRun _root_.Bool.false 513 _root_.Bool.true _root_.Bool.false
      (match typedSetKeyRun _root_.Bool.true 513 _root_.Bool.true _root_.Bool.false typedSetKeyState with
        | .ok (_, state) => state
        | .error _ => typedSetKeyState) with
      | .ok (_, state) => state
      | .error _ => typedSetKeyState) with
  | .ok (outputs, state) =>
      outputs.lookup "wasPresent" == some (.bool _root_.Bool.false) &&
      match state.trees.lookup "memoSet" with
      | some (.map entries) => entries.length == 3 && entries.contains
          (.record [(.bool, [1]), (.uint 65535, [514])], .null)
      | _ => _root_.Bool.false
  | .error _ => _root_.Bool.false

#guard match typedSetKeyRun _root_.Bool.true 513 _root_.Bool.false _root_.Bool.true
    (match typedSetKeyRun _root_.Bool.true 514 _root_.Bool.true _root_.Bool.false
      (match typedSetKeyRun _root_.Bool.false 513 _root_.Bool.true _root_.Bool.false
        (match typedSetKeyRun _root_.Bool.true 513 _root_.Bool.true _root_.Bool.false typedSetKeyState with
          | .ok (_, state) => state
          | .error _ => typedSetKeyState) with
        | .ok (_, state) => state
        | .error _ => typedSetKeyState) with
      | .ok (_, state) => state
      | .error _ => typedSetKeyState) with
  | .ok (outputs, state) =>
      outputs.lookup "wasPresent" == some (.bool _root_.Bool.true) &&
      match state.trees.lookup "memoSet" with
      | some (.map entries) => entries.length == 2 && !entries.contains
          (.record [(.bool, [1]), (.uint 65535, [513])], .null)
      | _ => _root_.Bool.false
  | .error _ => _root_.Bool.false

private def undisclosedRecordSetMember : Entrypoint := {
  name := "privateProbe"
  circuit := {name := "privateProbe", inputs := [
    {name := "active", ty := .bool, visibility := .«private»},
    {name := "amount", ty := .uint 65535, visibility := .«private»}]}
  effects := [.memberRecordSet "memoSet" "present" [
    .mk .bool (.ref "active"), .mk (.uint 65535) (.ref "amount")]]
  effectSpans := [{}]
}

#guard match Disclosure.entrypoint undisclosedRecordSetMember with
  | .error diagnostic => diagnostic.message.contains "undisclosed private parameter" &&
      diagnostic.message.contains "public record Set membership guard 'memoSet'"
  | .ok _ => _root_.Bool.false
