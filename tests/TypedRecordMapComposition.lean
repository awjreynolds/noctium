import Noctium.Frontend
import Noctium.Backend.Impact
import Noctium.Backend.Zkir
import Noctium.Compiler

open scoped Noctium
open Lean
open Noctium

noctium_circuit recordMapCompositionInputs where
  public active : Bool
  public amount : UInt 16
  public accepted : Bool
  public code : UInt 16
end

noctium_circuit recordMapCompositionKey where
  public active : Bool
  public amount : UInt 16
end

noctium_contract RecordMapComposition where
  tree receipts : struct Memo {
    active : Bool
    amount : UInt 16
  } => struct Receipt {
    accepted : Bool
    code : UInt 16
  }

  entry put uses recordMapCompositionInputs where
    insert receipts[fields(active, amount)] := fields(accepted, code)
  end

  entry contains uses recordMapCompositionKey where
    member receipts[fields(active, amount)] as found
    return isFound : Bool := found
  end

  entry lookup uses recordMapCompositionKey where
    read receipts[fields(active, amount)] as stored
    return storedAccepted : Bool := stored_accepted
    return storedCode : UInt 16 := stored_code
  end

  entry deleteMemo uses recordMapCompositionKey where
    member receipts[fields(active, amount)] as beforeMember
    remove receipts[fields(active, amount)]
    member receipts[fields(active, amount)] as afterMember
    return presentBefore : Bool := beforeMember
    return presentAfter : Bool := afterMember
  end
end

private def recordMapCompositionEntry (name : String) : Entrypoint :=
  (RecordMapComposition.entrypoints.find? (·.name == name)).getD
    {name := "missing", circuit := {name := "missing"}}

private def recordMapCompositionContext : EvalContext := {
  modulus := Field.modulus
  poseidon2 := fun _ _ _ => .error "unused by record Map composition fixture"
}

private def recordMapCompositionInitialState : LedgerState :=
  {trees := [("receipts", .map [])]}

private def recordMapCompositionPut (active : _root_.Bool) (amount : Nat)
    (accepted : _root_.Bool) (code : Nat) (state : LedgerState) :=
  (recordMapCompositionEntry "put").run recordMapCompositionContext [
    ("active", .bool active), ("amount", .uint 65535 amount),
    ("accepted", .bool accepted), ("code", .uint 65535 code)] state

private def recordMapCompositionMember (active : _root_.Bool) (amount : Nat)
    (state : LedgerState) :=
  (recordMapCompositionEntry "contains").run recordMapCompositionContext [
    ("active", .bool active), ("amount", .uint 65535 amount)] state

private def recordMapCompositionLookup (active : _root_.Bool) (amount : Nat)
    (state : LedgerState) :=
  (recordMapCompositionEntry "lookup").run recordMapCompositionContext [
    ("active", .bool active), ("amount", .uint 65535 amount)] state

private def recordMapCompositionRemove (active : _root_.Bool) (amount : Nat)
    (state : LedgerState) :=
  (recordMapCompositionEntry "deleteMemo").run recordMapCompositionContext [
    ("active", .bool active), ("amount", .uint 65535 amount)] state

#guard (RecordMapComposition.validate Capabilities.source).isOk
#guard ((recordMapCompositionEntry "put").validate Capabilities.source RecordMapComposition.state).isOk
#guard ((recordMapCompositionEntry "contains").validate Capabilities.source RecordMapComposition.state).isOk
#guard ((recordMapCompositionEntry "lookup").validate Capabilities.source RecordMapComposition.state).isOk
#guard ((recordMapCompositionEntry "deleteMemo").validate Capabilities.source RecordMapComposition.state).isOk

private def guardedRecordMapCompositionPut : Entrypoint := {
  (recordMapCompositionEntry "put") with
  effectGuards := [some (.ref "active")]
}

private def guardedRecordMapCompositionLookup : Entrypoint := {
  (recordMapCompositionEntry "lookup") with
  effectGuards := [some (.ref "active")]
}

#guard (guardedRecordMapCompositionPut.validate
  Capabilities.source RecordMapComposition.state).isOk
#guard (guardedRecordMapCompositionLookup.validate
  Capabilities.source RecordMapComposition.state).isOk
#guard (Disclosure.entrypoint guardedRecordMapCompositionPut).isOk
#guard (Disclosure.entrypoint guardedRecordMapCompositionLookup).isOk
#guard match Backend.Impact.lower RecordMapComposition.state guardedRecordMapCompositionPut with
  | .ok plan => match plan.activityGuards.reverse.take 4 with
      | [some (.ref "active"), some (.ref "active"), some (.ref "active"), some (.ref "active")] =>
          _root_.Bool.true
      | _ => _root_.Bool.false
  | .error _ => _root_.Bool.false

private def sealedRecordMapCompositionState :=
  RecordMapComposition.state.map fun declaration => {declaration with «sealed» := _root_.Bool.true}

#guard match (recordMapCompositionEntry "put").validate
    Capabilities.source sealedRecordMapCompositionState with
  | .error diagnostic => diagnostic.message.contains "sealed state 'receipts'"
  | .ok _ => _root_.Bool.false

#guard match RecordMapComposition.state with
  | [{kind := .tree (.recordMapComposite _ _ _ _), ..}] => _root_.Bool.true
  | _ => _root_.Bool.false

#guard match Backend.Impact.lower RecordMapComposition.state (recordMapCompositionEntry "put") with
  | .ok plan =>
      plan.operations.any (fun operation => match operation with
        | .indexPath 0 _root_.Bool.true [] => _root_.Bool.true
        | _ => _root_.Bool.false) &&
      plan.operations.any (fun operation => match operation with
        | .pushFields _ values _root_.Bool.false => values.map LedgerFieldExpr.ty == [.bool, .uint 65535]
        | _ => _root_.Bool.false) &&
      plan.operations.any (fun operation => match operation with
        | .pushFields _ values _root_.Bool.true => values.map LedgerFieldExpr.ty == [.bool, .uint 65535]
        | _ => _root_.Bool.false) &&
      plan.operations.any (fun operation => match operation with
        | .insert levels => levels == 2
        | _ => _root_.Bool.false)
  | .error _ => _root_.Bool.false

#guard match Backend.Impact.lower RecordMapComposition.state (recordMapCompositionEntry "lookup") with
  | .ok plan =>
      plan.operations.any (fun operation => match operation with
        | .indexRecordPath 0 _ values [] => values.map LedgerFieldExpr.ty == [.bool, .uint 65535]
        | _ => _root_.Bool.false) &&
      plan.reads.any (fun binding => binding.ty == .bool) &&
      plan.reads.any (fun binding => binding.ty == .uint 65535)
  | .error _ => _root_.Bool.false

#guard match Backend.Zkir.lowerEntrypoint RecordMapComposition.state (recordMapCompositionEntry "lookup") with
  | .ok _ => _root_.Bool.true
  | .error _ => _root_.Bool.false

#guard match recordMapCompositionPut _root_.Bool.true 513 _root_.Bool.true 7 recordMapCompositionInitialState with
  | .ok (_, state) => state.trees.lookup "receipts" == some (.map [
      (.record [(.bool, [1]), (.uint 65535, [513])],
        .composite (.structure "RecordMapComposition.Receipt") [.bool _root_.Bool.true, .uint 65535 7])])
  | .error _ => _root_.Bool.false

#guard match recordMapCompositionMember _root_.Bool.true 513
    (match recordMapCompositionPut _root_.Bool.true 513 _root_.Bool.true 7 recordMapCompositionInitialState with
      | .ok (_, state) => state
      | .error _ => recordMapCompositionInitialState) with
  | .ok (outputs, _) => outputs.lookup "isFound" == some (.bool _root_.Bool.true)
  | .error _ => _root_.Bool.false

#guard match recordMapCompositionLookup _root_.Bool.true 513
    (match recordMapCompositionPut _root_.Bool.true 513 _root_.Bool.true 7 recordMapCompositionInitialState with
      | .ok (_, state) => state
      | .error _ => recordMapCompositionInitialState) with
  | .ok (outputs, _) =>
      outputs.lookup "storedAccepted" == some (.bool _root_.Bool.true) &&
      outputs.lookup "storedCode" == some (.uint 65535 7)
  | .error _ => _root_.Bool.false

#guard match recordMapCompositionRemove _root_.Bool.true 513
    (match recordMapCompositionPut _root_.Bool.true 513 _root_.Bool.true 7 recordMapCompositionInitialState with
      | .ok (_, state) => state
      | .error _ => recordMapCompositionInitialState) with
  | .ok (outputs, state) =>
      outputs.lookup "presentBefore" == some (.bool _root_.Bool.true) &&
      outputs.lookup "presentAfter" == some (.bool _root_.Bool.false) &&
      state.trees.lookup "receipts" == some (.map [])
  | .error _ => _root_.Bool.false

#guard match recordMapCompositionLookup _root_.Bool.true 513 recordMapCompositionInitialState with
  | .error _ => _root_.Bool.true
  | .ok _ => _root_.Bool.false
