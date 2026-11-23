import Noctium.Frontend
import Noctium.Backend.Impact
import Noctium.Backend.Zkir
import Noctium.Disclosure

open scoped Noctium
open Noctium

noctium_circuit recordMapDefaultInputs where
  private active : Bool
  private nonce : UInt 16
  public enabled : Bool
end

noctium_circuit recordMapSeedInputs where
  private active : Bool
  private nonce : UInt 16
  private amount : UInt 16
  private accepted : Bool
  private receiptAmount : UInt 16
end

noctium_contract RecordMapDefaults where
  tree memos : struct Memo {
    active : Bool
    nonce : UInt 16
  } => UInt 16
  tree receipts : struct Memo {
    active : Bool
    nonce : UInt 16
  } => struct Receipt {
    accepted : Bool
    amount : UInt 16
  }

  entry seedRecordMaps uses recordMapSeedInputs where
    insert memos[fields(disclose(active), disclose(nonce))] := disclose(amount)
    insert receipts[fields(disclose(active), disclose(nonce))] :=
      fields(disclose(accepted), disclose(receiptAmount))
  end

  entry defaultRecordMaps uses recordMapDefaultInputs where
    when enabled insertDefault memos[fields(disclose(active), disclose(nonce))]
    when enabled insertDefault receipts[fields(disclose(active), disclose(nonce))]
  end

  entry defaultRecordMapsUnconditional uses recordMapDefaultInputs where
    insertDefault memos[fields(disclose(active), disclose(nonce))]
    insertDefault receipts[fields(disclose(active), disclose(nonce))]
  end
end

private def recordMapDefaultEntry (name : String) : Entrypoint :=
  (RecordMapDefaults.entrypoints.find? (·.name == name)).getD
    {name := "missing", circuit := {name := "missing"}}

#guard (recordMapDefaultEntry "seedRecordMaps").validate Capabilities.source RecordMapDefaults.state |>.isOk
#guard (recordMapDefaultEntry "defaultRecordMaps").validate Capabilities.source RecordMapDefaults.state |>.isOk
#guard (recordMapDefaultEntry "defaultRecordMapsUnconditional").validate Capabilities.source RecordMapDefaults.state |>.isOk

#guard match Backend.Impact.lower RecordMapDefaults.state (recordMapDefaultEntry "defaultRecordMaps") with
  | .ok plan => plan.operations.filterMap (fun operation => match operation with
      | .insert levels => some levels
      | _ => none) == [2, 2]
  | .error _ => _root_.Bool.false

#guard match Backend.Zkir.lowerEntrypoint RecordMapDefaults.state
    (recordMapDefaultEntry "defaultRecordMaps") with
  | .ok _ => _root_.Bool.true
  | .error _ => _root_.Bool.false

#guard match Backend.Zkir.lowerEntrypoint RecordMapDefaults.state
    (recordMapDefaultEntry "defaultRecordMapsUnconditional") with
  | .ok _ => _root_.Bool.true
  | .error _ => _root_.Bool.false

private def recordMapDefaultContext : EvalContext := {
  modulus := Field.modulus
  poseidon2 := fun _ _ _ => .error "unused by record Map default fixture"
}

private def recordMapDefaultRun (active : _root_.Bool) (nonce : Nat)
    (enabled : _root_.Bool) (state : LedgerState) :=
  (recordMapDefaultEntry "defaultRecordMaps").run recordMapDefaultContext [
    ("active", .bool active), ("nonce", .uint 65535 nonce), ("enabled", .bool enabled)] state

private def recordMapSeedRun (active : _root_.Bool) (nonce amount : Nat)
    (accepted : _root_.Bool) (receiptAmount : Nat) (state : LedgerState) :=
  (recordMapDefaultEntry "seedRecordMaps").run recordMapDefaultContext [
    ("active", .bool active), ("nonce", .uint 65535 nonce),
    ("amount", .uint 65535 amount), ("accepted", .bool accepted),
    ("receiptAmount", .uint 65535 receiptAmount)] state

private def recordMapDefaultEmptyState : LedgerState := {
  trees := [("memos", .map []), ("receipts", .map [])]
}

private def recordMapDefaultA : Value :=
  .record [(.bool, [1]), (.uint 65535, [513])]

private def recordMapDefaultB : Value :=
  .record [(.bool, [0]), (.uint 65535, [513])]

private def recordMapDefaultSeeded : LedgerState :=
  match recordMapSeedRun _root_.Bool.true 513 19 _root_.Bool.true 91
      recordMapDefaultEmptyState with
  | .error _ => recordMapDefaultEmptyState
  | .ok (_, aState) => match recordMapSeedRun _root_.Bool.false 513 22
      _root_.Bool.false 42 aState with
    | .error _ => recordMapDefaultEmptyState
    | .ok (_, state) => state

#guard match recordMapDefaultRun _root_.Bool.true 513 _root_.Bool.true
    recordMapDefaultEmptyState with
  | .ok (_, state) =>
      state.trees.lookup "memos" == some (.map [(recordMapDefaultA, .scalar (.uint 65535 0))]) &&
      state.trees.lookup "receipts" == some (.map [(recordMapDefaultA,
        .composite (.structure "RecordMapDefaults.Receipt") [.bool _root_.Bool.false, .uint 65535 0])])
  | .error _ => _root_.Bool.false

#guard match recordMapDefaultRun _root_.Bool.true 513 _root_.Bool.true
    recordMapDefaultSeeded with
  | .ok (_, state) =>
      state.trees.lookup "memos" == some (.map [
        (recordMapDefaultA, .scalar (.uint 65535 0)),
        (recordMapDefaultB, .scalar (.uint 65535 22))]) &&
      state.trees.lookup "receipts" == some (.map [
        (recordMapDefaultA,
          .composite (.structure "RecordMapDefaults.Receipt") [.bool _root_.Bool.false, .uint 65535 0]),
        (recordMapDefaultB,
          .composite (.structure "RecordMapDefaults.Receipt") [.bool _root_.Bool.false, .uint 65535 42])])
  | .error _ => _root_.Bool.false

#guard match recordMapDefaultRun _root_.Bool.true 513 _root_.Bool.false
    recordMapDefaultSeeded with
  | .ok (_, state) => state == recordMapDefaultSeeded
  | .error _ => _root_.Bool.false

/-- undisclosed private parameter 'active' -/
#guard_msgs (substring := true) in
noctium_contract RecordMapDefaultUndisclosed where
  tree hidden : struct Memo {
    active : Bool
    nonce : UInt 16
  } => UInt 16

  entry update uses recordMapDefaultInputs where
    when enabled insertDefault hidden[fields(active, nonce)]
  end
end
