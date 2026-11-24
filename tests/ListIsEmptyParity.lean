import Noctium.Backend.Impact
import Noctium.Backend.Zkir
import Noctium.Frontend

open scoped Noctium
open Noctium

noctium_circuit listIsEmptyParityInputs where
  private owner : Bytes32
  private emptySpender : Bytes32
  private populatedSpender : Bytes32
  private missingOwner : Bytes32
  private missingSpender : Bytes32
  public probeMissing : Bool
end

noctium_circuit listIsEmptyParitySeedInputs where
  private owner : Bytes32
  private emptySpender : Bytes32
  private populatedSpender : Bytes32
end

noctium_contract ListIsEmptyParity where
  list emptyBytes : Bytes 0
  list oneEmptyByte : Bytes 0
  tree memos : Bytes32 => Bytes32 => List struct Memo {
    x : Native
    y : Native
  }

  entry seed uses listIsEmptyParitySeedInputs arguments [owner, emptySpender,
      populatedSpender] where
    insert memos[disclose(owner)] := emptyMap
    reset memos[disclose(owner)][disclose(emptySpender)]
    reset memos[disclose(owner)][disclose(populatedSpender)]
    pushFront oneEmptyByte := bytes(0, "")
    pushFront memos[disclose(owner)][disclose(populatedSpender)] := fields(17, 42)
  end

  entry inspect uses listIsEmptyParityInputs arguments [owner, emptySpender,
      populatedSpender, missingOwner, missingSpender] where
    isEmpty emptyBytes as emptyBytesEmpty
    isEmpty oneEmptyByte as oneEmptyByteEmpty
    isEmpty memos[disclose(owner)][disclose(emptySpender)] as emptyRecordListEmpty
    isEmpty memos[disclose(owner)][disclose(populatedSpender)] as populatedRecordListEmpty
    when probeMissing isEmpty memos[disclose(missingOwner)][disclose(missingSpender)]
      as missingRecordListEmpty
    return emptyBytesResult : Bool := emptyBytesEmpty
    return oneEmptyByteResult : Bool := oneEmptyByteEmpty
    return emptyRecordListResult : Bool := emptyRecordListEmpty
    return populatedRecordListResult : Bool := populatedRecordListEmpty
    return missingRecordListResult : Bool := missingRecordListEmpty
  end
end

private def listIsEmptyParityEntry : Entrypoint :=
  match ListIsEmptyParity.entrypoints.find? (·.name == "inspect") with
  | some found => found
  | none => {name := "missing", circuit := {name := "missing"}}

private def listIsEmptyParitySeedEntry : Entrypoint :=
  match ListIsEmptyParity.entrypoints.find? (·.name == "seed") with
  | some found => found
  | none => {name := "missing", circuit := {name := "missing"}}

private def listIsEmptyParityOwner (byte : Nat) : Value :=
  .bytes 32 (List.replicate 32 byte)

private def listIsEmptyParityState : LedgerState := {
  trees := [
    ("emptyBytes", .list []),
    ("oneEmptyByte", .list [[.bytes 0 []]]),
    ("memos", .map [
      (listIsEmptyParityOwner 1, .map [
        (listIsEmptyParityOwner 2, .list []),
        (listIsEmptyParityOwner 3, .list [[.native 17, .native 42]])])])]
}

private def listIsEmptyParityEmptyState : LedgerState := {
  trees := [("emptyBytes", .list []), ("oneEmptyByte", .list []), ("memos", .map [])]
}

private def listIsEmptyParitySeedRun :=
  listIsEmptyParitySeedEntry.run {
    modulus := Field.modulus
    poseidon2 := fun _ _ _ => .error "unused by List.isEmpty fixture"
  } [
    ("owner", listIsEmptyParityOwner 1),
    ("emptySpender", listIsEmptyParityOwner 2),
    ("populatedSpender", listIsEmptyParityOwner 3)
  ] listIsEmptyParityEmptyState

private def listIsEmptyParityRun (probeMissing : _root_.Bool) :=
  listIsEmptyParityEntry.run {
    modulus := Field.modulus
    poseidon2 := fun _ _ _ => .error "unused by List.isEmpty fixture"
  } [
    ("owner", listIsEmptyParityOwner 1),
    ("emptySpender", listIsEmptyParityOwner 2),
    ("populatedSpender", listIsEmptyParityOwner 3),
    ("missingOwner", listIsEmptyParityOwner 4),
    ("missingSpender", listIsEmptyParityOwner 5),
    ("probeMissing", .bool probeMissing)
  ] listIsEmptyParityState

#guard ListIsEmptyParity.entrypoints.length == 2
#guard (listIsEmptyParityEntry.validate Capabilities.source ListIsEmptyParity.state).isOk
#guard (listIsEmptyParitySeedEntry.validate Capabilities.source ListIsEmptyParity.state).isOk
#guard (Backend.Impact.lower ListIsEmptyParity.state listIsEmptyParityEntry).isOk
#guard (Backend.Impact.lower ListIsEmptyParity.state listIsEmptyParitySeedEntry).isOk
#guard (Backend.Zkir.lowerEntrypoint ListIsEmptyParity.state listIsEmptyParityEntry).isOk
#guard (Backend.Zkir.lowerEntrypoint ListIsEmptyParity.state listIsEmptyParitySeedEntry).isOk

#guard match listIsEmptyParitySeedRun with
  | .ok (outputs, state) =>
      outputs.isEmpty &&
      state.trees.lookup "emptyBytes" == some (.list []) &&
      state.trees.lookup "oneEmptyByte" == some (.list [[.bytes 0 []]]) &&
      match state.trees.lookup "memos" with
      | some (.map owners) =>
          match owners.lookup (listIsEmptyParityOwner 1) with
          | some (.map spenders) =>
              spenders.lookup (listIsEmptyParityOwner 2) == some (.list []) &&
              spenders.lookup (listIsEmptyParityOwner 3) ==
                some (.list [[.native 17, .native 42]])
          | _ => Bool.false
      | _ => Bool.false
  | .error _ => Bool.false

#guard match listIsEmptyParityRun Bool.false with
  | .ok (outputs, state) =>
      outputs.lookup "emptyBytesResult" == some (.bool Bool.true) &&
      outputs.lookup "oneEmptyByteResult" == some (.bool Bool.false) &&
      outputs.lookup "emptyRecordListResult" == some (.bool Bool.true) &&
      outputs.lookup "populatedRecordListResult" == some (.bool Bool.false) &&
      outputs.lookup "missingRecordListResult" == some (.bool Bool.false) &&
      state == listIsEmptyParityState
  | .error _ => Bool.false

#guard match listIsEmptyParityRun Bool.true with
  | .error _ => Bool.true
  | .ok _ => Bool.false

#guard listIsEmptyParityEntry.effects.length == 5
#guard listIsEmptyParityEntry.effectGuards.length == 5
