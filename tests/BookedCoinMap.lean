import Noctium.Disclosure
import Noctium.Frontend

open scoped Noctium
open Noctium

noctium_circuit bookedCoinMapInputs where
  public key : Bytes32
  private nonce : Bytes32
  private color : Bytes32
  private amount : UInt 128
  private isContract : Bool
  private recipient : Bytes32
end

noctium_contract BookedCoinMap where
  tree coins : Bytes32 => struct Coin {
    nonce : Bytes32
    color : Bytes32
    value : UInt 128
    mtIndex : UInt 64
  }

  entry store uses bookedCoinMapInputs where
    insertShieldedCoinMap(coins, key, disclose(nonce), disclose(color),
      disclose(amount), disclose(isContract), disclose(recipient))
  end
end

private def bookedCoinMapEntry : Entrypoint :=
  match BookedCoinMap.entrypoints with
  | found :: _ => found
  | [] => {name := "missing", circuit := {name := "missing"}}

#guard bookedCoinMapEntry.name == "store"
#guard bookedCoinMapEntry.effects.length == 1
#guard bookedCoinMapEntry.effectGuards.length == 1 &&
  bookedCoinMapEntry.effectGuards.all Option.isNone
#guard match bookedCoinMapEntry.effects with
  | [.insertShieldedCoinMap "coins" (.ref "key") _ _ _ _ _ []] => Bool.true
  | _ => Bool.false
#guard (bookedCoinMapEntry.validate Capabilities.source BookedCoinMap.state).isOk
#guard (Disclosure.entrypoint bookedCoinMapEntry).isOk

#guard match BookedCoinMap.state with
  | [{kind := .tree (.map (.bytes 32) (.composite environment recordType)), ..}] =>
      (LedgerValueType.shieldedCoinRecordFields environment recordType).isOk
  | _ => Bool.false

private def bookedCoinMapUndisclosed : Entrypoint :=
  {bookedCoinMapEntry with effects := bookedCoinMapEntry.effects.map fun effect =>
    match effect with
    | .insertShieldedCoinMap state key _ color amount isContract recipient keys =>
        .insertShieldedCoinMap state key (.ref "nonce") color amount isContract recipient keys
    | _ => effect}

#guard match Disclosure.entrypoint bookedCoinMapUndisclosed with
  | .error diagnostic => diagnostic.message.contains "undisclosed private"
  | .ok _ => Bool.false

private def bookedCoinMapWrongKey : List StateDecl :=
  BookedCoinMap.state.map fun declaration =>
    match declaration.kind with
    | .tree (.map _ value) =>
        {declaration with kind := .tree (.map .native value)}
    | _ => declaration

#guard match bookedCoinMapEntry.validate Capabilities.source bookedCoinMapWrongKey with
  | .error diagnostic => diagnostic.message.contains "Bytes32-keyed Map with a qualified coin record value"
  | .ok _ => Bool.false

private def bookedCoinMapGuarded : Entrypoint :=
  {bookedCoinMapEntry with effectGuards := [some (.bool Bool.true)]}

#guard match bookedCoinMapGuarded.validate Capabilities.source BookedCoinMap.state with
  | .error _ => Bool.true
  | .ok _ => Bool.false
