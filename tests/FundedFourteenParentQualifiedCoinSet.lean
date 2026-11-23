import Noctium.Disclosure
import Noctium.Frontend

open scoped Noctium
open Noctium

noctium_circuit fundedFourteenParentQualifiedCoinSetOwnersInputs where
  public selectedOwner : Bytes32
  public selectedGroup : Bytes32
  public otherGroup : Bytes32
end

noctium_circuit fundedFourteenParentQualifiedCoinSetInputs where
  public domain : Bytes32
  public owner : Bytes32
  public group : Bytes32
  private nonce : Bytes32
  private color : Bytes32
end

noctium_contract FundedFourteenParentQualifiedCoinSet where
  tree pot : Bytes32 => struct Coin {
    nonce : Bytes32
    color : Bytes32
    value : UInt 128
    mtIndex : UInt 64
  }
  tree deepCoinSets :
    Bytes32 => Bytes32 => Bytes32 => Bytes32 =>
    Bytes32 => Bytes32 => Bytes32 => Bytes32 =>
    Bytes32 => Bytes32 => Bytes32 => Bytes32 =>
    Bytes32 => Bytes32 => Set struct Coin {
    nonce : Bytes32
    color : Bytes32
    value : UInt 128
    mtIndex : UInt 64
  }

  entry initializeOwners uses fundedFourteenParentQualifiedCoinSetOwnersInputs where
    reset deepCoinSets[selectedOwner]
    reset deepCoinSets[selectedOwner][selectedGroup]
    reset deepCoinSets[selectedOwner][selectedGroup][selectedGroup]
    reset deepCoinSets[selectedOwner][selectedGroup][selectedGroup][selectedGroup]
    reset deepCoinSets[selectedOwner][selectedGroup][selectedGroup][selectedGroup][selectedGroup]
    reset deepCoinSets[selectedOwner][selectedGroup][selectedGroup][selectedGroup][selectedGroup][selectedGroup]
    reset deepCoinSets[selectedOwner][selectedGroup][selectedGroup][selectedGroup][selectedGroup][selectedGroup][selectedGroup]
    reset deepCoinSets[selectedOwner][selectedGroup][selectedGroup][selectedGroup][selectedGroup][selectedGroup][selectedGroup][selectedGroup]
    reset deepCoinSets[selectedOwner][selectedGroup][selectedGroup][selectedGroup][selectedGroup][selectedGroup][selectedGroup][selectedGroup][selectedGroup]
    reset deepCoinSets[selectedOwner][selectedGroup][selectedGroup][selectedGroup][selectedGroup][selectedGroup][selectedGroup][selectedGroup][selectedGroup][selectedGroup]
    reset deepCoinSets[selectedOwner][selectedGroup][selectedGroup][selectedGroup][selectedGroup][selectedGroup][selectedGroup][selectedGroup][selectedGroup][selectedGroup][selectedGroup]
    reset deepCoinSets[selectedOwner][selectedGroup][selectedGroup][selectedGroup][selectedGroup][selectedGroup][selectedGroup][selectedGroup][selectedGroup][selectedGroup][selectedGroup][selectedGroup]
    reset deepCoinSets[selectedOwner][selectedGroup][selectedGroup][selectedGroup][selectedGroup][selectedGroup][selectedGroup][selectedGroup][selectedGroup][selectedGroup][selectedGroup][selectedGroup][selectedGroup]
    reset deepCoinSets[selectedOwner][selectedGroup][selectedGroup][selectedGroup][selectedGroup][selectedGroup][selectedGroup][selectedGroup][selectedGroup][selectedGroup][selectedGroup][selectedGroup][selectedGroup][selectedGroup]
    reset deepCoinSets[selectedOwner][selectedGroup][selectedGroup][selectedGroup][selectedGroup][selectedGroup][selectedGroup][selectedGroup][selectedGroup][selectedGroup][selectedGroup][selectedGroup][selectedGroup][otherGroup]
  end

  entry tip uses fundedFourteenParentQualifiedCoinSetInputs where
    readSelf as own
    mintShielded(domain, 5)
    receiveShieldedToMap(pot, disclose(nonce), disclose(color), 5)
    insertShieldedCoinSet(
      deepCoinSets[owner][group][group][group][group][group][group][group][group][group][group][group][group][group],
      disclose(nonce), disclose(color), 5)
  end
end

private def fundedFourteenParentQualifiedCoinSetEntry (name : String) : Entrypoint :=
  (FundedFourteenParentQualifiedCoinSet.entrypoints.find? (·.name == name)).getD
    {name := "missing", circuit := {name := "missing"}}

private def fundedFourteenParentQualifiedCoinSetPath (owner group : String) (depth : Nat) :
    List String :=
  owner :: List.replicate depth group

#guard FundedFourteenParentQualifiedCoinSet.entrypoints.length == 2
#guard ((fundedFourteenParentQualifiedCoinSetEntry "initializeOwners").validate
  Capabilities.source FundedFourteenParentQualifiedCoinSet.state).isOk
#guard ((fundedFourteenParentQualifiedCoinSetEntry "tip").validate
  Capabilities.source FundedFourteenParentQualifiedCoinSet.state).isOk
#guard (Disclosure.entrypoint
  (fundedFourteenParentQualifiedCoinSetEntry "initializeOwners")).isOk
#guard (Disclosure.entrypoint
  (fundedFourteenParentQualifiedCoinSetEntry "tip")).isOk

#guard (fundedFourteenParentQualifiedCoinSetEntry "tip").circuit.inputs.map (·.name) ==
  ["domain", "owner", "group", "nonce", "color"]
#guard (fundedFourteenParentQualifiedCoinSetEntry "tip").effectGuards.all Option.isNone

#guard ((fundedFourteenParentQualifiedCoinSetEntry "initializeOwners").effects.filterMap
    (fun (effect : Effect) =>
      match effect with
      | .emptyMapPath "deepCoinSets" keys => some (keys.map fun key =>
          match key with
          | .mk (.bytes 32) (.ref name) => name
          | _ => "")
      | _ => none)) ==
  ((List.range 14).map fun depth =>
      fundedFourteenParentQualifiedCoinSetPath "selectedOwner" "selectedGroup" depth) ++
    [fundedFourteenParentQualifiedCoinSetPath "selectedOwner" "selectedGroup" 12 ++ ["otherGroup"]]

#guard match ((fundedFourteenParentQualifiedCoinSetEntry "tip").effects.filterMap
    fun (effect : Effect) =>
    match effect with
    | .insertShieldedCoinSet .. => some effect
    | _ => none) with
  | [.insertShieldedCoinSet "deepCoinSets" _ _ _ (.ref selfAddressName) keys] =>
      keys.map (fun key =>
        match key with
        | .mk (.bytes 32) (.ref name) => name
        | _ => "") ==
          fundedFourteenParentQualifiedCoinSetPath "owner" "group" 13 &&
        (fundedFourteenParentQualifiedCoinSetEntry "tip").effects.any fun
          | .readContractAddress name => name == selfAddressName
          | _ => Bool.false
  | _ => Bool.false
