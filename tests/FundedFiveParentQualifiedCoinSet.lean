import Noctium.Disclosure
import Noctium.Frontend

open scoped Noctium
open Noctium

noctium_circuit fundedFiveParentQualifiedCoinSetOwnersInputs where
  public selectedOwner : Bytes32
  public otherOwner : Bytes32
  public selectedGroup : Bytes32
  public otherGroup : Bytes32
end

noctium_circuit fundedFiveParentQualifiedCoinSetInputs where
  public domain : Bytes32
  public owner : Bytes32
  public group : Bytes32
  private nonce : Bytes32
  private color : Bytes32
end

noctium_contract FundedFiveParentQualifiedCoinSet where
  tree pot : Bytes32 => struct Coin {
    nonce : Bytes32
    color : Bytes32
    value : UInt 128
    mtIndex : UInt 64
  }
  tree deepCoinSets : Bytes32 => Bytes32 => Bytes32 => Bytes32 => Bytes32 => Set struct Coin {
    nonce : Bytes32
    color : Bytes32
    value : UInt 128
    mtIndex : UInt 64
  }
  entry initializeOwners uses fundedFiveParentQualifiedCoinSetOwnersInputs where
    reset deepCoinSets[selectedOwner]
    reset deepCoinSets[selectedOwner][selectedGroup]
    reset deepCoinSets[selectedOwner][selectedGroup][selectedGroup]
    reset deepCoinSets[selectedOwner][selectedGroup][selectedGroup][selectedGroup]
    reset deepCoinSets[selectedOwner][selectedGroup][selectedGroup][selectedGroup][selectedGroup]
    reset deepCoinSets[selectedOwner][otherGroup]
    reset deepCoinSets[selectedOwner][otherGroup][otherGroup]
    reset deepCoinSets[selectedOwner][otherGroup][otherGroup][otherGroup]
    reset deepCoinSets[selectedOwner][otherGroup][otherGroup][otherGroup][otherGroup]

    reset deepCoinSets[otherOwner]
    reset deepCoinSets[otherOwner][selectedGroup]
    reset deepCoinSets[otherOwner][selectedGroup][selectedGroup]
    reset deepCoinSets[otherOwner][selectedGroup][selectedGroup][selectedGroup]
    reset deepCoinSets[otherOwner][selectedGroup][selectedGroup][selectedGroup][selectedGroup]
    reset deepCoinSets[otherOwner][otherGroup]
    reset deepCoinSets[otherOwner][otherGroup][otherGroup]
    reset deepCoinSets[otherOwner][otherGroup][otherGroup][otherGroup]
    reset deepCoinSets[otherOwner][otherGroup][otherGroup][otherGroup][otherGroup]

  end

  entry tip uses fundedFiveParentQualifiedCoinSetInputs where
    readSelf as own
    mintShielded(domain, 5)
    receiveShieldedToMap(pot, disclose(nonce), disclose(color), 5)
    insertShieldedCoinSet(
      deepCoinSets[owner][group][group][group][group],
      disclose(nonce), disclose(color), 5)
  end
end

private def fundedFiveParentQualifiedCoinSetEntry (name : String) : Entrypoint :=
  (FundedFiveParentQualifiedCoinSet.entrypoints.find? (·.name == name)).getD
    {name := "missing", circuit := {name := "missing"}}

private def fundedFiveParentQualifiedCoinSetPath (owner group : String) (depth : Nat) :
    List String :=
  owner :: List.replicate depth group

#guard FundedFiveParentQualifiedCoinSet.entrypoints.length == 2
#guard ((fundedFiveParentQualifiedCoinSetEntry "initializeOwners").validate
  Capabilities.source FundedFiveParentQualifiedCoinSet.state).isOk
#guard ((fundedFiveParentQualifiedCoinSetEntry "tip").validate
  Capabilities.source FundedFiveParentQualifiedCoinSet.state).isOk
#guard (Disclosure.entrypoint
  (fundedFiveParentQualifiedCoinSetEntry "initializeOwners")).isOk
#guard (Disclosure.entrypoint
  (fundedFiveParentQualifiedCoinSetEntry "tip")).isOk

#guard (fundedFiveParentQualifiedCoinSetEntry "tip").circuit.inputs.map (·.name) ==
  ["domain", "owner", "group", "nonce", "color"]
#guard (fundedFiveParentQualifiedCoinSetEntry "tip").effectGuards.all Option.isNone

#guard ((fundedFiveParentQualifiedCoinSetEntry "initializeOwners").effects.filterMap
    (fun (effect : Effect) =>
      match effect with
      | .emptyMapPath "deepCoinSets" keys => some (keys.map fun key =>
          match key with
          | .mk (.bytes 32) (.ref name) => name
          | _ => "")
      | _ => none)) == [
        fundedFiveParentQualifiedCoinSetPath "selectedOwner" "selectedGroup" 0,
        fundedFiveParentQualifiedCoinSetPath "selectedOwner" "selectedGroup" 1,
        fundedFiveParentQualifiedCoinSetPath "selectedOwner" "selectedGroup" 2,
        fundedFiveParentQualifiedCoinSetPath "selectedOwner" "selectedGroup" 3,
        fundedFiveParentQualifiedCoinSetPath "selectedOwner" "selectedGroup" 4,
        fundedFiveParentQualifiedCoinSetPath "selectedOwner" "otherGroup" 1,
        fundedFiveParentQualifiedCoinSetPath "selectedOwner" "otherGroup" 2,
        fundedFiveParentQualifiedCoinSetPath "selectedOwner" "otherGroup" 3,
        fundedFiveParentQualifiedCoinSetPath "selectedOwner" "otherGroup" 4,
        fundedFiveParentQualifiedCoinSetPath "otherOwner" "selectedGroup" 0,
        fundedFiveParentQualifiedCoinSetPath "otherOwner" "selectedGroup" 1,
        fundedFiveParentQualifiedCoinSetPath "otherOwner" "selectedGroup" 2,
        fundedFiveParentQualifiedCoinSetPath "otherOwner" "selectedGroup" 3,
        fundedFiveParentQualifiedCoinSetPath "otherOwner" "selectedGroup" 4,
        fundedFiveParentQualifiedCoinSetPath "otherOwner" "otherGroup" 1,
        fundedFiveParentQualifiedCoinSetPath "otherOwner" "otherGroup" 2,
        fundedFiveParentQualifiedCoinSetPath "otherOwner" "otherGroup" 3,
        fundedFiveParentQualifiedCoinSetPath "otherOwner" "otherGroup" 4 ]

#guard match ((fundedFiveParentQualifiedCoinSetEntry "tip").effects.filterMap
    fun (effect : Effect) =>
    match effect with
    | .insertShieldedCoinSet .. => some effect
    | _ => none) with
  | [.insertShieldedCoinSet "deepCoinSets" _ _ _ (.ref selfAddressName)
        [ .mk (.bytes 32) (.ref "owner"), .mk (.bytes 32) (.ref "group")
        , .mk (.bytes 32) (.ref "group"), .mk (.bytes 32) (.ref "group")
        , .mk (.bytes 32) (.ref "group") ] ] =>
      (fundedFiveParentQualifiedCoinSetEntry "tip").effects.any fun
        | .readContractAddress name => name == selfAddressName
        | _ => Bool.false
  | _ => Bool.false
