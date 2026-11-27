import Noctium.Frontend

open scoped Noctium

noctium_enum LeafMarker where
  Empty
  Live
end

noctium_enum OtherMarker where
  Empty
  Live
end

noctium_circuit wrongEnumLeafInput where
  private marker : OtherMarker
end

/- error: MerkleTree enum leaf type mismatch -/
#guard_msgs (substring := true) in
noctium_contract RejectWrongEnumHistoricLeaf where
  historicMerkleTree history : 2 of LeafMarker

  entry appendLeaf uses wrongEnumLeafInput where
    insertLeaf history := disclose(marker)
  end
end

noctium_circuit enumLeafInput where
  private marker : LeafMarker
end

noctium_circuit enumLeafRoot where
  public expectedRoot : Native
end

noctium_contract EnumHistoricMerkleLeaf where
  historicMerkleTree history : 2 of LeafMarker

  entry appendLeaf uses enumLeafInput where
    insertLeaf history := disclose(marker)
  end

  entry verifyRoot uses enumLeafRoot where
    checkRoot history against expectedRoot as known
    return knownRoot : Bool := known
  end
end
