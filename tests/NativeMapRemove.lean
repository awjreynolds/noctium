import Noctium.Frontend

open scoped Noctium

noctium_circuit mapRemoveInputs where
  public owner : Bytes32
  public spender : Bytes32
  public enabled : Bool
end

noctium_circuit mapRemoveSeedInputs where
  public ownerA : Bytes32
  public ownerB : Bytes32
  public target : Bytes32
  public sibling : Bytes32
end

noctium_contract NativeMapRemove where
  tree escrow : Bytes32 => Bytes32 => struct EscrowRecord {
    x : Native
    y : Native
  }
  entry seed uses mapRemoveSeedInputs where
    insert escrow[ownerA] := emptyMap
    insert escrow[ownerA][target] := fields(10, 11)
    insert escrow[ownerA][sibling] := fields(20, 21)
    insert escrow[ownerB] := emptyMap
    insert escrow[ownerB][target] := fields(30, 31)
  end
  entry «remove» uses mapRemoveInputs where
    when enabled remove escrow[owner][spender]
  end
end
