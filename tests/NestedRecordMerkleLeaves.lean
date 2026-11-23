import Noctium.Frontend

open scoped Noctium
open Noctium

noctium_circuit nestedMerkleInputs where
  private tag : Bytes 3
  private accepted : Bool
  private count : UInt 16
  private position : UInt 64
  public enabled : Bool
end

noctium_contract NativeNestedRecordMerkleLeaves where
  merkleTree ordinary : 2 of struct Leaf {
    tag : Bytes 3
    details : struct Meta {
      approved : Bool
      count : UInt 16
    }
  }
  historicMerkleTree archive : 2 of struct Leaf {
    tag : Bytes 3
    details : struct Meta {
      approved : Bool
      count : UInt 16
    }
  }

  entry append uses nestedMerkleInputs where
    insertLeaf ordinary := fields(disclose(tag), disclose(accepted), disclose(count))
    insertLeaf archive := fields(disclose(tag), disclose(accepted), disclose(count))
  end

  entry setIndex uses nestedMerkleInputs where
    when enabled insertLeafIndex ordinary at disclose(position) :=
      fields(disclose(tag), disclose(accepted), disclose(count))
    when enabled insertLeafIndex archive at disclose(position) :=
      fields(disclose(tag), disclose(accepted), disclose(count))
  end

  entry setDefault uses nestedMerkleInputs where
    when enabled insertLeafDefault ordinary at disclose(position)
    when enabled insertLeafDefault archive at disclose(position)
  end
end

private def checkNestedRecordPreimages : Except String _root_.Bool := do
  let [appendCall, writeCall, defaultCall] := NativeNestedRecordMerkleLeaves.entrypoints
    | throw "expected append, index and default entrypoints"
  let context : EvalContext := {
    modulus := Field.modulus
    poseidon2 := fun _ _ _ => .error "unused"
    persistentHash32 := fun bytes =>
      pure ((bytes.length :: bytes) ++ List.replicate (31 - bytes.length) 0)
  }
  let inputs := [("tag", Value.bytes 3 [12, 0, 0]), ("accepted", Value.bool Bool.true),
    ("count", Value.uint 65535 258)]
  let domain := [109, 100, 110, 58, 108, 104]
  let check (call : Entrypoint) (payload : List Nat) : Except String _root_.Bool := do
    let hashes := call.effects.filterMap fun effect => match effect with
      | .merkleTreeInsertHash _ hash | .merkleTreeInsertHashIndex _ hash _ => some hash
      | _ => none
    let actual ← hashes.mapM fun hash => hash.eval context inputs
    let expected := domain ++ payload
    pure (actual == List.replicate 2 ((expected.length :: expected) ++ List.replicate 19 0))
  pure ((← check appendCall [12, 0, 0, 1, 2, 1]) &&
    (← check writeCall [12, 0, 0, 1, 2, 1]) &&
    (← check defaultCall (List.replicate 6 0)))

#guard checkNestedRecordPreimages.toOption == some Bool.true

/-- ledger record field count does not match its checked layout -/
#guard_msgs (substring := true) in
noctium_contract MalformedNestedRecordLeaf where
  merkleTree claims : 2 of struct Leaf {
    tag : Bytes 3
    details : struct Meta {
      approved : Bool
      count : UInt 16
    }
  }
  entry put uses nestedMerkleInputs where
    insertLeaf claims := fields(disclose(tag), disclose(accepted))
  end
end
