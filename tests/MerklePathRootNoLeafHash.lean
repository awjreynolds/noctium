import Noctium.Frontend
import Noctium.Types.MerklePath
import Noctium.Helpers.MerklePath
import Noctium.Backend.NativeExpected
import Noctium.Backend.Zkir

open scoped Noctium
open Noctium
open Noctium.Types

private def merklePathId : DeclId := "MerklePathRootNoLeafHash.Path"

private def merklePathEnvironment : CompositeEnv :=
  MerklePath.environment {} merklePathId (.bytes 32) 2

private def merklePathType : CompositeType := MerklePath.pathType merklePathId

private def merklePathWire : Helpers.Wire.Codec := {
  payload := merklePathType
  frameBytes := 98
  composites := merklePathEnvironment
}

private def merkleLeafWire : Helpers.Wire.Codec := {
  payload := .bytes 32
  frameBytes := 32
}

private def merklePathRootNoLeafHashProgram : Helpers.Program :=
  Helpers.MerklePath.rootNoLeafHashProgram merklePathId 2

#guard
  let helper := Helpers.MerklePath.rootNoLeafHashProgram merklePathId 3
  match helper.declarations with
  | [declaration] => (Helpers.checkDeclaration helper declaration).isOk
  | _ => Bool.false

noctium_witness proofPath() : Payload merklePathWire

noctium_witness_circuit merklePathRootInputs using merklePathWire, merkleLeafWire
    with merklePathRootNoLeafHashProgram where
  let proof := witness proofPath()
  let encodedLeaf := encode(merkleLeafWire, field(proof, leaf))
  let path := field(proof, path)
  let currentRoot := invoke(merklePathRootNoLeafHash, [encodedLeaf, path])
  output candidateRoot : Native := disclose(currentRoot)
end

/- error: undisclosed private -/
#guard_msgs (substring := true) in
noctium_witness_circuit rejectsUndisclosedMerklePathRoot
    using merklePathWire, merkleLeafWire with merklePathRootNoLeafHashProgram where
  let proof := witness proofPath()
  let encodedLeaf := encode(merkleLeafWire, field(proof, leaf))
  let path := field(proof, path)
  let currentRoot := invoke(merklePathRootNoLeafHash, [encodedLeaf, path])
  output candidateRoot : Native := currentRoot
end

noctium_contract MerklePathRootNoLeafHashSource where
  entry digest uses merklePathRootInputs where
    return root : Native := candidateRoot
  end
end

private def merklePathRootEntry : Entrypoint :=
  match MerklePathRootNoLeafHashSource.entrypoints with
  | ep :: _ => ep
  | _ => {name := "missing", circuit := {name := "missing"}}

#guard match Backend.Native.expectedEntrypoint MerklePathRootNoLeafHashSource.state
    merklePathRootEntry with
  | .ok _ => Bool.true
  | .error _ => Bool.false

#guard match Backend.Zkir.lowerEntrypoint MerklePathRootNoLeafHashSource.state
    merklePathRootEntry with
  | .ok _ => Bool.true
  | .error _ => Bool.false

private def validMerklePathValue : AggregateValue :=
  MerklePath.pathValue merklePathId (.bytes (List.range 32)) [
    MerklePath.pathEntryValue 17 Bool.true,
    MerklePath.pathEntryValue 29 Bool.false
  ]

private def malformedMerklePathBool : AggregateValue :=
  MerklePath.pathValue merklePathId (.bytes (List.range 32)) [
    .structure MerklePath.pathEntryId [
      ("sibling", MerklePath.digestValue 17),
      ("goes_left", .scalar .bool 2)
    ],
    MerklePath.pathEntryValue 29 Bool.false
  ]

private def malformedMerklePathShape : AggregateValue :=
  MerklePath.pathValue merklePathId (.bytes (List.range 32)) [
    MerklePath.pathEntryValue 17 Bool.true
  ]

#guard match Types.compileType merklePathEnvironment merklePathType with
  | .ok compiled =>
      match Types.checkValue compiled validMerklePathValue with
      | .ok checked => checked.leaves == List.range 32 ++ [17, 1, 29, 0]
      | .error _ => Bool.false
  | .error _ => Bool.false

#guard match Types.compileType merklePathEnvironment merklePathType with
  | .ok compiled =>
      match Types.checkValue compiled malformedMerklePathBool with
      | .error _ => Bool.true
      | .ok _ => Bool.false
  | .error _ => Bool.false

#guard match Types.compileType merklePathEnvironment merklePathType with
  | .ok compiled =>
      match Types.checkValue compiled malformedMerklePathShape with
      | .error "aggregate vector length mismatch" => Bool.true
      | _ => Bool.false
  | .error _ => Bool.false
