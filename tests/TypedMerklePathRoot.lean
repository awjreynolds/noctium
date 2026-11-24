import Noctium.Frontend
import Noctium.Types.MerklePath
import Noctium.Helpers.MerklePath
import Noctium.Backend.NativeExpected
import Noctium.Backend.Zkir

open scoped Noctium
open Noctium
open Noctium.Types

private def leafMarkerId : DeclId := "TypedMerklePathRoot.LeafMarker"
private def mixedLeafId : DeclId := "TypedMerklePathRoot.MixedMerkleLeaf"
private def merklePathId : DeclId := "TypedMerklePathRoot.Path"

private def mixedLeafEnvironment : CompositeEnv := {
  enumerations := [{id := leafMarkerId, variants := [{name := "Only"}]}]
  structures := [{id := mixedLeafId, fields := [
    {name := "tag", type := .bytes 3},
    {name := "details", type := .tuple [
      .scalar .bool, .scalar (.uint 65535), .enumeration leafMarkerId
    ]}
  ]}]
}

private def mixedLeafType : CompositeType := .structure mixedLeafId

private def typedMerklePathRootResult : Except String Helpers.Program :=
  Helpers.MerklePath.rootTypedLeafProgram mixedLeafEnvironment merklePathId mixedLeafType 2

private def typedMerklePathRootProgram : Helpers.Program :=
  typedMerklePathRootResult.toOption.getD {}

private def typedPathWire : Helpers.Wire.Codec := {
  payload := MerklePath.pathType merklePathId
  frameBytes := 73
  composites := typedMerklePathRootProgram.composites
}

#guard match typedMerklePathRootResult with
  | .ok program =>
      match program.declarations with
      | [declaration] =>
          declaration.parameters.map (fun parameter => (parameter.name, parameter.ty)) ==
            [("path", .native)] &&
          declaration.compositeParameters == [("path", MerklePath.pathType merklePathId)] &&
          (Helpers.checkDeclaration program declaration).isOk
      | _ => Bool.false
  | .error _ => Bool.false

#guard match Helpers.MerklePath.rootTypedLeafProgram mixedLeafEnvironment
    "TypedMerklePathRoot.DepthThree" mixedLeafType 3 with
  | .ok program =>
      match program.declarations with
      | [declaration] => (Helpers.checkDeclaration program declaration).isOk
      | _ => Bool.false
  | .error _ => Bool.false

#guard match Helpers.MerklePath.rootTypedLeafProgram {}
    "TypedMerklePathRoot.UnitPath" .unit 2 with
  | .ok program =>
      match program.declarations with
      | [declaration] => (Helpers.checkDeclaration program declaration).isOk
      | _ => Bool.false
  | .error _ => Bool.false

private def unsupportedLeafEnvironment : CompositeEnv := {
  enumerations := [{id := "TypedMerklePathRoot.PayloadMarker", variants := [{
    name := "Payload"
    fields := [{name := "flag", type := .scalar .bool}]
  }]}]
  structures := [{id := "TypedMerklePathRoot.UnsupportedLeaf", fields := [
    {name := "marker", type := .enumeration "TypedMerklePathRoot.PayloadMarker"}
  ]}]
}

#guard match Helpers.MerklePath.rootTypedLeafProgram unsupportedLeafEnvironment
    "TypedMerklePathRoot.UnsupportedPath" (.structure "TypedMerklePathRoot.UnsupportedLeaf") 2 with
  | .error "unsupported mixed FAB field layout" => Bool.true
  | _ => Bool.false

noctium_witness proofPath() : Payload typedPathWire

noctium_witness_circuit typedMerklePathRootInputs using typedPathWire
    with typedMerklePathRootProgram where
  let proof := witness proofPath()
  output root := disclose(invoke(merklePathRootTypedLeaf, [proof]))
end

/- error: undisclosed private -/
#guard_msgs (substring := true) in
noctium_witness_circuit rejectsUndisclosedTypedMerklePathRoot using typedPathWire
    with typedMerklePathRootProgram where
  let proof := witness proofPath()
  output root := invoke(merklePathRootTypedLeaf, [proof])
end

noctium_contract TypedMerklePathRootSource where
  entry root uses typedMerklePathRootInputs where
    return root
  end
end

private def typedMerklePathRootEntry : Entrypoint :=
  match TypedMerklePathRootSource.entrypoints with
  | ep :: _ => ep
  | _ => {name := "missing", circuit := {name := "missing"}}

#guard match Backend.Native.expectedEntrypoint TypedMerklePathRootSource.state
    typedMerklePathRootEntry with
  | .ok _ => Bool.true
  | .error _ => Bool.false

#guard match Backend.Zkir.lowerEntrypoint TypedMerklePathRootSource.state
    typedMerklePathRootEntry with
  | .ok _ => Bool.true
  | .error _ => Bool.false
