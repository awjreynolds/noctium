import Noctium.Helpers
import Noctium.Helpers.Wire
import Noctium.Types.MerklePath

namespace Noctium.Helpers.MerklePath

private def rootFold (depth : Nat) (path initial : Term) : List Statement :=
  let steps := (List.range depth).flatMap fun level =>
    let entry := Term.project path (.vectorIndex level)
    let sibling := Term.project (Term.project entry (.field "sibling")) (.field "field")
    let goesLeft := Term.project entry (.field "goes_left")
    let current := Term.ref s!"current{level}"
    let delta := s!"delta{level}"
    -- Order both hash inputs with fixed arithmetic on the checked direction bit.
    let deltaValue := Term.binary .mul (.cast .native goesLeft)
      (.binary .sub current sibling)
    [Statement.bind delta (.scalar .native) deltaValue,
      .bind s!"current{level + 1}" (.scalar .native)
        (.bytes .transientHashNativeVector [
          .binary .add sibling (.ref delta),
          .binary .sub current (.ref delta)
        ])]
  Statement.bind "current0" (.scalar .native) initial ::
    steps ++ [.return (some (.composite Types.MerklePath.digestType
      [.ref s!"current{depth}"]))]

/-- Build a checked source helper for the no-leaf-hash root of a statically
depth-bounded canonical Merkle path. The caller supplies the encoded Bytes32
leaf. -/
def rootNoLeafHashProgram (pathId : Types.DeclId) (depth : Nat) : Program :=
  let pathType : Types.CompositeType :=
    .vector depth (.structure Types.MerklePath.pathEntryId)
  let path := Term.ref "path"
  {
    declarations := [{
      id := ⟨0, 0⟩
      name := "merklePathRootNoLeafHash"
      parameters := [⟨"leafBytes", .bytes 32⟩, ⟨"path", .native⟩]
      compositeParameters := [("path", pathType)]
      result := .composite Types.MerklePath.digestType
      body := rootFold depth path (.bytes .degradeToNative [.ref "leafBytes"])
    }]
    composites := Types.MerklePath.environment {} pathId (.bytes 32) depth
  }

/-- Build a checked root helper for one canonical typed leaf and its fixed-depth
Compact path. The generated preimage binds the literal `mdn:lh` domain to the
checked FAB leaf layout. -/
def rootTypedLeafProgram (base : Types.CompositeEnv) (pathId : Types.DeclId)
    (leafType : Types.CompositeType) (depth : Nat) : Except String Program := do
  let preimageId := pathId ++ ".LeafPreimage"
  let preimageType : Types.CompositeType := .structure preimageId
  let preimageEnvironment : Types.CompositeEnv := {
    structures := base.structures ++ [{
      id := preimageId
      fields := [
        {name := "domain", type := .bytes 6},
        {name := "leaf", type := leafType}
      ]
    }]
    enumerations := base.enumerations
  }
  let composites := Types.MerklePath.environment preimageEnvironment pathId leafType depth
  let pathType := Types.MerklePath.pathType pathId
  let pathCompiled ← (Types.compileType composites pathType).mapError (·.message)
  let leafCompiled ← (Types.compileType composites leafType).mapError (·.message)
  let digestLayout : Types.Layout := .structure Types.MerklePath.digestId [
    ("field", .scalar .nativeField)
  ]
  let pathEntryLayout : Types.Layout := .structure Types.MerklePath.pathEntryId [
    ("sibling", digestLayout),
    ("goes_left", .scalar .booleanField)
  ]
  unless pathCompiled.checked.value == .structure pathId [
      ("leaf", leafCompiled.checked.value),
      ("path", .vector depth pathEntryLayout)
    ] do
    throw "unsupported Merkle path layout"
  let preimageCompiled ← (Types.compileType composites preimageType).mapError (·.message)
  unless preimageCompiled.checked.value == .structure preimageId [
      ("domain", .bytes 6 .byteField),
      ("leaf", leafCompiled.checked.value)
    ] do
    throw "unsupported Merkle leaf preimage layout"
  let preimageOperands ← Helpers.Wire.fabDigestOperands preimageCompiled (.ref "path")
  let parameters := preimageOperands.map Prod.fst
  unless parameters.head? == some (.bytes 6) do
    throw "unsupported Merkle leaf preimage layout"
  let path := Term.project (.ref "path") (.field "path")
  let domain := Term.bytes (.bytesLiteral 6 [109, 100, 110, 58, 108, 104]) []
  let hash := Term.bytes (.fabDigest .persistentHash preimageType parameters)
    (domain :: (preimageOperands.drop 1).map Prod.snd)
  pure {
    declarations := [{
      id := ⟨0, 0⟩
      name := "merklePathRootTypedLeaf"
      parameters := [⟨"path", .native⟩]
      compositeParameters := [("path", pathType)]
      result := .composite Types.MerklePath.digestType
      body := rootFold depth path (.bytes .degradeToNative [hash])
    }]
    composites
  }

end Noctium.Helpers.MerklePath
