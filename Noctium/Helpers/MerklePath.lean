import Noctium.Helpers
import Noctium.Types.MerklePath

namespace Noctium.Helpers.MerklePath

/-- Build a checked source helper for the no-leaf-hash root of a statically
depth-bounded canonical Merkle path. The caller supplies the encoded Bytes32
leaf. -/
def rootNoLeafHashProgram (pathId : Types.DeclId) (depth : Nat) : Program :=
  let pathType : Types.CompositeType :=
    .vector depth (.structure Types.MerklePath.pathEntryId)
  let path := Term.ref "path"
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
  let body := .bind "current0" (.scalar .native) (.bytes .degradeToNative [.ref "leafBytes"]) ::
    steps ++ [.return (some (.ref s!"current{depth}"))]
  {
    declarations := [{
      id := ⟨0, 0⟩
      name := "merklePathRootNoLeafHash"
      parameters := [⟨"leafBytes", .bytes 32⟩, ⟨"path", .native⟩]
      compositeParameters := [("path", pathType)]
      result := .scalar .native
      body
    }]
    composites := Types.MerklePath.environment {} pathId (.bytes 32) depth
  }

end Noctium.Helpers.MerklePath
