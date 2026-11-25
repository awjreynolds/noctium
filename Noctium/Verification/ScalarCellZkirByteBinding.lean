import Noctium.Verification.ArtifactBytes
import Noctium.Verification.NativeRelationJson

namespace Noctium.Verification.ScalarCellZkirByteBinding

open Lean

/-- Parse exact artifact bytes and apply the strict scalar-call decoder. -/
def decodeScalarCallBytes (bytes : ArtifactBytes.Bytes) : Except String NativeRelationJson.ScalarCall := do
  let json ← ArtifactBytes.parse bytes
  NativeRelationJson.decodeScalarCall json

/-- A successfully decoded call comes from the parser-selected tree. -/
theorem checked_tree {bytes : ArtifactBytes.Bytes} {call : NativeRelationJson.ScalarCall}
    (decoded : decodeScalarCallBytes bytes = .ok call) :
    ArtifactBytes.parse bytes = .ok (ArtifactBytes.tree bytes) ∧
      NativeRelationJson.decodeScalarCall (ArtifactBytes.tree bytes) = .ok call := by
  unfold decodeScalarCallBytes at decoded
  exact ArtifactBytes.validated_tree NativeRelationJson.decodeScalarCall bytes call decoded

end Noctium.Verification.ScalarCellZkirByteBinding
