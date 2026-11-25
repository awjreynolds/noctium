import Noctium.Verification.ImpactPlanAgreement
import Noctium.Verification.ImpactPreviewBinding
import Noctium.Verification.ImpactStatementScalar
import Noctium.Verification.ImpactTranscriptSchedule

namespace Noctium.Verification.ImpactPlanStatement

open ImpactCallPreview

/-- Length and compute cost of a native partition before skipped fields are inserted. -/
structure Partition where
  operationCount : Nat
  computeTime : Nat

/-- Native inputs to the scalar statement model. The plan does not select
partition lengths, initial costs, effects, call identity, or commitments. -/
structure Inputs where
  cost : ImpactPreviewGas.CostModel
  metadata : ImpactPreviewBinding.Metadata
  communication : NativeRelation.Scalar
  guaranteed : Option Partition
  fallible : Option Partition

private def operationCount (partition : Option Partition) : Nat :=
  (partition.map Partition.operationCount).getD 0

/-- Construct the public statement from resolved scalar operations, their
activity, and metadata from the native call before preview. -/
def publicInputs (inputs : Inputs) (operations : List NativeState.Op)
    (activity : List (Option Nat)) : Option (List NativeRelation.Scalar) := do
  let guaranteedCount := operationCount inputs.guaranteed
  let fallibleCount := operationCount inputs.fallible
  if guaranteedCount + fallibleCount != operations.length then
    none
  else
    let guaranteed := inputs.guaranteed.map fun part =>
      ⟨operations.take guaranteedCount, part.computeTime⟩
    let fallible := inputs.fallible.map fun part =>
      ⟨operations.drop guaranteedCount, part.computeTime⟩
    let call ← previewCall inputs.cost ⟨guaranteed, fallible⟩ activity
    let header ← ImpactPreviewBinding.header inputs.metadata call inputs.communication
    ImpactCallStatement.publicInputs ImpactStatementScalar.opFields header call

/-- Read the scalar schedule from exact artifact bytes and construct its
public statement under the supplied native call metadata. -/
def fromBytes (fuel : Nat) (ctx : EvalContext) (env : EvalEnv)
    (keyWidth : Nat → Option Nat) (bytes : ArtifactBytes.Bytes) (inputs : Inputs) :
    Option (List NativeRelation.Scalar) := do
  let raw ← (ArtifactBytes.parse bytes).toOption
  let operations ← ImpactPlanAgreement.evaluatePlan fuel ctx env raw
  let activity ← ImpactTranscriptSchedule.evaluateSchedule fuel ctx env keyWidth raw
  publicInputs inputs operations activity

end Noctium.Verification.ImpactPlanStatement
