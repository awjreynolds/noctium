import Noctium.Verification.ImpactPlanAgreement
import Noctium.Verification.ImpactPreviewBinding
import Noctium.Verification.ImpactStatementScalar
import Noctium.Verification.ImpactTranscriptSchedule

namespace Noctium.Verification.ImpactPlanStatement

open ImpactCallPreview
open ImpactNoopPreview ImpactStatementPayload

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

private def previewFor (inputs : Inputs) (operations : List NativeState.Op)
    (activity : List (Option Nat)) :
    Option (ImpactCallPreview.CallTranscripts
      (ImpactNoopPreview.PreviewEntry NativeState.Op)) := do
  let guaranteedCount := operationCount inputs.guaranteed
  let fallibleCount := operationCount inputs.fallible
  if guaranteedCount + fallibleCount != operations.length then
    none
  else
    let guaranteed := inputs.guaranteed.map fun part =>
      ⟨operations.take guaranteedCount, part.computeTime⟩
    let fallible := inputs.fallible.map fun part =>
      ⟨operations.drop guaranteedCount, part.computeTime⟩
    previewCall inputs.cost ⟨guaranteed, fallible⟩ activity

/-- Build the ledger header from the same checked operation partition and
preview used to construct the public statement. -/
def headerFor (inputs : Inputs) (operations : List NativeState.Op)
    (activity : List (Option Nat)) : Option ImpactCallStatement.Header := do
  let call ← previewFor inputs operations activity
  ImpactPreviewBinding.header inputs.metadata call inputs.communication

/-- Construct the public statement from resolved scalar operations, their
activity, and metadata from the native call before preview. -/
def publicInputs (inputs : Inputs) (operations : List NativeState.Op)
    (activity : List (Option Nat)) : Option (List NativeRelation.Scalar) := do
    let call ← previewFor inputs operations activity
    let header ← ImpactPreviewBinding.header inputs.metadata call inputs.communication
    ImpactCallStatement.publicInputs ImpactStatementScalar.opFields header call

private theorem scheduledPartitionPayload_source (encode : α → List NativeRelation.Scalar)
    (before : Option (ImpactCallPreview.Transcript α))
    {activity : List (Option Nat)} {fields : List NativeRelation.Scalar}
    (accepted : ImpactCallStatement.scheduledPartitionPayload encode before activity =
      some fields) :
    scheduledPayload encode ((before.map ImpactCallPreview.Transcript.program).getD [])
      activity = some fields := by
  cases before with
  | none =>
      simp only [ImpactCallStatement.scheduledPartitionPayload] at accepted
      split at accepted
      · simp_all [scheduledPayload]
      · contradiction
  | some before =>
      exact accepted

private theorem partMatches_activeCount (cost : ImpactPreviewGas.CostModel)
    {before : Option (ImpactCallPreview.Transcript α)}
    {after : Option (ImpactCallPreview.Transcript (ImpactNoopPreview.PreviewEntry α))}
    {activity : List (Option Nat)}
    (partProof : ImpactCallPreview.PartMatches cost before after activity) :
    activeCount activity = ((before.map ImpactCallPreview.Transcript.program).getD []).length := by
  cases before with
  | none =>
      cases after with
      | none =>
          have empty : activity = [] := partProof
          subst activity
          simp [activeCount]
      | some after => simp [ImpactCallPreview.PartMatches] at partProof
  | some before =>
      cases after with
      | none => simp [ImpactCallPreview.PartMatches] at partProof
      | some after =>
          exact partProof.2.1

private theorem partitionPayload_matches (encode : α → List NativeRelation.Scalar)
    (cost : ImpactPreviewGas.CostModel)
    {before : Option (ImpactCallPreview.Transcript α)}
    {after : Option (ImpactCallPreview.Transcript (ImpactNoopPreview.PreviewEntry α))}
    {used : List (Option Nat)}
    (partProof : ImpactCallPreview.PartMatches cost before after used) :
    ImpactCallStatement.scheduledPartitionPayload encode before used =
      some (ImpactStatementPayload.payload encode (ImpactCallStatement.partitionEntries after)) := by
  cases before with
  | none =>
      cases after with
      | none =>
          have empty : used = [] := partProof
          subst used
          rfl
      | some after => simp [ImpactCallPreview.PartMatches] at partProof
  | some before =>
      cases after with
      | none => simp [ImpactCallPreview.PartMatches] at partProof
      | some after => exact payload_of_previewProgram encode partProof.1

private theorem scheduledPayload_append (encode : α → List NativeRelation.Scalar)
    {leftProgram rightProgram : List α}
    {leftActivity rightActivity : List (Option Nat)}
    {leftFields rightFields : List NativeRelation.Scalar}
    (leftAccepted : scheduledPayload encode leftProgram leftActivity = some leftFields)
    (rightAccepted : scheduledPayload encode rightProgram rightActivity = some rightFields)
    (leftCount : activeCount leftActivity = leftProgram.length) :
    scheduledPayload encode (leftProgram ++ rightProgram) (leftActivity ++ rightActivity) =
      some (leftFields ++ rightFields) := by
  induction leftActivity generalizing leftProgram leftFields with
  | nil =>
      have programEmpty : leftProgram = [] := by
        cases leftProgram with
        | nil => rfl
        | cons operation rest => simp [activeCount] at leftCount
      subst leftProgram
      have fieldsEmpty : leftFields = [] := by
        simpa [scheduledPayload] using leftAccepted
      subst leftFields
      simpa [scheduledPayload] using rightAccepted
  | cons marker rest ih =>
      cases marker with
      | none =>
          cases leftProgram with
          | nil => simp [activeCount] at leftCount
          | cons operation program =>
              simp only [scheduledPayload, Option.map_eq_some_iff] at leftAccepted
              obtain ⟨tailFields, tailAccepted, fieldsEq⟩ := leftAccepted
              have tailCount : activeCount rest = program.length := by
                simpa [activeCount] using leftCount
              have appended := ih tailAccepted tailCount
              simp only [List.cons_append, scheduledPayload]
              rw [appended]
              change some (encode operation ++ (tailFields ++ rightFields)) = _
              rw [← List.append_assoc, fieldsEq]
      | some count =>
          simp only [scheduledPayload, Option.map_eq_some_iff] at leftAccepted
          obtain ⟨tailFields, tailAccepted, fieldsEq⟩ := leftAccepted
          have tailCount : activeCount rest = leftProgram.length := by
            simpa [activeCount] using leftCount
          have appended := ih tailAccepted tailCount
          simp only [List.cons_append, scheduledPayload]
          rw [appended]
          change some (List.replicate count NativeRelation.zero ++
            (tailFields ++ rightFields)) = _
          rw [← List.append_assoc, fieldsEq]

/-- Successful statement construction retains the exact call header and the
source-scheduled scalar payload represented by its fields. -/
theorem publicInputs_header_and_payload (inputs : Inputs)
    (operations : List NativeState.Op) (activity : List (Option Nat))
    {fields : List NativeRelation.Scalar}
    (accepted : publicInputs inputs operations activity = some fields) :
    ∃ (header : ImpactCallStatement.Header) (payload : List NativeRelation.Scalar),
      fields = [header.bindingInput, header.communicationsCommitment] ++ payload ∧
      scheduledPayload ImpactStatementScalar.opFields operations activity = some payload ∧
      headerFor inputs operations activity = some header := by
  by_cases countsMatch :
      operationCount inputs.guaranteed + operationCount inputs.fallible = operations.length
  · simp [publicInputs, previewFor, countsMatch, Bind.bind, Option.bind_eq_some_iff] at accepted
    obtain ⟨call, previewed, header, headed, statementAccepted⟩ := accepted
    let before : ImpactCallPreview.CallTranscripts NativeState.Op :=
      ⟨inputs.guaranteed.map fun part =>
          ⟨operations.take (operationCount inputs.guaranteed), part.computeTime⟩,
        inputs.fallible.map fun part =>
          ⟨operations.drop (operationCount inputs.guaranteed), part.computeTime⟩⟩
    have callPreview : previewCall inputs.cost before activity = some call := previewed
    have headerReconstructed : headerFor inputs operations activity = some header := by
      simp [headerFor, previewFor, before, countsMatch, callPreview, headed]
    obtain ⟨guaranteedActivity, fallibleActivity, activitySplit,
      guaranteedMatches, fallibleMatches, _⟩ :=
      previewCall_sound inputs.cost before activity callPreview
    let guaranteedFields := ImpactStatementPayload.payload ImpactStatementScalar.opFields
      (ImpactCallStatement.partitionEntries call.guaranteed)
    let fallibleFields := ImpactStatementPayload.payload ImpactStatementScalar.opFields
      (ImpactCallStatement.partitionEntries call.fallible)
    have layout := (ImpactCallStatement.publicInputs_success_iff
      ImpactStatementScalar.opFields header call fields).mp statementAccepted |>.1
    have guaranteedAccepted := partitionPayload_matches ImpactStatementScalar.opFields
      inputs.cost guaranteedMatches
    have fallibleAccepted := partitionPayload_matches ImpactStatementScalar.opFields
      inputs.cost fallibleMatches
    have guaranteedSource :
        ((before.guaranteed.map ImpactCallPreview.Transcript.program).getD []) =
          operations.take (operationCount inputs.guaranteed) := by
      cases h : inputs.guaranteed <;> simp [before, operationCount, h]
    have fallibleSource :
        ((before.fallible.map ImpactCallPreview.Transcript.program).getD []) =
          operations.drop (operationCount inputs.guaranteed) := by
      cases h : inputs.fallible with
      | none =>
          have countEq : operationCount inputs.guaranteed = operations.length := by
            simpa [operationCount, h] using countsMatch
          simp [before, h, countEq]
      | some part => simp [before, h]
    have guaranteedAcceptedSource := scheduledPartitionPayload_source
      ImpactStatementScalar.opFields before.guaranteed guaranteedAccepted
    have fallibleAcceptedSource := scheduledPartitionPayload_source
      ImpactStatementScalar.opFields before.fallible fallibleAccepted
    rw [guaranteedSource] at guaranteedAcceptedSource
    rw [fallibleSource] at fallibleAcceptedSource
    have guaranteedActive : activeCount guaranteedActivity =
        (operations.take (operationCount inputs.guaranteed)).length := by
      rw [← guaranteedSource]
      exact partMatches_activeCount inputs.cost guaranteedMatches
    have guaranteedActive' : activeCount guaranteedActivity =
        (operations.take (operationCount inputs.guaranteed)).length := guaranteedActive
    have payloadAccepted := scheduledPayload_append ImpactStatementScalar.opFields
      guaranteedAcceptedSource fallibleAcceptedSource guaranteedActive'
    have operationReconstruction :
        operations.take (operationCount inputs.guaranteed) ++
          operations.drop (operationCount inputs.guaranteed) = operations := by
      exact List.take_append_drop _ _
    have splitReconstruction : guaranteedActivity ++ fallibleActivity = activity :=
      activitySplit
    refine ⟨header, guaranteedFields ++ fallibleFields, ?_, ?_, ?_⟩
    · simpa [guaranteedFields, fallibleFields, List.append_assoc] using layout
    · rw [← operationReconstruction, ← splitReconstruction]
      exact payloadAccepted
    · exact headerReconstructed
  · simp [publicInputs, previewFor, countsMatch] at accepted

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
