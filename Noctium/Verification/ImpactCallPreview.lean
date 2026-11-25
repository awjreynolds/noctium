import Noctium.Verification.ImpactActivityPartition
import Noctium.Verification.ImpactPreviewGas

namespace Noctium.Verification.ImpactCallPreview

open ImpactActivityPartition ImpactNoopPreview ImpactPreviewGas

structure Transcript (α : Type u) where
  program : List α
  computeTime : Nat

structure CallTranscripts (α : Type u) where
  guaranteed : Option (Transcript α)
  fallible : Option (Transcript α)

private def programLength (part : Option (Transcript α)) : Nat :=
  ((part.map Transcript.program).getD []).length

/-- A present transcript consumes its operations and the skips immediately
after them. An absent transcript leaves the activity cursor unchanged. -/
def previewPartition (cost : CostModel) (part : Option (Transcript α))
    (activity : List (Option Nat)) :
    Option (Option (Transcript (PreviewEntry α)) × List (Option Nat)) :=
  match part with
  | none => some (none, activity)
  | some before => do
      let (used, remaining) ← takeInterval before.program.length activity
      let entries ← previewProgram before.program used
      let time ← checkedComputeTime cost before.computeTime entries
      pure (some ⟨entries, time⟩, remaining)

/-- Preview the guaranteed and fallible transcripts selected by the runtime.
The partition and the original compute times are inputs to this model.
Program lengths represent Rust slices and the operations represent the
admitted scalar program before any Noops have been inserted. -/
def previewCall (cost : CostModel) (call : CallTranscripts α)
    (activity : List (Option Nat)) : Option (CallTranscripts (PreviewEntry α)) := do
  if activeCount activity ≠ programLength call.guaranteed + programLength call.fallible then
    none
  else
    let (guaranteed, remaining) ← previewPartition cost call.guaranteed activity
    let (fallible, trailing) ← previewPartition cost call.fallible remaining
    if trailing.isEmpty then some ⟨guaranteed, fallible⟩ else none

/-- Each present partition keeps its active operations and receives the exact
skipped width and the sum of the checked Noop compute-time charges. -/
def PartMatches (cost : CostModel) (before : Option (Transcript α))
    (after : Option (Transcript (PreviewEntry α))) (used : List (Option Nat)) : Prop :=
  match before, after with
  | none, none => used = []
  | some before, some after =>
      activeCount used = before.program.length ∧
      activeProjection after.program = before.program ∧
      skippedWidth after.program = activityWidth used ∧
      after.computeTime = before.computeTime + addedGas cost after.program ∧
      after.computeTime ≤ u64Max
  | _, _ => False

theorem previewPartition_sound (cost : CostModel) (before : Option (Transcript α))
    (activity : List (Option Nat)) {after : Option (Transcript (PreviewEntry α))}
    {remaining : List (Option Nat)}
    (accepted : previewPartition cost before activity = some (after, remaining)) :
    ∃ used, used ++ remaining = activity ∧ PartMatches cost before after used ∧
      (before.isSome → remaining = [] ∨ ∃ rest, remaining = none :: rest) := by
  cases before with
  | none =>
      cases accepted
      exact ⟨[], rfl, rfl, by simp⟩
  | some before =>
      unfold previewPartition at accepted
      cases split : takeInterval before.program.length activity with
      | none => simp [split] at accepted
      | some interval =>
          obtain ⟨used, rest⟩ := interval
          cases previewed : previewProgram before.program used with
          | none => simp [split, previewed] at accepted
          | some entries =>
              cases charged : checkedComputeTime cost before.computeTime entries with
              | none => simp [split, previewed, charged] at accepted
              | some time =>
                  simp [split, previewed, charged] at accepted
                  obtain ⟨rfl, rfl⟩ := accepted
                  obtain ⟨whole, count, boundary⟩ := takeInterval_sound split
                  obtain ⟨_, order, width⟩ := previewProgram_success previewed
                  have sumTime : ImpactPreviewGas.computeTime cost before.computeTime entries =
                      some time := by simpa only [checkedComputeTime_eq_computeTime] using charged
                  obtain ⟨total, bounded⟩ :=
                    (computeTime_success_iff cost before.computeTime entries time).mp sumTime
                  exact ⟨used, whole, ⟨count, order, width, total, bounded⟩, fun _ => boundary⟩

/-- Successful call preview accounts for the entire schedule without moving
activity across the boundary after a present guaranteed transcript. -/
theorem previewCall_sound (cost : CostModel) (before : CallTranscripts α)
    (activity : List (Option Nat)) {after : CallTranscripts (PreviewEntry α)}
    (accepted : previewCall cost before activity = some after) :
    ∃ guaranteedActivity fallibleActivity,
      guaranteedActivity ++ fallibleActivity = activity ∧
      PartMatches cost before.guaranteed after.guaranteed guaranteedActivity ∧
      PartMatches cost before.fallible after.fallible fallibleActivity ∧
      (before.guaranteed.isSome →
        fallibleActivity = [] ∨ ∃ rest, fallibleActivity = none :: rest) := by
  unfold previewCall at accepted
  split at accepted
  · contradiction
  · cases guaranteed : previewPartition cost before.guaranteed activity with
    | none => simp [guaranteed] at accepted
    | some first =>
      obtain ⟨firstPart, remaining⟩ := first
      cases fallible : previewPartition cost before.fallible remaining with
      | none => simp [guaranteed, fallible] at accepted
      | some second =>
        obtain ⟨secondPart, trailing⟩ := second
        cases trailing with
        | cons _ _ => simp [guaranteed, fallible] at accepted
        | nil =>
          simp [guaranteed, fallible] at accepted
          subst after
          obtain ⟨firstUsed, whole, firstMatches, boundary⟩ :=
            previewPartition_sound cost before.guaranteed activity guaranteed
          obtain ⟨lastUsed, tail, lastMatches, _⟩ :=
            previewPartition_sound cost before.fallible remaining fallible
          simp only [List.append_nil] at tail
          subst remaining
          exact ⟨firstUsed, lastUsed, whole, firstMatches, lastMatches, boundary⟩

end Noctium.Verification.ImpactCallPreview
