import Noctium.Verification.GuardedReadDescriptorTrace
import Noctium.Verification.GuardedEffectEvaluation
import Noctium.Verification.GuardedPlanAssertions

namespace Noctium.Verification.GuardedEffectReadTape

open Backend
open GenericStateCheckedReadTrace
open GuardedReadDescriptorTrace
open GuardedEffectEvaluation
open GuardedPlanAssertions

/-- One accepted source effect's operation and public read chunks. -/
inductive GuardedEffectReadChunkTrace (state : List StateDecl)
    (guards : List (Option (Expr .bool))) :
    List (Effect × Nat) → Impact.Plan → Impact.Plan → List Nat →
      List (List Impact.Op) → List (List Impact.Read) → Prop where
  | nil (before : Impact.Plan) :
      GuardedEffectReadChunkTrace state guards [] before before [] [] []
  | cons {item : Effect × Nat} {rest : List (Effect × Nat)}
      {before next result : Impact.Plan} {offsets : List Nat}
      {operationChunk : List Impact.Op} {operationChunks : List (List Impact.Op)}
      {readChunk : List Impact.Read} {readChunks : List (List Impact.Read)}
      (accepted : Impact.appendEffectWithActivity state item.1
        (guards[item.2]?.getD none) before = .ok next)
      (operationSuffix : next.operations = before.operations ++ operationChunk)
      (readSuffix : next.reads = before.reads ++ readChunk)
      (metadataExact : readChunk.map readMetadata =
        effectReadChunk item.1 before.reads.length)
      (guardExact : ∀ read ∈ readChunk,
        read.guard = guards[item.2]?.getD none)
      (assertionSuffix : next.guards = before.guards ++
        guardedEffectAssertionChunk (guards[item.2]?.getD none) item.1 before.reads.length)
      (tail : GuardedEffectReadChunkTrace state guards rest next result offsets
        operationChunks readChunks) :
      GuardedEffectReadChunkTrace state guards (item :: rest) before result
        (next.operations.length :: offsets) (operationChunk :: operationChunks)
        (readChunk :: readChunks)

private theorem accepted_step_read_chunk (state : List StateDecl) (guards : List (Option (Expr .bool)))
    (item : Effect × Nat) (before after : Impact.Plan)
    (scope : GuardedScalarReadEffect (guards[item.2]?.getD none) item.1)
    (accepted : Impact.appendEffectWithActivity state item.1
      (guards[item.2]?.getD none) before = .ok after) :
    ∃ readChunk : List Impact.Read,
      after.reads = before.reads ++ readChunk ∧
      readChunk.map readMetadata = effectReadChunk item.1 before.reads.length ∧
      (∀ read ∈ readChunk, read.guard = guards[item.2]?.getD none) := by
  obtain ⟨readChunk, readSuffix, descriptorFacts⟩ :=
    GuardedReadDescriptorTrace.appendEffectWithActivity_guarded_reads_append
      state item.1 (guards[item.2]?.getD none) scope before after accepted
  have metadata := GenericStateCheckedReadTrace.appendEffectWithActivity_guarded_read_chunk
    state item.1 (guards[item.2]?.getD none) scope before after accepted
  change after.reads.map readMetadata =
      before.reads.map readMetadata ++ effectReadChunk item.1 before.reads.length at metadata
  rw [readSuffix, List.map_append] at metadata
  have metadataExact := List.append_cancel_left metadata
  exact ⟨readChunk, readSuffix, metadataExact,
    fun read present => (descriptorFacts read present).2⟩

/-- The accepted operation chunks and scoped read effects determine a
descriptor chunk for every source effect, with one shared live ordinal. -/
theorem of_operation_chunks {state : List StateDecl}
    {guards : List (Option (Expr .bool))} {items : List (Effect × Nat)}
    {initial result : Impact.Plan} {offsets : List Nat}
    {operationChunks : List (List Impact.Op)}
    (scope : GuardedScalarReadEffects guards items)
    (operationTrace : GuardedEffectOperationChunks state guards items initial result
      offsets operationChunks) :
    ∃ descriptorChunks,
      GuardedEffectReadChunkTrace state guards items initial result offsets
        operationChunks descriptorChunks := by
  induction operationTrace with
  | nil before => exact ⟨[], .nil before⟩
  | @cons item rest before next result offsets operationChunk operationChunks
      accepted operationSuffix tail ih =>
    have headScope : GuardedScalarReadEffect
        (guards[item.2]?.getD none) item.1 := scope item (by simp)
    have tailScope : GuardedScalarReadEffects guards rest := by
      intro found member
      exact scope found (List.mem_cons_of_mem item member)
    obtain ⟨readChunk, readSuffix, metadataExact, guardExact⟩ :=
      accepted_step_read_chunk state guards item before next headScope accepted
    have assertionSuffix := GuardedPlanAssertions.appendEffectWithActivity_guarded_assertion_chunk
      state item.1 (guards[item.2]?.getD none) headScope before next accepted
    obtain ⟨readChunks, tailTrace⟩ := ih tailScope
    exact ⟨readChunk :: readChunks, .cons accepted operationSuffix readSuffix
      metadataExact guardExact assertionSuffix tailTrace⟩

/-- The per-effect descriptor chunks preserve the accepted plan's read order. -/
theorem read_descriptors_append
    {state : List StateDecl} {guards : List (Option (Expr .bool))}
    {items : List (Effect × Nat)} {initial result : Impact.Plan}
    {offsets : List Nat} {operationChunks : List (List Impact.Op)}
    {descriptorChunks : List (List Impact.Read)}
    (trace : GuardedEffectReadChunkTrace state guards items initial result offsets
      operationChunks descriptorChunks) :
    result.reads = initial.reads ++ descriptorChunks.flatten := by
  induction trace with
  | nil before => simp
  | @cons item rest before next result offsets operationChunk operationChunks
      readChunk readChunks accepted operationSuffix readSuffix metadataExact guardExact
      assertionSuffix tail ih =>
    calc
      result.reads = next.reads ++ readChunks.flatten := ih
      _ = (before.reads ++ readChunk) ++ readChunks.flatten := by rw [readSuffix]
      _ = before.reads ++ (readChunk :: readChunks).flatten := by simp [List.append_assoc]

/-- Earlier source assertions remain in the final production plan. This keeps
generated requireAbsent assertions available to authenticate their read rows. -/
theorem guard_subset
    {state : List StateDecl} {guards : List (Option (Expr .bool))}
    {items : List (Effect × Nat)} {initial result : Impact.Plan}
    {offsets : List Nat} {operationChunks : List (List Impact.Op)}
    {descriptorChunks : List (List Impact.Read)}
    (trace : GuardedEffectReadChunkTrace state guards items initial result offsets
      operationChunks descriptorChunks) :
    ∀ assertion ∈ initial.guards, assertion ∈ result.guards := by
  induction trace with
  | nil before => exact fun _ member => member
  | @cons item rest before next result offsets operationChunk operationChunks
      readChunk readChunks accepted operationSuffix readSuffix metadataExact guardExact
      assertionSuffix tail ih =>
    intro assertion member
    have inNext : assertion ∈ next.guards := by
      rw [assertionSuffix]
      exact List.mem_append_left _ member
    exact ih assertion inNext
