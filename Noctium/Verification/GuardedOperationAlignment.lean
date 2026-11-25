import Noctium.Verification.GuardedPlanActivity
import Noctium.Verification.GuardedEffectEvaluation

namespace Noctium.Verification.GuardedOperationAlignment
open Backend
open GenericStateCheckedReadTrace
open GuardedPlanActivity

/-- Expand each source guard across the operations emitted by its effect. -/
def effectOperationGuards (guards : List (Option (Expr .bool)))
    (items : List (Effect × Nat)) (chunks : List (List Impact.Op)) :
    List (Option (Expr .bool)) :=
  (items.zip chunks).flatMap fun (item, chunk) =>
    List.replicate chunk.length (guards[item.2]?.getD none)

/-- The accepted effect chunks account for every operation guard after an
aligned prefix. They also preserve alignment with the final operation list. -/
theorem operationGuards_of_chunks {state : List StateDecl}
    {guards : List (Option (Expr .bool))} {items : List (Effect × Nat)}
    {before plan : Impact.Plan} {offsets : List Nat}
    {chunks : List (List Impact.Op)}
    (scope : GuardedScalarReadEffects guards items)
    (chunksShape : GuardedEffectEvaluation.GuardedEffectOperationChunks state guards
      items before plan offsets chunks)
    (aligned : (operationGuards before).length = before.operations.length) :
    operationGuards plan = operationGuards before ++
        effectOperationGuards guards items chunks ∧
      (operationGuards plan).length = plan.operations.length := by
  induction chunksShape with
  | nil before =>
    exact ⟨by simp [effectOperationGuards], aligned⟩
  | @cons item rest before next plan offsets chunk chunks step operationPrefix tail ih =>
    have headScope := scope item (by simp)
    obtain ⟨exactChunk, exactOperations, exactGuards⟩ :=
      GuardedPlanActivity.appendActivity_chunk state item.1
        (guards[item.2]?.getD none) headScope before next aligned step
    have chunkEq : exactChunk = chunk := by
      apply List.append_cancel_left
      calc
        before.operations ++ exactChunk = next.operations := exactOperations.symm
        _ = before.operations ++ chunk := operationPrefix
    have nextAligned : (operationGuards next).length = next.operations.length := by
      rw [exactGuards, exactOperations]
      simp [List.length_append, List.length_replicate, aligned]
    have tailScope : GuardedScalarReadEffects guards rest := by
      intro nextItem member
      exact scope nextItem (List.mem_cons_of_mem item member)
    obtain ⟨tailGuards, resultAligned⟩ := ih tailScope nextAligned
    constructor
    · rw [tailGuards, exactGuards, chunkEq]
      simp [effectOperationGuards, List.append_assoc]
    · exact resultAligned

end Noctium.Verification.GuardedOperationAlignment
