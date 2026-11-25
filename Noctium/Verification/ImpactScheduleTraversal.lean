import Lean

namespace Noctium.Verification.ImpactScheduleTraversal

universe u v

/-- Pointwise eventual agreement on every member of a finite schedule yields
one fuel bound for the whole `Option` traversal. -/
theorem mapM_eventually_agrees {α : Type u} {β : Type v}
    (items : List α) (left right : Nat → α → Option β)
    (pointwise : ∀ item ∈ items,
      ∃ minimum, ∀ fuel, minimum ≤ fuel → left fuel item = right fuel item) :
    ∃ minimum, ∀ fuel, minimum ≤ fuel →
      items.mapM (left fuel) = items.mapM (right fuel) := by
  induction items with
  | nil =>
      exact ⟨0, fun _ _ => rfl⟩
  | cons item rest ih =>
      obtain ⟨headMinimum, headAgrees⟩ := pointwise item (by simp)
      have tailPointwise : ∀ value ∈ rest,
          ∃ minimum, ∀ fuel, minimum ≤ fuel → left fuel value = right fuel value := by
        intro value member
        exact pointwise value (List.mem_cons_of_mem _ member)
      obtain ⟨tailMinimum, tailAgrees⟩ := ih tailPointwise
      refine ⟨max headMinimum tailMinimum, ?_⟩
      intro fuel enough
      have headEq := headAgrees fuel (by omega)
      have tailEq := tailAgrees fuel (by omega)
      simp only [List.mapM_cons, headEq, tailEq]

end Noctium.Verification.ImpactScheduleTraversal
