import Noctium.Verification.ImpactNoopPreview

namespace Noctium.Verification.ImpactActivityPartition

open ImpactNoopPreview

/--
Take one activity interval containing exactly `count` active markers. Skip
markers before, between, and after those active markers belong to the interval.
The result stops immediately before the next active marker. With `count = 0`,
this takes only the leading skips.
-/
private def takeIntervalAux : Nat → List (Option Nat) →
    Option (List (Option Nat) × List (Option Nat))
  | 0, [] => some ([], [])
  | 0, none :: rest => some ([], none :: rest)
  | 0, some width :: rest =>
      (takeIntervalAux 0 rest).map fun (interval, suffix) =>
        (some width :: interval, suffix)
  | _ + 1, [] => none
  | count + 1, none :: rest =>
      (takeIntervalAux count rest).map fun (interval, suffix) =>
        (none :: interval, suffix)
  | count + 1, some width :: rest =>
      (takeIntervalAux (count + 1) rest).map fun (interval, suffix) =>
        (some width :: interval, suffix)

/-- Cursor prefix selection for one Rust transcript activity interval. -/
def takeInterval (count : Nat) (activity : List (Option Nat)) :
    Option (List (Option Nat) × List (Option Nat)) :=
  takeIntervalAux count activity

theorem activeCount_append (left right : List (Option Nat)) :
    activeCount (left ++ right) = activeCount left + activeCount right := by
  induction left with
  | nil => simp [activeCount]
  | cons entry rest ih =>
      cases entry <;> simp [activeCount, ih] <;> omega

theorem takeInterval_sound {count : Nat} {activity interval suffix : List (Option Nat)}
    (taken : takeInterval count activity = some (interval, suffix)) :
    interval ++ suffix = activity ∧
    activeCount interval = count ∧
    (suffix = [] ∨ ∃ rest : List (Option Nat), suffix = none :: rest) := by
  induction activity generalizing count interval suffix with
  | nil =>
      cases count <;> simp_all [takeInterval, takeIntervalAux, activeCount]
  | cons entry rest ih =>
      cases entry with
      | none =>
          cases count with
          | zero =>
              simp_all [takeInterval, takeIntervalAux, activeCount]
              right
              exact ⟨rest, taken.2.symm⟩
          | succ count =>
              simp only [takeInterval, takeIntervalAux, Option.map_eq_some_iff] at taken
              rcases taken with ⟨⟨tailInterval, tailSuffix⟩, tailTaken, rfl, rfl⟩
              obtain ⟨recompose, countEq, tailEnd⟩ := ih tailTaken
              refine ⟨?_, ?_, ?_⟩
              · simp [recompose]
              · simp [activeCount, countEq]
              · exact tailEnd
      | some width =>
          cases count with
          | zero =>
              simp only [takeInterval, takeIntervalAux, Option.map_eq_some_iff] at taken
              rcases taken with ⟨⟨tailInterval, tailSuffix⟩, tailTaken, rfl, rfl⟩
              obtain ⟨recompose, countEq, tailEnd⟩ := ih tailTaken
              refine ⟨?_, ?_, ?_⟩
              · simp [recompose]
              · exact countEq
              · exact tailEnd
          | succ count =>
              simp only [takeInterval, takeIntervalAux, Option.map_eq_some_iff] at taken
              rcases taken with ⟨⟨tailInterval, tailSuffix⟩, tailTaken, rfl, rfl⟩
              obtain ⟨recompose, countEq, tailEnd⟩ := ih tailTaken
              refine ⟨?_, ?_, ?_⟩
              · simp [recompose]
              · exact countEq
              · exact tailEnd

theorem takeInterval_complete {count : Nat} {activity : List (Option Nat)}
    (fits : count ≤ activeCount activity) :
    ∃ interval suffix, takeInterval count activity = some (interval, suffix) := by
  induction activity generalizing count with
  | nil =>
      have countZero : count = 0 := by
        simpa [activeCount] using fits
      subst count
      exact ⟨[], [], rfl⟩
  | cons entry rest ih =>
      cases entry with
      | none =>
          cases count with
          | zero => exact ⟨[], none :: rest, rfl⟩
          | succ count =>
              have fitsRest : count ≤ activeCount rest := by
                simpa [activeCount] using fits
              obtain ⟨interval, suffix, taken⟩ := ih fitsRest
              have takenAux : takeIntervalAux count rest = some (interval, suffix) := by
                simpa [takeInterval] using taken
              exact ⟨none :: interval, suffix, by
                simp [takeInterval, takeIntervalAux, takenAux]⟩
      | some width =>
          cases count with
          | zero =>
              obtain ⟨interval, suffix, taken⟩ := ih (Nat.zero_le _)
              have takenAux : takeIntervalAux 0 rest = some (interval, suffix) := by
                simpa [takeInterval] using taken
              exact ⟨some width :: interval, suffix, by
                simp [takeInterval, takeIntervalAux, takenAux]⟩
          | succ count =>
              have fitsRest : count + 1 ≤ activeCount rest := by
                simpa [activeCount] using fits
              obtain ⟨interval, suffix, taken⟩ := ih fitsRest
              have takenAux : takeIntervalAux (count + 1) rest = some (interval, suffix) := by
                simpa [takeInterval] using taken
              exact ⟨some width :: interval, suffix, by
                simp [takeInterval, takeIntervalAux, takenAux]⟩

end Noctium.Verification.ImpactActivityPartition
