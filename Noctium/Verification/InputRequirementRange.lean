import Noctium.Backend.NativeExpected

namespace Noctium.Verification.InputRequirementRange

open Backend.Native

private theorem zipIdx_map_below (inputs : List InputRequirement) (start lower upper : Nat) (guard : Term)
    (before : start + inputs.length ≤ lower) :
    ((inputs.zipIdx start).map fun ((input, position) : InputRequirement × Nat) =>
      if lower ≤ position && position < upper then
        {input with activityGuard := some guard} else input) = inputs := by
  induction inputs generalizing start lower upper with
  | nil => simp
  | cons head tail ih =>
    simp only [List.length_cons] at before
    simp only [List.zipIdx_cons, List.map_cons]
    have start_lt_lower : start < lower := by omega
    have head_out : ¬ (lower ≤ start && start < upper) := by simp [Nat.not_le_of_gt start_lt_lower]
    have tail_before : start + 1 + tail.length ≤ lower := by omega
    simp only [head_out]
    simpa [Nat.add_assoc] using ih (start + 1) lower upper tail_before

private theorem zipIdx_map_inside (inputs : List InputRequirement) (start lower upper : Nat) (guard : Term)
    (afterLower : lower ≤ start) (beforeUpper : start + inputs.length ≤ upper) :
    ((inputs.zipIdx start).map fun ((input, position) : InputRequirement × Nat) =>
      if lower ≤ position && position < upper then
        {input with activityGuard := some guard} else input) =
      inputs.map fun input => {input with activityGuard := some guard} := by
  induction inputs generalizing start lower upper with
  | nil => simp
  | cons head tail ih =>
    simp only [List.length_cons] at beforeUpper
    simp only [List.zipIdx_cons, List.map_cons]
    have head_in : lower ≤ start := afterLower
    have head_before : start < upper := by omega
    have tail_lower : lower ≤ start + 1 := by omega
    have tail_upper : start + 1 + tail.length ≤ upper := by omega
    simp only [head_in, head_before]
    simpa [Nat.add_assoc] using ih (start + 1) lower upper tail_lower tail_upper

private theorem zipIdx_map_above (inputs : List InputRequirement) (start lower upper : Nat) (guard : Term)
    (after : upper ≤ start) :
    ((inputs.zipIdx start).map fun ((input, position) : InputRequirement × Nat) =>
      if lower ≤ position && position < upper then
        {input with activityGuard := some guard} else input) = inputs := by
  induction inputs generalizing start upper lower with
  | nil => simp
  | cons head tail ih =>
    simp only [List.zipIdx_cons, List.map_cons]
    have start_not_lt_upper : ¬ start < upper := Nat.not_lt.mpr after
    have head_out : ¬ (lower ≤ start && start < upper) := by simp [start_not_lt_upper]
    have tail_after : upper ≤ start + 1 := by omega
    simp only [head_out]
    simpa [Nat.add_assoc] using ih (start + 1) lower upper tail_after

/-- Attach one activity guard to exactly the requirements in a source block.
The prefix and suffix retain their original requirements. -/
theorem attach_guard (pre block suffix : List InputRequirement) (guard : Term) :
    ((pre ++ block ++ suffix).zipIdx.map fun ((input, position) : InputRequirement × Nat) =>
      if pre.length ≤ position && position < pre.length + block.length then
        {input with activityGuard := some guard} else input) =
      pre ++ (block.map fun input => {input with activityGuard := some guard}) ++ suffix := by
  rw [show pre ++ block ++ suffix = pre ++ (block ++ suffix) by simp [List.append_assoc]]
  rw [List.zipIdx_append]
  simp only [List.map_append]
  rw [List.zipIdx_append]
  simp only [List.map_append]
  have pre_eq :
      (pre.zipIdx.map fun ((input, position) : InputRequirement × Nat) =>
        if pre.length ≤ position && position < pre.length + block.length then
          {input with activityGuard := some guard} else input) = pre := by
    simpa using zipIdx_map_below pre 0 pre.length (pre.length + block.length) guard (by omega)
  have block_eq :
      ((block.zipIdx pre.length).map fun ((input, position) : InputRequirement × Nat) =>
        if pre.length ≤ position && position < pre.length + block.length then
          {input with activityGuard := some guard} else input) =
        block.map fun input => {input with activityGuard := some guard} := by
    simpa [Nat.add_assoc] using
      zipIdx_map_inside block pre.length pre.length (pre.length + block.length) guard
        (Nat.le_refl _) (by omega)
  have suffix_eq :
      ((suffix.zipIdx (pre.length + block.length)).map
        fun ((input, position) : InputRequirement × Nat) =>
          if pre.length ≤ position && position < pre.length + block.length then
            {input with activityGuard := some guard} else input) = suffix := by
    simpa using zipIdx_map_above suffix (pre.length + block.length) pre.length
      (pre.length + block.length) guard (Nat.le_refl _)
  simp only [Nat.zero_add]
  rw [pre_eq, block_eq, suffix_eq]
  simp [List.append_assoc]
