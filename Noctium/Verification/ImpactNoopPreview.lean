import Lean

universe u

namespace Noctium.Verification.ImpactNoopPreview

/-!
Each call models one complete transcript program interval. Its activity slice
includes leading and trailing skips, and its `none` entries must match exactly
that program's operation count. The runtime resets its Noop merge accumulator
for each transcript call, so this model does not carry a pending run across
program boundaries.
-/

/-- The largest skip count accepted by the Rust transcript preview. -/
def u32Max : Nat := 2 ^ 32 - 1

/-- An abstract transcript operation, or a Noop inserted from activity. -/
inductive PreviewEntry (α : Type u) where
  | active (operation : α)
  | noop (count : Nat)
  deriving Repr

/-- The active operations keep their original order after padding. -/
def activeProjection : List (PreviewEntry α) → List α
  | [] => []
  | .active operation :: rest => operation :: activeProjection rest
  | .noop _ :: rest => activeProjection rest

/-- Total width of the inserted Noop entries. -/
def skippedWidth : List (PreviewEntry α) → Nat
  | [] => 0
  | .active _ :: rest => skippedWidth rest
  | .noop count :: rest => count + skippedWidth rest

/-- Number of active transcript operations requested by a schedule. -/
def activeCount : List (Option Nat) → Nat
  | [] => 0
  | none :: rest => activeCount rest + 1
  | some _ :: rest => activeCount rest

theorem activeCount_eq_filter_length (activity : List (Option Nat)) :
    activeCount activity = (activity.filter Option.isNone).length := by
  induction activity with
  | nil => simp [activeCount]
  | cons entry rest ih =>
      cases entry <;> simp [activeCount, ih]

/-- Total scheduled Noop width, before insertion. -/
def activityWidth : List (Option Nat) → Nat
  | [] => 0
  | none :: rest => activityWidth rest
  | some count :: rest => count + activityWidth rest

/-- Width of the leading contiguous run of scheduled Noops. -/
def leadingSkipWidth : List (Option Nat) → Nat
  | some count :: rest => count + leadingSkipWidth rest
  | none :: _ => 0
  | [] => 0

/--
Every count and every contiguous Noop run must fit in u32. Rust merges
adjacent Noops with checked addition, so this predicate also captures the
overflow rejection for that merge. The expansion below leaves the run
unmerged as an explicit first stage.
-/
def skipRunsFit : List (Option Nat) → Bool
  | [] => true
  | none :: rest => skipRunsFit rest
  | some count :: rest =>
      decide (count ≤ u32Max) &&
        (decide (leadingSkipWidth (some count :: rest) ≤ u32Max) &&
          skipRunsFit rest)

/--
Expand one complete transcript interval. `none` consumes exactly one source
operation. `some n` consumes no source operation and inserts a Noop of width
`n`. The schedule must account for every source operation and contain no extra
active entries.
-/
private def expandProgramRaw : List α → List (Option Nat) → Option (List (PreviewEntry α))
  | [], [] => some []
  | _ :: _, [] => none
  | program, some count :: activity =>
      if count ≤ u32Max then
        (expandProgramRaw program activity).map
          (fun tail => PreviewEntry.noop count :: tail)
      else
        none
  | operation :: program, none :: activity =>
      (expandProgramRaw program activity).map
        (fun tail => PreviewEntry.active operation :: tail)
  | [], none :: _ => none

/--
Checked single-interval padding. Adjacent scheduled Noops remain separate in
the result, after their combined width has passed the Rust u32 merge check.
-/
private def expandProgram (program : List α) (activity : List (Option Nat)) :
    Option (List (PreviewEntry α)) :=
  if skipRunsFit activity then expandProgramRaw program activity else none

private theorem expandProgramRaw_success
    {program : List α} {activity : List (Option Nat)}
    {output : List (PreviewEntry α)}
    (expanded : expandProgramRaw program activity = some output) :
    activeCount activity = program.length ∧
      activeProjection output = program ∧
      skippedWidth output = activityWidth activity := by
  induction activity generalizing program output with
  | nil =>
      cases program with
      | nil =>
          cases output with
          | nil => simp [activeCount, activeProjection, skippedWidth, activityWidth]
          | cons entry rest => simp [expandProgramRaw] at expanded
      | cons operation program =>
          simp [expandProgramRaw] at expanded
  | cons entry activity ih =>
      cases entry with
      | some count =>
          by_cases countFits : count ≤ u32Max
          · cases tailExpansion : expandProgramRaw program activity with
            | none =>
                simp [expandProgramRaw, countFits, tailExpansion] at expanded
            | some tail =>
                have outputEq : PreviewEntry.noop count :: tail = output := by
                  simpa [expandProgramRaw, countFits, tailExpansion] using expanded
                subst output
                obtain ⟨activeCountEq, activeProjectionEq, skippedWidthEq⟩ :=
                  ih tailExpansion
                constructor
                · simpa [activeCount] using activeCountEq
                constructor
                · simpa [activeProjection] using activeProjectionEq
                · simp [skippedWidth, activityWidth, skippedWidthEq]
          · simp [expandProgramRaw, countFits] at expanded
      | none =>
          cases program with
          | nil =>
              simp [expandProgramRaw] at expanded
          | cons operation program =>
              cases tailExpansion : expandProgramRaw program activity with
              | none =>
                  simp [expandProgramRaw, tailExpansion] at expanded
              | some tail =>
                  have outputEq : PreviewEntry.active operation :: tail = output := by
                    simpa [expandProgramRaw, tailExpansion] using expanded
                  subst output
                  obtain ⟨activeCountEq, activeProjectionEq, skippedWidthEq⟩ :=
                    ih tailExpansion
                  constructor
                  · simpa [activeCount] using congrArg Nat.succ activeCountEq
                  constructor
                  · simp [activeProjection, activeProjectionEq]
                  · simpa [skippedWidth, activityWidth] using skippedWidthEq

private theorem expandProgramRaw_complete
    {program : List α} {activity : List (Option Nat)}
    (activeCountEq : activeCount activity = program.length)
    (fits : skipRunsFit activity = true) :
    ∃ output, expandProgramRaw program activity = some output := by
  induction activity generalizing program with
  | nil =>
      cases program with
      | nil => exact ⟨[], by simp [expandProgramRaw]⟩
      | cons operation program => simp [activeCount] at activeCountEq
  | cons entry activity ih =>
      cases entry with
      | some count =>
          have fitParts := fits
          simp only [skipRunsFit, Bool.and_eq_true] at fitParts
          have countFits : count ≤ u32Max := of_decide_eq_true fitParts.1
          have restFits : skipRunsFit activity = true := fitParts.2.2
          have restCountEq : activeCount activity = program.length := by
            simpa [activeCount] using activeCountEq
          obtain ⟨tail, tailExpanded⟩ := ih restCountEq restFits
          exact ⟨.noop count :: tail, by
            simp [expandProgramRaw, countFits, tailExpanded]⟩
      | none =>
          have restFits : skipRunsFit activity = true := by
            simpa [skipRunsFit] using fits
          cases program with
          | nil =>
              simp [activeCount] at activeCountEq
          | cons operation program =>
              have restCountEq : activeCount activity = program.length := by
                simpa [activeCount] using activeCountEq
              obtain ⟨tail, tailExpanded⟩ := ih restCountEq restFits
              exact ⟨.active operation :: tail, by
                simp [expandProgramRaw, tailExpanded]⟩

private theorem expandProgram_success
    {program : List α} {activity : List (Option Nat)}
    {output : List (PreviewEntry α)}
    (expanded : expandProgram program activity = some output) :
    activeCount activity = program.length ∧
      activeProjection output = program ∧
      skippedWidth output = activityWidth activity := by
  unfold expandProgram at expanded
  cases fits : skipRunsFit activity with
  | false => simp [fits] at expanded
  | true =>
      have rawExpansion : expandProgramRaw program activity = some output := by
        simpa [fits] using expanded
      exact expandProgramRaw_success rawExpansion

private theorem expandProgram_complete
    {program : List α} {activity : List (Option Nat)}
    (activeCountEq : activeCount activity = program.length)
    (fits : skipRunsFit activity = true) :
    ∃ output, expandProgram program activity = some output := by
  obtain ⟨output, rawExpansion⟩ :=
    expandProgramRaw_complete activeCountEq fits
  exact ⟨output, by simpa [expandProgram, fits] using rawExpansion⟩

/-- Unmerged expansion rejects a missing or extra active operation. -/
private theorem expansion_rejects_active_count_mismatch
    (program : List α) (activity : List (Option Nat))
    (mismatch : activeCount activity ≠ program.length) :
    expandProgram program activity = none := by
  cases expanded : expandProgram program activity with
  | none => rfl
  | some output =>
      obtain ⟨countEq, _, _⟩ := expandProgram_success expanded
      exact False.elim (mismatch countEq)

private def prependNoop (count : Nat) (rest : List (PreviewEntry α)) : List (PreviewEntry α) :=
  if count = 0 then rest else
    match rest with
    | .noop next :: tail => .noop (count + next) :: tail
    | _ => .noop count :: rest

/-- Coalesce adjacent skips and drop zero-width runs after the merge bound
has been checked. The supplied scalar program contains only active operations. -/
def coalesceNoops : List (PreviewEntry α) → List (PreviewEntry α)
  | [] => []
  | .active operation :: rest => .active operation :: coalesceNoops rest
  | .noop count :: rest => prependNoop count (coalesceNoops rest)

private theorem prependNoop_activeProjection (count : Nat) (rest : List (PreviewEntry α)) :
    activeProjection (prependNoop count rest) = activeProjection rest := by
  by_cases empty : count = 0
  · simp [prependNoop, empty]
  · cases rest with
    | nil => simp [prependNoop, activeProjection, empty]
    | cons entry tail =>
      cases entry <;> simp [prependNoop, activeProjection, empty]

private theorem prependNoop_skippedWidth (count : Nat) (rest : List (PreviewEntry α)) :
    skippedWidth (prependNoop count rest) = count + skippedWidth rest := by
  by_cases empty : count = 0
  · simp [prependNoop, empty]
  · cases rest with
    | nil => simp [prependNoop, skippedWidth, empty]
    | cons entry tail =>
      cases entry <;> simp [prependNoop, skippedWidth, empty, Nat.add_assoc]

/-- Coalescing preserves the ordered active program. -/
theorem coalesceNoops_activeProjection (program : List (PreviewEntry α)) :
    activeProjection (coalesceNoops program) = activeProjection program := by
  induction program with
  | nil => rfl
  | cons entry rest ih =>
      cases entry <;> simp [coalesceNoops, activeProjection, prependNoop_activeProjection, ih]

/-- Coalescing preserves the full skipped field width. -/
theorem coalesceNoops_skippedWidth (program : List (PreviewEntry α)) :
    skippedWidth (coalesceNoops program) = skippedWidth program := by
  induction program with
  | nil => rfl
  | cons entry rest ih =>
      cases entry <;> simp [coalesceNoops, skippedWidth, prependNoop_skippedWidth, ih]

/-- Render a complete transcript interval as operations and coalesced Noops. -/
def previewProgram (program : List α) (activity : List (Option Nat)) :
    Option (List (PreviewEntry α)) :=
  (expandProgram program activity).map coalesceNoops

theorem previewProgram_success
    {program : List α} {activity : List (Option Nat)}
    {entries : List (PreviewEntry α)}
    (previewed : previewProgram program activity = some entries) :
    activeCount activity = program.length ∧
      activeProjection entries = program ∧
      skippedWidth entries = activityWidth activity := by
  unfold previewProgram at previewed
  cases expansion : expandProgram program activity with
  | none => simp [expansion] at previewed
  | some expanded =>
      have matched : coalesceNoops expanded = entries := by simpa [expansion] using previewed
      subst entries
      obtain ⟨count, order, width⟩ := expandProgram_success expansion
      exact ⟨count, (coalesceNoops_activeProjection expanded).trans order,
        (coalesceNoops_skippedWidth expanded).trans width⟩

theorem previewProgram_preserves
    {program : List α} {activity : List (Option Nat)}
    (activeCountEq : activeCount activity = program.length)
    (fits : skipRunsFit activity = true) :
    ∃ output,
      previewProgram program activity = some output ∧
      activeProjection output = program ∧
      skippedWidth output = activityWidth activity := by
  obtain ⟨expanded, found⟩ := expandProgram_complete activeCountEq fits
  have previewed : previewProgram program activity = some (coalesceNoops expanded) := by
    simp [previewProgram, found]
  obtain ⟨_, order, width⟩ := previewProgram_success previewed
  exact ⟨_, previewed, order, width⟩

/-- A full interval rejects a missing or extra active operation. -/
theorem rejects_active_count_mismatch
    (program : List α) (activity : List (Option Nat))
    (mismatch : activeCount activity ≠ program.length) :
    previewProgram program activity = none := by
  simp [previewProgram, expansion_rejects_active_count_mismatch program activity mismatch]

/-- An individual or merged skip count outside u32 rejects the interval. -/
theorem rejects_skip_overflow
    (program : List α) (activity : List (Option Nat))
    (doesNotFit : skipRunsFit activity = false) :
    previewProgram program activity = none := by
  simp [previewProgram, expandProgram, doesNotFit]

end Noctium.Verification.ImpactNoopPreview
