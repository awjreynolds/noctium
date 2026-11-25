import Noctium.Verification.ImpactNoopPreview

namespace Noctium.Verification.ImpactPreviewGas

open ImpactNoopPreview

/-- The largest value accepted by Rust's checked `u64` gas arithmetic. -/
def u64Max : Nat := 2 ^ 64 - 1

/-- The two nonnegative parameters used to price a Noop run. -/
structure CostModel where
  noopConstant : Nat
  noopCoefficient : Nat
  deriving Repr, DecidableEq

/-- Cost of one Noop run, matching `constant + coefficient * count`. -/
def noopGas (cost : CostModel) (count : Nat) : Nat :=
  cost.noopConstant + cost.noopCoefficient * count

/-- A Rust-style checked conversion for a nonnegative intermediate. -/
def checkedU64 (value : Nat) : Option Nat :=
  if value ≤ u64Max then some value else none

/-- Checked nonnegative addition and multiplication used by the runtime. -/
def checkedAdd (left right : Nat) : Option Nat := checkedU64 (left + right)

def checkedMul (left right : Nat) : Option Nat := checkedU64 (left * right)

/-- Model the checked multiply followed by the checked constant addition. -/
def checkedNoopGas (cost : CostModel) (count : Nat) : Option Nat := do
  let linear ← checkedMul cost.noopCoefficient count
  checkedAdd cost.noopConstant linear

/--
Sum Noop charges in a transcript that has already been coalesced. Zero-width
entries contribute no charge, as the Rust preview drops them before billing.
-/
def addedGas (cost : CostModel) : List (PreviewEntry α) → Nat
  | [] => 0
  | .active _ :: rest => addedGas cost rest
  | .noop count :: rest =>
      (if count = 0 then 0 else noopGas cost count) + addedGas cost rest

/--
Accumulate already-coalesced Noop runs from left to right, checking each
Noop's multiplication, charge addition, and accumulated addition.
-/
def checkedAccumulate (cost : CostModel) : Nat → List (PreviewEntry α) → Option Nat
  | accumulated, [] => checkedU64 accumulated
  | accumulated, .active _ :: rest => checkedAccumulate cost accumulated rest
  | accumulated, .noop count :: rest =>
      if count = 0 then checkedAccumulate cost accumulated rest else do
        let charge ← checkedNoopGas cost count
        let next ← checkedAdd accumulated charge
        checkedAccumulate cost next rest

/-- Checked sum of Noop charges, starting at zero as the Rust preview does. -/
def checkedAddedGas (cost : CostModel) (entries : List (PreviewEntry α)) : Option Nat :=
  checkedAccumulate cost 0 entries

/-- Checked runtime sequence, including the final addition to original time. -/
def checkedComputeTime (cost : CostModel) (original : Nat)
    (entries : List (PreviewEntry α)) : Option Nat := do
  let added ← checkedAddedGas cost entries
  checkedAdd original added

/--
Compute the previewed compute-time total. A single bound check on the
mathematical sum captures Rust's checked `u64` multiply/add stages: all inputs
and charges are nonnegative, so every intermediate is bounded by this total.
The entries are expected to be coalesced by `ImpactNoopPreview.previewProgram`.
-/
def computeTime (cost : CostModel) (original : Nat)
    (entries : List (PreviewEntry α)) : Option Nat :=
  let total := original + addedGas cost entries
  if total ≤ u64Max then some total else none

/-- Success returns exactly the original time plus the per-run Noop charges. -/
theorem computeTime_success_iff (cost : CostModel) (original : Nat)
    (entries : List (PreviewEntry α)) (total : Nat) :
    computeTime cost original entries = some total ↔
      total = original + addedGas cost entries ∧ total ≤ u64Max := by
  by_cases hBound : original + addedGas cost entries ≤ u64Max
  · simp [computeTime, hBound]
    omega
  · simp [computeTime, hBound]
    omega

/-- Any preview whose total exceeds `u64Max` is rejected. -/
theorem computeTime_overflow (cost : CostModel) (original : Nat)
    (entries : List (PreviewEntry α))
    (overflow : u64Max < original + addedGas cost entries) :
    computeTime cost original entries = none := by
  simp [computeTime]
  omega


private theorem checked_bind_add (value offset : Nat) :
    (checkedU64 value).bind (fun input => checkedU64 (input + offset)) =
      checkedU64 (value + offset) := by
  by_cases fits : value ≤ u64Max
  · simp [checkedU64, fits]
  · have overflow : ¬ value + offset ≤ u64Max := by omega
    simp [checkedU64, fits, overflow]

private theorem checkedNoopGas_eq_checkedU64 (cost : CostModel) (count : Nat) :
    checkedNoopGas cost count = checkedU64 (noopGas cost count) := by
  unfold checkedNoopGas checkedMul checkedAdd noopGas
  change (checkedU64 (cost.noopCoefficient * count)).bind
    (fun input => checkedU64 (cost.noopConstant + input)) = _
  simp only [Nat.add_comm cost.noopConstant, checked_bind_add]

/--
The staged Noop checks collapse to one bound on the natural sum. Each checked
stage is monotone because every cost parameter and operation count is natural.
-/
private theorem checkedAccumulate_eq_checkedU64 (cost : CostModel)
    (accumulated : Nat) (entries : List (PreviewEntry α)) :
    checkedAccumulate cost accumulated entries =
      checkedU64 (accumulated + addedGas cost entries) := by
  induction entries generalizing accumulated with
  | nil => simp [checkedAccumulate, addedGas]
  | cons entry rest ih =>
      cases entry with
      | active operation => simp [checkedAccumulate, addedGas, ih]
      | noop count =>
          by_cases zero : count = 0
          · simp [checkedAccumulate, addedGas, zero, ih]
          · simp only [checkedAccumulate, addedGas, zero, ite_false,
              checkedNoopGas_eq_checkedU64]
            change (checkedU64 (noopGas cost count)).bind (fun charge =>
              (checkedU64 (accumulated + charge)).bind (fun next =>
                checkedAccumulate cost next rest)) = _
            simp only [ih, checked_bind_add]
            simp only [Nat.add_comm accumulated, Nat.add_assoc, checked_bind_add]

/-- The staged Rust-style checks and the aggregate compute-time model agree. -/
theorem checkedComputeTime_eq_computeTime (cost : CostModel) (original : Nat)
    (entries : List (PreviewEntry α)) :
    checkedComputeTime cost original entries = computeTime cost original entries := by
  unfold checkedComputeTime checkedAddedGas checkedAdd computeTime
  rw [checkedAccumulate_eq_checkedU64]
  change (checkedU64 (0 + addedGas cost entries)).bind
    (fun added => checkedU64 (original + added)) =
      checkedU64 (original + addedGas cost entries)
  simp only [Nat.zero_add, Nat.add_comm original, checked_bind_add]

end Noctium.Verification.ImpactPreviewGas
