import Noctium.Verification.GuardedImpactTranscript

namespace Noctium.Verification.GuardedScalarWitnessCheck

open NativeRelation GuardedScalarRows GuardedImpactTranscript

/-- Decide the existing ordinary constraints. Guarded preprocessing rows
carry no ordinary field constraint. -/
private def ordinaryHoldsDecidable (hash : Hash) (assignment : Assignment)
    (row : Row) : Decidable (ordinaryHolds hash assignment row) := by
  cases row with
  | strict instruction =>
    cases instruction <;> unfold ordinaryHolds Instruction.Holds <;> infer_instance
  | publicInput output guard => exact isTrue trivial
  | impact guard inputs => exact isTrue trivial

private def ordinaryHoldsBool (hash : Hash) (assignment : Assignment)
    (row : Row) : Bool :=
  match ordinaryHoldsDecidable hash assignment row with
  | .isTrue _ => true
  | .isFalse _ => false

private theorem ordinaryHoldsBool_eq_true_iff (hash : Hash) (assignment : Assignment)
    (row : Row) : ordinaryHoldsBool hash assignment row = true ↔
      ordinaryHolds hash assignment row := by
  cases decision : ordinaryHoldsDecidable hash assignment row with
  | isTrue holds => simp [ordinaryHoldsBool, decision, holds]
  | isFalse notHolds => simp [ordinaryHoldsBool, decision, notHolds]

/-- Check every strict row's independent field constraints. Public-input and
Impact rows are checked by their transcript preprocessing obligations. -/
def check (hash : Hash) (assignment : Assignment) (rows : List Row) : Bool :=
  rows.all (ordinaryHoldsBool hash assignment)

theorem check_sound (hash : Hash) (assignment : Assignment) (rows : List Row)
    (accepted : check hash assignment rows = true) :
    ∀ row ∈ rows, GuardedImpactTranscript.ordinaryHolds hash assignment row := by
  intro row member
  exact (ordinaryHoldsBool_eq_true_iff hash assignment row).mp
    ((List.all_eq_true.mp accepted) row member)

theorem check_complete (hash : Hash) (assignment : Assignment) (rows : List Row)
    (holds : ∀ row ∈ rows, ordinaryHolds hash assignment row) :
    check hash assignment rows = true :=
  List.all_eq_true.mpr fun row present =>
    (ordinaryHoldsBool_eq_true_iff hash assignment row).mpr (holds row present)

end Noctium.Verification.GuardedScalarWitnessCheck
