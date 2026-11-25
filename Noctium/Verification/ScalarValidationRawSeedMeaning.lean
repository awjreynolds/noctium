import Noctium.Backend.NativeProducer
import Noctium.Verification.ScalarValidationMeaning
import Noctium.Verification.ScalarValidationNativeLoop

namespace Noctium.Verification.ScalarValidationRawSeedMeaning

open Lean Backend.Native NativeRelation
open Noctium.Verification.ScalarValidationMeaning
open Noctium.Verification.ScalarValidationArithmeticLoop (NativeDefinitions)
open Noctium.Verification.ScalarValidationNativeLoop (define_nativeDefinitions)

private theorem forIn_preserves {α : Type} {items : List α}
    {initial final : State} {step : α → State → Except String State}
    (property : State → Prop) (initialProperty : property initial)
    (preserved : ∀ item state next, property state → step item state = .ok next →
      property next)
    (accepted : forIn items initial (fun item state => do
      let next ← step item state
      pure (.yield next)) = .ok final) :
    property final := by
  induction items generalizing initial final with
  | nil =>
    simp only [List.forIn_nil] at accepted
    cases accepted
    exact initialProperty
  | cons head tail ih =>
    rw [List.forIn_cons] at accepted
    cases checked : step head initial with
    | error message => simp [checked, Bind.bind, Except.bind] at accepted
    | ok middle =>
      simp only [checked, bind_pure_comp] at accepted
      exact ih (preserved head initial middle initialProperty checked) accepted

private theorem emptyNativeDefinitions : NativeDefinitions ({} : State) := by
  intro identifier fact found
  simp at found

private theorem define_assertionCount {state next : State} {name : String} {fact : Fact}
    (accepted : define state name fact = .ok next) :
    next.assertionCount = state.assertionCount := by
  unfold define at accepted
  simp only [Noctium.Verification.ScalarValidationMeaning.bind_ok] at accepted
  rcases accepted with ⟨_, _, _, _, result⟩
  simp only [Pure.pure, Except.pure] at result
  cases result
  rfl

/-- A successful raw header seed establishes scalar meaning and Native typing
for every fact defined by the producer. Header names use the same assignment
for source inputs and satisfying witnesses, so each seeded field input has its
canonical field bound. Foreign requirements stay outside this theorem. -/
theorem seedRawInputs_meaning_and_nativeDefinitions
    {hash : Hash} {inputs witness : Assignment}
    {expected : Expected} {rawInputs : Array Json} {seed : State}
    (nativeOnly : ∀ required ∈ expected.rawInputs, required.ty.isForeign = false)
    (inputAgreement : ∀ required ∈ expected.rawInputs,
      witness required.identifier = inputs required.identifier)
    (accepted : seedRawInputs expected rawInputs = .ok seed) :
    StateMeaning hash inputs witness seed ∧ NativeDefinitions seed := by
  unfold seedRawInputs at accepted
  simp only [Noctium.Verification.ScalarValidationMeaning.bind_ok] at accepted
  rcases accepted with ⟨loopState, loopAccepted, result⟩
  cases result
  apply forIn_preserves
    (fun state => StateMeaning hash inputs witness state ∧ NativeDefinitions state)
    ⟨empty_meaning hash inputs witness, emptyNativeDefinitions⟩
  · intro item state next invariants stepAccepted
    obtain ⟨required, requiredLookup, _, _, defined⟩ :=
      seedRawInput_native_parts nativeOnly stepAccepted
    have requiredMember : required ∈ expected.rawInputs := by
      rcases List.getElem?_eq_some_iff.mp requiredLookup with ⟨inRange, indexEq⟩
      have member := List.getElem_mem inRange
      rw [indexEq] at member
      exact member
    refine ⟨define_meaning invariants.1
      (input_fact_meaning (inputAgreement required requiredMember)) defined, ?_⟩
    exact define_nativeDefinitions invariants.2 rfl defined
  · exact loopAccepted

/-- Scalar meaning remains available to callers that do not need the Native
type invariant. -/
theorem seedRawInputs_meaning {hash : Hash} {inputs witness : Assignment}
    {expected : Expected} {rawInputs : Array Json} {seed : State}
    (nativeOnly : ∀ required ∈ expected.rawInputs, required.ty.isForeign = false)
    (inputAgreement : ∀ required ∈ expected.rawInputs,
      witness required.identifier = inputs required.identifier)
    (accepted : seedRawInputs expected rawInputs = .ok seed) :
    StateMeaning hash inputs witness seed :=
  (seedRawInputs_meaning_and_nativeDefinitions nativeOnly inputAgreement accepted).1

/-- An accepted native-only raw header seed leaves the producer's typed
source assertion ordinal at its initial zero value. -/
theorem seedRawInputs_assertionCount {expected : Expected} {rawInputs : Array Json}
    {seed : State}
    (nativeOnly : ∀ required ∈ expected.rawInputs, required.ty.isForeign = false)
    (accepted : seedRawInputs expected rawInputs = .ok seed) :
    seed.assertionCount = 0 := by
  unfold seedRawInputs at accepted
  simp only [Noctium.Verification.ScalarValidationMeaning.bind_ok] at accepted
  rcases accepted with ⟨loopState, loopAccepted, result⟩
  cases result
  apply forIn_preserves (initial := ({} : State))
    (fun state => state.assertionCount = 0) rfl
  · intro item state next stateCount stepAccepted
    obtain ⟨required, _, _, _, defined⟩ :=
      seedRawInput_native_parts nativeOnly stepAccepted
    have countPreserved := define_assertionCount defined
    calc
      next.assertionCount = state.assertionCount := countPreserved
      _ = 0 := stateCount
  · exact loopAccepted

end Noctium.Verification.ScalarValidationRawSeedMeaning
