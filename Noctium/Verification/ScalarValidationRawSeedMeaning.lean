import Noctium.Backend.NativeProducer
import Noctium.Verification.ScalarValidationMeaning

namespace Noctium.Verification.ScalarValidationRawSeedMeaning

open Lean Backend.Native NativeRelation
open Noctium.Verification.ScalarValidationMeaning

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

/-- A successful raw header seed establishes scalar meaning for every fact
defined by the producer. Header names use the same assignment for source inputs
and satisfying witnesses, so each seeded field input has its canonical field
bound. Foreign requirements stay outside this theorem. -/
theorem seedRawInputs_meaning {hash : Hash} {inputs witness : Assignment}
    {expected : Expected} {rawInputs : Array Json} {seed : State}
    (nativeOnly : ∀ required ∈ expected.rawInputs, required.ty.isForeign = false)
    (inputAgreement : ∀ required ∈ expected.rawInputs,
      witness required.identifier = inputs required.identifier)
    (accepted : seedRawInputs expected rawInputs = .ok seed) :
    StateMeaning hash inputs witness seed := by
  unfold seedRawInputs at accepted
  simp only [Noctium.Verification.ScalarValidationMeaning.bind_ok] at accepted
  rcases accepted with ⟨loopState, loopAccepted, result⟩
  cases result
  apply forIn_preserves (StateMeaning hash inputs witness)
    (empty_meaning hash inputs witness)
  · intro item state next invariant stepAccepted
    obtain ⟨required, requiredLookup, _, _, defined⟩ :=
      seedRawInput_native_parts nativeOnly stepAccepted
    have requiredMember : required ∈ expected.rawInputs := by
      rcases List.getElem?_eq_some_iff.mp requiredLookup with ⟨inRange, indexEq⟩
      have member := List.getElem_mem inRange
      rw [indexEq] at member
      exact member
    exact define_meaning invariant
      (input_fact_meaning (inputAgreement required requiredMember)) defined
  · exact loopAccepted

end Noctium.Verification.ScalarValidationRawSeedMeaning
