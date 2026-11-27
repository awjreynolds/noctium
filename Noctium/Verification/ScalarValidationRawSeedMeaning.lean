import Noctium.Backend.NativeProducer
import Noctium.Verification.ScalarValidationMeaning
import Noctium.Verification.ScalarValidationNativeLoop
import Noctium.Verification.ScalarValidationNativeDefinitions

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

private theorem lookup_none_fresh {definitions : List (String × Fact)} {name : String}
    (absent : definitions.lookup name = none) : name ∉ definitions.map Prod.fst := by
  intro member
  obtain ⟨pair, present, sameName⟩ := List.mem_map.mp member
  have different := List.lookup_eq_none_iff.mp absent pair present
  simp [sameName] at different

private theorem nodup_append_singleton {names : List String} {name : String}
    (nodup : names.Nodup) (fresh : name ∉ names) : (names ++ [name]).Nodup := by
  induction names with
  | nil => simp
  | cons head tail ih =>
    have headFreshTail : head ∉ tail := (List.nodup_cons.mp nodup).1
    have tailNodup : tail.Nodup := (List.nodup_cons.mp nodup).2
    have nameFreshTail : name ∉ tail := by
      intro member
      exact fresh (List.mem_cons_of_mem head member)
    apply List.nodup_cons.mpr
    constructor
    · intro member
      rcases List.mem_append.mp member with member | member
      · exact headFreshTail member
      · simp only [List.mem_singleton] at member
        subst name
        exact fresh (List.mem_cons_self)
    · exact ih tailNodup nameFreshTail

private theorem seedRawInputs_loop_names {expected : Expected}
    {items : List (Json × Nat)} {initial final : State}
    {step : (Json × Nat) → State → Except String State}
    (accepted : forIn items initial (fun item state => do
      let next ← step item state
      pure (.yield next)) = .ok final)
    (nativeParts : ∀ item state next, step item state = .ok next →
      ∃ required, expected.rawInputs[item.2]? = some required ∧
        required.visibility = .«private» ∧ required.ty.isBytes = false ∧
        define state required.identifier
          ({term := .input required.identifier, maximum := Field.modulus - 1} : Fact) =
            .ok next)
    (headerName : ∀ item state next, step item state = .ok next →
      ∃ required, expected.rawInputs[item.2]? = some required ∧
        stringField item.1 "name" = .ok required.identifier)
    (initialNamesNodup : (initial.definitions.map Prod.fst).Nodup) :
    ∃ names,
      (items.map Prod.fst).mapM (fun rawInput => stringField rawInput "name") = .ok names ∧
      final.definitions.map Prod.fst = initial.definitions.map Prod.fst ++ names ∧
      (final.definitions.map Prod.fst).Nodup := by
  induction items generalizing initial final with
  | nil =>
    simp only [List.forIn_nil] at accepted
    cases accepted
    exact ⟨[], by
      simp only [List.map_nil, List.mapM_nil, Pure.pure, Except.pure], by simp,
      initialNamesNodup⟩
  | cons item tail ih =>
    rw [List.forIn_cons] at accepted
    cases stepAccepted : step item initial with
    | error message => simp [stepAccepted, Bind.bind, Except.bind] at accepted
    | ok middle =>
      simp only [stepAccepted, bind_pure_comp] at accepted
      obtain ⟨required, requiredLookup, _, _, defined⟩ :=
        nativeParts item initial middle stepAccepted
      obtain ⟨namedRequired, namedLookup, headerName⟩ :=
        headerName item initial middle stepAccepted
      have sameRequired : required = namedRequired :=
        Option.some.inj (requiredLookup.symm.trans namedLookup)
      subst namedRequired
      obtain ⟨appended, absent⟩ := define_appended_and_missing defined
      have freshName : required.identifier ∉ initial.definitions.map Prod.fst :=
        lookup_none_fresh absent
      have middleNamesNodup : (middle.definitions.map Prod.fst).Nodup := by
        rw [appended]
        simp only [List.map_append, List.map_cons, List.map_nil]
        exact nodup_append_singleton initialNamesNodup freshName
      obtain ⟨tailNames, tailNameParse, tailDefinitions, tailNodup⟩ :=
        ih accepted middleNamesNodup
      refine ⟨required.identifier :: tailNames, ?_, ?_, tailNodup⟩
      · simp only [List.map_cons, List.mapM_cons, headerName, tailNameParse,
          Bind.bind, Except.bind, Pure.pure, Except.pure]
      · calc
          final.definitions.map Prod.fst = middle.definitions.map Prod.fst ++ tailNames :=
            tailDefinitions
          _ = (initial.definitions.map Prod.fst ++ [required.identifier]) ++ tailNames := by
            rw [appended]
            simp
          _ = initial.definitions.map Prod.fst ++ (required.identifier :: tailNames) := by
            simp [List.append_assoc]

/-- Successful native-only raw header seeding records each parsed header name
in the same order as the definitions it appends, with unique definition names. -/
theorem seedRawInputs_names_and_nodup {expected : Expected}
    {rawInputs : Array Json} {seed : State}
    (nativeOnly : ∀ required ∈ expected.rawInputs, required.ty.isForeign = false)
    (accepted : seedRawInputs expected rawInputs = .ok seed) :
    rawInputs.toList.mapM (fun rawInput => stringField rawInput "name") =
        .ok (seed.definitions.map Prod.fst) ∧
      (seed.definitions.map Prod.fst).Nodup := by
  unfold seedRawInputs at accepted
  simp only [Noctium.Verification.ScalarValidationMeaning.bind_ok] at accepted
  rcases accepted with ⟨loopState, loopAccepted, result⟩
  cases result
  obtain ⟨names, parsed, definitions, nodup⟩ :=
    seedRawInputs_loop_names loopAccepted
      (by
        intro item state next stepAccepted
        exact seedRawInput_native_parts nativeOnly stepAccepted)
      (by
        intro item state next stepAccepted
        exact seedRawInput_header_name stepAccepted)
      (by simp)
  constructor
  · have itemHeaders : (rawInputs.toList.zipIdx).map Prod.fst = rawInputs.toList := by simp
    rw [itemHeaders] at parsed
    simpa [definitions] using parsed
  · simpa [definitions] using nodup

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

/-- An accepted native-only raw header seed leaves the ordered Impact cursor
at its initial zero value. -/
theorem seedRawInputs_groupCount {expected : Expected} {rawInputs : Array Json}
    {seed : State}
    (nativeOnly : ∀ required ∈ expected.rawInputs, required.ty.isForeign = false)
    (accepted : seedRawInputs expected rawInputs = .ok seed) :
    seed.groupCount = 0 := by
  unfold seedRawInputs at accepted
  simp only [Noctium.Verification.ScalarValidationMeaning.bind_ok] at accepted
  rcases accepted with ⟨loopState, loopAccepted, result⟩
  cases result
  apply forIn_preserves (initial := ({} : State))
    (fun state => state.groupCount = 0) rfl
  · intro item state next stateGroupCount stepAccepted
    obtain ⟨required, _, _, _, defined⟩ :=
      seedRawInput_native_parts nativeOnly stepAccepted
    have countPreserved :=
      Noctium.Verification.ScalarValidationNativeDefinitions.define_groupCount defined
    calc
      next.groupCount = state.groupCount := countPreserved
      _ = 0 := stateGroupCount
  · exact loopAccepted

end Noctium.Verification.ScalarValidationRawSeedMeaning
