import Lean
import Noctium.ScalarPolicy
import Std.Data.HashMap.Lemmas

namespace Noctium.Backend.RangeDedup
open Lean

def key? (instruction : Json) : Option (String × Nat) := do
  let object ← instruction.getObj?.toOption
  guard (object.size == 3)
  let opcode ← (instruction.getObjVal? "op" >>= Json.getStr?).toOption
  guard (opcode == "constrain_bits")
  let operand ← (instruction.getObjVal? "val" >>= Json.getStr?).toOption
  guard (operand.startsWith '%')
  let bits ← (instruction.getObjVal? "bits" >>= Json.getNat?).toOption
  guard (0 < bits && bits ≤ ScalarPolicy.maxBits)
  pure (operand, bits)

private structure State where
  widths : Std.HashMap String Nat := {}
  retained : Array Json := #[]

private def step (state : State) (instruction : Json) : State :=
  match key? instruction with
  | none => {state with retained := state.retained.push instruction}
  | some (operand, bits) =>
    if (state.widths[operand]?.any (· ≤ bits)) then state
    else ⟨state.widths.insert operand bits, state.retained.push instruction⟩

/-- A prior unconditional check at an equal or narrower width already bounds
the same immutable SSA operand. Retain earlier checks before any narrowing. -/
def run (instructions : Array Json) : Array Json :=
  (instructions.foldl step {}).retained

def assertionOperand? (instruction : Json) : Option String := do
  let object ← instruction.getObj?.toOption
  guard (object.size == 2)
  guard ((← (instruction.getObjVal? "op" >>= Json.getStr?).toOption) == "assert")
  let operand ← (instruction.getObjVal? "cond" >>= Json.getStr?).toOption
  guard (operand.startsWith '%' && operand.length > 1 && operand.utf8ByteSize ≤ 1024)
  pure operand

private structure AssertionState where
  seen : Std.HashMap String Unit := {}
  retained : Array Json := #[]

private def assertionStep (state : AssertionState) (instruction : Json) : AssertionState :=
  match assertionOperand? instruction with
  | none => {state with retained := state.retained.push instruction}
  | some operand =>
    if (state.seen[operand]?).isSome then state
    else {
      seen := state.seen.insert operand ()
      retained := state.retained.push instruction
    }

/-- Remove later exact assertions on the same SSA condition. Guarded, malformed,
immediate and non-assert instructions pass through unchanged. -/
def removeDuplicateAssertions (instructions : Array Json) : Array Json :=
  (instructions.foldl assertionStep {}).retained

private theorem removeDuplicateAssertions_push_unrecognized (instructions : Array Json)
    (item : Json) (unrecognized : assertionOperand? item = none) :
    removeDuplicateAssertions (instructions.push item) =
      (removeDuplicateAssertions instructions).push item := by
  simp [removeDuplicateAssertions, assertionStep, unrecognized]

private theorem removeDuplicateAssertions_push_duplicate (instructions : Array Json)
    (item : Json) (operand : String)
    (recognized : assertionOperand? item = some operand)
    (seen : ((instructions.foldl assertionStep {}).seen[operand]?).isSome = true) :
    removeDuplicateAssertions (instructions.push item) = removeDuplicateAssertions instructions := by
  simp [removeDuplicateAssertions, assertionStep, recognized, seen]

private theorem removeDuplicateAssertions_push_kept (instructions : Array Json)
    (item : Json)
    (kept : (assertionStep (instructions.foldl assertionStep {}) item).retained =
      (instructions.foldl assertionStep {}).retained.push item) :
    removeDuplicateAssertions (instructions.push item) =
      (removeDuplicateAssertions instructions).push item := by
  simpa only [removeDuplicateAssertions, Array.foldl_push] using kept

private theorem assertionStep_seen_congruent (state : AssertionState)
    (left right : Json) (same : assertionOperand? left = assertionOperand? right) :
    (assertionStep state left).seen = (assertionStep state right).seen := by
  unfold assertionStep
  rw [same]
  cases key : assertionOperand? right with
  | none => rfl
  | some operand => by_cases seen : operand ∈ state.seen <;> simp [seen]

private theorem assertionStep_seen_map_congruent (left right : AssertionState)
    (leftItem rightItem : Json) (sameSeen : left.seen = right.seen)
    (sameKey : assertionOperand? leftItem = assertionOperand? rightItem) :
    (assertionStep left leftItem).seen = (assertionStep right rightItem).seen := by
  unfold assertionStep
  rw [sameKey]
  cases key : assertionOperand? rightItem with
  | none => simp [sameSeen]
  | some operand =>
    by_cases member : operand ∈ right.seen <;> simp [member, sameSeen]

private theorem assertionStep_retained (state : AssertionState) (item : Json) :
    (assertionStep state item).retained = state.retained ∨
      (assertionStep state item).retained = state.retained.push item := by
  unfold assertionStep
  split
  · exact .inr rfl
  · split
    · exact .inl rfl
    · exact .inr rfl

private theorem assertionFold_sublist (items : List Json) (state : AssertionState) :
    (items.foldl assertionStep state).retained.toList.Sublist
      (state.retained.toList ++ items) := by
  induction items generalizing state with
  | nil => simp
  | cons item rest ih =>
    have retained := ih (assertionStep state item)
    rcases assertionStep_retained state item with dropped | kept
    · rw [dropped] at retained
      exact retained.trans ((List.Sublist.cons item (List.Sublist.refl rest)).append_left _)
    · simpa [kept, List.append_assoc] using retained

/-- Removing repeated assertions keeps every remaining JSON instruction in order. -/
theorem removeDuplicateAssertions_sublist (instructions : Array Json) :
    (removeDuplicateAssertions instructions).toList.Sublist instructions.toList := by
  simpa [removeDuplicateAssertions, Array.foldl_toList] using
    assertionFold_sublist instructions.toList {}

private theorem assertionStep_observation (observe : Json → List α) (state : AssertionState)
    (item : Json)
    (silent : ∀ operand, assertionOperand? item = some operand → observe item = []) :
    (assertionStep state item).retained.toList.flatMap observe =
      state.retained.toList.flatMap observe ++ observe item := by
  cases key : assertionOperand? item with
  | none => simp [assertionStep, key]
  | some operand =>
    rcases assertionStep_retained state item with dropped | kept
    · simp [dropped, silent operand key]
    · simp [kept]

private theorem assertionFold_observation (observe : Json → List α) (items : List Json)
    (state : AssertionState)
    (silent : ∀ item ∈ items, ∀ operand,
      assertionOperand? item = some operand → observe item = []) :
    (items.foldl assertionStep state).retained.toList.flatMap observe =
      state.retained.toList.flatMap observe ++ items.flatMap observe := by
  induction items generalizing state with
  | nil => simp
  | cons item rest ih =>
    rw [List.foldl_cons,
      ih (assertionStep state item) (fun other member =>
        silent other (List.mem_cons_of_mem _ member)),
      assertionStep_observation observe state item (silent item List.mem_cons_self)]
    simp [List.append_assoc]

/-- Any observation silent on recognized direct assertions keeps its ordered
sequence when repeated assertions are removed. -/
theorem removeDuplicateAssertions_preserves_observation (instructions : Array Json)
    (observe : Json → List α)
    (silent : ∀ item ∈ instructions.toList, ∀ operand,
      assertionOperand? item = some operand → observe item = []) :
    (removeDuplicateAssertions instructions).toList.flatMap observe =
      instructions.toList.flatMap observe := by
  simpa [removeDuplicateAssertions, Array.foldl_toList] using
    assertionFold_observation observe instructions.toList {} silent

private def AssertionTracks (state : AssertionState) : Prop :=
  ∀ operand, (state.seen[operand]?).isSome = true →
    ∃ item ∈ state.retained.toList, assertionOperand? item = some operand

private theorem assertionStep_tracks (state : AssertionState) (instruction : Json)
    (tracks : AssertionTracks state) : AssertionTracks (assertionStep state instruction) := by
  unfold assertionStep
  split
  · intro operand found
    obtain ⟨earlier, member, key⟩ := tracks operand found
    exact ⟨earlier, by simp [member], key⟩
  · next operand key =>
    split
    · exact tracks
    · intro name found
      by_cases same : operand = name
      · subst name
        change ((state.seen.insert operand ())[operand]?).isSome = true at found
        simp at found
        exact ⟨instruction, by simp, key⟩
      · obtain ⟨earlier, member, earlierKey⟩ := tracks name (by
          simpa [Std.HashMap.getElem?_insert, same] using found)
        exact ⟨earlier, by simp [member], earlierKey⟩

private theorem assertionStep_tracks_fold (instructions : List Json)
    (state : AssertionState) (tracks : AssertionTracks state) :
    AssertionTracks (instructions.foldl assertionStep state) := by
  induction instructions generalizing state with
  | nil => simpa using tracks
  | cons instruction rest ih =>
    rw [List.foldl_cons]
    exact ih (assertionStep state instruction) (assertionStep_tracks state instruction tracks)

private theorem assertion_seen_preserved (state : AssertionState) (instruction : Json)
    (operand : String) (found : (state.seen[operand]?).isSome = true) :
    ((assertionStep state instruction).seen[operand]?).isSome = true := by
  unfold assertionStep
  split
  · simpa using found
  · next other key =>
    split
    · simpa using found
    · by_cases same : other = operand
      · subst other
        simp
      · simpa [Std.HashMap.getElem?_insert, same] using found

private theorem assertion_seen_preserved_fold (instructions : List Json)
    (state : AssertionState) (operand : String)
    (found : (state.seen[operand]?).isSome = true) :
    ((instructions.foldl assertionStep state).seen[operand]?).isSome = true := by
  induction instructions generalizing state with
  | nil => simpa using found
  | cons instruction rest ih =>
    rw [List.foldl_cons]
    exact ih (assertionStep state instruction)
      (assertion_seen_preserved state instruction operand found)

private theorem assertion_seen_fold_member (instructions : List Json)
    (state : AssertionState) (instruction : Json) (member : instruction ∈ instructions)
    (key : assertionOperand? instruction = some operand) :
    ((instructions.foldl assertionStep state).seen[operand]?).isSome = true := by
  induction instructions generalizing state with
  | nil => simp at member
  | cons first rest ih =>
    simp only [List.mem_cons] at member
    rw [List.foldl_cons]
    rcases member with same | member
    · subst first
      have headSeen : ((assertionStep state instruction).seen[operand]?).isSome = true := by
        unfold assertionStep
        rw [key]
        by_cases already : operand ∈ state.seen <;> simp [already]
      exact assertion_seen_preserved_fold rest (assertionStep state instruction) operand headSeen
    · exact ih (assertionStep state first) member

/-- An exact repeated assertion on one immutable SSA operand adds the same
nonzero condition twice, which is equivalent to asserting it once. -/
theorem duplicateAssertion_preserves (read : String → Nat) (operand : String) :
    (read operand ≠ 0 ∧ read operand ≠ 0) ↔ read operand ≠ 0 := by
  constructor
  · exact And.left
  · intro holds
    exact ⟨holds, holds⟩

/-- Every recognized assertion operand in the input remains represented by a
retained assertion with the same condition. -/
theorem removeDuplicateAssertions_retains_operand (instructions : Array Json)
    (item : Json) (member : item ∈ instructions.toList)
    (recognized : assertionOperand? item = some operand) :
    ∃ retained ∈ (removeDuplicateAssertions instructions).toList,
      assertionOperand? retained = some operand := by
  have seen : ((instructions.toList.foldl assertionStep {}).seen[operand]?).isSome = true :=
    assertion_seen_fold_member instructions.toList {} item member recognized
  have tracks : AssertionTracks (instructions.foldl assertionStep {}) := by
    simpa only [Array.foldl_toList] using
      assertionStep_tracks_fold instructions.toList {}
        (by intro name found; simp at found)
  exact tracks operand (by simpa only [Array.foldl_toList] using seen)

def comparison? (item : Json) : Option ((String × String × Nat) × String) := do
  let object ← item.getObj?.toOption
  guard (object.size == 5)
  guard ((← (item.getObjVal? "op" >>= Json.getStr?).toOption) == "less_than")
  let left ← (item.getObjVal? "a" >>= Json.getStr?).toOption
  let right ← (item.getObjVal? "b" >>= Json.getStr?).toOption
  let width ← (item.getObjVal? "bits" >>= Json.getNat?).toOption
  let output ← (item.getObjVal? "output" >>= Json.getStr?).toOption
  pure ((left, right, width), output)

/-- JSON Copy emitted when a duplicate comparison result gets a fresh name. -/
def comparisonCopyJson (first output : String) : Json := Json.mkObj [
  ("op", toJson ("copy" : String)), ("val", toJson first), ("output", toJson output)]

private structure ComparisonState where
  seen : Std.HashMap (String × String × Nat) String := {}
  retained : Array Json := #[]

private def comparisonStep (state : ComparisonState) (item : Json) : ComparisonState :=
  match comparison? item with
  | none => {state with retained := state.retained.push item}
  | some (key, output) =>
    match state.seen[key]? with
    | some first =>
      {state with retained := state.retained.push (comparisonCopyJson first output)}
    | none => {
      seen := state.seen.insert key output
      retained := state.retained.push item
    }

private theorem comparison_none_of_assertion {item : Json} {operand : String}
    (recognized : assertionOperand? item = some operand) : comparison? item = none := by
  unfold assertionOperand? at recognized
  rcases Option.bind_eq_some_iff.mp recognized with ⟨object, objectParsed, objectRest⟩
  rcases Option.bind_eq_some_iff.mp objectRest with ⟨_, objectSize, opcodeRest⟩
  have objectSize' : object.size = 2 := by
    simp [guard] at objectSize
    assumption
  rcases Option.bind_eq_some_iff.mp opcodeRest with ⟨opcode, opcodeParsed, opcodeGuardRest⟩
  rcases Option.bind_eq_some_iff.mp opcodeGuardRest with ⟨_, opcodeEq, _⟩
  have opcodeEq' : opcode = "assert" := by
    simp [guard] at opcodeEq
    assumption
  unfold comparison?
  rw [objectParsed, opcodeParsed]
  simp [guard, objectSize', opcodeEq']

private theorem comparisonStep_assertion (state : ComparisonState) (item : Json)
    {operand : String} (recognized : assertionOperand? item = some operand) :
    comparisonStep state item = {state with retained := state.retained.push item} := by
  simp [comparisonStep, comparison_none_of_assertion recognized]

private theorem assertionOpcode {item : Json} {operand : String}
    (recognized : assertionOperand? item = some operand) :
    (item.getObjVal? "op" >>= Json.getStr?).toOption = some "assert" := by
  unfold assertionOperand? at recognized
  rcases Option.bind_eq_some_iff.mp recognized with ⟨object, _, objectRest⟩
  rcases Option.bind_eq_some_iff.mp objectRest with ⟨_, _, opcodeRest⟩
  rcases Option.bind_eq_some_iff.mp opcodeRest with ⟨opcode, opcodeParsed, opcodeGuardRest⟩
  rcases Option.bind_eq_some_iff.mp opcodeGuardRest with ⟨_, opcodeEq, _⟩
  have opcodeEq' : opcode = "assert" := by
    simp [guard] at opcodeEq
    assumption
  simpa [opcodeEq'] using opcodeParsed

private theorem comparisonCopyJson_opcode (first output : String) :
    ((comparisonCopyJson first output).getObjVal? "op" >>= Json.getStr?).toOption = some "copy" := by
  let fields := [("op", toJson ("copy" : String)), ("val", toJson first),
    ("output", toJson output)]
  have distinct : fields.Pairwise (fun a b => ¬ compare a.1 b.1 = .eq) := by
    simp [fields, List.pairwise_cons]
  have lookup : (Std.TreeMap.Raw.ofList fields compare)["op"]? =
      some (toJson ("copy" : String)) := by
    exact Std.TreeMap.Raw.getElem?_ofList_of_mem (l := fields) (k := "op") (k' := "op")
      (v := toJson ("copy" : String)) (by simp) distinct (by simp [fields])
  have lookup' : (Std.TreeMap.Raw.ofList [
      ("op", toJson ("copy" : String)), ("val", toJson first),
      ("output", toJson output)] compare)["op"]? = some (toJson ("copy" : String)) := by
    simpa [fields] using lookup
  simp only [Lean.ToJson.toJson] at lookup'
  simp [comparisonCopyJson, Json.mkObj, Json.getObjVal?, lookup', Json.getStr?,
    Lean.ToJson.toJson, Std.TreeMap.Raw.get?_eq_getElem?]
  rfl

private theorem comparisonCopyJson_not_assertion (first output : String) :
    assertionOperand? (comparisonCopyJson first output) = none := by
  cases parsed : assertionOperand? (comparisonCopyJson first output) with
  | none => rfl
  | some operand =>
    have opcode := assertionOpcode parsed
    rw [comparisonCopyJson_opcode] at opcode
    simp at opcode

private theorem comparisonStep_seen_congruent (left right : ComparisonState)
    (same : left.seen = right.seen) (item : Json) :
    (comparisonStep left item).seen = (comparisonStep right item).seen := by
  cases parsed : comparison? item with
  | none => simpa [comparisonStep, parsed] using same
  | some pair =>
    obtain ⟨key, output⟩ := pair
    cases seen : left.seen[key]? with
    | none =>
      have rightSeen : right.seen[key]? = none := by simpa [same] using seen
      simp [comparisonStep, parsed, seen, rightSeen]
      rw [same]
    | some first =>
      have rightSeen : right.seen[key]? = some first := by simpa [same] using seen
      simp [comparisonStep, parsed, seen, rightSeen]
      exact same

private theorem comparisonStep_shared_emission (left right : ComparisonState)
    (same : left.seen = right.seen) (item : Json) :
    ∃ emitted, (comparisonStep left item).retained = left.retained.push emitted ∧
      (comparisonStep right item).retained = right.retained.push emitted ∧
      assertionOperand? emitted = assertionOperand? item := by
  cases parsed : comparison? item with
  | none => exact ⟨item, by simp [comparisonStep, parsed], by simp [comparisonStep, parsed], rfl⟩
  | some pair =>
    obtain ⟨key, output⟩ := pair
    have itemNotAssertion : assertionOperand? item = none := by
      cases recognized : assertionOperand? item with
      | none => rfl
      | some operand =>
        have comparisonNone := comparison_none_of_assertion recognized
        rw [comparisonNone] at parsed
        contradiction
    cases seen : left.seen[key]? with
    | none =>
      have rightSeen : right.seen[key]? = none := by simpa [same] using seen
      refine ⟨item, ?_, ?_, ?_⟩
      · simp [comparisonStep, parsed, seen]
      · simp [comparisonStep, parsed, rightSeen]
      · rfl
    | some first =>
      have rightSeen : right.seen[key]? = some first := by simpa [same] using seen
      refine ⟨comparisonCopyJson first output, ?_, ?_, ?_⟩
      · simp [comparisonStep, parsed, seen]
      · simp [comparisonStep, parsed, rightSeen]
      · rw [comparisonCopyJson_not_assertion, itemNotAssertion]

private theorem comparisonStep_assertion_projection (state : ComparisonState) (item : Json) :
    ∃ emitted, (comparisonStep state item).retained = state.retained.push emitted ∧
      assertionOperand? emitted = assertionOperand? item := by
  cases parsed : comparison? item with
  | none => exact ⟨item, by simp [comparisonStep, parsed], rfl⟩
  | some pair =>
    obtain ⟨key, output⟩ := pair
    have itemNotAssertion : assertionOperand? item = none := by
      cases recognized : assertionOperand? item with
      | none => rfl
      | some operand =>
        have comparisonNone := comparison_none_of_assertion recognized
        rw [comparisonNone] at parsed
        contradiction
    cases seen : state.seen[key]? with
    | none => exact ⟨item, by simp [comparisonStep, parsed, seen], rfl⟩
    | some first =>
      refine ⟨comparisonCopyJson first output, by simp [comparisonStep, parsed, seen], ?_⟩
      rw [comparisonCopyJson_not_assertion, itemNotAssertion]

private structure ComparisonAssertionState where
  assertions : AssertionState := {}
  filtered : ComparisonState := {}
  full : ComparisonState := {}

private def comparisonAssertionStep (state : ComparisonAssertionState) (item : Json) :
    ComparisonAssertionState :=
  match assertionOperand? item with
  | none => {
      assertions := assertionStep state.assertions item
      filtered := comparisonStep state.filtered item
      full := comparisonStep state.full item
    }
  | some operand =>
    if (state.assertions.seen[operand]?).isSome then {
      assertions := assertionStep state.assertions item
      filtered := state.filtered
      full := comparisonStep state.full item
    } else {
      assertions := assertionStep state.assertions item
      filtered := comparisonStep state.filtered item
      full := comparisonStep state.full item
    }

private def ComparisonAssertionInvariant (state : ComparisonAssertionState) : Prop :=
  state.filtered = state.assertions.retained.foldl comparisonStep {} ∧
  state.filtered.seen = state.full.seen ∧
  state.filtered.retained = removeDuplicateAssertions state.full.retained ∧
  state.assertions.seen = (state.full.retained.foldl assertionStep {}).seen

private theorem comparisonAssertionStep_preserves (state : ComparisonAssertionState)
    (item : Json) (invariant : ComparisonAssertionInvariant state) :
    ComparisonAssertionInvariant (comparisonAssertionStep state item) := by
  rcases invariant with ⟨filteredEq, sameCache, sameAssertions, assertionSeen⟩
  cases recognized : assertionOperand? item with
  | none =>
    simp [comparisonAssertionStep, recognized]
    obtain ⟨emitted, filteredEmit, fullEmit, sameKey⟩ :=
      comparisonStep_shared_emission state.filtered state.full sameCache item
    refine ⟨?_, ?_, ?_, ?_⟩
    · rw [filteredEq]
      simp only [assertionStep, recognized]
      rw [Array.foldl_push]
    · exact comparisonStep_seen_congruent state.filtered state.full sameCache item
    · rw [filteredEmit, fullEmit, sameAssertions]
      rw [removeDuplicateAssertions_push_unrecognized _ emitted (by
        rw [sameKey, recognized])]
    · change (assertionStep state.assertions item).seen =
        ((comparisonStep state.full item).retained.foldl assertionStep {}).seen
      rw [fullEmit, Array.foldl_push]
      exact assertionStep_seen_map_congruent state.assertions
        (state.full.retained.foldl assertionStep {}) item emitted assertionSeen sameKey.symm
  | some operand =>
    cases seen : (state.assertions.seen[operand]?).isSome with
    | true =>
      simp [comparisonAssertionStep, recognized, seen]
      refine ⟨?_, ?_, ?_, ?_⟩
      · simpa [assertionStep, recognized, seen] using filteredEq
      · rw [comparisonStep_assertion state.full item recognized]
        exact sameCache
      · change state.filtered.retained =
          removeDuplicateAssertions (comparisonStep state.full item).retained
        rw [comparisonStep_assertion state.full item recognized, sameAssertions]
        have fullSeen :
            ((state.full.retained.foldl assertionStep {}).seen[operand]?).isSome = true := by
          simpa [assertionSeen] using seen
        rw [removeDuplicateAssertions_push_duplicate _ item operand recognized fullSeen]
      · change (assertionStep state.assertions item).seen =
          ((comparisonStep state.full item).retained.foldl assertionStep {}).seen
        rw [comparisonStep_assertion state.full item recognized, Array.foldl_push]
        have fullSeen :
            ((state.full.retained.foldl assertionStep {}).seen[operand]?).isSome = true := by
          simpa [assertionSeen] using seen
        simp [assertionStep, recognized, fullSeen, assertionSeen]
    | false =>
      simp [comparisonAssertionStep, recognized, seen]
      obtain ⟨emitted, filteredEmit, fullEmit, sameKey⟩ :=
        comparisonStep_shared_emission state.filtered state.full sameCache item
      have fullUnseen :
          ((state.full.retained.foldl assertionStep {}).seen[operand]?).isSome = false := by
        simpa [assertionSeen] using seen
      have emittedKept :
          (assertionStep (state.full.retained.foldl assertionStep {}) emitted).retained =
            (state.full.retained.foldl assertionStep {}).retained.push emitted := by
        simp [assertionStep, sameKey, recognized, fullUnseen]
      refine ⟨?_, ?_, ?_, ?_⟩
      · rw [filteredEq]
        simp [assertionStep, recognized, seen]
      · exact comparisonStep_seen_congruent state.filtered state.full sameCache item
      · rw [filteredEmit, fullEmit, sameAssertions]
        rw [removeDuplicateAssertions_push_kept _ emitted emittedKept]
      · change (assertionStep state.assertions item).seen =
          ((comparisonStep state.full item).retained.foldl assertionStep {}).seen
        rw [fullEmit, Array.foldl_push]
        exact assertionStep_seen_map_congruent state.assertions
          (state.full.retained.foldl assertionStep {}) item emitted assertionSeen sameKey.symm

/-- Reuse the result of an identical, earlier comparison over immutable SSA
operands. Keep output identifiers, check ordering and per-use assertions. -/
def reuseComparisons (instructions : Array Json) : Array Json :=
  (instructions.foldl comparisonStep {}).retained

private theorem comparisonAssertionFold_preserves (items : List Json)
    (state : ComparisonAssertionState) (invariant : ComparisonAssertionInvariant state) :
    ComparisonAssertionInvariant (items.foldl comparisonAssertionStep state) := by
  induction items generalizing state with
  | nil => simpa using invariant
  | cons item rest ih =>
    rw [List.foldl_cons]
    exact ih (comparisonAssertionStep state item)
      (comparisonAssertionStep_preserves state item invariant)

private theorem comparisonAssertionStep_full (state : ComparisonAssertionState)
    (item : Json) :
    (comparisonAssertionStep state item).full = comparisonStep state.full item := by
  cases key : assertionOperand? item with
  | none => simp [comparisonAssertionStep, key]
  | some operand =>
    simp only [comparisonAssertionStep, key]
    split <;> rfl

private theorem comparisonAssertionFold_full (items : List Json)
    (state : ComparisonAssertionState) :
    (items.foldl comparisonAssertionStep state).full =
      items.foldl comparisonStep state.full := by
  induction items generalizing state with
  | nil => rfl
  | cons item rest ih =>
    simpa only [List.foldl_cons, comparisonAssertionStep_full] using
      ih (comparisonAssertionStep state item)

private theorem comparisonAssertionStep_assertions (state : ComparisonAssertionState)
    (item : Json) :
    (comparisonAssertionStep state item).assertions = assertionStep state.assertions item := by
  cases key : assertionOperand? item with
  | none => simp [comparisonAssertionStep, key]
  | some operand =>
    by_cases seen : (state.assertions.seen[operand]?).isSome = true <;>
      simp [comparisonAssertionStep, key, seen]

private theorem comparisonAssertionFold_assertions (items : List Json)
    (state : ComparisonAssertionState) :
    (items.foldl comparisonAssertionStep state).assertions =
      items.foldl assertionStep state.assertions := by
  induction items generalizing state with
  | nil => rfl
  | cons item rest ih =>
    simpa only [List.foldl_cons, comparisonAssertionStep_assertions] using
      ih (comparisonAssertionStep state item)

/-- Assertion deduplication commutes with comparison reuse. Assertion rows do
not update the comparison cache, and comparison copies preserve each row's
assertion classification. -/
theorem reuseComparisons_removeDuplicateAssertions (instructions : Array Json) :
    reuseComparisons (removeDuplicateAssertions instructions) =
      removeDuplicateAssertions (reuseComparisons instructions) := by
  let initial : ComparisonAssertionState := {}
  have invariant : ComparisonAssertionInvariant
      (instructions.toList.foldl comparisonAssertionStep initial) := by
    exact comparisonAssertionFold_preserves instructions.toList initial (by
      simp [ComparisonAssertionInvariant, initial, removeDuplicateAssertions])
  rcases invariant with ⟨filteredIsReuse, _, filteredIsDedupedFull, _⟩
  have assertionsState := comparisonAssertionFold_assertions instructions.toList initial
  have fullState := comparisonAssertionFold_full instructions.toList initial
  have assertions :
      (instructions.toList.foldl assertionStep {}).retained =
        removeDuplicateAssertions instructions := by
    simp [removeDuplicateAssertions, Array.foldl_toList]
  have filtered :
      (instructions.toList.foldl comparisonAssertionStep initial).filtered.retained =
        reuseComparisons (removeDuplicateAssertions instructions) := by
    rw [filteredIsReuse, assertionsState, assertions]
    rfl
  have full :
      (instructions.toList.foldl comparisonAssertionStep initial).full.retained =
        reuseComparisons instructions := by
    rw [fullState]
    simp [reuseComparisons, Array.foldl_toList, initial]
  calc
    reuseComparisons (removeDuplicateAssertions instructions) =
        (instructions.toList.foldl comparisonAssertionStep initial).filtered.retained := by
      exact filtered.symm
    _ = removeDuplicateAssertions
        ((instructions.toList.foldl comparisonAssertionStep initial).full.retained) :=
      filteredIsDedupedFull
    _ = removeDuplicateAssertions (reuseComparisons instructions) := by rw [full]

/-- Two comparisons with the same recognized cache key retain the first JSON
instruction and emit the exact Copy object for the second result. -/
theorem reuseComparisons_pair (first later : Json)
    (key : String × String × Nat) (firstOutput laterOutput : String)
    (firstKey : comparison? first = some (key, firstOutput))
    (laterKey : comparison? later = some (key, laterOutput)) :
    reuseComparisons #[first, later] = #[first, comparisonCopyJson firstOutput laterOutput] := by
  simp [reuseComparisons, comparisonStep, firstKey, laterKey]

/-- The cache key is the ordered pair of operand spellings and bit width. -/
theorem comparison_key_vector :
    comparison? (Json.mkObj [("op", toJson ("less_than" : String)),
      ("a", toJson ("%left" : String)), ("b", toJson ("%right" : String)),
      ("bits", toJson (16 : Nat)), ("output", toJson ("%first" : String))]) =
        some (("%left", "%right", 16), "%first") := by
  decide

theorem comparisonCopyJson_vector :
    comparisonCopyJson "%first" "%duplicate" = Json.mkObj [
      ("op", toJson ("copy" : String)), ("val", toJson ("%first" : String)),
      ("output", toJson ("%duplicate" : String))] := by
  rfl

private def ComparisonTracks (state : ComparisonState) : Prop :=
  ∀ key first, state.seen[key]? = some first →
    ∃ item ∈ state.retained.toList, comparison? item = some (key, first)

private theorem comparisonStep_tracks (state : ComparisonState) (item : Json)
    (tracks : ComparisonTracks state) : ComparisonTracks (comparisonStep state item) := by
  unfold comparisonStep
  cases comparisonKey : comparison? item with
  | none =>
    intro key first found
    obtain ⟨earlier, member, source⟩ := tracks key first found
    exact ⟨earlier, by simp [member], source⟩
  | some entry =>
    obtain ⟨key, output⟩ := entry
    cases lookup : state.seen[key]? with
    | some first =>
      intro other prior found
      simp only [lookup] at found ⊢
      obtain ⟨earlier, member, source⟩ := tracks other prior found
      exact ⟨earlier, by simp [member], source⟩
    | none =>
      intro other prior found
      simp only [lookup] at found ⊢
      by_cases same : key = other
      · subst other
        change (state.seen.insert key output)[key]? = some prior at found
        simp at found
        subst prior
        exact ⟨item, by simp, comparisonKey⟩
      · obtain ⟨earlier, member, source⟩ := tracks other prior (by
          simpa [Std.HashMap.getElem?_insert, same] using found)
        exact ⟨earlier, by simp [member], source⟩

private theorem comparisonStep_tracks_fold (items : List Json) (state : ComparisonState)
    (tracks : ComparisonTracks state) :
    ComparisonTracks (items.foldl comparisonStep state) := by
  induction items generalizing state with
  | nil => simpa using tracks
  | cons item rest ih =>
    rw [List.foldl_cons]
    exact ih (comparisonStep state item) (comparisonStep_tracks state item tracks)

/-- At a duplicate cache hit, the output is a Copy of the earlier output name,
and the cache invariant points to a retained comparison with the exact same
ordered operands and width. -/
private theorem comparisonStep_duplicate (state : ComparisonState) (item : Json)
    (key : String × String × Nat) (output first : String)
    (recognized : comparison? item = some (key, output))
    (cached : state.seen[key]? = some first)
    (tracks : ComparisonTracks state) :
    ∃ earlier ∈ state.retained.toList,
      comparison? earlier = some (key, first) ∧
      (comparisonStep state item).retained =
        state.retained.push (comparisonCopyJson first output) := by
  obtain ⟨earlier, member, source⟩ := tracks key first cached
  refine ⟨earlier, member, source, ?_⟩
  simp [comparisonStep, recognized, cached]

/-- A duplicate reached after any prefix of the actual reuse traversal has a
retained first comparison with the same cache key, and emits its exact Copy. -/
private theorem reuseComparisons_duplicate_step (priorItems : List Json) (item : Json)
    (key : String × String × Nat) (output first : String)
    (recognized : comparison? item = some (key, output))
    (cached : (priorItems.foldl comparisonStep {}).seen[key]? = some first) :
    ∃ earlier ∈ (priorItems.foldl comparisonStep {}).retained.toList,
      comparison? earlier = some (key, first) ∧
      (comparisonStep (priorItems.foldl comparisonStep {}) item).retained =
        (priorItems.foldl comparisonStep {}).retained.push (comparisonCopyJson first output) := by
  apply comparisonStep_duplicate
  · exact recognized
  · exact cached
  · exact comparisonStep_tracks_fold priorItems {} (by
      intro prior result found
      simp at found)

private theorem comparisonCopy_no_key (prior output : String) :
    comparison? (comparisonCopyJson prior output) = none := by
  rfl

private def ComparisonSources (source : List Json) (state : ComparisonState) : Prop :=
  ∀ item ∈ state.retained.toList, (comparison? item).isSome = true → item ∈ source

private theorem comparisonStep_sources (source : List Json) (state : ComparisonState)
    (item : Json) (member : item ∈ source) (sources : ComparisonSources source state) :
    ComparisonSources source (comparisonStep state item) := by
  intro retained retainedMember recognized
  cases key : comparison? item with
  | none =>
    simp [comparisonStep, key, Array.toList_push] at retainedMember
    rcases retainedMember with next | next
    · exact sources retained (by simpa using next) recognized
    · simpa [next] using member
  | some entry =>
    obtain ⟨keyValue, output⟩ := entry
    cases cached : state.seen[keyValue]? with
    | none =>
      simp [comparisonStep, key, cached, Array.toList_push] at retainedMember
      rcases retainedMember with next | next
      · exact sources retained (by simpa using next) recognized
      · simpa [next] using member
    | some first =>
      simp [comparisonStep, key, cached, Array.toList_push] at retainedMember
      rcases retainedMember with next | next
      · exact sources retained (by simpa using next) recognized
      · simp [next, comparisonCopy_no_key] at recognized

private theorem comparisonStep_prefix_satisfaction (source : Array Json)
    (prior rest : List Json) (state : ComparisonState) (item : Json)
    (tracks : ComparisonTracks state) (sources : ComparisonSources prior state)
    (holds : Json → Prop)
    (invariant : (∀ output ∈ state.retained.toList, holds output) ↔
      (∀ original ∈ prior, holds original))
    (sourceSplit : source.toList = prior ++ item :: rest)
    (bridge : ∀ prior later rest, source.toList = prior ++ later :: rest →
      (∀ original ∈ prior, holds original) →
      ∀ earlier ∈ prior, ∀ key first output,
        comparison? earlier = some (key, first) → comparison? later = some (key, output) →
        ((holds earlier ∧ holds (comparisonCopyJson first output)) ↔
          (holds earlier ∧ holds later))) :
    (∀ output ∈ (comparisonStep state item).retained.toList, holds output) ↔
      (∀ original ∈ prior ++ [item], holds original) := by
  cases recognized : comparison? item with
  | none =>
    simpa only [comparisonStep, recognized, Array.toList_push,
      List.forall_mem_append, List.forall_mem_singleton] using
        (and_congr invariant Iff.rfl)
  | some entry =>
    obtain ⟨key, output⟩ := entry
    cases cached : state.seen[key]? with
    | none =>
      simpa only [comparisonStep, recognized, cached, Array.toList_push,
        List.forall_mem_append, List.forall_mem_singleton] using
          (and_congr invariant Iff.rfl)
    | some first =>
      obtain ⟨earlier, earlierMember, earlierKey, pushed⟩ :=
        comparisonStep_duplicate state item key output first recognized cached tracks
      have earlierInPrefix := sources earlier earlierMember (by simp [earlierKey])
      rw [pushed, Array.toList_push]
      simp only [List.forall_mem_append, List.forall_mem_singleton]
      constructor
      · rintro ⟨retainedHolds, copyHolds⟩
        have prefixHolds := invariant.mp retainedHolds
        have earlierHolds := prefixHolds earlier earlierInPrefix
        have bridgeHolds := bridge prior item rest sourceSplit prefixHolds
          earlier earlierInPrefix key first output earlierKey recognized
        obtain ⟨_, itemHolds⟩ := bridgeHolds.mp ⟨earlierHolds, copyHolds⟩
        exact ⟨prefixHolds, itemHolds⟩
      · rintro ⟨prefixHolds, itemHolds⟩
        have retainedHolds := invariant.mpr prefixHolds
        have earlierHolds := retainedHolds earlier earlierMember
        have bridgeHolds := bridge prior item rest sourceSplit prefixHolds
          earlier earlierInPrefix key first output earlierKey recognized
        obtain ⟨_, copyHolds⟩ := bridgeHolds.mpr ⟨earlierHolds, itemHolds⟩
        exact ⟨retainedHolds, copyHolds⟩

private theorem comparisonFold_prefix_satisfaction (source : Array Json)
    (holds : Json → Prop)
    (bridge : ∀ prior later rest, source.toList = prior ++ later :: rest →
      (∀ original ∈ prior, holds original) →
      ∀ earlier ∈ prior, ∀ key first output,
        comparison? earlier = some (key, first) → comparison? later = some (key, output) →
        ((holds earlier ∧ holds (comparisonCopyJson first output)) ↔
          (holds earlier ∧ holds later))) :
    ∀ (prior items : List Json) (state : ComparisonState),
      ComparisonTracks state → ComparisonSources prior state →
      ((∀ output ∈ state.retained.toList, holds output) ↔
        (∀ original ∈ prior, holds original)) →
      source.toList = prior ++ items →
      ((∀ output ∈ (items.foldl comparisonStep state).retained.toList, holds output) ↔
        (∀ original ∈ prior ++ items, holds original)) := by
  intro prior items
  induction items generalizing prior with
  | nil =>
    intro state tracks sources invariant sourceSplit
    simpa using invariant
  | cons item rest ih =>
    intro state tracks sources invariant sourceSplit
    have sourceStep : source.toList = prior ++ item :: rest := by
      simpa using sourceSplit
    let next := comparisonStep state item
    have nextTracks := comparisonStep_tracks state item tracks
    have nextSources : ComparisonSources (prior ++ [item]) next := by
      apply comparisonStep_sources (prior ++ [item]) state item
      · exact List.mem_append_right _ (List.mem_singleton_self item)
      · intro retained retainedMember recognized
        exact List.mem_append_left _ (sources retained retainedMember recognized)
    have nextInvariant := comparisonStep_prefix_satisfaction source prior rest state item
      tracks sources holds invariant sourceStep bridge
    have nextSplit : source.toList = (prior ++ [item]) ++ rest := by
      simpa [List.append_assoc] using sourceSplit
    have restResult := ih (prior := prior ++ [item]) next nextTracks nextSources
      nextInvariant nextSplit
    simpa [next, List.append_assoc] using restResult

/-- Replacing repeated comparisons preserves satisfaction when the copy and
original comparison agree under facts from the raw prefix. -/
theorem reuseComparisons_preserves_prefix_satisfaction (source : Array Json)
    (holds : Json → Prop)
    (bridge : ∀ prior later rest, source.toList = prior ++ later :: rest →
      (∀ item ∈ prior, holds item) →
      ∀ earlier ∈ prior, ∀ key first output,
        comparison? earlier = some (key, first) → comparison? later = some (key, output) →
        ((holds earlier ∧ holds (comparisonCopyJson first output)) ↔
          (holds earlier ∧ holds later))) :
    (∀ item ∈ (reuseComparisons source).toList, holds item) ↔
      (∀ item ∈ source.toList, holds item) := by
  simpa [reuseComparisons, Array.foldl_toList] using
    comparisonFold_prefix_satisfaction source holds bridge [] source.toList {} (by
      intro key first found
      simp at found) (by simp [ComparisonSources]) (by simp) (by simp)

/-- Every comparison pair used by the fold comes from the exact input vector. -/
theorem reuseComparisons_preserves_source_satisfaction (source : Array Json)
    (holds : Json → Prop)
    (bridge : ∀ earlier ∈ source.toList, ∀ later ∈ source.toList, ∀ key first output,
      comparison? earlier = some (key, first) → comparison? later = some (key, output) →
      ((holds earlier ∧ holds (comparisonCopyJson first output)) ↔ (holds earlier ∧ holds later))) :
    (∀ item ∈ (reuseComparisons source).toList, holds item) ↔
      (∀ item ∈ source.toList, holds item) := by
  apply reuseComparisons_preserves_prefix_satisfaction source holds
  intro prior later rest split _ earlier earlierMember key first output earlierKey laterKey
  have inSource : earlier ∈ source.toList := by
    rw [split]
    exact List.mem_append_left _ earlierMember
  have laterInSource : later ∈ source.toList := by
    rw [split]
    simp
  exact bridge earlier inSource later laterInSource key first output earlierKey laterKey

private theorem comparisonFold_observations (source items : List Json) (state : ComparisonState)
    (tracks : ComparisonTracks state) (sources : ComparisonSources source state)
    (remaining : ∀ item ∈ items, item ∈ source) (observe : Json → List α)
    (copied : ∀ earlier ∈ source, ∀ later ∈ source, ∀ key first output,
      comparison? earlier = some (key, first) → comparison? later = some (key, output) →
      observe (comparisonCopyJson first output) = observe later) :
    (items.foldl comparisonStep state).retained.toList.flatMap observe =
      state.retained.toList.flatMap observe ++ items.flatMap observe := by
  induction items generalizing state with
  | nil => simp
  | cons item rest ih =>
    have itemInSource := remaining item List.mem_cons_self
    rw [List.foldl_cons, ih (comparisonStep state item) (comparisonStep_tracks _ _ tracks)
      (comparisonStep_sources source state item itemInSource sources)
      (fun other member => remaining other (List.mem_cons_of_mem _ member))]
    cases key : comparison? item with
    | none => simp [comparisonStep, key, Array.toList_push, List.append_assoc]
    | some found =>
      obtain ⟨keyValue, output⟩ := found
      cases cached : state.seen[keyValue]? with
      | none => simp [comparisonStep, key, cached, Array.toList_push, List.append_assoc]
      | some first =>
        obtain ⟨earlier, member, earlierKey, pushed⟩ :=
          comparisonStep_duplicate state item keyValue output first key cached tracks
        have earlierInSource := sources earlier member (by simp [earlierKey])
        rw [pushed, Array.toList_push, List.flatMap_append]
        simp [copied earlier earlierInSource item itemInSource keyValue first output earlierKey key,
          List.append_assoc]

/-- The fold preserves ordered observations whenever each emitted Copy agrees
with the actual source comparison it replaces. -/
theorem reuseComparisons_preserves_observations (source : Array Json) (observe : Json → List α)
    (copied : ∀ earlier ∈ source.toList, ∀ later ∈ source.toList, ∀ key first output,
      comparison? earlier = some (key, first) → comparison? later = some (key, output) →
      observe (comparisonCopyJson first output) = observe later) :
    (reuseComparisons source).toList.flatMap observe = source.toList.flatMap observe := by
  simpa [reuseComparisons, Array.foldl_toList] using
    comparisonFold_observations source.toList source.toList {} (by
      intro key first found
      simp at found) (by simp [ComparisonSources]) (fun _ member => member) observe copied

private theorem step_retained (state : State) (item : Json) :
    (step state item).retained = state.retained ∨
      (step state item).retained = state.retained.push item := by
  unfold step
  split
  · exact .inr rfl
  · split
    · exact .inl rfl
    · exact .inr rfl

private theorem step_observation (observe : Json → List α) (state : State) (item : Json)
    (silent : ∀ name width, key? item = some (name, width) → observe item = []) :
    (step state item).retained.toList.flatMap observe =
      state.retained.toList.flatMap observe ++ observe item := by
  cases key : key? item with
  | none => simp [step, key]
  | some entry =>
    obtain ⟨operand, bits⟩ := entry
    rcases step_retained state item with retained | retained
    · simp [retained, silent operand bits key]
    · simp [retained]

private theorem fold_observations (observe : Json → List α) (instructions : List Json)
    (state : State)
    (silent : ∀ item ∈ instructions, ∀ name width, key? item = some (name, width) → observe item = []) :
    (instructions.foldl step state).retained.toList.flatMap observe =
      state.retained.toList.flatMap observe ++ instructions.flatMap observe := by
  induction instructions generalizing state with
  | nil => simp
  | cons item rest ih =>
    rw [List.foldl_cons, ih (step state item) (fun x hx => silent x (List.mem_cons_of_mem _ hx)),
      step_observation observe state item (silent item List.mem_cons_self)]
    simp [List.append_assoc]

private def Tracks (state : State) : Prop :=
  ∀ name width, state.widths[name]? = some width →
    ∃ item ∈ state.retained.toList, key? item = some (name, width)

private theorem tracks_step (state : State) (item : Json) (tracks : Tracks state) :
    Tracks (step state item) := by
  unfold step
  split
  next =>
    intro name width found
    obtain ⟨earlier, member, key⟩ := tracks name width found
    exact ⟨earlier, by simp [member], key⟩
  next operand bits key =>
    split
    · exact tracks
    · intro name width found
      by_cases same : operand = name
      · subst name
        change (state.widths.insert operand bits)[operand]? = some width at found
        simp at found
        subst width
        exact ⟨item, by simp, key⟩
      · obtain ⟨earlier, member, check⟩ := tracks name width (by
          simpa [Std.HashMap.getElem?_insert, same] using found)
        exact ⟨earlier, by simp [member], check⟩

private theorem fold_sublist (items : List Json) (state : State) :
    (items.foldl step state).retained.toList.Sublist (state.retained.toList ++ items) := by
  induction items generalizing state with
  | nil => simp
  | cons item rest ih =>
    have retained := ih (step state item)
    rcases step_retained state item with dropped | kept
    · rw [dropped] at retained
      exact retained.trans ((List.Sublist.cons item (List.Sublist.refl rest)).append_left _)
    · simpa [kept, List.append_assoc] using retained

/-- Optimization only removes items and preserves the original ordering. -/
theorem sublist (instructions : Array Json) :
    (run instructions).toList.Sublist instructions.toList := by
  simpa [run, Array.foldl_toList] using fold_sublist instructions.toList {}

private theorem recover_satisfaction (holds : Json → Prop) (read : String → Nat)
    (items : List Json) (state : State) (tracks : Tracks state)
    (meaning : ∀ item ∈ state.retained.toList ++ items, ∀ name width,
      key? item = some (name, width) → (holds item ↔ read name < 2 ^ width))
    (accepted : ∀ item ∈ (items.foldl step state).retained.toList, holds item) :
    ∀ item ∈ state.retained.toList ++ items, holds item := by
  induction items generalizing state with
  | nil => simpa using accepted
  | cons item rest ih =>
    have nextMeaning : ∀ json ∈ (step state item).retained.toList ++ rest, ∀ name width,
        key? json = some (name, width) → (holds json ↔ read name < 2 ^ width) := by
      intro json member
      apply meaning json
      rcases step_retained state item with dropped | kept
      · rw [dropped] at member
        exact (List.Sublist.cons item (List.Sublist.refl rest)).append_left state.retained.toList
          |>.subset member
      · simpa [kept, List.append_assoc] using member
    have recovered := ih (step state item) (tracks_step state item tracks) nextMeaning accepted
    cases key : key? item with
    | none => simpa [step, key, List.append_assoc] using recovered
    | some check =>
      obtain ⟨operand, bits⟩ := check
      by_cases covered : state.widths[operand]?.any (· ≤ bits)
      · have current : holds item := by
          cases lookup : state.widths[operand]? with
          | none => simp [lookup] at covered
          | some width =>
            simp [lookup] at covered
            obtain ⟨earlier, member, earlierKey⟩ := tracks operand width lookup
            have earlierHolds := recovered earlier (by simp [step, key, lookup, covered, member])
            have bound := (meaning earlier (List.mem_append_left _ member) operand width earlierKey).mp
              earlierHolds
            exact (meaning item (by simp) operand bits key).mpr
              (Nat.lt_of_lt_of_le bound (Nat.pow_le_pow_right (by decide) covered))
        intro json member
        simp only [step, key, covered, ↓reduceIte] at recovered
        rcases List.mem_append.mp member with prefixMember | suffixMember
        · exact recovered json (List.mem_append_left _ prefixMember)
        · rcases List.mem_cons.mp suffixMember with rfl | suffixMember
          · exact current
          · exact recovered json (List.mem_append_right _ suffixMember)
      · simpa [step, key, covered, List.append_assoc] using recovered

/-- Removing an implied range check preserves satisfaction for every assignment,
including assignments rejected by the original program. -/
theorem preserves_satisfaction (instructions : Array Json) (holds : Json → Prop)
    (read : String → Nat)
    (meaning : ∀ item ∈ instructions.toList, ∀ name width, key? item = some (name, width) →
      (holds item ↔ read name < 2 ^ width)) :
    (∀ item ∈ (run instructions).toList, holds item) ↔
      (∀ item ∈ instructions.toList, holds item) := by
  constructor
  · simpa [run, Array.foldl_toList] using
      recover_satisfaction holds read instructions.toList {} (by simp [Tracks]) (by simpa using meaning)
  · intro accepted item member
    exact accepted item ((sublist _).subset member)

/-- Range constraints do not project an input, an Impact event, or an output. -/
theorem preserves_observations (instructions : Array Json) (observe : Json → List α)
    (silent : ∀ item ∈ instructions.toList, ∀ name width,
      key? item = some (name, width) → observe item = []) :
    (run instructions).toList.flatMap observe = instructions.toList.flatMap observe := by
  simpa [run, Array.foldl_toList] using fold_observations observe instructions.toList {} silent

end Noctium.Backend.RangeDedup
