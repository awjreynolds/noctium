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

/-- Reuse the result of an identical, earlier comparison over immutable SSA
operands. Keep output identifiers, check ordering and per-use assertions. -/
def reuseComparisons (instructions : Array Json) : Array Json :=
  (instructions.foldl comparisonStep {}).retained

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

private theorem holds_after_duplicate (holds : Json → Prop) (retainedPrefix : List Json)
    (earlier copy later : Json) (rest : List Json) (earlierMember : earlier ∈ retainedPrefix)
    (bridge : (holds earlier ∧ holds copy) ↔ (holds earlier ∧ holds later)) :
    (∀ item ∈ retainedPrefix ++ [copy] ++ rest, holds item) ↔
      (∀ item ∈ retainedPrefix ++ later :: rest, holds item) := by
  simp only [List.forall_mem_append, List.forall_mem_singleton, List.forall_mem_cons,
    List.append_assoc]
  constructor
  · rintro ⟨prefixHolds, copyHolds, restHolds⟩
    have earlierHolds := prefixHolds earlier earlierMember
    obtain ⟨_, laterHolds⟩ := bridge.mp ⟨earlierHolds, copyHolds⟩
    exact ⟨prefixHolds, laterHolds, restHolds⟩
  · rintro ⟨prefixHolds, laterHolds, restHolds⟩
    have earlierHolds := prefixHolds earlier earlierMember
    obtain ⟨_, copyHolds⟩ := bridge.mpr ⟨earlierHolds, laterHolds⟩
    exact ⟨prefixHolds, copyHolds, restHolds⟩

private theorem comparisonFold_satisfaction (items : List Json) (state : ComparisonState)
    (tracks : ComparisonTracks state) (holds : Json → Prop)
    (bridge : ∀ earlier later key first output,
      ((comparison? earlier = some (key, first) ∧
        comparison? later = some (key, output)) ∧
        (holds earlier ∧ holds (comparisonCopyJson first output))) ↔
      ((comparison? earlier = some (key, first) ∧
        comparison? later = some (key, output)) ∧
        (holds earlier ∧ holds later))) :
    (∀ item ∈ (items.foldl comparisonStep state).retained.toList, holds item) ↔
      (∀ item ∈ state.retained.toList ++ items, holds item) := by
  induction items generalizing state with
  | nil => simp
  | cons item rest ih =>
    rw [List.foldl_cons]
    have nextTracks := comparisonStep_tracks state item tracks
    have tailEquiv := ih (comparisonStep state item) nextTracks
    rw [tailEquiv]
    cases comparisonKey : comparison? item with
    | none =>
      simp [comparisonStep, comparisonKey, Array.toList_push, List.append_assoc]
    | some entry =>
      obtain ⟨key, output⟩ := entry
      cases cached : state.seen[key]? with
      | none =>
        simp [comparisonStep, comparisonKey, cached, Array.toList_push, List.append_assoc]
      | some first =>
        obtain ⟨earlier, earlierMember, earlierKey, pushed⟩ :=
          comparisonStep_duplicate state item key output first comparisonKey cached tracks
        rw [pushed, Array.toList_push]
        have parserFacts : comparison? earlier = some (key, first) ∧
            comparison? item = some (key, output) := ⟨earlierKey, comparisonKey⟩
        have bridgeHere : (holds earlier ∧ holds (comparisonCopyJson first output)) ↔
            (holds earlier ∧ holds item) :=
          ⟨fun h => (bridge earlier item key first output).mp ⟨parserFacts, h⟩ |>.2,
            fun h => (bridge earlier item key first output).mpr ⟨parserFacts, h⟩ |>.2⟩
        exact holds_after_duplicate holds state.retained.toList earlier
          (comparisonCopyJson first output) item rest earlierMember
          bridgeHere

/-- The production comparison-reuse fold preserves any JSON instruction
predicate with the stated semantic bridge for matching comparison keys. -/
theorem reuseComparisons_preserves_satisfaction (instructions : Array Json)
    (holds : Json → Prop)
    (bridge : ∀ earlier later key first output,
      ((comparison? earlier = some (key, first) ∧
        comparison? later = some (key, output)) ∧
        (holds earlier ∧ holds (comparisonCopyJson first output))) ↔
      ((comparison? earlier = some (key, first) ∧
        comparison? later = some (key, output)) ∧
        (holds earlier ∧ holds later))) :
    (∀ item ∈ (reuseComparisons instructions).toList, holds item) ↔
      (∀ item ∈ instructions.toList, holds item) := by
  simpa [reuseComparisons, Array.foldl_toList] using
    comparisonFold_satisfaction instructions.toList {} (by
      intro key first found
      simp at found) holds bridge

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
