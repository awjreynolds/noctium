import Noctium.Backend.NativeProducer
import Noctium.Verification.NativeRelationJson
import Noctium.Verification.ScalarParserAgreement
import Noctium.Verification.ScalarNormalization

namespace Noctium.Verification.ScalarValidation

open Lean Backend.Native NativeRelation ScalarNormalization

theorem bind_ok {α β : Type} {value : Except String α} {next : α → Except String β}
    {result : β} : (value >>= next) = .ok result ↔
      ∃ found, value = .ok found ∧ next found = .ok result := by
  cases value <;> simp [Bind.bind, Except.bind]

theorem map_ok {α β : Type} {value : Except String α} {next : α → β}
    {result : β} : next <$> value = .ok result ↔
      ∃ found, value = .ok found ∧ next found = result := by
  cases value <;> simp [Functor.map, Except.map]

theorem ensure_ok {condition : Bool} {message : String} :
    Backend.Native.ensure condition message = .ok () ↔ condition = true := by
  cases condition <;> simp [Backend.Native.ensure] <;> rfl

/-- Facts describe arbitrary satisfying native assignments, not an evaluator
chosen to agree with the source. The comparison tag is conditional on assertion. -/
structure FactMeaning (hash : Hash) (inputs witness : Assignment) (fact : Fact)
    (value : Scalar) : Prop where
  term : value = interpret hash inputs fact.term
  bound : value.val ≤ fact.maximum
  comparison : ∀ identifier exclusive,
    fact.assertedLessThan = some (identifier, exclusive) → value ≠ zero →
      (witness identifier).val < exclusive

def StateMeaning (hash : Hash) (inputs witness : Assignment) (state : State) : Prop :=
  ∀ identifier fact, (identifier, fact) ∈ state.definitions →
    FactMeaning hash inputs witness fact (witness identifier)

theorem lookup_member {α β : Type} [BEq α] [LawfulBEq α]
    {items : List (α × β)} {name : α} {value : β}
    (found : items.lookup name = some value) : (name, value) ∈ items := by
  induction items with
  | nil => simp at found
  | cons head tail ih =>
    rcases head with ⟨key, item⟩
    simp only [List.lookup_cons] at found
    split at found
    next equal =>
      have equal : name = key := eq_of_beq equal
      cases found
      simp [equal]
    next => exact List.mem_cons_of_mem _ (ih found)

theorem empty_meaning (hash : Hash) (inputs witness : Assignment) :
    StateMeaning hash inputs witness {} := by
  intro identifier fact found
  simp at found

theorem immediate_canonical {text : String} {number : Nat}
    (accepted : immediate text = .ok number) : number < Field.modulus := by
  unfold immediate at accepted
  simp only [bind_ok] at accepted
  rcases accepted with ⟨_, _, accepted⟩
  split at accepted
  next bytes decoded =>
    simp only [bind_ok] at accepted
    rcases accepted with ⟨_, _, _, _, _, ranged, result⟩
    have range := ensure_ok.mp ranged
    cases result
    exact of_decide_eq_true range
  next => contradiction

theorem scalar_le (number : Nat) : (scalar number).val ≤ number := Nat.mod_le _ _

theorem operand_meaning {hash : Hash} {inputs witness : Assignment} {state : State}
    {text : String} {fact : Fact}
    (invariant : StateMeaning hash inputs witness state)
    (accepted : operand state text = .ok fact) :
    FactMeaning hash inputs witness fact
      (if text.startsWith "0x" then interpret hash inputs fact.term else witness text) := by
  unfold operand at accepted
  split at accepted
  next immediateText =>
    simp only [bind_ok] at accepted
    rcases accepted with ⟨number, parsed, result⟩
    cases result
    simp only [immediateText, ↓reduceIte]
    exact ⟨rfl, by simpa only [interpret] using scalar_le number,
      by intro _ _ tag; cases tag⟩
  next referenceText =>
    simp only [bind_ok] at accepted
    rcases accepted with ⟨_, _, accepted⟩
    split at accepted
    next existing found =>
      cases accepted
      simpa only [referenceText, Bool.false_eq_true, ↓reduceIte] using
        invariant text _ (lookup_member found)
    next => contradiction

/-- Reading an already-decoded operand has the same meaning as the producer's
actual lookup, including its canonical immediate parser. -/
def OperandAgreement (hash : Hash) (inputs witness : Assignment)
    (fact : Fact) (value : Operand) : Prop :=
  FactMeaning hash inputs witness fact (value.read witness)

theorem stringField_eq (value : Json) (name : String) :
    NativeRelationJson.stringField value name = stringField value name := rfl

theorem reference_not_immediate {text : String} (reference : text.startsWith "%" = true) :
    text.startsWith "0x" = false :=
  NativeRelationJson.reference_not_immediate reference

theorem lessThan_opcode (bits : Nat) : (s!"less_than:{bits}").startsWith "less_than:" = true := by
  apply String.startsWith_string_iff.mpr
  change "less_than:".toList <+: ("less_than:" ++ toString bits).toList
  rw [String.toList_append]
  exact List.prefix_append _ _

theorem interpret_lessThan (hash : Hash) (inputs : Assignment) (bits : Nat)
    (left right : Backend.Native.Term) :
    interpret hash inputs (.binary s!"less_than:{bits}" left right) =
      bit (decide ((interpret hash inputs left).val < (interpret hash inputs right).val)) := by
  have starts := lessThan_opcode bits
  have notAdd : s!"less_than:{bits}" ≠ "add" := by intro h; rw [h] at starts; contradiction
  have notMul : s!"less_than:{bits}" ≠ "mul" := by intro h; rw [h] at starts; contradiction
  have notEq : s!"less_than:{bits}" ≠ "test_eq" := by intro h; rw [h] at starts; contradiction
  simp only [interpret, beq_iff_eq, notAdd, notMul, notEq, ↓reduceIte, starts]

theorem decoded_reference {instruction : Json} {name text : String} {value : Operand}
    (textParsed : stringField instruction name = .ok text)
    (decoded : NativeRelationJson.decodeOperandField instruction name = .ok value)
    (reference : text.startsWith "%" = true) : value = .reference text := by
  unfold stringField at textParsed
  unfold NativeRelationJson.decodeOperandField at decoded
  simp only [bind_ok] at textParsed decoded
  rcases textParsed with ⟨json, jsonParsed, textParsed⟩
  rcases decoded with ⟨same, sameParsed, decoded⟩
  rw [jsonParsed] at sameParsed
  cases sameParsed
  unfold NativeRelationJson.decodeOperand at decoded
  simp only [bind_ok] at decoded
  rcases decoded with ⟨sameText, sameParsed, decoded⟩
  rw [textParsed] at sameParsed
  cases sameParsed
  simp only [reference_not_immediate reference, Bool.false_eq_true, ↓reduceIte, bind_ok] at decoded
  rcases decoded with ⟨_, _, result⟩
  cases result
  rfl

theorem operand_decoded_meaning
    (immediateAgreement : ∀ text number, immediate text = .ok number ↔
      NativeRelationJson.decodeImmediate text = .ok number)
    {hash : Hash} {inputs witness : Assignment} {state : State}
    {json : Json} {text : String} {fact : Fact} {value : Operand}
    (invariant : StateMeaning hash inputs witness state)
    (textParsed : json.getStr? = .ok text)
    (accepted : operand state text = .ok fact)
    (decoded : NativeRelationJson.decodeOperand json = .ok value) :
    OperandAgreement hash inputs witness fact value := by
  unfold NativeRelationJson.decodeOperand at decoded
  simp only [bind_ok] at decoded
  rcases decoded with ⟨foundText, parsedText, decoded⟩
  rw [textParsed] at parsedText
  cases parsedText
  have meaning := operand_meaning invariant accepted
  by_cases isImmediate : text.startsWith "0x"
  · simp only [isImmediate, ↓reduceIte] at decoded meaning
    simp only [bind_ok] at decoded
    rcases decoded with ⟨number, parsed, result⟩
    have producerParsed := (immediateAgreement text number).mpr parsed
    unfold operand at accepted
    simp only [isImmediate, ↓reduceIte, bind_ok] at accepted
    rcases accepted with ⟨sameNumber, sameParsed, accepted⟩
    rw [producerParsed] at sameParsed
    cases sameParsed
    cases accepted
    cases result
    exact ⟨by simp only [Operand.read, interpret], scalar_le _,
      by intro _ _ tag; cases tag⟩
  · simp only [isImmediate, Bool.false_eq_true, ↓reduceIte] at decoded meaning
    simp only [bind_ok] at decoded
    rcases decoded with ⟨_, _, result⟩
    cases result
    exact meaning

theorem argument_decoded_meaning
    (immediateAgreement : ∀ text number, immediate text = .ok number ↔
      NativeRelationJson.decodeImmediate text = .ok number)
    {hash : Hash} {inputs witness : Assignment} {state : State}
    {instruction : Json} {name : String} {fact : Fact} {value : Operand}
    (invariant : StateMeaning hash inputs witness state)
    (accepted : argument state instruction name = .ok fact)
    (decoded : NativeRelationJson.decodeOperandField instruction name = .ok value) :
    OperandAgreement hash inputs witness fact value := by
  unfold argument stringField at accepted
  unfold NativeRelationJson.decodeOperandField at decoded
  simp only [bind_ok] at accepted decoded
  rcases accepted with ⟨text, ⟨json, parsed, textParsed⟩, accepted⟩
  rcases decoded with ⟨same, sameParsed, decoded⟩
  rw [parsed] at sameParsed
  cases sameParsed
  exact operand_decoded_meaning immediateAgreement invariant textParsed accepted decoded

theorem mapM_value_agreement {α β γ δ : Type} (left : α → Except String β)
    (right : α → Except String γ) (leftValue : β → δ) (rightValue : γ → δ)
    (agreement : ∀ item a b, left item = .ok a → right item = .ok b →
      leftValue a = rightValue b)
    {items : List α} {a : List β} {b : List γ}
    (accepted : items.mapM left = .ok a) (decoded : items.mapM right = .ok b) :
    a.map leftValue = b.map rightValue := by
  induction items generalizing a b with
  | nil =>
    simp only [List.mapM_nil] at accepted decoded
    cases accepted
    cases decoded
    rfl
  | cons head tail ih =>
    simp only [List.mapM_cons, bind_ok] at accepted decoded
    rcases accepted with ⟨aHead, aHeadParsed, aTail, aTailParsed, result⟩
    rcases decoded with ⟨bHead, bHeadParsed, bTail, bTailParsed, decodedResult⟩
    cases result
    cases decodedResult
    simp only [List.map_cons, agreement head aHead bHead aHeadParsed bHeadParsed,
      ih aTailParsed bTailParsed]

theorem arguments_decoded_meaning
    (immediateAgreement : ∀ text number, immediate text = .ok number ↔
      NativeRelationJson.decodeImmediate text = .ok number)
    {hash : Hash} {inputs witness : Assignment} {state : State}
    {instruction : Json} {name : String} {facts : List Fact} {values : List Operand}
    (invariant : StateMeaning hash inputs witness state)
    (accepted : arguments state instruction name = .ok facts)
    (decoded : (do NativeRelationJson.decodeOperands (← instruction.getObjVal? name)) = .ok values) :
    values.map (·.read witness) = facts.map (fun fact => interpret hash inputs fact.term) := by
  unfold arguments arrayField at accepted
  simp only [bind_ok] at accepted decoded
  rcases accepted with ⟨array, ⟨json, parsed, arrayParsed⟩, _, _, accepted⟩
  rcases decoded with ⟨same, sameParsed, decoded⟩
  rw [parsed] at sameParsed
  cases sameParsed
  unfold NativeRelationJson.decodeOperands at decoded
  simp only [bind_ok] at decoded
  rcases decoded with ⟨sameArray, sameParsed, decoded⟩
  rw [arrayParsed] at sameParsed
  cases sameParsed
  symm
  apply mapM_value_agreement _ _ _ _ ?_ accepted decoded
  intro item fact value factParsed valueParsed
  simp only [bind_ok] at factParsed
  rcases factParsed with ⟨text, textParsed, factParsed⟩
  exact (operand_decoded_meaning immediateAgreement invariant textParsed factParsed valueParsed).term.symm

theorem combine_fields {term : Backend.Native.Term} {maximum : Nat} {children : List Fact} {fact : Fact}
    (accepted : combine term maximum children = .ok fact) :
    fact.term = term ∧ fact.maximum = maximum ∧ fact.assertedLessThan = none := by
  unfold combine at accepted
  simp only [bind_ok] at accepted
  rcases accepted with ⟨_, _, result⟩
  cases result
  exact ⟨rfl, rfl, rfl⟩

theorem combine_meaning {hash : Hash} {inputs witness : Assignment}
    {term : Backend.Native.Term} {maximum : Nat} {children : List Fact} {fact : Fact}
    {value : Scalar}
    (accepted : combine term maximum children = .ok fact)
    (meaning : value = interpret hash inputs term) (bound : value.val ≤ maximum) :
    FactMeaning hash inputs witness fact value := by
  obtain ⟨termEq, maximumEq, noTag⟩ := combine_fields accepted
  refine ⟨by simpa only [termEq] using meaning,
    by simpa only [maximumEq] using bound, ?_⟩
  intro _ _ tag
  rw [noTag] at tag
  cases tag

theorem bound_of_boolean {hash : Hash} {inputs witness : Assignment}
    {fact : Fact} {value : Scalar} (meaning : FactMeaning hash inputs witness fact value)
    (accepted : requireBoolean fact = .ok ()) : value.val ≤ 1 :=
  Nat.le_trans meaning.bound ((require_boolean_iff fact).mp accepted)

theorem define_meaning {hash : Hash} {inputs witness : Assignment} {state next : State}
    {identifier : String} {fact : Fact}
    (invariant : StateMeaning hash inputs witness state)
    (meaning : FactMeaning hash inputs witness fact (witness identifier))
    (accepted : define state identifier fact = .ok next) :
    StateMeaning hash inputs witness next := by
  unfold define at accepted
  simp only [bind_ok] at accepted
  rcases accepted with ⟨_, _, _, fresh, result⟩
  cases result
  intro name found member
  simp only [List.mem_append, List.mem_singleton, Prod.mk.injEq] at member
  rcases member with member | ⟨sameName, sameFact⟩
  · exact invariant name found member
  · subst name
    subst found
    exact meaning

theorem refine_meaning {hash : Hash} {inputs witness : Assignment} {state next : State}
    {text : String} {maximum : Nat}
    (invariant : StateMeaning hash inputs witness state)
    (bounded : text.startsWith "%" = true → (witness text).val ≤ maximum)
    (accepted : refine state text maximum = .ok next) :
    StateMeaning hash inputs witness next := by
  unfold refine at accepted
  simp only [bind_ok] at accepted
  rcases accepted with ⟨fact, _, accepted⟩
  split at accepted
  next referenceText =>
    cases accepted
    intro name value member
    simp only [List.mem_map] at member
    rcases member with ⟨⟨oldName, oldValue⟩, member, equal⟩
    have meaning := invariant oldName oldValue member
    cases same : oldName == text
    · simp only [same, Bool.false_eq_true, ↓reduceIte, Prod.mk.injEq] at equal
      rcases equal with ⟨rfl, rfl⟩
      exact meaning
    · have nameEq : oldName = text := eq_of_beq same
      simp only [same, ↓reduceIte, Prod.mk.injEq] at equal
      rcases equal with ⟨rfl, rfl⟩
      refine ⟨meaning.term, ?_, meaning.comparison⟩
      exact Nat.le_min.mpr ⟨meaning.bound, by simpa [nameEq] using bounded referenceText⟩
  next =>
    simp only [bind_ok] at accepted
    rcases accepted with ⟨_, _, result⟩
    cases result
    exact invariant

theorem boolean_of_bound (value : Scalar) (bound : value.val ≤ 1) :
    value = zero ∨ value = one := by
  have cases : value.val = 0 ∨ value.val = 1 := by omega
  rcases cases with h | h
  · exact Or.inl (Fin.ext h)
  · exact Or.inr (Fin.ext h)

theorem asserted_boolean_one {value : Scalar} (bound : value.val ≤ 1)
    (nonzero : value ≠ zero) : value = one := by
  rcases boolean_of_bound value bound with h | h
  · exact False.elim (nonzero h)
  · exact h

theorem modular_add_bound (left right : Scalar) (leftMax rightMax : Nat)
    (leftBound : left.val ≤ leftMax) (rightBound : right.val ≤ rightMax) :
    (scalar (left.val + right.val)).val ≤
      if leftMax + rightMax < Field.modulus then leftMax + rightMax else Field.modulus - 1 := by
  split
  · exact Nat.le_trans (scalar_le _) (Nat.add_le_add leftBound rightBound)
  · have canonical := (scalar (left.val + right.val)).isLt
    omega

theorem modular_mul_bound (left right : Scalar) (leftMax rightMax : Nat)
    (leftBound : left.val ≤ leftMax) (rightBound : right.val ≤ rightMax) :
    (scalar (left.val * right.val)).val ≤
      if leftMax * rightMax < Field.modulus then leftMax * rightMax else Field.modulus - 1 := by
  split
  · exact Nat.le_trans (scalar_le _) (Nat.mul_le_mul leftBound rightBound)
  · have canonical := (scalar (left.val * right.val)).isLt
    omega

theorem defineResult_meaning {hash : Hash} {inputs witness : Assignment} {state next : State}
    {instruction : Json} {fact : Fact}
    (invariant : StateMeaning hash inputs witness state)
    (meaning : ∀ identifier, stringField instruction "output" = .ok identifier →
      FactMeaning hash inputs witness fact (witness identifier))
    (accepted : defineResult state instruction fact = .ok next) :
    StateMeaning hash inputs witness next := by
  unfold defineResult at accepted
  simp only [bind_ok] at accepted
  rcases accepted with ⟨identifier, parsed, accepted⟩
  exact define_meaning invariant (meaning identifier parsed) accepted

def SameCounters (left right : State) : Prop :=
  left.inputCount = right.inputCount ∧ left.groupCount = right.groupCount ∧
    left.assertionCount = right.assertionCount

theorem define_counters {state next : State} {identifier : String} {fact : Fact}
    (accepted : define state identifier fact = .ok next) : SameCounters next state := by
  unfold define at accepted
  simp only [bind_ok] at accepted
  rcases accepted with ⟨_, _, _, _, result⟩
  cases result
  exact ⟨rfl, rfl, rfl⟩

theorem defineResult_counters {state next : State} {instruction : Json} {fact : Fact}
    (accepted : defineResult state instruction fact = .ok next) : SameCounters next state := by
  unfold defineResult at accepted
  simp only [bind_ok] at accepted
  rcases accepted with ⟨_, _, defined⟩
  exact define_counters defined

theorem refine_counters {state next : State} {text : String} {maximum : Nat}
    (accepted : refine state text maximum = .ok next) : SameCounters next state := by
  unfold refine at accepted
  simp only [bind_ok] at accepted
  rcases accepted with ⟨_, _, accepted⟩
  split at accepted
  · cases accepted
    exact ⟨rfl, rfl, rfl⟩
  · simp only [bind_ok] at accepted
    rcases accepted with ⟨_, _, result⟩
    cases result
    exact ⟨rfl, rfl, rfl⟩

theorem state_checkBound {hash : Hash} {inputs witness : Assignment} {state : State}
    {term : Backend.Native.Term} {maximum : Nat}
    (invariant : StateMeaning hash inputs witness state)
    (accepted : checkBound state term maximum = .ok ()) :
    (interpret hash inputs term).val ≤ maximum := by
  unfold checkBound at accepted
  have bounded := ensure_ok.mp accepted
  cases term
  next value =>
    have bounded : value ≤ maximum := of_decide_eq_true bounded
    simpa only [interpret] using Nat.le_trans (scalar_le value) bounded
  all_goals
    obtain ⟨⟨identifier, fact⟩, member, factBound⟩ := List.any_eq_true.mp bounded
    have factBound := Bool.and_eq_true_iff.mp factBound
    have termEq := eq_of_beq factBound.1
    have meaning := invariant identifier fact member
    rw [← termEq, ← meaning.term]
    exact Nat.le_trans meaning.bound (of_decide_eq_true factBound.2)

theorem bound_requirements {hash : Hash} {inputs witness : Assignment} {state : State}
    {bounds : List (Backend.Native.Term × Nat)}
    (invariant : StateMeaning hash inputs witness state)
    (accepted : ∀ requirement ∈ bounds, checkBound state requirement.1 requirement.2 = .ok ()) :
    ∀ requirement ∈ bounds, (interpret hash inputs requirement.1).val ≤ requirement.2 := by
  intro requirement member
  exact state_checkBound invariant (accepted requirement member)

/-- This is the exact indexed `for` body in `Native.validate`. Indexes affect
diagnostics only. No second instruction checker is introduced. -/
def validationLoop (expected : Expected) (instructions : List (Json × Nat))
    (initial : State) : Except String State :=
  forIn instructions initial fun (instruction, index) state =>
    match validateInstruction expected state instruction with
    | .ok next => pure (.yield next)
    | .error message => do
      throw s!"native instruction {index}: {message}"
      pure (.yield state)

theorem forIn_checks {α : Type} {items : List α} {check : α → Except String Unit}
    {result : PUnit}
    (accepted : forIn items PUnit.unit (fun item _ => do
      check item
      pure (.yield PUnit.unit)) = .ok result) :
    ∀ item ∈ items, check item = .ok () := by
  induction items with
  | nil => simp
  | cons head tail ih =>
    rw [List.forIn_cons] at accepted
    cases checked : check head with
    | error error => simp [checked, Bind.bind, Except.bind] at accepted
    | ok value =>
      cases value
      simp only [checked, bind_pure_comp] at accepted
      intro item member
      rcases List.mem_cons.mp member with rfl | member
      · exact checked
      · exact ih accepted item member

structure ValidationResult (expected : Expected) (state : State) : Prop where
  inputs : state.inputCount = expected.inputs.length
  groups : state.groupCount = expected.groups.length
  assertions : state.assertionCount = expected.assertions.length
  inputBounds : ∀ input ∈ expected.inputs,
    checkBound state (.input input.identifier) (sourceMaximum input.ty) = .ok ()
  bounds : ∀ requirement ∈ expected.bounds,
    checkBound state requirement.1 requirement.2 = .ok ()

theorem validate_result {expected : Expected} {program : Json}
    (accepted : validate expected program = .ok ()) :
    ∃ instructions : Array Json, ∃ state : State,
      arrayField program "instructions" = .ok instructions ∧
      requireFinalOutput instructions.toList = .ok () ∧
      validationLoop expected instructions.toList.zipIdx {} = .ok state ∧
      ValidationResult expected state := by
  unfold validate at accepted
  simp only [bind_ok] at accepted
  rcases accepted with ⟨_, _, version, _, _, _, _, _, _, _, _, _, _, _, _, _,
    _, _, _, _, _, _, _, _, _, _, _, _, instructions, parsedInstructions,
    _, _, _, finalOutput, state, trace, _, inputCount, _, groupCount,
    _, assertionCount, _, inputBounds, _, bounds, _⟩
  refine ⟨instructions, state, parsedInstructions, finalOutput, trace, ?_⟩
  refine ⟨eq_of_beq (ensure_ok.mp inputCount), eq_of_beq (ensure_ok.mp groupCount),
    eq_of_beq (ensure_ok.mp assertionCount), ?_, ?_⟩
  · exact forIn_checks inputBounds
  · exact forIn_checks bounds

def InputAgreement (expected : Expected) (inputs witness : Assignment) : Prop :=
 ∀ requirement ∈ expected.inputs, witness requirement.identifier = inputs requirement.identifier

theorem step_meaning
    (immediateAgreement : ∀ text number, immediate text = .ok number ↔
      NativeRelationJson.decodeImmediate text = .ok number)
    (natAgreement : ∀ json name a b, natField json name = .ok a →
      NativeRelationJson.naturalField json name = .ok b → a = b)
    {hash : Hash} {inputs witness : Assignment} {expected : Expected}
    {state next : State} {raw : Json} {instruction : Instruction}
    (invariant : StateMeaning hash inputs witness state)
    (inputAgreement : InputAgreement expected inputs witness)
    (accepted : validateInstruction expected state raw = .ok next)
    (decoded : NativeRelationJson.decodeInstruction raw = .ok instruction)
    (holds : instruction.Holds hash witness) :
    StateMeaning hash inputs witness next := by
  unfold validateInstruction at accepted
  simp only [bind_ok] at accepted
  rcases accepted with ⟨opcode, op, descriptor, registry, _, fields, accepted⟩
  split at accepted
  case h_1 =>
    simp only [bind_ok] at accepted
    rcases accepted with ⟨_, _, _, _, _, _, _, _, accepted⟩
    split at accepted
    next requirement requirementParsed =>
      simp only [bind_ok] at accepted
      rcases accepted with ⟨output, outputParsed, _, schema, definedState, defined, result⟩
      have outputEq : output = requirement.identifier := eq_of_beq
        (Bool.and_eq_true_iff.mp (ensure_ok.mp schema)).1
      have inputEq : witness output = inputs output := by
        rw [outputEq]
        exact inputAgreement requirement (List.mem_of_getElem? requirementParsed)
      cases result
      apply define_meaning invariant ?_ defined
      refine ⟨by simpa only [interpret] using inputEq, ?_, ?_⟩
      · change (witness output).val ≤ Field.modulus - 1
        have canonical := (witness output).isLt
        omega
      · intro _ _ tag
        cases tag
    next => contradiction
  case h_2 =>
    simp only [bind_ok] at accepted
    rcases accepted with ⟨_, _, _, _, _, _, _, _, accepted⟩
    split at accepted
    next requirement requirementParsed =>
      simp only [bind_ok] at accepted
      rcases accepted with ⟨output, outputParsed, _, schema, definedState, defined, result⟩
      have outputEq : output = requirement.identifier := eq_of_beq
        (Bool.and_eq_true_iff.mp (ensure_ok.mp schema)).1
      have inputEq : witness output = inputs output := by
        rw [outputEq]
        exact inputAgreement requirement (List.mem_of_getElem? requirementParsed)
      cases result
      apply define_meaning invariant ?_ defined
      refine ⟨by simpa only [interpret] using inputEq, ?_, ?_⟩
      · change (witness output).val ≤ Field.modulus - 1
        have canonical := (witness output).isLt
        omega
      · intro _ _ tag
        cases tag
    next => contradiction
  case h_3 =>
    simp [bind_ok] at accepted
    rcases accepted with ⟨left, leftParsed, right, rightParsed, fact, combined, defined⟩
    simp [NativeRelationJson.decodeInstruction, stringField_eq, op, bind_ok, map_ok] at decoded
    rcases decoded with ⟨_, a, aParsed, b, bParsed, output, outputParsed, _, _, result⟩
    have leftMeaning := argument_decoded_meaning immediateAgreement invariant leftParsed aParsed
    have rightMeaning := argument_decoded_meaning immediateAgreement invariant rightParsed bParsed
    apply defineResult_meaning invariant ?_ defined
    intro identifier parsed
    rw [outputParsed] at parsed
    cases parsed
    apply combine_meaning combined
    · simp only [interpret, beq_self_eq_true, ↓reduceIte, ← leftMeaning.term, ← rightMeaning.term]
      exact holds
    · rw [holds]
      exact modular_add_bound _ _ _ _ leftMeaning.bound rightMeaning.bound
  case h_4 =>
    simp [bind_ok] at accepted
    rcases accepted with ⟨left, leftParsed, right, rightParsed, fact, combined, defined⟩
    simp [NativeRelationJson.decodeInstruction, stringField_eq, op, bind_ok, map_ok] at decoded
    rcases decoded with ⟨_, a, aParsed, b, bParsed, output, outputParsed, _, _, result⟩
    have leftMeaning := argument_decoded_meaning immediateAgreement invariant leftParsed aParsed
    have rightMeaning := argument_decoded_meaning immediateAgreement invariant rightParsed bParsed
    apply defineResult_meaning invariant ?_ defined
    intro identifier parsed
    rw [outputParsed] at parsed
    cases parsed
    apply combine_meaning combined
    · simp [← leftMeaning.term, ← rightMeaning.term]
      exact holds
    · rw [holds]
      exact modular_mul_bound _ _ _ _ leftMeaning.bound rightMeaning.bound
  case h_5 =>
    simp [bind_ok] at accepted
    rcases accepted with ⟨left, leftParsed, right, rightParsed, fact, combined, defined⟩
    simp [NativeRelationJson.decodeInstruction, stringField_eq, op, bind_ok, map_ok] at decoded
    rcases decoded with ⟨_, a, aParsed, b, bParsed, output, outputParsed, _, _, result⟩
    have leftMeaning := argument_decoded_meaning immediateAgreement invariant leftParsed aParsed
    have rightMeaning := argument_decoded_meaning immediateAgreement invariant rightParsed bParsed
    apply defineResult_meaning invariant ?_ defined
    intro identifier parsed
    rw [outputParsed] at parsed
    cases parsed
    apply combine_meaning combined
    · simp [← leftMeaning.term, ← rightMeaning.term]
      exact holds
    · rw [holds]
      exact by have h := bit_canonical (decide (a.read witness = b.read witness)); omega
  case h_6 =>
    simp [bind_ok] at accepted
    rcases accepted with ⟨value, valueParsed, fact, combined, defined⟩
    simp [NativeRelationJson.decodeInstruction, stringField_eq, op, bind_ok, map_ok] at decoded
    rcases decoded with ⟨_, a, aParsed, output, outputParsed, _, _, result⟩
    have valueMeaning := argument_decoded_meaning immediateAgreement invariant valueParsed aParsed
    apply defineResult_meaning invariant ?_ defined
    intro identifier parsed
    rw [outputParsed] at parsed
    cases parsed
    apply combine_meaning combined
    · simp [← valueMeaning.term]
      exact holds
    · split
      next zeroMax =>
        have zeroVal : (a.read witness).val = 0 := by have h := valueMeaning.bound; omega
        rw [holds]
        simp [zeroVal, scalar]
      next => have h := (witness output).isLt; omega
  case h_7 =>
    simp [bind_ok] at accepted
    rcases accepted with ⟨value, valueParsed, ⟨_, boolean⟩, fact, combined, defined⟩
    simp [NativeRelationJson.decodeInstruction, stringField_eq, op, bind_ok, map_ok] at decoded
    rcases decoded with ⟨_, a, aParsed, output, outputParsed, _, _, result⟩
    have valueMeaning := argument_decoded_meaning immediateAgreement invariant valueParsed aParsed
    apply defineResult_meaning invariant ?_ defined
    intro identifier parsed
    rw [outputParsed] at parsed
    cases parsed
    apply combine_meaning combined
    · simpa [interpret, ← valueMeaning.term, bit] using holds.2
    · rw [holds.2]
      split <;> simp [zero, one]
  case h_8 =>
    simp [bind_ok] at accepted
    rcases accepted with ⟨condition, conditionParsed, ⟨_, boolean⟩, yes, yesParsed, no, noParsed,
      fact, combined, defined⟩
    simp [NativeRelationJson.decodeInstruction, stringField_eq, op, bind_ok, map_ok] at decoded
    rcases decoded with ⟨_, bitValue, bitParsed, a, aParsed, b, bParsed,
      output, outputParsed, _, _, result⟩
    have conditionMeaning := argument_decoded_meaning immediateAgreement invariant conditionParsed bitParsed
    have yesMeaning := argument_decoded_meaning immediateAgreement invariant yesParsed aParsed
    have noMeaning := argument_decoded_meaning immediateAgreement invariant noParsed bParsed
    apply defineResult_meaning invariant ?_ defined
    intro identifier parsed
    rw [outputParsed] at parsed
    cases parsed
    apply combine_meaning combined
    · simpa [interpret, ← conditionMeaning.term, ← yesMeaning.term, ← noMeaning.term] using holds.2
    · rw [holds.2]
      split
      · exact Nat.le_trans yesMeaning.bound (Nat.le_max_left _ _)
      · exact Nat.le_trans noMeaning.bound (Nat.le_max_right _ _)
  case h_9 =>
    simp only [bind_ok] at accepted
    rcases accepted with ⟨text, textParsed, refined⟩
    simp [NativeRelationJson.decodeInstruction, stringField_eq, op, bind_ok, map_ok] at decoded
    rcases decoded with ⟨_, value, valueParsed, result⟩
    cases result
    apply refine_meaning invariant ?_ refined
    intro reference
    have valueEq := decoded_reference textParsed valueParsed reference
    rw [valueEq] at holds
    rcases holds with equal | equal <;> rw [Operand.read] at equal <;> rw [equal] <;> simp [zero, one]
  case h_10 =>
    simp only [bind_ok] at accepted
    rcases accepted with ⟨text, textParsed, width, widthParsed, refined⟩
    simp [NativeRelationJson.decodeInstruction, stringField_eq, op, bind_ok, map_ok] at decoded
    rcases decoded with ⟨_, bits, bitsParsed, _, value, valueParsed, rfl⟩
    have widthEq : width = bits := by
      unfold Backend.Native.width at widthParsed
      simp only [bind_ok] at widthParsed
      rcases widthParsed with ⟨found, foundParsed, _, _, result⟩
      cases result
      exact natAgreement raw "bits" _ bits foundParsed bitsParsed
    subst width
    apply refine_meaning invariant ?_ refined
    intro reference
    have valueEq := decoded_reference textParsed valueParsed reference
    rw [valueEq] at holds
    exact range_constraint_bound hash witness (.reference text) bits holds
  case h_11 =>
    simp only [bind_ok] at accepted
    rcases accepted with ⟨leftText, leftTextParsed, rightText, rightTextParsed,
      left, leftParsed, right, rightParsed, middle, leftRefined, rightRefined⟩
    simp [NativeRelationJson.decodeInstruction, stringField_eq, op, bind_ok, map_ok] at decoded
    rcases decoded with ⟨_, a, aParsed, b, bParsed, rfl⟩
    have leftArg : argument state raw "a" = .ok left := by
      unfold argument
      simp only [leftTextParsed]
      exact leftParsed
    have rightArg : argument state raw "b" = .ok right := by
      unfold argument
      simp only [rightTextParsed]
      exact rightParsed
    have leftMeaning := argument_decoded_meaning immediateAgreement invariant leftArg aParsed
    have rightMeaning := argument_decoded_meaning immediateAgreement invariant rightArg bParsed
    have equal : a.read witness = b.read witness := holds
    have leftBound : leftText.startsWith "%" = true →
        (witness leftText).val ≤ min left.maximum right.maximum := by
      intro reference
      have aEq := decoded_reference leftTextParsed aParsed reference
      have bound := Nat.le_min.mpr ⟨leftMeaning.bound, by simpa only [← equal] using rightMeaning.bound⟩
      simpa only [aEq, Operand.read] using bound
    have rightBound : rightText.startsWith "%" = true →
        (witness rightText).val ≤ min left.maximum right.maximum := by
      intro reference
      have bEq := decoded_reference rightTextParsed bParsed reference
      have bound := Nat.le_min.mpr ⟨by simpa only [equal] using leftMeaning.bound, rightMeaning.bound⟩
      simpa only [bEq, Operand.read] using bound
    exact refine_meaning (refine_meaning invariant leftBound leftRefined) rightBound rightRefined
  case h_12 =>
    simp only [bind_ok] at accepted
    rcases accepted with ⟨leftText, leftTextParsed, left, leftParsed, right, rightParsed,
      width, widthParsed, _, ranged, fact, combined, defined⟩
    simp [NativeRelationJson.decodeInstruction, stringField_eq, op, bind_ok, map_ok] at decoded
    rcases decoded with ⟨_, bits, bitsParsed, _, a, aParsed, b, bParsed,
      output, outputParsed, _, rfl⟩
    have widthEq : width = bits := by
      unfold Backend.Native.width at widthParsed
      simp only [bind_ok] at widthParsed
      rcases widthParsed with ⟨found, foundParsed, _, _, result⟩
      cases result
      exact natAgreement raw "bits" _ bits foundParsed bitsParsed
    subst width
    have leftArg : argument state raw "a" = .ok left := by
      unfold argument
      simp only [leftTextParsed]
      exact leftParsed
    have leftMeaning := argument_decoded_meaning immediateAgreement invariant leftArg aParsed
    have rightMeaning := argument_decoded_meaning immediateAgreement invariant rightParsed bParsed
    have ranges := Bool.and_eq_true_iff.mp (ensure_ok.mp ranged)
    have leftBound : (a.read witness).val < 2 ^ bits :=
      Nat.lt_of_le_of_lt leftMeaning.bound (of_decide_eq_true ranges.1)
    have rightBound : (b.read witness).val < 2 ^ bits :=
      Nat.lt_of_le_of_lt rightMeaning.bound (of_decide_eq_true ranges.2)
    have resultMeaning := holds leftBound rightBound
    have factMeaning : FactMeaning hash inputs witness fact (witness output) := by
      apply combine_meaning combined
      · rw [interpret_lessThan, ← leftMeaning.term, ← rightMeaning.term]
        exact resultMeaning
      · rw [resultMeaning]
        have h := bit_canonical (decide ((a.read witness).val < (b.read witness).val))
        omega
    apply defineResult_meaning invariant ?_ defined
    intro identifier parsed
    rw [outputParsed] at parsed
    cases parsed
    refine ⟨factMeaning.term, factMeaning.bound, ?_⟩
    intro identifier exclusive tag nonzero
    change (match right.term with
      | .constant bound => if leftText.startsWith "%" then some (leftText, bound) else none
      | _ => none) = some (identifier, exclusive) at tag
    cases rightTerm : right.term <;> simp only [rightTerm] at tag <;> try contradiction
    next bound =>
      split at tag
      next reference =>
        cases tag
        have leftReference := decoded_reference leftTextParsed aParsed reference
        have strict : (a.read witness).val < (b.read witness).val := by
          by_cases strict : (a.read witness).val < (b.read witness).val
          · exact strict
          · apply False.elim (nonzero ?_)
            simpa only [strict, decide_false, bit, Bool.false_eq_true, ↓reduceIte] using resultMeaning
        have constantBound : (b.read witness).val ≤ exclusive := by
          rw [rightMeaning.term, rightTerm]
          simpa only [interpret] using scalar_le exclusive
        simpa only [leftReference, Operand.read] using Nat.lt_of_lt_of_le strict constantBound
      next => contradiction
  case h_13 =>
    simp only [bind_ok] at accepted
    rcases accepted with ⟨value, valueParsed, _, boolean, accepted⟩
    simp [NativeRelationJson.decodeInstruction, stringField_eq, op, bind_ok, map_ok] at decoded
    rcases decoded with ⟨_, condition, conditionParsed, rfl⟩
    have valueMeaning := argument_decoded_meaning immediateAgreement invariant valueParsed conditionParsed
    have middleMeaning : StateMeaning hash inputs witness
        (if expected.assertions[state.assertionCount]? == some value.term then
          {state with assertionCount := state.assertionCount + 1} else state) := by
      split <;> exact invariant
    split at accepted
    next pair identifier exclusive tag =>
      simp only [bind_ok] at accepted
      rcases accepted with ⟨_, _, refined⟩
      have strict := valueMeaning.comparison identifier exclusive tag holds
      exact refine_meaning middleMeaning (by intro _; omega) refined
    next =>
      cases accepted
      exact middleMeaning
  case h_14 =>
    simp only [bind_ok] at accepted
    rcases accepted with ⟨values, valuesParsed, _, _, fact, combined, defined⟩
    simp [NativeRelationJson.decodeInstruction, stringField_eq, op, bind_ok, map_ok] at decoded
    rcases decoded with ⟨_, jsonValues, jsonParsed, nativeValues, valuesDecoded, output, outputParsed, _, rfl⟩
    have valuesMeaning := arguments_decoded_meaning immediateAgreement invariant valuesParsed (by
      simp only [jsonParsed]; exact valuesDecoded)
    apply defineResult_meaning invariant ?_ defined
    intro identifier parsed
    rw [outputParsed] at parsed
    cases parsed
    apply combine_meaning combined
    · simpa [Instruction.Holds, interpret, valuesMeaning, List.map_map, Function.comp_def] using holds
    · have canonical := (witness output).isLt
      omega
  case h_15 =>
    simp only [bind_ok] at accepted
    rcases accepted with ⟨_, _, _, _, _, _, _, _, _, _, accepted⟩
    split at accepted
    next group found =>
      simp only [bind_ok] at accepted
      rcases accepted with ⟨_, _, result⟩
      cases result
      exact invariant
    next => contradiction
  case h_16 =>
    simp only [bind_ok] at accepted
    rcases accepted with ⟨_, _, _, _, result⟩
    cases result
    exact invariant
  case h_17 => contradiction


theorem step_counters {expected : Expected} {state next : State} {raw : Json} {opcode : String}
    (op : stringField raw "op" = .ok opcode)
    (accepted : validateInstruction expected state raw = .ok next) :
    next.inputCount = state.inputCount + (if opcode == "public_input" || opcode == "private_input" then 1 else 0) ∧
    next.groupCount = state.groupCount + (if opcode == "impact" then 1 else 0) ∧
    (opcode ≠ "assert" → next.assertionCount = state.assertionCount) := by
  unfold validateInstruction at accepted
  simp only [bind_ok] at accepted
  rcases accepted with ⟨found, foundOp, descriptor, _, _, _, accepted⟩
  rw [op] at foundOp
  cases foundOp
  split at accepted
  case h_1 =>
    simp only [bind_ok] at accepted
    rcases accepted with ⟨_, _, _, _, _, _, _, _, accepted⟩
    split at accepted
    next requirement requirementParsed =>
      simp only [bind_ok] at accepted
      rcases accepted with ⟨output, _, _, _, middle, defined, result⟩
      have counters := define_counters defined
      cases result
      simpa [SameCounters] using counters
    next => contradiction
  case h_2 =>
    simp only [bind_ok] at accepted
    rcases accepted with ⟨_, _, _, _, _, _, _, _, accepted⟩
    split at accepted
    next requirement requirementParsed =>
      simp only [bind_ok] at accepted
      rcases accepted with ⟨output, _, _, _, middle, defined, result⟩
      have counters := define_counters defined
      cases result
      simpa [SameCounters] using counters
    next => contradiction
  case h_3 =>
    simp [bind_ok] at accepted
    rcases accepted with ⟨_, _, _, _, _, _, defined⟩
    have counters := defineResult_counters defined
    simpa [SameCounters] using counters
  case h_4 =>
    simp [bind_ok] at accepted
    rcases accepted with ⟨_, _, _, _, _, _, defined⟩
    have counters := defineResult_counters defined
    simpa [SameCounters] using counters
  case h_5 =>
    simp [bind_ok] at accepted
    rcases accepted with ⟨_, _, _, _, _, _, defined⟩
    have counters := defineResult_counters defined
    simpa [SameCounters] using counters
  case h_6 =>
    simp [bind_ok] at accepted
    rcases accepted with ⟨_, _, _, _, defined⟩
    have counters := defineResult_counters defined
    simpa [SameCounters] using counters
  case h_7 =>
    simp [bind_ok] at accepted
    rcases accepted with ⟨_, _, _, _, _, defined⟩
    have counters := defineResult_counters defined
    simpa [SameCounters] using counters
  case h_8 =>
    simp [bind_ok] at accepted
    rcases accepted with ⟨_, _, _, _, _, _, _, _, _, defined⟩
    have counters := defineResult_counters defined
    simpa [SameCounters] using counters
  case h_12 =>
    simp [bind_ok] at accepted
    rcases accepted with ⟨_, _, _, _, _, _, _, _, _, _, _, defined⟩
    have counters := defineResult_counters defined
    simpa [SameCounters] using counters
  case h_14 =>
    simp [bind_ok] at accepted
    rcases accepted with ⟨_, _, _, _, _, defined⟩
    have counters := defineResult_counters defined
    simpa [SameCounters] using counters
  case h_9 =>
    simp only [bind_ok] at accepted
    rcases accepted with ⟨_, _, refined⟩
    have counters := refine_counters refined
    simpa [SameCounters] using counters
  case h_10 =>
    simp only [bind_ok] at accepted
    rcases accepted with ⟨_, _, _, _, refined⟩
    have counters := refine_counters refined
    simpa [SameCounters] using counters
  case h_11 =>
    simp only [bind_ok] at accepted
    rcases accepted with ⟨_, _, _, _, _, _, _, _, _, leftRefined, rightRefined⟩
    have leftCounters := refine_counters leftRefined
    have rightCounters := refine_counters rightRefined
    simp only [SameCounters] at leftCounters rightCounters
    simp
    exact ⟨rightCounters.1.trans leftCounters.1,
      rightCounters.2.1.trans leftCounters.2.1, rightCounters.2.2.trans leftCounters.2.2⟩
  case h_13 =>
    simp only [bind_ok] at accepted
    rcases accepted with ⟨value, _, _, _, accepted⟩
    split at accepted
    next pair identifier exclusive tag =>
      simp only [bind_ok] at accepted
      rcases accepted with ⟨_, _, refined⟩
      have counters := refine_counters refined
      simp only [SameCounters] at counters
      simp
      refine ⟨counters.1.trans ?_, counters.2.1.trans ?_⟩ <;> split <;> rfl
    next =>
      cases accepted
      split <;> simp
  case h_15 =>
    simp only [bind_ok] at accepted
    rcases accepted with ⟨_, _, _, _, _, _, _, _, _, _, accepted⟩
    split at accepted
    next group found =>
      simp only [bind_ok] at accepted
      rcases accepted with ⟨_, _, result⟩
      cases result
      simp
    next => contradiction
  case h_16 =>
    simp only [bind_ok] at accepted
    rcases accepted with ⟨_, _, _, _, result⟩
    cases result
    simp
  case h_17 => contradiction

def AssertionsMeaning (hash : Hash) (inputs : Assignment) (expected : Expected) (count : Nat) : Prop :=
  ∀ term ∈ expected.assertions.take count, interpret hash inputs term = one

theorem assertions_advance {hash : Hash} {inputs : Assignment} {expected : Expected}
    {count : Nat} {term : Backend.Native.Term}
    (prior : AssertionsMeaning hash inputs expected count)
    (found : expected.assertions[count]? = some term)
    (meaning : interpret hash inputs term = one) :
    AssertionsMeaning hash inputs expected (count + 1) := by
  intro value member
  rw [List.take_add_one, found] at member
  simp only [Option.toList_some, List.mem_append, List.mem_singleton] at member
  rcases member with member | rfl
  · exact prior value member
  · exact meaning

theorem step_assertions
    (immediateAgreement : ∀ text number, immediate text = .ok number ↔
      NativeRelationJson.decodeImmediate text = .ok number)
    {hash : Hash} {inputs witness : Assignment} {expected : Expected}
    {state next : State} {raw : Json} {instruction : Instruction}
    (invariant : StateMeaning hash inputs witness state)
    (prior : AssertionsMeaning hash inputs expected state.assertionCount)
    (accepted : validateInstruction expected state raw = .ok next)
    (decoded : NativeRelationJson.decodeInstruction raw = .ok instruction)
    (holds : instruction.Holds hash witness) :
    AssertionsMeaning hash inputs expected next.assertionCount := by
  have original := accepted
  unfold validateInstruction at accepted
  simp only [bind_ok] at accepted
  rcases accepted with ⟨opcode, op, descriptor, registry, _, fields, accepted⟩
  by_cases isAssert : opcode = "assert"
  · subst opcode
    simp only [bind_ok] at accepted
    rcases accepted with ⟨value, valueParsed, booleanUnit, boolean, accepted⟩
    cases booleanUnit
    simp [NativeRelationJson.decodeInstruction, stringField_eq, op, bind_ok, map_ok] at decoded
    rcases decoded with ⟨_, condition, conditionParsed, rfl⟩
    have valueMeaning := argument_decoded_meaning immediateAgreement invariant valueParsed conditionParsed
    have asserted := asserted_boolean_one (bound_of_boolean valueMeaning boolean) holds
    have termMeaning : interpret hash inputs value.term = one := valueMeaning.term.symm.trans asserted
    let middle : State := if expected.assertions[state.assertionCount]? == some value.term then
      {state with assertionCount := state.assertionCount + 1} else state
    have middleMeaning : AssertionsMeaning hash inputs expected middle.assertionCount := by
      unfold middle
      split
      next matched => exact assertions_advance prior (eq_of_beq matched) termMeaning
      next => exact prior
    split at accepted
    next pair identifier exclusive tag =>
      simp only [bind_ok] at accepted
      rcases accepted with ⟨_, _, refined⟩
      have counters := refine_counters refined
      rw [counters.2.2]
      exact middleMeaning
    next =>
      cases accepted
      exact middleMeaning
  · have counters := step_counters op original
    rw [counters.2.2 isAssert]
    exact prior

theorem validationLoop_meaning
    (immediateAgreement : ∀ text number, immediate text = .ok number ↔
      NativeRelationJson.decodeImmediate text = .ok number)
    (natAgreement : ∀ json name a b, natField json name = .ok a →
      NativeRelationJson.naturalField json name = .ok b → a = b)
    {hash : Hash} {inputs witness : Assignment} {expected : Expected}
    {items : List (Json × Nat)} {instructions : List Instruction} {state next : State}
    (invariant : StateMeaning hash inputs witness state)
    (prior : AssertionsMeaning hash inputs expected state.assertionCount)
    (inputAgreement : InputAgreement expected inputs witness)
    (accepted : validationLoop expected items state = .ok next)
    (decoded : (items.map Prod.fst).mapM NativeRelationJson.decodeInstruction = .ok instructions)
    (holds : ∀ instruction ∈ instructions, instruction.Holds hash witness) :
    StateMeaning hash inputs witness next ∧ AssertionsMeaning hash inputs expected next.assertionCount := by
  induction items generalizing instructions state with
  | nil =>
    simp only [validationLoop, List.forIn_nil] at accepted
    cases accepted
    exact ⟨invariant, prior⟩
  | cons head tail ih =>
    rw [validationLoop, List.forIn_cons] at accepted
    cases checked : validateInstruction expected state head.1 with
    | error message =>
      simp [checked, Bind.bind, Except.bind] at accepted
    | ok middle =>
      simp only [checked, pure_bind] at accepted
      simp only [List.map_cons, List.mapM_cons, bind_ok] at decoded
      rcases decoded with ⟨instruction, instructionParsed, remaining, remainingParsed, result⟩
      cases result
      have instructionHolds := holds instruction (by simp)
      have nextInvariant := step_meaning immediateAgreement natAgreement invariant inputAgreement checked instructionParsed instructionHolds
      have nextAssertions := step_assertions immediateAgreement invariant prior checked instructionParsed instructionHolds
      exact ih nextInvariant nextAssertions accepted remainingParsed
        (by intro instruction member; exact holds instruction (List.mem_cons_of_mem _ member))

theorem decode_result {program : Json} {relation : Program}
    (decoded : NativeRelationJson.decode program = .ok relation) :
    ∃ instructions : Array Json,
      arrayField program "instructions" = .ok instructions ∧
      instructions.toList.mapM NativeRelationJson.decodeInstruction = .ok relation.instructions := by
  unfold NativeRelationJson.decode at decoded
  simp only [bind_ok] at decoded
  rcases decoded with ⟨_, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _,
    _, _, _, _, _, _, instructions, parsed, decodedInstructions, decodedParsed, result⟩
  cases result
  exact ⟨instructions, parsed, decodedParsed⟩

theorem zipIdx_values {α : Type} (items : List α) (offset : Nat) :
    (items.zipIdx offset).map Prod.fst = items := by
  induction items generalizing offset with
  | nil => rfl
  | cons head tail ih => simp only [List.zipIdx_cons, List.map_cons, ih]

structure ValidatedRequirements (hash : Hash) (inputs : Assignment) (expected : Expected) : Prop where
  inputBounds : ∀ requirement ∈ expected.inputs,
    (inputs requirement.identifier).val ≤ sourceMaximum requirement.ty
  bounds : ∀ requirement ∈ expected.bounds,
    (interpret hash inputs requirement.1).val ≤ requirement.2
  assertions : ∀ term ∈ expected.assertions, interpret hash inputs term = one

theorem validate_requirements_with_parsers
    (immediateAgreement : ∀ text number, immediate text = .ok number ↔
      NativeRelationJson.decodeImmediate text = .ok number)
    (natAgreement : ∀ json name a b, natField json name = .ok a →
      NativeRelationJson.naturalField json name = .ok b → a = b)
    {hash : Hash} {inputs witness : Assignment} {expected : Expected}
    {program : Json} {relation : Program}
    (inputAgreement : InputAgreement expected inputs witness)
    (accepted : validate expected program = .ok ())
    (decoded : NativeRelationJson.decode program = .ok relation)
    (holds : ∀ instruction ∈ relation.instructions, instruction.Holds hash witness) :
    ValidatedRequirements hash inputs expected := by
  obtain ⟨instructions, state, parsed, finalOutput, trace, final⟩ := validate_result accepted
  obtain ⟨decodedInstructions, decodedParsed, decodedTrace⟩ := decode_result decoded
  rw [parsed] at decodedParsed
  cases decodedParsed
  have initAssertions : AssertionsMeaning hash inputs expected 0 := by
    intro term member
    simp at member
  have meaning := validationLoop_meaning immediateAgreement natAgreement
    (empty_meaning hash inputs witness) initAssertions inputAgreement trace
    (by simpa only [zipIdx_values] using decodedTrace) holds
  refine ⟨?_, bound_requirements meaning.1 final.bounds, ?_⟩
  · intro requirement member
    have bounded := state_checkBound meaning.1 (final.inputBounds requirement member)
    simpa only [interpret] using bounded
  · have assertions := meaning.2
    rw [final.assertions] at assertions
    simpa only [AssertionsMeaning, List.take_length] using assertions

def instructionOpcode : Instruction → String
 | .input visibility _ => if visibility == .public then "public_input" else "private_input"
 | .boolean _ => "constrain_to_boolean"
 | .bits _ _ => "constrain_bits"
 | .lessThan _ _ _ _ => "less_than"
 | .add _ _ _ => "add"
 | .mul _ _ _ => "mul"
 | .neg _ _ => "neg"
 | .equal _ _ => "constrain_eq"
 | .testEq _ _ _ => "test_eq"
 | .not _ _ => "not"
 | .select _ _ _ _ => "cond_select"
 | .hash _ _ => "transient_hash"
 | .assert _ => "assert"
 | .impact _ _ => "impact"
 | .output _ => "output"

theorem decoded_opcode {raw : Json} {instruction : Instruction}
    (decoded : NativeRelationJson.decodeInstruction raw = .ok instruction) :
    stringField raw "op" = .ok (instructionOpcode instruction) := by
  unfold NativeRelationJson.decodeInstruction at decoded
  simp only [bind_ok, stringField_eq] at decoded
  rcases decoded with ⟨opcode, op, decoded⟩
  split at decoded
  all_goals
    simp [bind_ok, map_ok] at decoded
    first
    | grind [instructionOpcode]
    | skip
  case h_1 =>
    rcases decoded with ⟨_, _, _, _, _, _, _, output, _, _, rfl⟩
    have same : (Visibility.public == Visibility.public) = true := by decide
    simpa [instructionOpcode, same] using op
  case h_2 =>
    rcases decoded with ⟨_, _, _, _, _, _, _, output, _, _, rfl⟩
    have same : (Visibility.private == Visibility.public) = false := by decide
    simpa [instructionOpcode, same] using op
  case h_15 =>
    rcases decoded with ⟨_, guard, _, decoded⟩
    cases guard <;> simp [bind_ok, map_ok] at decoded
    grind [instructionOpcode]

def instructionGroups (witness : Assignment) : Instruction → List (List Scalar)
 | .impact _ values => [values.map (·.read witness)]
 | _ => []

theorem step_groups
    (immediateAgreement : ∀ text number, immediate text = .ok number ↔
      NativeRelationJson.decodeImmediate text = .ok number)
    {hash : Hash} {inputs witness : Assignment} {expected : Expected}
    {state next : State} {raw : Json} {instruction : Instruction}
    (invariant : StateMeaning hash inputs witness state)
    (accepted : validateInstruction expected state raw = .ok next)
    (decoded : NativeRelationJson.decodeInstruction raw = .ok instruction) :
    (expected.groups.take next.groupCount).map (List.map (interpret hash inputs)) =
      (expected.groups.take state.groupCount).map (List.map (interpret hash inputs)) ++
        instructionGroups witness instruction := by
  have op := decoded_opcode decoded
  cases instruction
  all_goals first
    | have groupCount := (step_counters op accepted).2.1
      simp [instructionOpcode] at groupCount
      simp only [groupCount, instructionGroups, List.append_nil]
      done
    | skip
  case input visibility output =>
    have counters := step_counters op accepted
    simp only [instructionOpcode] at counters
    split at counters <;> simp at counters <;>
      simp only [counters.2.1, instructionGroups, List.append_nil]
  case impact guard nativeValues =>
    change stringField raw "op" = .ok "impact" at op
    simp [validateInstruction, op, bind_ok] at accepted
    rcases accepted with ⟨_, _, _, _, _, _, _, _, _, values, valuesParsed, accepted⟩
    split at accepted
    next group groupParsed =>
      simp only [map_ok] at accepted
      rcases accepted with ⟨_, equalityCheck, result⟩
      cases result
      have matched : values.map (·.term) = group := eq_of_beq (ensure_ok.mp equalityCheck)
      simp [NativeRelationJson.decodeInstruction, stringField_eq, op, bind_ok] at decoded
      rcases decoded with ⟨_, decodedGuard, _, decoded⟩
      cases decodedGuard <;> simp [bind_ok, map_ok] at decoded
      rcases decoded with ⟨_, json, jsonParsed, valuesDecoded, _⟩
      have valuesMeaning := arguments_decoded_meaning immediateAgreement invariant valuesParsed (by
        simp only [jsonParsed]; exact valuesDecoded)
      have valueEq : nativeValues.map (·.read witness) = group.map (interpret hash inputs) := by
        rw [← matched]
        simpa only [List.map_map, Function.comp_def] using valuesMeaning
      change (expected.groups.take (state.groupCount + 1)).map (List.map (interpret hash inputs)) =
        (expected.groups.take state.groupCount).map (List.map (interpret hash inputs)) ++
          [nativeValues.map (·.read witness)]
      simp only [List.take_add_one, groupParsed, Option.toList_some, List.map_append,
        List.map_cons, List.map_nil, valueEq]
    next => contradiction

theorem step_output
    (immediateAgreement : ∀ text number, immediate text = .ok number ↔
      NativeRelationJson.decodeImmediate text = .ok number)
    {hash : Hash} {inputs witness : Assignment} {expected : Expected}
    {state next : State} {raw : Json} {values : List Operand}
    (invariant : StateMeaning hash inputs witness state)
    (accepted : validateInstruction expected state raw = .ok next)
    (decoded : NativeRelationJson.decodeInstruction raw = .ok (.output values)) :
    values.map (·.read witness) = expected.returns.map (interpret hash inputs) := by
  have op := decoded_opcode decoded
  change stringField raw "op" = .ok "output" at op
  simp [validateInstruction, op, bind_ok, map_ok] at accepted
  rcases accepted with ⟨_, _, _, facts, factsParsed, ⟨checkedUnit, equalityCheck⟩, rfl⟩
  have matched : facts.map (·.term) = expected.returns := eq_of_beq (ensure_ok.mp equalityCheck)
  simp [NativeRelationJson.decodeInstruction, stringField_eq, op, bind_ok, map_ok] at decoded
  rcases decoded with ⟨_, json, jsonParsed, valuesParsed⟩
  have valuesMeaning := arguments_decoded_meaning immediateAgreement invariant factsParsed (by
    simp only [jsonParsed]; exact valuesParsed)
  rw [← matched]
  simpa only [List.map_map, Function.comp_def] using valuesMeaning

theorem validationLoop_observations
    (immediateAgreement : ∀ text number, immediate text = .ok number ↔
      NativeRelationJson.decodeImmediate text = .ok number)
    (natAgreement : ∀ json name a b, natField json name = .ok a →
      NativeRelationJson.naturalField json name = .ok b → a = b)
    {hash : Hash} {inputs witness : Assignment} {expected : Expected}
    {items : List (Json × Nat)} {instructions : List Instruction} {state next : State}
    (invariant : StateMeaning hash inputs witness state)
    (inputAgreement : InputAgreement expected inputs witness)
    (accepted : validationLoop expected items state = .ok next)
    (decoded : (items.map Prod.fst).mapM NativeRelationJson.decodeInstruction = .ok instructions)
    (holds : ∀ instruction ∈ instructions, instruction.Holds hash witness) :
    (expected.groups.take next.groupCount).map (List.map (interpret hash inputs)) =
        (expected.groups.take state.groupCount).map (List.map (interpret hash inputs)) ++
          instructions.flatMap (instructionGroups witness) ∧
      ∀ values, .output values ∈ instructions →
        values.map (·.read witness) = expected.returns.map (interpret hash inputs) := by
  induction items generalizing instructions state with
  | nil =>
    simp only [validationLoop, List.forIn_nil] at accepted
    cases accepted
    simp only [List.map_nil, List.mapM_nil] at decoded
    cases decoded
    exact ⟨by simp, by simp⟩
  | cons head tail ih =>
    rw [validationLoop, List.forIn_cons] at accepted
    cases checked : validateInstruction expected state head.1 with
    | error message => simp [checked, Bind.bind, Except.bind] at accepted
    | ok middle =>
      simp only [checked, pure_bind] at accepted
      simp only [List.map_cons, List.mapM_cons, bind_ok] at decoded
      rcases decoded with ⟨instruction, instructionParsed, remaining, remainingParsed, result⟩
      cases result
      have instructionHolds := holds instruction (by simp)
      have nextInvariant := step_meaning immediateAgreement natAgreement invariant inputAgreement checked instructionParsed instructionHolds
      have rest := ih nextInvariant accepted remainingParsed
        (by intro instruction member; exact holds instruction (List.mem_cons_of_mem _ member))
      refine ⟨?_, ?_⟩
      · rw [rest.1, step_groups immediateAgreement invariant checked instructionParsed]
        simp only [List.flatMap_cons, List.append_assoc]
      · intro values member
        rcases List.mem_cons.mp member with first | restMember
        · subst instruction
          exact step_output immediateAgreement invariant checked instructionParsed
        · exact rest.2 values restMember

theorem groups_flatMap (program : Program) (witness : Assignment) :
    program.groups witness = program.instructions.flatMap (instructionGroups witness) := by
  unfold Program.groups
  induction program.instructions with
  | nil => rfl
  | cons instruction remaining ih =>
    cases instruction <;> simp [instructionGroups, ih]

theorem decoded_opcodes {raw : List Json} {instructions : List Instruction}
    (decoded : raw.mapM NativeRelationJson.decodeInstruction = .ok instructions) :
    raw.map Backend.Native.opcode = instructions.map instructionOpcode := by
  induction raw generalizing instructions with
  | nil =>
    simp only [List.mapM_nil] at decoded
    cases decoded
    rfl
  | cons head tail ih =>
    simp only [List.mapM_cons, bind_ok] at decoded
    rcases decoded with ⟨instruction, instructionParsed, remaining, remainingParsed, result⟩
    cases result
    have op := decoded_opcode instructionParsed
    have headEq : Backend.Native.opcode head = instructionOpcode instruction := by
      unfold Backend.Native.opcode
      rw [op]
      rfl
    simp only [List.map_cons, headEq, ih remainingParsed]

def outputGroups (witness : Assignment) (instructions : List Instruction) : List (List Scalar) :=
  instructions.filterMap fun instruction => match instruction with
    | .output values => some (values.map (·.read witness))
    | _ => none

theorem outputGroups_count (witness : Assignment) (instructions : List Instruction) :
    (outputGroups witness instructions).length =
      (instructions.map instructionOpcode).count "output" := by
  induction instructions with
  | nil => rfl
  | cons instruction remaining ih =>
    simp only [outputGroups] at ih
    cases instruction <;> simp [outputGroups, instructionOpcode, ih]
    next visibility output => split <;> simp_all

theorem returns_flatten (program : Program) (witness : Assignment) :
    program.returns witness = (outputGroups witness program.instructions).flatten := by
  unfold Program.returns outputGroups
  induction program.instructions with
  | nil => rfl
  | cons instruction remaining ih =>
    cases instruction <;> simp [ih]

theorem outputs_uniform {witness : Assignment} {instructions : List Instruction} {expected : List Scalar}
    (observed : ∀ values, .output values ∈ instructions → values.map (·.read witness) = expected) :
    ∀ group ∈ outputGroups witness instructions, group = expected := by
  intro group member
  obtain ⟨instruction, instructionMember, produces⟩ := List.mem_filterMap.mp member
  cases instruction <;> try contradiction
  next values =>
    cases produces
    exact observed values instructionMember

theorem returns_of_single_output {program : Program} {witness : Assignment} {expected : List Scalar}
    (count : (program.instructions.map instructionOpcode).count "output" = 1)
    (observed : ∀ values, .output values ∈ program.instructions → values.map (·.read witness) = expected) :
    program.returns witness = expected := by
  have lengthOne : (outputGroups witness program.instructions).length = 1 := by
    rw [outputGroups_count, count]
  obtain ⟨group, groupsEq⟩ := List.length_eq_one_iff.mp lengthOne
  have groupEq := outputs_uniform observed group (by rw [groupsEq]; simp)
  rw [returns_flatten, groupsEq, groupEq]
  simp

theorem validate_observations_with_parsers
    (immediateAgreement : ∀ text number, immediate text = .ok number ↔
      NativeRelationJson.decodeImmediate text = .ok number)
    (natAgreement : ∀ json name a b, natField json name = .ok a →
      NativeRelationJson.naturalField json name = .ok b → a = b)
    {hash : Hash} {inputs witness : Assignment} {expected : Expected}
    {program : Json} {relation : Program}
    (inputAgreement : InputAgreement expected inputs witness)
    (accepted : validate expected program = .ok ())
    (decoded : NativeRelationJson.decode program = .ok relation)
    (holds : ∀ instruction ∈ relation.instructions, instruction.Holds hash witness) :
    relation.groups witness = expected.groups.map (List.map (interpret hash inputs)) ∧
      relation.returns witness = expected.returns.map (interpret hash inputs) := by
  obtain ⟨instructions, state, parsed, finalOutput, trace, final⟩ := validate_result accepted
  obtain ⟨decodedInstructions, decodedParsed, decodedTrace⟩ := decode_result decoded
  rw [parsed] at decodedParsed
  cases decodedParsed
  have observations := validationLoop_observations immediateAgreement natAgreement
    (empty_meaning hash inputs witness) inputAgreement trace
    (by simpa only [zipIdx_values] using decodedTrace) holds
  refine ⟨?_, ?_⟩
  · rw [groups_flatMap]
    have groups := observations.1
    rw [final.groups] at groups
    simpa only [List.take_length, List.take_zero, List.map_nil, List.nil_append] using groups.symm
  · apply returns_of_single_output ?_ observations.2
    have shape := (final_output_required instructions.toList).mp finalOutput
    unfold finalOutputShape at shape
    have count := (Bool.and_eq_true_iff.mp (Bool.and_eq_true_iff.mp shape).1).2
    have countEq : (instructions.toList.map Backend.Native.opcode).count "output" = 1 := eq_of_beq count
    rw [decoded_opcodes decodedTrace] at countEq
    exact countEq

def inputSchema (requirement : InputRequirement) : Visibility × String :=
  (requirement.visibility, requirement.identifier)

def instructionInputs : Instruction → List (Visibility × String)
 | .input visibility output => [(visibility, output)]
 | _ => []

theorem step_inputs {expected : Expected} {state next : State} {raw : Json} {instruction : Instruction}
    (accepted : validateInstruction expected state raw = .ok next)
    (decoded : NativeRelationJson.decodeInstruction raw = .ok instruction) :
    (expected.inputs.take next.inputCount).map inputSchema =
      (expected.inputs.take state.inputCount).map inputSchema ++ instructionInputs instruction := by
  have op := decoded_opcode decoded
  cases instruction
  all_goals first
    | have inputCount := (step_counters op accepted).1
      simp [instructionOpcode] at inputCount
      simp only [inputCount, instructionInputs, List.append_nil]
      done
    | skip
  case input visibility output =>
    cases visibility
    case «public» =>
      have visible : (Visibility.public == Visibility.public) = true := by decide
      simp only [instructionOpcode, visible, ↓reduceIte] at op
      simp [validateInstruction, op, bind_ok] at accepted
      simp [NativeRelationJson.decodeInstruction, stringField_eq, op, bind_ok, map_ok] at decoded
      rcases decoded with ⟨_, _, _, _, _, _, _, outputParsed, _⟩
      rcases accepted with ⟨_, _, _, _, _, _, _, _, _, accepted⟩
      split at accepted
      next requirement requirementParsed =>
        simp [outputParsed, bind_ok, map_ok] at accepted
        rcases accepted with ⟨⟨_, schema⟩, middle, defined, result⟩
        have counters := define_counters defined
        have schema := Bool.and_eq_true_iff.mp (ensure_ok.mp schema)
        have outputEq : output = requirement.identifier := eq_of_beq schema.1
        have visibilityEq : requirement.visibility = .public := by
          cases found : requirement.visibility
          case «public» => rfl
          case «private» =>
            have different : (Visibility.private == Visibility.public) = false := by decide
            have impossible := schema.2
            simp [found, different] at impossible
        cases result
        change (expected.inputs.take (middle.inputCount + 1)).map inputSchema =
          (expected.inputs.take state.inputCount).map inputSchema ++ [(Visibility.public, output)]
        rw [counters.1, List.take_add_one, requirementParsed]
        simp only [Option.toList_some, List.map_append, List.map_cons, List.map_nil,
          inputSchema, visibilityEq, ← outputEq]
      next => contradiction
    case «private» =>
      have visible : (Visibility.private == Visibility.public) = false := by decide
      simp only [instructionOpcode, visible] at op
      simp [validateInstruction, op, bind_ok] at accepted
      simp [NativeRelationJson.decodeInstruction, stringField_eq, op, bind_ok, map_ok] at decoded
      rcases decoded with ⟨_, _, _, _, _, _, _, outputParsed, _⟩
      rcases accepted with ⟨_, _, _, _, _, _, _, _, _, accepted⟩
      split at accepted
      next requirement requirementParsed =>
        simp [outputParsed, bind_ok, map_ok] at accepted
        rcases accepted with ⟨⟨_, schema⟩, middle, defined, result⟩
        have counters := define_counters defined
        have schema := Bool.and_eq_true_iff.mp (ensure_ok.mp schema)
        have outputEq : output = requirement.identifier := eq_of_beq schema.1
        have visibilityEq : requirement.visibility = .private := by
          cases found : requirement.visibility
          case «private» => rfl
          case «public» =>
            have different : (Visibility.public == Visibility.public) = true := by decide
            have impossible := schema.2
            simp [found, different] at impossible
        cases result
        change (expected.inputs.take (middle.inputCount + 1)).map inputSchema =
          (expected.inputs.take state.inputCount).map inputSchema ++ [(Visibility.private, output)]
        rw [counters.1, List.take_add_one, requirementParsed]
        simp only [Option.toList_some, List.map_append, List.map_cons, List.map_nil,
          inputSchema, visibilityEq, ← outputEq]
      next => contradiction

theorem validationLoop_inputs {expected : Expected}
    {items : List (Json × Nat)} {instructions : List Instruction} {state next : State}
    (accepted : validationLoop expected items state = .ok next)
    (decoded : (items.map Prod.fst).mapM NativeRelationJson.decodeInstruction = .ok instructions) :
    (expected.inputs.take next.inputCount).map inputSchema =
      (expected.inputs.take state.inputCount).map inputSchema ++ instructions.flatMap instructionInputs := by
  induction items generalizing instructions state with
  | nil =>
    simp only [validationLoop, List.forIn_nil] at accepted
    cases accepted
    simp only [List.map_nil, List.mapM_nil] at decoded
    cases decoded
    simp
  | cons head tail ih =>
    rw [validationLoop, List.forIn_cons] at accepted
    cases checked : validateInstruction expected state head.1 with
    | error message => simp [checked, Bind.bind, Except.bind] at accepted
    | ok middle =>
      simp only [checked, pure_bind] at accepted
      simp only [List.map_cons, List.mapM_cons, bind_ok] at decoded
      rcases decoded with ⟨instruction, instructionParsed, remaining, remainingParsed, result⟩
      cases result
      have rest := ih accepted remainingParsed
      rw [rest, step_inputs checked instructionParsed]
      simp only [List.flatMap_cons, List.append_assoc]

def schemaValues (witness : Assignment) (visibility : Visibility) (schema : List (Visibility × String)) : List Scalar :=
  schema.filterMap fun (found, name) => if found == visibility then some (witness name) else none

theorem inputValues_schema (program : Program) (witness : Assignment) (visibility : Visibility) :
    program.inputValues visibility witness =
      schemaValues witness visibility (program.instructions.flatMap instructionInputs) := by
  unfold Program.inputValues schemaValues
  induction program.instructions with
  | nil => rfl
  | cons instruction remaining ih =>
    cases instruction <;> simp [instructionInputs, ih]
    next found name =>
      simp only [List.filterMap_cons]
      split <;> simp_all

theorem schemaValues_agree {inputs witness : Assignment} {requirements : List InputRequirement}
    (agreement : ∀ requirement ∈ requirements, witness requirement.identifier = inputs requirement.identifier)
    (visibility : Visibility) :
    schemaValues witness visibility (requirements.map inputSchema) =
      schemaValues inputs visibility (requirements.map inputSchema) := by
  induction requirements with
  | nil => rfl
  | cons requirement remaining ih =>
    have headAgreement := agreement requirement (by simp)
    have tailAgreement := ih (by intro requirement member; exact agreement requirement (List.mem_cons_of_mem _ member))
    simp only [List.map_cons, schemaValues, inputSchema, List.filterMap_cons]
    split <;> simp_all [schemaValues]

theorem validate_inputs {inputs witness : Assignment} {expected : Expected}
    {program : Json} {relation : Program}
    (inputAgreement : InputAgreement expected inputs witness)
    (accepted : validate expected program = .ok ())
    (decoded : NativeRelationJson.decode program = .ok relation) :
    ∀ visibility, relation.inputValues visibility witness =
      schemaValues inputs visibility (expected.inputs.map inputSchema) := by
  obtain ⟨instructions, state, parsed, finalOutput, trace, final⟩ := validate_result accepted
  obtain ⟨decodedInstructions, decodedParsed, decodedTrace⟩ := decode_result decoded
  rw [parsed] at decodedParsed
  cases decodedParsed
  have schema := validationLoop_inputs trace (by simpa only [zipIdx_values] using decodedTrace)
  rw [final.inputs] at schema
  simp only [List.take_length, List.take_zero, List.map_nil, List.nil_append] at schema
  intro visibility
  rw [inputValues_schema, ← schema]
  exact schemaValues_agree inputAgreement visibility

theorem validate_requirements
    {hash : Hash} {inputs witness : Assignment} {expected : Expected}
    {program : Json} {relation : Program}
    (inputAgreement : InputAgreement expected inputs witness)
    (accepted : validate expected program = .ok ())
    (decoded : NativeRelationJson.decode program = .ok relation)
    (holds : ∀ instruction ∈ relation.instructions, instruction.Holds hash witness) :
    ValidatedRequirements hash inputs expected :=
  validate_requirements_with_parsers ScalarParserAgreement.producer_immediate_success
    ScalarParserAgreement.natField_naturalField_agree inputAgreement accepted decoded holds

theorem validate_observations
    {hash : Hash} {inputs witness : Assignment} {expected : Expected}
    {program : Json} {relation : Program}
    (inputAgreement : InputAgreement expected inputs witness)
    (accepted : validate expected program = .ok ())
    (decoded : NativeRelationJson.decode program = .ok relation)
    (holds : ∀ instruction ∈ relation.instructions, instruction.Holds hash witness) :
    relation.groups witness = expected.groups.map (List.map (interpret hash inputs)) ∧
      relation.returns witness = expected.returns.map (interpret hash inputs) :=
  validate_observations_with_parsers ScalarParserAgreement.producer_immediate_success
    ScalarParserAgreement.natField_naturalField_agree inputAgreement accepted decoded holds

/-- Exact native transcript observations and all established source requirements.
`returns` records the host observation. Authentication comes from the exact
ordered Impact groups, whose source schedule is proved separately. -/
structure ValidatedRelation (hash : Hash) (inputs : Assignment) (expected : Expected)
    (relation : Program) (streams : InputStreams) (witness : Assignment)
    (publicGroups : List (List Scalar)) : Prop where
  requirements : ValidatedRequirements hash inputs expected
  publicInputs : streams.publicValues = schemaValues inputs .public (expected.inputs.map inputSchema)
  privateInputs : streams.privateValues = schemaValues inputs .private (expected.inputs.map inputSchema)
  groups : publicGroups = expected.groups.map (List.map (interpret hash inputs))
  returns : relation.returns witness = expected.returns.map (interpret hash inputs)

/-- Arbitrary satisfying native witnesses pass through the mandatory validator's
actual indexed fold. No Boolean or UInt input range is assumed by this theorem. -/
theorem validate_sound
    {hash : Hash} {inputs witness : Assignment} {expected : Expected}
    {program : Json} {relation : Program} {streams : InputStreams}
    {publicGroups : List (List Scalar)}
    (inputAgreement : InputAgreement expected inputs witness)
    (accepted : validate expected program = .ok ())
    (decoded : NativeRelationJson.decode program = .ok relation)
    (satisfies : CircuitSatisfies hash relation streams witness publicGroups) :
    ValidatedRelation hash inputs expected relation streams witness publicGroups := by
  have requirements := validate_requirements inputAgreement accepted decoded satisfies.instructions
  have inputs := validate_inputs inputAgreement accepted decoded
  have observations := validate_observations inputAgreement accepted decoded satisfies.instructions
  exact ⟨requirements, satisfies.publicInputs.symm.trans (inputs .public),
    satisfies.privateInputs.symm.trans (inputs .private),
    satisfies.groups.symm.trans observations.1, observations.2⟩

theorem validate_observed_returns
    {hash : Hash} {inputs witness : Assignment} {expected : Expected}
    {program : Json} {relation : Program} {streams : InputStreams}
    {publicGroups : List (List Scalar)} {returns : List Scalar}
    (inputAgreement : InputAgreement expected inputs witness)
    (accepted : validate expected program = .ok ())
    (decoded : NativeRelationJson.decode program = .ok relation)
    (satisfies : Satisfies hash relation streams witness publicGroups returns) :
    ValidatedRelation hash inputs expected relation streams witness publicGroups ∧
      returns = expected.returns.map (interpret hash inputs) := by
  have sound := validate_sound inputAgreement accepted decoded satisfies.circuit
  exact ⟨sound, satisfies.outputs.symm.trans sound.returns⟩

end Noctium.Verification.ScalarValidation
