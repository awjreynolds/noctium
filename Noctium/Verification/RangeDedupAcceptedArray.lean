import Noctium.Verification.RangeDedupProducer
import Noctium.Verification.RangeDedupComparisonMeaning
import Noctium.Verification.RangeDedupAssertMeaning
import Noctium.Verification.RangeDedupWholeTrace
import Noctium.Verification.RangeDedupKernel
import Noctium.Verification.ScalarValidationNativeLoop
import Noctium.Verification.ScalarValidationOutputMeaning

namespace Noctium.Verification.RangeDedupAcceptedArray

open Lean Backend.Native NativeRelation NativeRelationJson
open Noctium.Backend.RangeDedup
open Noctium.Verification.RangeDedup
open Noctium.Verification.RangeDedupProducer
open Noctium.Verification.ScalarValidationMeaning
open Noctium.Verification.ScalarValidationArithmeticLoop
open Noctium.Verification.ScalarValidationNativeLoop
open Noctium.Verification.ScalarValidationOutputMeaning
open Noctium.Verification.ScalarNormalization

private theorem refine_nativeDefinitions {state next : Backend.Native.State}
    {text : String} {maximum : Nat}
    (definitions : NativeDefinitions state)
    (accepted : Backend.Native.refine state text maximum = .ok next) :
    NativeDefinitions next := by
  unfold Backend.Native.refine at accepted
  simp only [ScalarValidationMeaning.bind_ok] at accepted
  rcases accepted with ⟨fact, _, accepted⟩
  cases reference : text.startsWith "%" with
  | true =>
    simp only [reference, ↓reduceIte, Pure.pure, Except.pure] at accepted
    rcases accepted with ⟨_, _, result⟩
    cases result
    intro name found member
    simp only [List.mem_map] at member
    rcases member with ⟨⟨oldName, oldFact⟩, oldMember, equal⟩
    have sameName : oldName = name := by simpa using congrArg Prod.fst equal
    have sameFact :
        (if oldName == text then {oldFact with maximum := min oldFact.maximum maximum}
          else oldFact) = found := by simpa using congrArg Prod.snd equal
    subst name
    subst found
    have valueTypeUnchanged :
        (if oldName == text then {oldFact with maximum := min oldFact.maximum maximum}
          else oldFact).valueType = oldFact.valueType := by
      split <;> rfl
    rw [valueTypeUnchanged]
    exact definitions _ _ oldMember
  | false =>
    simp only [reference, Bool.false_eq_true, ↓reduceIte] at accepted
    simp [Backend.Native.ensure] at accepted
    rcases accepted with ⟨_, result⟩
    by_cases bounded : fact.maximum ≤ maximum
    · simp [bounded] at result
      cases result
      exact definitions
    · simp [bounded, Except.map, Functor.map] at result

private theorem accepted_assert_nativeDefinitions
    {expected : Backend.Native.Expected} {state next : Backend.Native.State}
    {raw : Json}
    (definitions : NativeDefinitions state)
    (opcode : Backend.Native.stringField raw "op" = .ok "assert")
    (accepted : Backend.Native.validateInstruction expected state raw = .ok next) :
    NativeDefinitions next := by
  unfold Backend.Native.validateInstruction at accepted
  simp only [ScalarValidationMeaning.bind_ok] at accepted
  rcases accepted with ⟨opcodeName, opcodeParsed, descriptor, descriptorParsed,
    registry, fieldsParsed, accepted⟩
  have opcodeEq : opcodeName = "assert" := Except.ok.inj (opcodeParsed.symm.trans opcode)
  subst opcodeName
  simp at accepted
  simp only [ScalarValidationMeaning.bind_ok] at accepted
  rcases accepted with ⟨value, valueParsed, _, booleanAccepted, accepted⟩
  let assertionCounted := if expected.assertions[state.assertionCount]? == some value.term then
    {state with assertionCount := state.assertionCount + 1} else state
  let assertionState : Backend.Native.State :=
    {assertionCounted with
      establishedAssertions := (value.term :: assertionCounted.establishedAssertions).eraseDups}
  have assertionDefinitions : NativeDefinitions assertionState := by
    intro name fact member
    cases matched : (expected.assertions[state.assertionCount]? == some value.term)
    · exact definitions name fact (by
        simpa [assertionState, assertionCounted, matched] using member)
    · exact definitions name fact (by
        simpa [assertionState, assertionCounted, matched] using member)
  split at accepted
  · simp only [ScalarValidationMeaning.bind_ok] at accepted
    rcases accepted with ⟨_, _, refined⟩
    exact refine_nativeDefinitions assertionDefinitions refined
  · cases accepted
    exact assertionDefinitions

private theorem accepted_lessThan_nativeDefinitions
    {expected : Backend.Native.Expected} {state next : Backend.Native.State}
    {raw : Json}
    (definitions : NativeDefinitions state)
    (opcode : Backend.Native.stringField raw "op" = .ok "less_than")
    (accepted : Backend.Native.validateInstruction expected state raw = .ok next) :
    NativeDefinitions next := by
  obtain ⟨leftText, _, right, _, fact, _, _, _, _, _, _, combined, defined⟩ :=
    RangeDedupComparisonMeaning.acceptedLessThanDefinition opcode accepted
  have factNative : fact.valueType = NativeValueType.native := combine_native combined
  have definedFactNative :
      ({fact with assertedLessThan := match right.term with
        | .constant bound => if ['%'] <+: leftText.toList then some (leftText, bound) else none
        | _ => none}).valueType = NativeValueType.native := by
    simpa using factNative
  exact defineResult_nativeDefinitions definitions definedFactNative defined

/-- The bounded producer trace class used below permits arbitrary ordering of
native input/arithmetic steps, comparisons, assertions, and a checked output.
Other producer opcodes need their own state-meaning step before they enter this
induction. -/
inductive AcceptedMeaningStep (hash : Hash) (witness : Assignment) (raw : Json) : Prop where
  | native (steps : NativeStepHolds hash witness raw) : AcceptedMeaningStep hash witness raw
  | boolean {value : Operand}
      (opcode : Backend.Native.stringField raw "op" = .ok "constrain_to_boolean")
      (decoded : NativeRelationJson.decodeInstruction raw = .ok (.boolean value))
      (holds : Instruction.Holds hash witness (.boolean value)) :
      AcceptedMeaningStep hash witness raw
  | bits {value : Operand} {width : Nat}
      (opcode : Backend.Native.stringField raw "op" = .ok "constrain_bits")
      (decoded : NativeRelationJson.decodeInstruction raw = .ok (.bits value width))
      (holds : Instruction.Holds hash witness (.bits value width)) :
      AcceptedMeaningStep hash witness raw
  | lessThan {left right : Operand} {width : Nat} {output : String}
      (opcode : Backend.Native.stringField raw "op" = .ok "less_than")
      (decoded : NativeRelationJson.decodeInstruction raw = .ok (.lessThan left right width output))
      (holds : Instruction.Holds hash witness (.lessThan left right width output)) :
      AcceptedMeaningStep hash witness raw
  | assertion {condition : Operand}
      (opcode : Backend.Native.stringField raw "op" = .ok "assert")
      (decoded : NativeRelationJson.decodeInstruction raw = .ok (.assert condition))
      (holds : Instruction.Holds hash witness (.assert condition)) :
      AcceptedMeaningStep hash witness raw
  | constrainEq {left right : Operand}
      (opcode : Backend.Native.stringField raw "op" = .ok "constrain_eq")
      (decoded : NativeRelationJson.decodeInstruction raw = .ok (.equal left right))
      (holds : Instruction.Holds hash witness (.equal left right)) :
      AcceptedMeaningStep hash witness raw
  | testEq {left right : Operand} {output : String}
      (opcode : Backend.Native.stringField raw "op" = .ok "test_eq")
      (decoded : NativeRelationJson.decodeInstruction raw =
        .ok (.testEq left right output))
      (holds : Instruction.Holds hash witness (.testEq left right output)) :
      AcceptedMeaningStep hash witness raw
  | copy {source destination : String}
      (opcode : Backend.Native.stringField raw "op" = .ok "copy")
      (decoded : NativeRelationJson.decodeInstruction raw =
        .ok (.equal (.reference source) (.reference destination)))
      (holds : Instruction.Holds hash witness
        (.equal (.reference source) (.reference destination))) :
      AcceptedMeaningStep hash witness raw
  | output {values : List Operand}
      (opcode : Backend.Native.stringField raw "op" = .ok "output")
      (decoded : NativeRelationJson.decodeInstruction raw = .ok (.output values)) :
      AcceptedMeaningStep hash witness raw

private theorem decodedLessThanFields {raw : Json} {left right : Operand}
    {width : Nat} {output : String}
    (opcode : Backend.Native.stringField raw "op" = .ok "less_than")
    (decoded : NativeRelationJson.decodeInstruction raw =
      .ok (.lessThan left right width output)) :
    NativeRelationJson.decodeOperandField raw "a" = .ok left ∧
      NativeRelationJson.decodeOperandField raw "b" = .ok right ∧
      NativeRelationJson.naturalField raw "bits" = .ok width := by
  unfold NativeRelationJson.decodeInstruction at decoded
  simp only [ScalarValidationMeaning.bind_ok,
    ScalarValidationOutputMeaning.nativeJson_stringField_eq] at decoded
  rcases decoded with ⟨opcodeName, opcodeParsed, body⟩
  have opcodeEq : opcodeName = "less_than" := Except.ok.inj (opcodeParsed.symm.trans opcode)
  subst opcodeName
  simp only [ScalarValidationMeaning.bind_ok] at body
  rcases body with ⟨_, _, body⟩
  rcases body with ⟨_, bitsParsed, body⟩
  rcases body with ⟨_, _, body⟩
  rcases body with ⟨_, leftParsed, body⟩
  rcases body with ⟨_, rightParsed, body⟩
  rcases body with ⟨_, _, body⟩
  rcases body with ⟨_, _, result⟩
  simp only [Pure.pure, Except.pure] at result
  have resultEq := Except.ok.inj result
  injection resultEq with leftEq rightEq widthEq outputEq
  subst left right width output
  exact ⟨leftParsed, rightParsed, bitsParsed⟩

private theorem decodedConstrainEqOperands {raw : Json} {left right : Operand}
    (opcode : Backend.Native.stringField raw "op" = .ok "constrain_eq")
    (decoded : NativeRelationJson.decodeInstruction raw = .ok (.equal left right)) :
    NativeRelationJson.decodeOperandField raw "a" = .ok left ∧
      NativeRelationJson.decodeOperandField raw "b" = .ok right := by
  unfold NativeRelationJson.decodeInstruction at decoded
  simp only [ScalarValidationMeaning.bind_ok,
    ScalarValidationOutputMeaning.nativeJson_stringField_eq] at decoded
  rcases decoded with ⟨opcodeName, opcodeParsed, body⟩
  have opcodeEq : opcodeName = "constrain_eq" :=
    Except.ok.inj (opcodeParsed.symm.trans opcode)
  subst opcodeName
  simp only [ScalarValidationMeaning.bind_ok] at body
  rcases body with ⟨_, _, leftValue, leftParsed, rightValue, result⟩
  rcases result with ⟨rightParsed, result⟩
  simp only [Pure.pure, Except.pure] at result
  have resultEq := Except.ok.inj result
  injection resultEq with leftEq rightEq
  subst left right
  exact ⟨leftParsed, rightParsed⟩

private theorem decodedTestEqFields {raw : Json} {left right : Operand} {output : String}
    (opcode : Backend.Native.stringField raw "op" = .ok "test_eq")
    (decoded : NativeRelationJson.decodeInstruction raw =
      .ok (.testEq left right output)) :
    NativeRelationJson.decodeOperandField raw "a" = .ok left ∧
      NativeRelationJson.decodeOperandField raw "b" = .ok right ∧
      Backend.Native.stringField raw "output" = .ok output := by
  unfold NativeRelationJson.decodeInstruction at decoded
  simp only [ScalarValidationMeaning.bind_ok,
    ScalarValidationOutputMeaning.nativeJson_stringField_eq] at decoded
  rcases decoded with ⟨opcodeName, opcodeParsed, body⟩
  have opcodeEq : opcodeName = "test_eq" :=
    Except.ok.inj (opcodeParsed.symm.trans opcode)
  subst opcodeName
  simp only [ScalarValidationMeaning.bind_ok] at body
  rcases body with ⟨_, _, leftName, leftParsed, rightName, rightParsed,
    outputName, outputParsed, _, _, result⟩
  simp only [Pure.pure, Except.pure] at result
  have resultEq := Except.ok.inj result
  injection resultEq with leftEq rightEq outputEq
  subst left right output
  exact ⟨leftParsed, rightParsed, outputParsed⟩

private theorem decodedBooleanField {raw : Json} {value : Operand}
    (opcode : Backend.Native.stringField raw "op" = .ok "constrain_to_boolean")
    (decoded : NativeRelationJson.decodeInstruction raw = .ok (.boolean value)) :
    NativeRelationJson.decodeOperandField raw "val" = .ok value := by
  simp [NativeRelationJson.decodeInstruction,
    ScalarValidationOutputMeaning.nativeJson_stringField_eq, opcode,
    ScalarValidationMeaning.bind_ok, ScalarValidationOutputMeaning.map_ok] at decoded
  rcases decoded with ⟨_, valueParsed⟩
  exact valueParsed

private theorem decodedBitsFields {raw : Json} {value : Operand} {width : Nat}
    (opcode : Backend.Native.stringField raw "op" = .ok "constrain_bits")
    (decoded : NativeRelationJson.decodeInstruction raw = .ok (.bits value width)) :
    NativeRelationJson.decodeOperandField raw "val" = .ok value ∧
      NativeRelationJson.naturalField raw "bits" = .ok width := by
  simp [NativeRelationJson.decodeInstruction,
    ScalarValidationOutputMeaning.nativeJson_stringField_eq, opcode,
    ScalarValidationMeaning.bind_ok, ScalarValidationOutputMeaning.map_ok] at decoded
  rcases decoded with ⟨_, foundWidth, widthParsed, _, foundValue, valueParsed, result⟩
  rcases result with ⟨valueEq, widthEq⟩
  cases valueEq
  cases widthEq
  exact ⟨valueParsed, widthParsed⟩

private theorem reference_not_immediate {text : String}
    (reference : text.startsWith "%" = true) : text.startsWith "0x" = false := by
  have prefixed : ['%'] <+: text.toList := by simpa using reference
  rcases prefixed with ⟨tail, equal⟩
  apply String.startsWith_string_eq_false_iff.mpr
  rw [← equal]
  simp

private theorem decodedReference {raw : Json} {name text : String} {value : Operand}
    (textParsed : Backend.Native.stringField raw name = .ok text)
    (decoded : NativeRelationJson.decodeOperandField raw name = .ok value)
    (reference : text.startsWith "%" = true) : value = .reference text := by
  unfold Backend.Native.stringField at textParsed
  unfold NativeRelationJson.decodeOperandField at decoded
  simp only [ScalarValidationMeaning.bind_ok] at textParsed decoded
  rcases textParsed with ⟨json, jsonParsed, textParsed⟩
  rcases decoded with ⟨same, sameParsed, decoded⟩
  rw [jsonParsed] at sameParsed
  cases sameParsed
  unfold NativeRelationJson.decodeOperand at decoded
  simp only [ScalarValidationMeaning.bind_ok] at decoded
  rcases decoded with ⟨sameText, sameTextParsed, decoded⟩
  rw [textParsed] at sameTextParsed
  cases sameTextParsed
  simp only [reference_not_immediate reference, Bool.false_eq_true, ↓reduceIte,
    ScalarValidationMeaning.bind_ok] at decoded
  rcases decoded with ⟨_, _, result⟩
  cases result
  rfl

/-- The accepted producer loop's per-item bounds become concrete bounds for
each decoded comparison under that occurrence's checked prefix meaning. This
works for every list member, including repeated pairs separated by other
instructions. -/
theorem accepted_lessThan_witnessBounds
    {hash : Hash} {inputs witness : Assignment} {expected : Backend.Native.Expected}
    {state next : Backend.Native.State}
    {raw : Json} {left right : Operand} {width : Nat} {output : String}
    (meaning : StateMeaning hash inputs witness state)
    (opcode : Backend.Native.stringField raw "op" = .ok "less_than")
    (decoded : NativeRelationJson.decodeInstruction raw =
      .ok (.lessThan left right width output))
    (accepted : Backend.Native.validateInstruction expected state raw = .ok next) :
    (left.read witness).val < 2 ^ width ∧ (right.read witness).val < 2 ^ width := by
  obtain ⟨_, _, _, producerWidth, _, _, leftAccepted, rightAccepted, widthAccepted,
    leftMaximum, rightMaximum, _, _⟩ :=
    RangeDedupComparisonMeaning.acceptedLessThanDefinition opcode accepted
  have fields := decodedLessThanFields opcode decoded
  have widthEq := Noctium.Verification.ScalarParserAgreement.natField_naturalField_agree raw "bits"
    producerWidth width (by
      unfold Backend.Native.width at widthAccepted
      simp only [ScalarValidationMeaning.bind_ok] at widthAccepted
      rcases widthAccepted with ⟨found, fieldParsed, _, equal⟩
      have same : found = producerWidth := Except.ok.inj equal.2
      rw [← same]
      exact fieldParsed) fields.2.2
  have leftMeaning := argument_decoded_meaning meaning leftAccepted fields.1
  have rightMeaning := argument_decoded_meaning meaning rightAccepted fields.2.1
  constructor
  · exact Nat.lt_of_le_of_lt leftMeaning.bound (by simpa [widthEq] using leftMaximum)
  · exact Nat.lt_of_le_of_lt rightMeaning.bound (by simpa [widthEq] using rightMaximum)

/-- An accepted guarded public ledger input preserves both the scalar meaning
invariant and the native-definition typing invariant used by the comparison
trace proof. This is the guarded-input step needed before widening its loop
schema beyond unconditional transcript inputs. -/
theorem accepted_guarded_public_input_preserves
    {hash : Hash} {inputs witness : Assignment} {expected : Backend.Native.Expected}
    {state next : Backend.Native.State} {raw : Json} {requirement : InputRequirement}
    {guardTerm : Backend.Native.Term}
    (meaning : StateMeaning hash inputs witness state)
    (definitions : NativeDefinitions state)
    (selected : expected.inputs[state.inputCount]? = some requirement)
    (nonforeignInput : requirement.ty.isForeign = false)
    (guarded : requirement.activityGuard = some guardTerm)
    (inputAgreement : witness requirement.identifier = inputs requirement.identifier)
    (opcode : Backend.Native.stringField raw "op" = .ok "public_input")
    (accepted : Backend.Native.validateInstruction expected state raw = .ok next) :
    StateMeaning hash inputs witness next ∧ NativeDefinitions next := by
  exact ⟨guarded_public_input_step_meaning meaning selected nonforeignInput guarded
      inputAgreement opcode accepted,
    guarded_public_input_nativeDefinitions_step definitions selected nonforeignInput guarded
      opcode accepted⟩

private theorem acceptedMeaningStep_preserves
    {hash : Hash} {inputs witness : Assignment} {expected : Backend.Native.Expected}
    {state next : Backend.Native.State} {raw : Json}
    (meaning : StateMeaning hash inputs witness state)
    (definitions : NativeDefinitions state)
    (inputSchema : ∀ requirement ∈ expected.inputs,
      requirement.ty.isForeign = false)
    (inputAgreement : ∀ requirement ∈ expected.inputs,
      witness requirement.identifier = inputs requirement.identifier)
    (step : AcceptedMeaningStep hash witness raw)
    (accepted : Backend.Native.validateInstruction expected state raw = .ok next) :
    StateMeaning hash inputs witness next ∧ NativeDefinitions next := by
  cases step with
  | native nativeStep =>
    cases nativeStep with
    | publicInput opcode =>
      obtain ⟨requirement, selected⟩ := accepted_input_requirement_selected
        (visibility := .«public») (by simpa [inputOpcode] using opcode) accepted
      have member : requirement ∈ expected.inputs := List.mem_of_getElem? selected
      have nonforeignInput := inputSchema requirement member
      have agreement := inputAgreement requirement member
      cases guarded : requirement.activityGuard with
      | none =>
        exact ⟨public_input_step_meaning meaning selected nonforeignInput guarded agreement
            opcode accepted,
          input_nativeDefinitions_step (visibility := .«public») definitions selected nonforeignInput
            guarded (by simpa [inputOpcode] using opcode) accepted⟩
      | some guardTerm =>
        exact ⟨guarded_public_input_step_meaning meaning selected nonforeignInput guarded
            agreement opcode accepted,
          guarded_public_input_nativeDefinitions_step definitions selected nonforeignInput
            guarded (by simpa [inputOpcode] using opcode) accepted⟩
    | privateInput opcode =>
      obtain ⟨requirement, selected⟩ := accepted_input_requirement_selected
        (visibility := .«private») (by simpa [inputOpcode] using opcode) accepted
      have member : requirement ∈ expected.inputs := List.mem_of_getElem? selected
      have nonforeignInput := inputSchema requirement member
      have unguarded := accepted_private_input_unguarded selected
        (by simpa [inputOpcode] using opcode) accepted
      have agreement := inputAgreement requirement member
      exact ⟨private_input_step_meaning meaning selected nonforeignInput unguarded agreement
          opcode accepted,
        input_nativeDefinitions_step (visibility := .«private») definitions selected nonforeignInput
          unguarded (by simpa [inputOpcode] using opcode) accepted⟩
    | arithmetic arithmeticStep =>
      cases arithmeticStep with
      | add _ _ _ opcode decoded holds =>
        exact accepted_native_add_step_meaning meaning definitions opcode accepted decoded holds
      | mul _ _ _ opcode decoded holds =>
        exact accepted_native_mul_step_meaning meaning definitions opcode accepted decoded holds
      | neg _ _ opcode decoded holds =>
        exact accepted_native_neg_step_meaning meaning definitions opcode accepted decoded holds
  | boolean opcode decoded holds =>
    unfold Backend.Native.validateInstruction at accepted
    simp only [ScalarValidationMeaning.bind_ok] at accepted
    rcases accepted with ⟨opcodeName, opcodeParsed, descriptor, descriptorParsed,
      registry, fieldsParsed, accepted⟩
    have opcodeEq : opcodeName = "constrain_to_boolean" :=
      Except.ok.inj (opcodeParsed.symm.trans opcode)
    subst opcodeName
    simp at accepted
    simp only [ScalarValidationMeaning.bind_ok] at accepted
    rcases accepted with ⟨text, textParsed, refined⟩
    have valueParsed := decodedBooleanField opcode decoded
    have bounded : text.startsWith "%" = true → (witness text).val ≤ 1 := by
      intro reference
      have valueEq := decodedReference textParsed valueParsed reference
      rw [valueEq] at holds
      change witness text = zero ∨ witness text = one at holds
      rcases holds with equal | equal
      · have valueBound : (witness text).val = 0 := by
          simpa [zero] using congrArg (fun value : Scalar => value.val) equal
        omega
      · have valueBound : (witness text).val = 1 := by
          simpa [one] using congrArg (fun value : Scalar => value.val) equal
        omega
    exact ⟨RangeDedupAssertMeaning.refineMeaning meaning bounded refined,
      refine_nativeDefinitions definitions refined⟩
  | @bits value bitsWidth opcode decoded holds =>
    unfold Backend.Native.validateInstruction at accepted
    simp only [ScalarValidationMeaning.bind_ok] at accepted
    rcases accepted with ⟨opcodeName, opcodeParsed, descriptor, descriptorParsed,
      registry, fieldsParsed, accepted⟩
    have opcodeEq : opcodeName = "constrain_bits" :=
      Except.ok.inj (opcodeParsed.symm.trans opcode)
    subst opcodeName
    simp at accepted
    simp only [ScalarValidationMeaning.bind_ok] at accepted
    rcases accepted with ⟨text, textParsed, producerWidth, widthParsed, refined⟩
    have fields := decodedBitsFields opcode decoded
    have widthAgreement := ScalarParserAgreement.natField_naturalField_agree raw "bits"
      producerWidth bitsWidth (by
        unfold Backend.Native.width at widthParsed
        simp only [ScalarValidationMeaning.bind_ok] at widthParsed
        rcases widthParsed with ⟨found, fieldParsed, _, _, result⟩
        cases result
        exact fieldParsed) fields.2
    have bounded : text.startsWith "%" = true →
        (witness text).val ≤ 2 ^ producerWidth - 1 := by
      intro reference
      have valueEq := decodedReference textParsed fields.1 reference
      rw [valueEq] at holds
      have valueBound := NativeRelation.range_constraint_bound hash witness
        (.reference text) bitsWidth holds
      simpa [Operand.read, widthAgreement] using valueBound
    exact ⟨RangeDedupAssertMeaning.refineMeaning meaning bounded refined,
      refine_nativeDefinitions definitions refined⟩
  | lessThan opcode decoded holds =>
    exact ⟨RangeDedupComparisonMeaning.lessThanStepMeaning meaning opcode decoded holds accepted,
      accepted_lessThan_nativeDefinitions definitions opcode accepted⟩
  | assertion opcode decoded holds =>
    exact ⟨RangeDedupAssertMeaning.assertStepMeaning meaning opcode decoded holds accepted,
      accepted_assert_nativeDefinitions definitions opcode accepted⟩
  | @copy source destination opcode decoded holds =>
    obtain ⟨sourceFact, sourceAccepted, sourceNative, defined⟩ :=
      accepted_copy_components definitions opcode accepted
    have typed := defineResult_nativeDefinitions definitions sourceNative defined
    have fields := NativeRelationJson.decodeInstruction_copyFields opcode decoded
    have sourceDecoded : NativeRelationJson.decodeOperandField raw "val" =
        .ok (.reference source) := by
      exact NativeRelationJson.decodeOperandField_reference_of_stringField fields.1 fields.2.2
    have sourceMeaning := argument_decoded_meaning meaning sourceAccepted sourceDecoded
    have sourceDestinationEqual : witness source = witness destination := by
      change Operand.read witness (.reference source) =
        Operand.read witness (.reference destination)
      exact holds
    have destinationMeaning : FactMeaning hash inputs witness sourceFact (witness destination) := by
      refine ⟨?_, ?_, ?_⟩
      · rw [← sourceDestinationEqual]
        exact sourceMeaning.term
      · rw [← sourceDestinationEqual]
        exact sourceMeaning.bound
      · intro identifier exclusive asserted nonzero
        apply sourceMeaning.comparison identifier exclusive asserted
        change witness source ≠ zero
        rw [sourceDestinationEqual]
        exact nonzero
    have outputMeaning : ∀ identifier,
        Backend.Native.stringField raw "output" = .ok identifier →
        FactMeaning hash inputs witness sourceFact (witness identifier) := by
      intro identifier parsed
      have same : identifier = destination := Except.ok.inj (parsed.symm.trans fields.2.1)
      subst identifier
      exact destinationMeaning
    exact ⟨defineResult_meaning meaning outputMeaning defined, typed⟩
  | @constrainEq left right opcode decoded holds =>
    unfold Backend.Native.validateInstruction at accepted
    simp only [ScalarValidationMeaning.bind_ok] at accepted
    rcases accepted with ⟨opcodeName, opcodeParsed, descriptor, descriptorParsed,
      registry, fieldsParsed, accepted⟩
    have opcodeEq : opcodeName = "constrain_eq" :=
      Except.ok.inj (opcodeParsed.symm.trans opcode)
    subst opcodeName
    simp at accepted
    simp only [ScalarValidationMeaning.bind_ok] at accepted
    rcases accepted with ⟨leftText, leftTextParsed, rightText, rightTextParsed,
      leftFact, leftAccepted, rightFact, rightAccepted, _, transition⟩
    have leftArgument : Backend.Native.argument state raw "a" = .ok leftFact := by
      unfold Backend.Native.argument
      rw [leftTextParsed]
      exact leftAccepted
    have rightArgument : Backend.Native.argument state raw "b" = .ok rightFact := by
      unfold Backend.Native.argument
      rw [rightTextParsed]
      exact rightAccepted
    have leftNative := argument_native_of_state definitions leftArgument
    have rightNative := argument_native_of_state definitions rightArgument
    have fields := decodedConstrainEqOperands opcode decoded
    have leftMeaning := argument_decoded_meaning meaning leftArgument fields.1
    have rightMeaning := argument_decoded_meaning meaning rightArgument fields.2
    have readsEqual : left.read witness = right.read witness := holds
    have sameType : (leftFact.valueType == rightFact.valueType) = true := by
      rw [leftNative, rightNative]
      decide
    have nativeType : (leftFact.valueType == Backend.Native.NativeValueType.native) = true := by
      rw [leftNative]
      decide
    rw [sameType, nativeType] at transition
    simp [Backend.Native.ensure] at transition
    rcases transition with ⟨_, transition⟩
    simp only [ScalarValidationMeaning.bind_ok] at transition
    rcases transition with ⟨middle, leftRefined, transition⟩
    cases rightRefined : Backend.Native.refine middle rightText
        (min leftFact.maximum rightFact.maximum) with
    | error message =>
      simp [rightRefined, Except.map, Functor.map] at transition
    | ok afterRight =>
      simp [rightRefined, Except.map, Functor.map] at transition
      have finalStateEq := transition
      have definitionsEq : next.definitions = afterRight.definitions := by
        have projected := congrArg (fun value : Backend.Native.State => value.definitions) finalStateEq
        simpa using projected.symm
      have afterLeftMeaning : StateMeaning hash inputs witness middle := by
        have boundedLeft : leftText.startsWith "%" = true →
            (witness leftText).val ≤ min leftFact.maximum rightFact.maximum := by
          intro reference
          have leftReference := decodedReference leftTextParsed fields.1 reference
          have rightBound : (left.read witness).val ≤ rightFact.maximum := by
            calc
              (left.read witness).val = (right.read witness).val := by
                exact congrArg (fun value : Scalar => value.val) readsEqual
              _ ≤ rightFact.maximum := rightMeaning.bound
          have leftBound : (witness leftText).val ≤ leftFact.maximum := by
            simpa [leftReference, Operand.read] using leftMeaning.bound
          have rightBoundAtText : (witness leftText).val ≤ rightFact.maximum := by
            simpa [leftReference, Operand.read] using rightBound
          exact Nat.le_min.mpr ⟨leftBound, rightBoundAtText⟩
        exact RangeDedupAssertMeaning.refineMeaning meaning boundedLeft leftRefined
      have afterLeftDefinitions : NativeDefinitions middle :=
        refine_nativeDefinitions definitions leftRefined
      have afterRightMeaning : StateMeaning hash inputs witness afterRight := by
        have boundedRight : rightText.startsWith "%" = true →
            (witness rightText).val ≤ min leftFact.maximum rightFact.maximum := by
          intro reference
          have rightReference := decodedReference rightTextParsed fields.2 reference
          have leftBound : (right.read witness).val ≤ leftFact.maximum := by
            calc
              (right.read witness).val = (left.read witness).val := by
                exact congrArg (fun value : Scalar => value.val) readsEqual.symm
              _ ≤ leftFact.maximum := leftMeaning.bound
          have rightBound : (witness rightText).val ≤ rightFact.maximum := by
            simpa [rightReference, Operand.read] using rightMeaning.bound
          have leftBoundAtText : (witness rightText).val ≤ leftFact.maximum := by
            simpa [rightReference, Operand.read] using leftBound
          exact Nat.le_min.mpr ⟨leftBoundAtText, rightBound⟩
        exact RangeDedupAssertMeaning.refineMeaning afterLeftMeaning boundedRight rightRefined
      have afterRightDefinitions : NativeDefinitions afterRight :=
        refine_nativeDefinitions afterLeftDefinitions rightRefined
      have finalMeaning : StateMeaning hash inputs witness next := by
        intro identifier fact member
        have sameMember : (identifier, fact) ∈ afterRight.definitions := by
          simpa [definitionsEq] using member
        exact afterRightMeaning identifier fact sameMember
      have finalDefinitions : NativeDefinitions next := by
        intro identifier fact member
        have sameMember : (identifier, fact) ∈ afterRight.definitions := by
          simpa [definitionsEq] using member
        exact afterRightDefinitions identifier fact sameMember
      exact ⟨finalMeaning, finalDefinitions⟩
  | @testEq left right output opcode decoded holds =>
    obtain ⟨leftFact, rightFact, fact, leftAccepted, rightAccepted,
      leftNative, rightNative, combined, defined⟩ :=
      accepted_testEq_components definitions opcode accepted
    have fields := decodedTestEqFields opcode decoded
    have leftMeaning := argument_decoded_meaning meaning leftAccepted fields.1
    have rightMeaning := argument_decoded_meaning meaning rightAccepted fields.2.1
    have holdsEquation : witness output =
        bit (decide (left.read witness = right.read witness)) := by
      simpa [Instruction.Holds] using holds
    have resultMeaning :
        interpret hash inputs (.binary "test_eq" leftFact.term rightFact.term) =
          some (witness output) := by
      simp [interpret, leftMeaning.term, rightMeaning.term, holdsEquation]
    have resultBound : (witness output).val ≤ 1 := by
      rw [holdsEquation]
      rcases bit_canonical (decide (left.read witness = right.read witness)) with zeroValue | oneValue
      · rw [zeroValue]
        omega
      · rw [oneValue]
        omega
    have factMeaning : FactMeaning hash inputs witness fact (witness output) :=
      combine_meaning combined resultMeaning resultBound
    have outputMeaning : ∀ identifier,
        Backend.Native.stringField raw "output" = .ok identifier →
        FactMeaning hash inputs witness fact (witness identifier) := by
      intro identifier parsed
      have same : identifier = output := Except.ok.inj (parsed.symm.trans fields.2.2)
      subst identifier
      exact factMeaning
    have meaningNext := defineResult_meaning meaning outputMeaning defined
    have factNative := combine_native combined
    have definitionsNext := defineResult_nativeDefinitions definitions factNative defined
    exact ⟨meaningNext, definitionsNext⟩
  | output opcode decoded =>
    have outputMeaning := accepted_output_meaning meaning accepted opcode decoded
    rw [outputMeaning.1]
    exact ⟨meaning, definitions⟩

/-- Thread producer meaning through any accepted indexed trace in the declared
step class and retain the invariant at every instruction pre-state. This lets
separate comparisons use their actual checked prefix definitions even when
other supported instructions occur between them. -/
theorem accepted_loop_meaning_at_steps
    {hash : Hash} {inputs witness : Assignment} {expected : Backend.Native.Expected}
    {items : List (Json × Nat)} {initial final : Backend.Native.State}
    (initialMeaning : StateMeaning hash inputs witness initial)
    (initialDefinitions : NativeDefinitions initial)
    (inputSchema : ∀ requirement ∈ expected.inputs,
      requirement.ty.isForeign = false)
    (inputAgreement : ∀ requirement ∈ expected.inputs,
      witness requirement.identifier = inputs requirement.identifier)
    (steps : ∀ item ∈ items, AcceptedMeaningStep hash witness item.1)
    (accepted : Backend.Native.validateInstructionLoop expected items initial = .ok final) :
    StateMeaning hash inputs witness final ∧ NativeDefinitions final ∧
      ∀ raw index, (raw, index) ∈ items →
        ∃ state next, StateMeaning hash inputs witness state ∧ NativeDefinitions state ∧
          Backend.Native.validateInstruction expected state raw = .ok next ∧
          StateMeaning hash inputs witness next ∧ NativeDefinitions next := by
  induction items generalizing initial final with
  | nil =>
    have initialEq : initial = final := by injection accepted
    subst final
    exact ⟨initialMeaning, initialDefinitions, by simp⟩
  | cons head tail ih =>
    rw [Backend.Native.validateInstructionLoop, List.forIn_cons] at accepted
    cases checked : Backend.Native.validateInstruction expected initial head.1 with
    | error message => simp [checked, Bind.bind, Except.bind] at accepted
    | ok next =>
      simp only [checked, bind_pure_comp] at accepted
      have after := acceptedMeaningStep_preserves initialMeaning initialDefinitions
        inputSchema inputAgreement (steps head (by simp)) checked
      obtain ⟨finalMeaning, finalDefinitions, tailVisits⟩ :=
        ih after.1 after.2
          (fun item member => steps item (List.mem_cons_of_mem _ member)) accepted
      refine ⟨finalMeaning, finalDefinitions, ?_⟩
      intro raw index member
      have headOrTail : (raw, index) = head ∨ (raw, index) ∈ tail := by
        simpa only [List.mem_cons] using member
      rcases headOrTail with headMember | tailMember
      · have rawEq : raw = head.1 := congrArg Prod.fst headMember
        have indexEq : index = head.2 := congrArg Prod.snd headMember
        subst raw
        subst index
        exact ⟨initial, next, initialMeaning, initialDefinitions, checked,
          after.1, after.2⟩
      · exact tailVisits raw index tailMember

private theorem foldObservation_copyJson (source destination : String) :
    Noctium.Verification.RangeDedupWholeTrace.foldObservation
        (comparisonCopyJson source destination) =
      [.comparisonOutput destination] := by
  have noKey : comparison? (comparisonCopyJson source destination) = none := rfl
  rw [Noctium.Verification.RangeDedupWholeTrace.foldObservation, noKey,
    comparisonCopyJson_decodes]

/-- Compose the exact whole-array pass with accepted producer meaning for
arbitrary traces in `AcceptedMeaningStep`, including any number of comparisons
interleaved with inputs, arithmetic, assertions, and outputs. The existing
all-witness fold theorem still requires `ComparisonBitChecks`; this result also
exposes producer-derived bounds at every accepted comparison for the chosen
assignment. -/
theorem acceptedArrayWholeFold
    {hash : Hash} {inputs witness : Assignment} {expected : Backend.Native.Expected}
    {source : Array Json} {original : List Instruction}
    {initial final : Backend.Native.State}
    (initialMeaning : StateMeaning hash inputs witness initial)
    (initialDefinitions : NativeDefinitions initial)
    (inputSchema : ∀ requirement ∈ expected.inputs,
      requirement.ty.isForeign = false)
    (inputAgreement : ∀ requirement ∈ expected.inputs,
      witness requirement.identifier = inputs requirement.identifier)
    (steps : ∀ item ∈ source.toList.zipIdx, AcceptedMeaningStep hash witness item.1)
    (decoded : source.toList.mapM decodeInstruction = .ok original)
    (ranges : ComparisonBitChecks original)
    (accepted : Backend.Native.validateInstructionLoop expected source.toList.zipIdx
      initial = .ok final) :
    ∃ optimized,
      (reuseComparisons source).toList.mapM decodeInstruction = .ok optimized ∧
      optimized.filter stableOutsideComparisons = original.filter stableOutsideComparisons ∧
      (∀ candidateHash candidateWitness,
        (∀ instruction ∈ optimized, Instruction.Holds candidateHash candidateWitness instruction) ↔
        (∀ instruction ∈ original, Instruction.Holds candidateHash candidateWitness instruction)) ∧
      (reuseComparisons source).toList.flatMap
          Noctium.Verification.RangeDedupWholeTrace.foldObservation =
        source.toList.flatMap Noctium.Verification.RangeDedupWholeTrace.foldObservation ∧
      StateMeaning hash inputs witness final ∧ NativeDefinitions final ∧
      (∀ raw index, (raw, index) ∈ source.toList.zipIdx →
        ∀ left right width output,
          Backend.Native.stringField raw "op" = .ok "less_than" →
          NativeRelationJson.decodeInstruction raw =
            .ok (.lessThan left right width output) →
          (left.read witness).val < 2 ^ width ∧ (right.read witness).val < 2 ^ width) ∧
      (∀ raw index, (raw, index) ∈ source.toList.zipIdx →
        ∀ values, Backend.Native.stringField raw "op" = .ok "output" →
          NativeRelationJson.decodeInstruction raw = .ok (.output values) →
          expected.returns.map (interpret hash inputs) =
            (values.map (·.read witness)).map some) := by
  obtain ⟨optimized, optimizedDecoded, stable, equivalent⟩ :=
    reuseComparisons_preserves_decoded source original decoded ranges
  have observations := Backend.RangeDedup.reuseComparisons_preserves_observations
    source Noctium.Verification.RangeDedupWholeTrace.foldObservation (by
      intro earlier earlierMember later laterMember key first output earlierKey laterKey
      rw [foldObservation_copyJson first output]
      simp [Noctium.Verification.RangeDedupWholeTrace.foldObservation, laterKey])
  obtain ⟨finalMeaning, finalDefinitions, visits⟩ := accepted_loop_meaning_at_steps
    initialMeaning initialDefinitions inputSchema inputAgreement steps accepted
  refine ⟨optimized, optimizedDecoded, stable, equivalent, observations,
    finalMeaning, finalDefinitions, ?_, ?_⟩
  · intro raw index member left right width output opcode decodedComparison
    obtain ⟨state, next, before, _, checked, _, _⟩ := visits raw index member
    exact accepted_lessThan_witnessBounds before opcode decodedComparison checked
  · intro raw index member values opcode decodedOutput
    obtain ⟨state, next, before, _, checked, _, _⟩ := visits raw index member
    exact (accepted_output_meaning before checked opcode decodedOutput).2

private theorem acceptedLoopCut {expected : Backend.Native.Expected}
    {prelude rest : List (Json × Nat)} {item : Json × Nat}
    {initial final : Backend.Native.State}
    (accepted : Backend.Native.validateInstructionLoop expected (prelude ++ item :: rest)
      initial = .ok final) :
    ∃ before after,
      Backend.Native.validateInstructionLoop expected prelude initial = .ok before ∧
      Backend.Native.validateInstruction expected before item.1 = .ok after := by
  induction prelude generalizing initial with
  | nil =>
    rw [List.nil_append, Backend.Native.validateInstructionLoop, List.forIn_cons] at accepted
    cases checked : Backend.Native.validateInstruction expected initial item.1 with
    | error message => simp [checked, Bind.bind, Except.bind] at accepted
    | ok after => exact ⟨initial, after, rfl, checked⟩
  | cons head tail ih =>
    rw [List.cons_append, Backend.Native.validateInstructionLoop, List.forIn_cons] at accepted
    cases checked : Backend.Native.validateInstruction expected initial head.1 with
    | error message => simp [checked, Bind.bind, Except.bind] at accepted
    | ok next =>
      simp only [checked, bind_pure_comp] at accepted
      obtain ⟨before, after, prefixChecked, itemChecked⟩ := ih accepted
      refine ⟨before, after, ?_, itemChecked⟩
      rw [Backend.Native.validateInstructionLoop, List.forIn_cons]
      simp only [checked, bind_pure_comp]
      exact prefixChecked

/-- An instruction is in the producer meaning proof's supported step class
when its decoded relation supplies the corresponding step premise. -/
def SupportsMeaning (raw : Json) : Prop :=
  ∀ hash witness,
    (∀ instruction, decodeInstruction raw = .ok instruction →
      Instruction.Holds hash witness instruction) →
    AcceptedMeaningStep hash witness raw

/-- Bounds for one accepted comparison follow from satisfaction of its
original prefix. No condition on the comparison result or suffix is needed. -/
theorem acceptedComparisonBoundsFromPrefix
    {hash : Hash} {witness : Assignment} {expected : Backend.Native.Expected}
    {source : Array Json} {initial final : Backend.Native.State}
    (initialMeaning : StateMeaning hash witness witness initial)
    (initialDefinitions : NativeDefinitions initial)
    (inputSchema : ∀ requirement ∈ expected.inputs,
      requirement.ty.isForeign = false)
    (steps : ∀ raw ∈ source.toList, SupportsMeaning raw)
    (accepted : Backend.Native.validateInstructionLoop expected source.toList.zipIdx
      initial = .ok final)
    {prelude rest : List Json} {raw : Json} {left right : Operand}
    {width : Nat} {output : String}
    (split : source.toList = prelude ++ raw :: rest)
    (prefixHolds : ∀ item ∈ prelude, ∀ instruction,
      decodeInstruction item = .ok instruction → Instruction.Holds hash witness instruction)
    (opcode : NativeRelationJson.stringField raw "op" = .ok "less_than")
    (decoded : decodeInstruction raw = .ok (.lessThan left right width output)) :
    (left.read witness).val < 2 ^ width ∧ (right.read witness).val < 2 ^ width := by
  rw [split, List.zipIdx_append, List.zipIdx_cons] at accepted
  obtain ⟨before, _, checkedPrefix, checkedComparison⟩ := acceptedLoopCut accepted
  have prefixSteps : ∀ item ∈ prelude.zipIdx, AcceptedMeaningStep hash witness item.1 := by
    intro item indexed
    have member : item.1 ∈ prelude := by
      rw [← List.zipIdx_map_fst 0 prelude]
      exact List.mem_map_of_mem indexed
    have sourceMember : item.1 ∈ source.toList := by
      rw [split]
      exact List.mem_append_left _ member
    exact steps item.1 sourceMember hash witness (prefixHolds item.1 member)
  have ⟨beforeMeaning, _, _⟩ := accepted_loop_meaning_at_steps initialMeaning
    initialDefinitions inputSchema (fun _ _ => rfl) prefixSteps checkedPrefix
  exact accepted_lessThan_witnessBounds beforeMeaning
    (by simpa only [ScalarValidationOutputMeaning.nativeJson_stringField_eq] using opcode)
    decoded checkedComparison

/-- The exact comparison rewrite preserves satisfaction for every assignment on
an accepted array in the stated producer step class. Each rewrite uses bounds
from the original prefix as the pass advances. -/
theorem acceptedArrayReusePreserves
    {expected : Backend.Native.Expected} {source : Array Json}
    {original : List Instruction} {initial final : Backend.Native.State}
    (initialMeaning : ∀ hash witness, StateMeaning hash witness witness initial)
    (initialDefinitions : NativeDefinitions initial)
    (inputSchema : ∀ requirement ∈ expected.inputs,
      requirement.ty.isForeign = false)
    (steps : ∀ raw ∈ source.toList, SupportsMeaning raw)
    (decoded : source.toList.mapM decodeInstruction = .ok original)
    (accepted : Backend.Native.validateInstructionLoop expected source.toList.zipIdx
      initial = .ok final) :
    ∃ optimized,
      (reuseComparisons source).toList.mapM decodeInstruction = .ok optimized ∧
      optimized.filter stableOutsideComparisons = original.filter stableOutsideComparisons ∧
      ∀ hash witness,
        (∀ instruction ∈ optimized, Instruction.Holds hash witness instruction) ↔
        (∀ instruction ∈ original, Instruction.Holds hash witness instruction) := by
  apply reuseComparisons_preserves_decoded_of_prefix_ranges source original decoded
  intro hash witness prelude raw rest left right width output split prefixHolds opcode comparison
  exact acceptedComparisonBoundsFromPrefix (initialMeaning hash witness) initialDefinitions
    inputSchema steps accepted split prefixHolds opcode comparison

/-- The accepted producer prefix also preserves the full kernel interface,
including ordered inputs, Impact groups and returns. -/
theorem acceptedArrayReusePreservesKernel
    {expected : Backend.Native.Expected} {source : Array Json}
    {initial final : Backend.Native.State} {left right : Program}
    (initialMeaning : ∀ hash witness, StateMeaning hash witness witness initial)
    (initialDefinitions : NativeDefinitions initial)
    (inputSchema : ∀ requirement ∈ expected.inputs,
      requirement.ty.isForeign = false)
    (steps : ∀ raw ∈ source.toList, SupportsMeaning raw)
    (sourceDecoded : source.toList.mapM decodeInstruction = .ok left.instructions)
    (runDecoded : (reuseComparisons source).toList.mapM decodeInstruction = .ok right.instructions)
    (accepted : Backend.Native.validateInstructionLoop expected source.toList.zipIdx
      initial = .ok final) :
    ∀ hash streams witness groups returns,
      (Satisfies hash left streams witness groups returns ↔
        Satisfies hash right streams witness groups returns) := by
  obtain ⟨optimized, optimizedDecoded, stable, holds⟩ :=
    acceptedArrayReusePreserves initialMeaning initialDefinitions inputSchema steps
      sourceDecoded accepted
  have equality : optimized = right.instructions :=
    Except.ok.inj (optimizedDecoded.symm.trans runDecoded)
  apply RangeDedupKernel.comparisonRewrite_preserves_kernel left right
  · rw [← equality]
    exact stable.symm
  · intro hash witness
    simpa only [equality] using (holds hash witness).symm

end Noctium.Verification.RangeDedupAcceptedArray
