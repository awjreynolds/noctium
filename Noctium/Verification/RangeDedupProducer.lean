import Noctium.Verification.RangeDedup
import Noctium.Backend.NativeProducer
import Noctium.Verification.NativeRelationJson
import Noctium.Verification.ScalarParserAgreement
import Noctium.Verification.ScalarValidationMeaning

namespace Noctium.Verification.RangeDedupProducer

open Lean Backend.Native NativeRelation NativeRelationJson
open Noctium.Backend.RangeDedup
open Noctium.Verification.RangeDedup
open Noctium.Verification.ScalarValidationMeaning

private theorem producerBindOk {ε α β} {first : Except ε α} {next : α → Except ε β}
    {value : β} : (first >>= next) = .ok value ↔
      ∃ intermediate, first = .ok intermediate ∧ next intermediate = .ok value := by
  cases first <;> simp [Bind.bind, Except.bind]

private theorem producerEnsureOk {condition : Bool} {message : String} :
    Backend.Native.ensure condition message = .ok () ↔ condition = true := by
  cases condition <;> simp [Backend.Native.ensure] <;> rfl

private theorem decodedLessThanOperands {raw : Json} {left right : Operand}
    {width : Nat} {output : String}
    (opcode : Backend.Native.stringField raw "op" = .ok "less_than")
    (decoded : decodeInstruction raw = .ok (.lessThan left right width output)) :
    NativeRelationJson.decodeOperandField raw "a" = .ok left ∧
      NativeRelationJson.decodeOperandField raw "b" = .ok right := by
  unfold NativeRelationJson.decodeInstruction at decoded
  simp only [producerBindOk, ScalarValidationMeaning.nativeJson_stringField_eq] at decoded
  rcases decoded with ⟨opcodeName, opcodeParsed, body⟩
  have opcodeEq : opcodeName = "less_than" := Except.ok.inj (opcodeParsed.symm.trans opcode)
  subst opcodeName
  simp only [producerBindOk] at body
  rcases body with ⟨_, _, body⟩
  rcases body with ⟨decodedWidth, widthParsed, body⟩
  rcases body with ⟨_, rangeChecked, body⟩
  rcases body with ⟨decodedLeft, leftDecoded, body⟩
  rcases body with ⟨decodedRight, rightDecoded, body⟩
  rcases body with ⟨decodedOutput, outputParsed, body⟩
  rcases body with ⟨_, outputChecked, result⟩
  simp only [Pure.pure, Except.pure] at result
  have resultEq : Instruction.lessThan decodedLeft decodedRight decodedWidth decodedOutput =
      Instruction.lessThan left right width output := Except.ok.inj result
  injection resultEq with leftEq rightEq widthEq outputEq
  subst left right
  exact ⟨leftDecoded, rightDecoded⟩

/-- Facts returned by one successful NativeProducer `less_than` check.
`bits` is the producer's strict parser result, and both operand maxima pass
the exact precondition used by its checked comparison transition. -/
def AcceptedLessThanFacts (raw : Json) (state : Backend.Native.State) : Prop :=
  ∃ (bits : Nat) (left right : Backend.Native.Fact),
    Backend.Native.natField raw "bits" = .ok bits ∧
    Backend.Native.argument state raw "a" = .ok left ∧
    Backend.Native.argument state raw "b" = .ok right ∧
    left.maximum < 2 ^ bits ∧ right.maximum < 2 ^ bits

/-- The checked transition itself establishes both operand maximum bounds.
This exposes the facts consumed by the actual comparison case in
`NativeProducer.validateInstruction`. -/
theorem acceptedLessThanFacts {expected : Backend.Native.Expected}
    {state next : Backend.Native.State} {raw : Json}
    (opcode : Backend.Native.stringField raw "op" = .ok "less_than")
    (accepted : Backend.Native.validateInstruction expected state raw = .ok next) :
    AcceptedLessThanFacts raw state := by
  unfold Backend.Native.validateInstruction at accepted
  simp only [producerBindOk] at accepted
  rcases accepted with ⟨opcodeName, opcodeParsed, descriptor, descriptorParsed, registry,
    fieldsParsed, accepted⟩
  have opcodeNameEq : opcodeName = "less_than" :=
    Except.ok.inj (opcodeParsed.symm.trans opcode)
  subst opcodeName
  simp at accepted
  simp only [producerBindOk] at accepted
  rcases accepted with ⟨leftText, leftTextParsed, left, leftParsed,
    right, rightParsed, bits, bitsParsed, _, rangeAccepted, fact, combined, result⟩
  have range := producerEnsureOk.mp rangeAccepted
  have range := Bool.and_eq_true_iff.mp range
  have leftBound : left.maximum < 2 ^ bits := of_decide_eq_true range.1
  have rightBound : right.maximum < 2 ^ bits := of_decide_eq_true range.2
  have producerWidth : Backend.Native.natField raw "bits" = .ok bits := by
    unfold Backend.Native.width at bitsParsed
    simp only [producerBindOk] at bitsParsed
    rcases bitsParsed with ⟨found, fieldParsed, _, equal⟩
    have same : found = bits := Except.ok.inj equal.2
    rw [← same]
    exact fieldParsed
  have leftArgument : Backend.Native.argument state raw "a" = .ok left := by
    unfold Backend.Native.argument
    rw [leftTextParsed]
    change (do
      let found ← Backend.Native.operand state leftText
      Backend.Native.ensure (found.valueType == Backend.Native.NativeValueType.native)
        "native instruction operand must have Native type"
      pure found) = .ok left at leftParsed
    simp only [producerBindOk] at leftParsed
    rcases leftParsed with ⟨found, operandAccepted, _, equal⟩
    have same : found = left := Except.ok.inj equal.2
    subst left
    simpa only [leftTextParsed, Bind.bind, Except.bind] using operandAccepted
  have rightArgument : Backend.Native.argument state raw "b" = .ok right := by
    unfold Backend.Native.argument
    change (do
      let text ← Backend.Native.stringField raw "b"
      let found ← Backend.Native.operand state text
      Backend.Native.ensure (found.valueType == Backend.Native.NativeValueType.native)
        "native instruction operand must have Native type"
      pure found) = .ok right at rightParsed
    simp only [producerBindOk] at rightParsed
    rcases rightParsed with ⟨rightText, rightTextParsed, rightNative⟩
    rcases rightNative with ⟨found, operandAccepted, _, _, equal⟩
    have same : found = right := Except.ok.inj equal
    subst right
    rw [rightTextParsed]
    simpa only [Bind.bind, Except.bind] using operandAccepted
  exact ⟨bits, left, right, producerWidth, leftArgument, rightArgument,
    leftBound, rightBound⟩

/-- A successful #719 producer loop exposes the exact pre-state and accepted
transition for every indexed instruction. -/
theorem validateInstructionLoop_step {expected : Backend.Native.Expected}
    {items : List (Json × Nat)} {initial final : Backend.Native.State}
    (accepted : Backend.Native.validateInstructionLoop expected items initial = .ok final)
    {raw : Json} {index : Nat} (member : (raw, index) ∈ items) :
    ∃ state next,
      Backend.Native.validateInstruction expected state raw = .ok next := by
  obtain ⟨_, visits⟩ := Backend.Native.validateInstructionLoop_prefixInvariant
    (expected := expected) (items := items) (initial := initial) (final := final)
    (property := fun _ => True) True.intro
    (by intro state next instruction _ _; trivial) accepted
  obtain ⟨state, next, _, checked, _⟩ := visits raw index member
  exact ⟨state, next, checked⟩

/-- A comparison entry in an accepted NativeProducer loop therefore carries
the producer's actual parsed width and checked operand maximum bounds. -/
theorem acceptedLoopLessThanFacts {expected : Backend.Native.Expected}
    {items : List (Json × Nat)} {initial final : Backend.Native.State}
    (accepted : Backend.Native.validateInstructionLoop expected items initial = .ok final)
    {raw : Json} {index : Nat} (member : (raw, index) ∈ items)
    (opcode : Backend.Native.stringField raw "op" = .ok "less_than") :
    ∃ state next, Backend.Native.validateInstruction expected state raw = .ok next ∧
      AcceptedLessThanFacts raw state := by
  obtain ⟨state, next, checked⟩ := validateInstructionLoop_step accepted member
  exact ⟨state, next, checked, acceptedLessThanFacts opcode checked⟩

/-! This module joins the checked native producer loop to the exact Copy
semantics used by comparison reuse. It does not claim whole-array parity. -/

/-- Equal recognized keys with producer-derived operand bounds rewrite to the
exact emitted Copy, whose decoded relation is equivalent to the duplicate
comparison at the same witness. -/
theorem reuseComparisons_pair_bridge_with_bounds (hash : Hash) (witness : Assignment)
    (earlier later : Json) (leftKey rightKey : String) (width : Nat)
    (firstOutput duplicateOutput : String)
    (left₁ right₁ : Operand) (width₁ : Nat) (output₁ : String)
    (left₂ right₂ : Operand) (width₂ : Nat) (output₂ : String)
    (earlierKey : comparison? earlier = some ((leftKey, rightKey, width), firstOutput))
    (laterKey : comparison? later = some ((leftKey, rightKey, width), duplicateOutput))
    (earlierDecoded : decodeInstruction earlier =
      .ok (.lessThan left₁ right₁ width₁ output₁))
    (laterDecoded : decodeInstruction later =
      .ok (.lessThan left₂ right₂ width₂ output₂))
    (leftBound : (left₁.read witness).val < 2 ^ width)
    (rightBound : (right₁.read witness).val < 2 ^ width) :
    reuseComparisons #[earlier, later] =
        #[earlier, comparisonCopyJson firstOutput duplicateOutput] ∧
      decodeInstruction (comparisonCopyJson firstOutput duplicateOutput) =
        .ok (.equal (.reference firstOutput) (.reference duplicateOutput)) ∧
      ((Instruction.Holds hash witness
          (.lessThan left₁ right₁ width firstOutput) ∧
        Instruction.Holds hash witness
          (.equal (.reference firstOutput) (.reference duplicateOutput))) ↔
        (Instruction.Holds hash witness
          (.lessThan left₁ right₁ width firstOutput) ∧
        Instruction.Holds hash witness
          (.lessThan left₁ right₁ width duplicateOutput))) := by
  obtain ⟨leftEq, rightEq, widthEq₁, widthEq₂, outputEq₁, outputEq₂⟩ :=
    equalComparisonKeys_decode_agree earlier later leftKey rightKey width
      firstOutput duplicateOutput left₁ right₁ width₁ output₁ left₂ right₂ width₂ output₂
      earlierKey laterKey earlierDecoded laterDecoded
  have earlierCanonical : decodeInstruction earlier =
      .ok (.lessThan left₁ right₁ width firstOutput) := by
    rw [widthEq₁, outputEq₁] at earlierDecoded
    exact earlierDecoded
  have laterCanonical : decodeInstruction later =
      .ok (.lessThan left₁ right₁ width duplicateOutput) := by
    rw [widthEq₂, outputEq₂, ← leftEq, ← rightEq] at laterDecoded
    exact laterDecoded
  have firstValid := comparison_decode_output_valid earlier leftKey rightKey firstOutput width
    left₁ right₁ width₁ output₁ earlierKey earlierDecoded
  have duplicateValid := comparison_decode_output_valid later leftKey rightKey duplicateOutput width
    left₂ right₂ width₂ output₂ laterKey laterDecoded
  have emittedCopy := NativeRelationJson.decodeInstruction_copyJson firstOutput duplicateOutput
    firstValid duplicateValid
  refine ⟨reuseComparisons_pair earlier later (leftKey, rightKey, width) firstOutput
    duplicateOutput earlierKey laterKey, emittedCopy, ?_⟩
  exact lessThanEqualCopyPreserves hash witness left₁ right₁ width firstOutput duplicateOutput
    leftBound rightBound

/-- Compose the accepted producer bounds for both comparison occurrences with
the exact emitted-Copy relation. Each operand bound comes from the actual
ScalarValidationMeaning invariant at that occurrence's producer pre-state. -/
theorem acceptedProducerPairCopyBridge (hash : Hash) (inputs witness : Assignment)
    (expected : Backend.Native.Expected)
    (earlier later : Json) (state₁ next₁ state₂ next₂ : Backend.Native.State)
    (leftKey rightKey : String) (width : Nat) (firstOutput duplicateOutput : String)
    (left₁ right₁ : Operand) (width₁ : Nat) (output₁ : String)
    (left₂ right₂ : Operand) (width₂ : Nat) (output₂ : String)
    (earlierOpcode : Backend.Native.stringField earlier "op" = .ok "less_than")
    (laterOpcode : Backend.Native.stringField later "op" = .ok "less_than")
    (earlierAccepted : Backend.Native.validateInstruction expected state₁ earlier = .ok next₁)
    (laterAccepted : Backend.Native.validateInstruction expected state₂ later = .ok next₂)
    (earlierKey : comparison? earlier = some ((leftKey, rightKey, width), firstOutput))
    (laterKey : comparison? later = some ((leftKey, rightKey, width), duplicateOutput))
    (earlierDecoded : decodeInstruction earlier =
      .ok (.lessThan left₁ right₁ width₁ output₁))
    (laterDecoded : decodeInstruction later =
      .ok (.lessThan left₂ right₂ width₂ output₂))
    (earlierMeaning : StateMeaning hash inputs witness state₁)
    (laterMeaning : StateMeaning hash inputs witness state₂) :
    reuseComparisons #[earlier, later] =
        #[earlier, comparisonCopyJson firstOutput duplicateOutput] ∧
      decodeInstruction (comparisonCopyJson firstOutput duplicateOutput) =
        .ok (.equal (.reference firstOutput) (.reference duplicateOutput)) ∧
      ((Instruction.Holds hash witness
          (.lessThan left₁ right₁ width firstOutput) ∧
        Instruction.Holds hash witness
          (.equal (.reference firstOutput) (.reference duplicateOutput))) ↔
        (Instruction.Holds hash witness
          (.lessThan left₁ right₁ width firstOutput) ∧
        Instruction.Holds hash witness
          (.lessThan left₁ right₁ width duplicateOutput))) ∧
      (left₁.read witness).val < 2 ^ width ∧
      (right₁.read witness).val < 2 ^ width ∧
      (left₂.read witness).val < 2 ^ width ∧
      (right₂.read witness).val < 2 ^ width := by
  obtain ⟨earlierBits, earlierLeft, earlierRight, earlierWidthParsed,
      earlierLeftParsed, earlierRightParsed, earlierLeftMaximum, earlierRightMaximum⟩ :=
    acceptedLessThanFacts earlierOpcode earlierAccepted
  obtain ⟨laterBits, laterLeft, laterRight, laterWidthParsed,
      laterLeftParsed, laterRightParsed, laterLeftMaximum, laterRightMaximum⟩ :=
    acceptedLessThanFacts laterOpcode laterAccepted
  have earlierDecoderWidth := comparison_key_width_field earlier leftKey rightKey firstOutput
    width earlierKey
  have laterDecoderWidth := comparison_key_width_field later leftKey rightKey duplicateOutput
    width laterKey
  have earlierWidthEq := ScalarParserAgreement.natField_naturalField_agree earlier "bits"
    earlierBits width earlierWidthParsed earlierDecoderWidth
  have laterWidthEq := ScalarParserAgreement.natField_naturalField_agree later "bits"
    laterBits width laterWidthParsed laterDecoderWidth
  obtain ⟨earlierLeftDecoded, earlierRightDecoded⟩ :=
    decodedLessThanOperands earlierOpcode earlierDecoded
  obtain ⟨laterLeftDecoded, laterRightDecoded⟩ :=
    decodedLessThanOperands laterOpcode laterDecoded
  have earlierLeftFactMeaning := argument_decoded_meaning earlierMeaning
    earlierLeftParsed earlierLeftDecoded
  have earlierRightFactMeaning := argument_decoded_meaning earlierMeaning
    earlierRightParsed earlierRightDecoded
  have laterLeftFactMeaning := argument_decoded_meaning laterMeaning
    laterLeftParsed laterLeftDecoded
  have laterRightFactMeaning := argument_decoded_meaning laterMeaning
    laterRightParsed laterRightDecoded
  have earlierLeftValueBound : (left₁.read witness).val ≤ earlierLeft.maximum :=
    earlierLeftFactMeaning.bound
  have earlierRightValueBound : (right₁.read witness).val ≤ earlierRight.maximum :=
    earlierRightFactMeaning.bound
  have laterLeftValueBound : (left₂.read witness).val ≤ laterLeft.maximum :=
    laterLeftFactMeaning.bound
  have laterRightValueBound : (right₂.read witness).val ≤ laterRight.maximum :=
    laterRightFactMeaning.bound
  have earlierLeftBound : (left₁.read witness).val < 2 ^ width := by
    have bound := Nat.lt_of_le_of_lt earlierLeftValueBound earlierLeftMaximum
    rw [earlierWidthEq] at bound
    exact bound
  have earlierRightBound : (right₁.read witness).val < 2 ^ width := by
    have bound := Nat.lt_of_le_of_lt earlierRightValueBound earlierRightMaximum
    rw [earlierWidthEq] at bound
    exact bound
  have laterLeftBound : (left₂.read witness).val < 2 ^ width := by
    have bound := Nat.lt_of_le_of_lt laterLeftValueBound laterLeftMaximum
    rw [laterWidthEq] at bound
    exact bound
  have laterRightBound : (right₂.read witness).val < 2 ^ width := by
    have bound := Nat.lt_of_le_of_lt laterRightValueBound laterRightMaximum
    rw [laterWidthEq] at bound
    exact bound
  have pair := reuseComparisons_pair_bridge_with_bounds hash witness earlier later
    leftKey rightKey width firstOutput duplicateOutput left₁ right₁ width₁ output₁
    left₂ right₂ width₂ output₂ earlierKey laterKey earlierDecoded laterDecoded
    earlierLeftBound earlierRightBound
  exact ⟨pair.1, pair.2.1, pair.2.2, earlierLeftBound, earlierRightBound,
    laterLeftBound, laterRightBound⟩

/-- Lift the checked pair bridge to two actual visits in one accepted producer
loop. The invariant preservation premise supplies soundness at both visit
pre-states through the #719 prefix theorem. -/
theorem acceptedLoopProducerPairCopyBridge (hash : Hash) (inputs witness : Assignment)
    (expected : Backend.Native.Expected) (items : List (Json × Nat))
    (initial final : Backend.Native.State)
    (earlier later : Json) (earlierIndex laterIndex : Nat)
    (leftKey rightKey : String) (width : Nat) (firstOutput duplicateOutput : String)
    (left₁ right₁ : Operand) (width₁ : Nat) (output₁ : String)
    (left₂ right₂ : Operand) (width₂ : Nat) (output₂ : String)
    (accepted : Backend.Native.validateInstructionLoop expected items initial = .ok final)
    (initialMeaning : StateMeaning hash inputs witness initial)
    (meaningPreserved : ∀ {state next instruction},
      StateMeaning hash inputs witness state →
      Backend.Native.validateInstruction expected state instruction = .ok next →
      StateMeaning hash inputs witness next)
    (earlierMember : (earlier, earlierIndex) ∈ items)
    (laterMember : (later, laterIndex) ∈ items)
    (earlierOpcode : Backend.Native.stringField earlier "op" = .ok "less_than")
    (laterOpcode : Backend.Native.stringField later "op" = .ok "less_than")
    (earlierKey : comparison? earlier = some ((leftKey, rightKey, width), firstOutput))
    (laterKey : comparison? later = some ((leftKey, rightKey, width), duplicateOutput))
    (earlierDecoded : decodeInstruction earlier =
      .ok (.lessThan left₁ right₁ width₁ output₁))
    (laterDecoded : decodeInstruction later =
      .ok (.lessThan left₂ right₂ width₂ output₂)) :
    reuseComparisons #[earlier, later] =
        #[earlier, comparisonCopyJson firstOutput duplicateOutput] ∧
      decodeInstruction (comparisonCopyJson firstOutput duplicateOutput) =
        .ok (.equal (.reference firstOutput) (.reference duplicateOutput)) ∧
      ((Instruction.Holds hash witness
          (.lessThan left₁ right₁ width firstOutput) ∧
        Instruction.Holds hash witness
          (.equal (.reference firstOutput) (.reference duplicateOutput))) ↔
        (Instruction.Holds hash witness
          (.lessThan left₁ right₁ width firstOutput) ∧
        Instruction.Holds hash witness
          (.lessThan left₁ right₁ width duplicateOutput))) ∧
      (left₁.read witness).val < 2 ^ width ∧
      (right₁.read witness).val < 2 ^ width ∧
      (left₂.read witness).val < 2 ^ width ∧
      (right₂.read witness).val < 2 ^ width := by
  obtain ⟨_, visits⟩ := Backend.Native.validateInstructionLoop_prefixInvariant
    (expected := expected) (items := items) (initial := initial) (final := final)
    (property := StateMeaning hash inputs witness) initialMeaning
    (by intro state next instruction stateMeaning checked; exact meaningPreserved stateMeaning checked)
    accepted
  obtain ⟨state₁, next₁, earlierMeaning, earlierAccepted, _⟩ :=
    visits earlier earlierIndex earlierMember
  obtain ⟨state₂, next₂, laterMeaning, laterAccepted, _⟩ :=
    visits later laterIndex laterMember
  exact acceptedProducerPairCopyBridge hash inputs witness expected earlier later
    state₁ next₁ state₂ next₂ leftKey rightKey width firstOutput duplicateOutput
    left₁ right₁ width₁ output₁ left₂ right₂ width₂ output₂ earlierOpcode laterOpcode
    earlierAccepted laterAccepted earlierKey laterKey earlierDecoded laterDecoded
    earlierMeaning laterMeaning

end Noctium.Verification.RangeDedupProducer
