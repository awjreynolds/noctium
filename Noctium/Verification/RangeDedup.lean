import Noctium.Backend.RangeDedup
import Noctium.Verification.NativeRelationJson

namespace Noctium.Verification.RangeDedup

open Lean NativeRelation NativeRelationJson
open Noctium.Backend.RangeDedup

private theorem naturalField_of_getNat (item : Json) (field : String) (width : Nat)
    (found : (item.getObjVal? field >>= Json.getNat?) = .ok width) :
    naturalField item field = .ok width := by
  cases lookup : item.getObjVal? field with
  | error message => simp [lookup, bind, Except.bind] at found
  | ok json =>
    simp only [lookup, bind, Except.bind] at found
    cases json with
    | num number =>
      obtain ⟨mantissa, exponent⟩ := number
      cases mantissa <;> cases exponent <;>
        simp [Json.getNat?, naturalField, lookup, bind, Except.bind, pure, Except.pure, ensure] at found ⊢
      exact Except.ok.inj found
    | _ => simp [Json.getNat?, throw] at found

private theorem prefix_disjoint (name : String) (starts : name.startsWith '%' = true) :
    name.startsWith "0x" = false := by
  simp only [String.startsWith_char_eq_head?, beq_iff_eq] at starts
  cases isHex : name.startsWith "0x"
  · rfl
  · obtain ⟨suffix, eq⟩ := String.startsWith_string_iff.mp isHex
    rw [← eq] at starts
    simp at starts

private theorem option_guard_some (condition : Prop) [Decidable condition] (witness : Unit) :
    guard (f := Option) condition = some witness ↔ condition := by
  cases witness
  by_cases test : condition <;> simp [guard, test, pure, failure]

private theorem toOption_some {result : Except String α} {value : α}
    (found : result.toOption = some value) : result = .ok value := by
  cases result <;> simp_all [Except.toOption]

private theorem key_fields (item : Json) (name : String) (bits : Nat)
    (key : key? item = some (name, bits)) :
    stringField item "op" = .ok "constrain_bits" ∧
      stringField item "val" = .ok name ∧
      name.startsWith '%' = true ∧ naturalField item "bits" = .ok bits := by
  simp only [key?, bind, Option.bind_eq_some_iff, option_guard_some, pure,
    Option.some.injEq, Prod.mk.injEq] at key
  obtain ⟨_, _, _, _, opcodeValue, opcode, _, opcodeEq, operandValue, operand, _, starts,
    bitWidth, width, _, _, rfl, rfl⟩ := key
  have opcodeEq := beq_iff_eq.mp opcodeEq
  exact ⟨opcodeEq ▸ toOption_some opcode, toOption_some operand, starts,
    naturalField_of_getNat item "bits" _ (toOption_some width)⟩

private theorem comparison_fields (item : Json) (left right output : String) (width : Nat)
    (key : comparison? item = some ((left, right, width), output)) :
    stringField item "op" = .ok "less_than" ∧
      stringField item "a" = .ok left ∧ stringField item "b" = .ok right ∧
      naturalField item "bits" = .ok width ∧ stringField item "output" = .ok output := by
  simp only [comparison?, bind, Option.bind_eq_some_iff, option_guard_some, pure,
    Option.some.injEq, Prod.mk.injEq] at key
  obtain ⟨_, _, _, _, opcode, opcodeValue, _, opcodeEq, leftValue, leftFound,
    rightValue, rightFound, widthValue, widthFound, outputValue, outputFound,
    tupleMatches, outputMatches⟩ := key
  have opcodeMatches : opcode = "less_than" := of_decide_eq_true opcodeEq
  have opcodeField : stringField item "op" = .ok "less_than" := by
    have decoded := toOption_some opcodeValue
    rw [opcodeMatches] at decoded
    simpa [stringField, Bind.bind] using decoded
  have leftEq := tupleMatches.1
  have rightEq := tupleMatches.2.1
  have widthEq := tupleMatches.2.2
  have outputEq := outputMatches
  have leftField : stringField item "a" = .ok leftValue := by
    simpa [stringField, Bind.bind] using toOption_some leftFound
  have rightField : stringField item "b" = .ok rightValue := by
    simpa [stringField, Bind.bind] using toOption_some rightFound
  have widthField := naturalField_of_getNat item "bits" widthValue (toOption_some widthFound)
  have outputField : stringField item "output" = .ok outputValue := by
    simpa [stringField, Bind.bind] using toOption_some outputFound
  rw [leftEq] at leftField
  rw [rightEq] at rightField
  rw [widthEq] at widthField
  rw [outputEq] at outputField
  exact ⟨opcodeField, leftField, rightField, widthField, outputField⟩

private theorem decodeOperandField_from_string (item : Json) (field text : String)
    (parsed : stringField item field = .ok text) :
    decodeOperandField item field = decodeOperand (toJson text) := by
  cases found : item.getObjVal? field with
  | error message => simp [stringField, found, bind, Except.bind] at parsed
  | ok value =>
    cases value with
    | str value =>
      simp only [stringField, found, bind, Except.bind, Json.getStr?] at parsed
      have same : value = text := by
        change Except.ok value = Except.ok text at parsed
        exact Except.ok.inj parsed
      subst text
      simp [decodeOperandField, found, toJson, bind, Except.bind]
    | _ => simp [stringField, found, bind, Except.bind, Json.getStr?] at parsed

theorem comparison_decode_agrees (item : Json) (leftKey rightKey keyOutput : String)
    (keyWidth : Nat) (left right : Operand) (decodedWidth : Nat) (decodedOutput : String)
    (key : comparison? item = some ((leftKey, rightKey, keyWidth), keyOutput))
    (decoded : decodeInstruction item =
      .ok (.lessThan left right decodedWidth decodedOutput)) :
    decodeOperand (toJson leftKey) = .ok left ∧
      decodeOperand (toJson rightKey) = .ok right ∧
      decodedWidth = keyWidth ∧ decodedOutput = keyOutput ∧
      NativeRelationJson.validIdentifier keyOutput = true := by
  obtain ⟨opcodeField, leftField, rightField, widthField, outputField⟩ :=
    comparison_fields item leftKey rightKey keyOutput keyWidth key
  have leftDecoded := decodeOperandField_from_string item "a" leftKey leftField
  have rightDecoded := decodeOperandField_from_string item "b" rightKey rightField
  unfold decodeInstruction at decoded
  simp only [opcodeField, bind, Except.bind] at decoded
  cases exact : exactFields item ["op", "a", "b", "bits", "output"] with
  | error message => simp [exact] at decoded
  | ok _ =>
    simp only [exact, widthField] at decoded
    cases bounded : ensure (0 < keyWidth && keyWidth ≤ ScalarPolicy.maxBits)
        "unsupported native bit width" with
    | error message => simp [bounded] at decoded
    | ok _ =>
      simp only [bounded, leftDecoded, rightDecoded, outputField] at decoded
      cases leftValue : decodeOperand (toJson leftKey) with
      | error message => simp [leftValue] at decoded
      | ok decodedLeft =>
        simp only [leftValue] at decoded
        cases rightValue : decodeOperand (toJson rightKey) with
        | error message => simp [rightValue] at decoded
        | ok decodedRight =>
          simp only [rightValue] at decoded
          cases outputValid : ensure (validIdentifier keyOutput) "invalid native SSA definition" with
          | error message => simp [outputValid] at decoded
          | ok _ =>
            have keyOutputValid : NativeRelationJson.validIdentifier keyOutput = true := by
              simpa [NativeRelationJson.ensure] using outputValid
            simp only [outputValid, pure, Except.pure] at decoded
            simp only [Except.ok.injEq, Instruction.lessThan.injEq] at decoded
            rcases decoded with ⟨leftEq, rightEq, widthEq, outputEq⟩
            subst left
            subst right
            subst decodedWidth
            subst decodedOutput
            exact ⟨rfl, rfl, rfl, rfl, keyOutputValid⟩

/-- A recognized comparison that decodes successfully has exactly the keyed
operand width and output. This form does not assume the decoded instruction's
constructor in advance, and also carries the output identifier check needed by
native SSA admission. -/
theorem exists_comparison_decode (item : Json) (leftKey rightKey keyOutput : String)
    (keyWidth : Nat) (instruction : Instruction)
    (key : comparison? item = some ((leftKey, rightKey, keyWidth), keyOutput))
    (decoded : decodeInstruction item = .ok instruction) :
    ∃ left right,
      instruction = .lessThan left right keyWidth keyOutput ∧
      decodeOperand (toJson leftKey) = .ok left ∧
      decodeOperand (toJson rightKey) = .ok right ∧
      NativeRelationJson.validIdentifier keyOutput = true := by
  obtain ⟨opcodeField, leftField, rightField, widthField, outputField⟩ :=
    comparison_fields item leftKey rightKey keyOutput keyWidth key
  have leftDecoded := decodeOperandField_from_string item "a" leftKey leftField
  have rightDecoded := decodeOperandField_from_string item "b" rightKey rightField
  unfold decodeInstruction at decoded
  simp only [opcodeField, bind, Except.bind] at decoded
  cases exact : exactFields item ["op", "a", "b", "bits", "output"] with
  | error message => simp [exact] at decoded
  | ok _ =>
    simp only [exact, widthField] at decoded
    cases bounded : ensure (0 < keyWidth && keyWidth ≤ ScalarPolicy.maxBits)
        "unsupported native bit width" with
    | error message => simp [bounded] at decoded
    | ok _ =>
      simp only [bounded, leftDecoded, rightDecoded, outputField] at decoded
      cases leftValue : decodeOperand (toJson leftKey) with
      | error message => simp [leftValue] at decoded
      | ok decodedLeft =>
        simp only [leftValue] at decoded
        cases rightValue : decodeOperand (toJson rightKey) with
        | error message => simp [rightValue] at decoded
        | ok decodedRight =>
          simp only [rightValue] at decoded
          cases outputValid : ensure (validIdentifier keyOutput) "invalid native SSA definition" with
          | error message => simp [outputValid] at decoded
          | ok _ =>
            have keyOutputValid : NativeRelationJson.validIdentifier keyOutput = true := by
              simpa [NativeRelationJson.ensure] using outputValid
            simp only [outputValid, pure, Except.pure, Except.ok.injEq] at decoded
            cases instruction with
            | lessThan left right decodedWidth decodedOutput =>
              simp only [Instruction.lessThan.injEq] at decoded
              rcases decoded with ⟨leftEq, rightEq, widthEq, outputEq⟩
              subst left
              subst right
              subst decodedWidth
              subst decodedOutput
              exact ⟨decodedLeft, decodedRight, rfl, rfl, rfl, keyOutputValid⟩
            | _ => cases decoded

/-- Successful native decoding of two equal comparison keys yields the same
ordered typed operands and width. Decoded output names follow their respective
recognized JSON fields, so this statement also permits distinct destinations.
The raw operand strings pass through `decodeOperand`, including immediates. -/
theorem equalComparisonKeys_decode_agree (earlier later : Json)
    (leftKey rightKey : String) (width : Nat) (firstOutput duplicateOutput : String)
    (left₁ right₁ : Operand) (width₁ : Nat) (output₁ : String)
    (left₂ right₂ : Operand) (width₂ : Nat) (output₂ : String)
    (earlierKey : comparison? earlier = some ((leftKey, rightKey, width), firstOutput))
    (laterKey : comparison? later = some ((leftKey, rightKey, width), duplicateOutput))
    (decoded₁ : decodeInstruction earlier =
      .ok (.lessThan left₁ right₁ width₁ output₁))
    (decoded₂ : decodeInstruction later =
      .ok (.lessThan left₂ right₂ width₂ output₂)) :
    left₁ = left₂ ∧ right₁ = right₂ ∧ width₁ = width ∧ width₂ = width ∧
      output₁ = firstOutput ∧ output₂ = duplicateOutput := by
  obtain ⟨decodeLeft₁, decodeRight₁, widthEq₁, outputEq₁, _⟩ :=
    comparison_decode_agrees earlier leftKey rightKey firstOutput width
      left₁ right₁ width₁ output₁ earlierKey decoded₁
  obtain ⟨decodeLeft₂, decodeRight₂, widthEq₂, outputEq₂, _⟩ :=
    comparison_decode_agrees later leftKey rightKey duplicateOutput width
      left₂ right₂ width₂ output₂ laterKey decoded₂
  have leftEq : left₁ = left₂ :=
    Except.ok.inj (decodeLeft₁.symm.trans decodeLeft₂)
  have rightEq : right₁ = right₂ :=
    Except.ok.inj (decodeRight₁.symm.trans decodeRight₂)
  exact ⟨leftEq, rightEq, widthEq₁, widthEq₂, outputEq₁, outputEq₂⟩

private theorem key_instruction (item : Json) (instruction : Instruction) (name : String)
    (bits : Nat) (key : key? item = some (name, bits))
    (decoded : decodeInstruction item = .ok instruction) :
    instruction = .bits (.reference name) bits := by
  obtain ⟨opcode, operand, starts, width⟩ := key_fields item name bits key
  simp only [decodeInstruction, opcode, bind, Except.bind] at decoded
  cases fields : exactFields item ["op", "val", "bits"] with
  | error message => simp [fields] at decoded
  | ok _ =>
    simp only [fields, width] at decoded
    cases allowed : ensure (0 < bits && bits ≤ ScalarPolicy.maxBits) "unsupported native bit width" with
    | error message => simp [allowed] at decoded
    | ok _ =>
      simp only [allowed, decodeOperandField, bind, Except.bind] at decoded
      have text : (item.getObjVal? "val" >>= Json.getStr?) = .ok name := operand
      cases json : item.getObjVal? "val" with
      | error message => simp [json, bind, Except.bind] at text
      | ok value =>
        simp only [json, bind, Except.bind] at text
        simp only [json, decodeOperand, text, bind, Except.bind, prefix_disjoint name starts,
          Bool.false_eq_true, ↓reduceIte] at decoded
        cases valid : ensure (validIdentifier name) "invalid native SSA reference" with
        | error message => simp [valid] at decoded
        | ok _ => simpa [valid, pure, Except.pure] using decoded.symm

private def decodedItem (item : Json) : Instruction :=
  (decodeInstruction item).toOption.getD (.output [])

private theorem decode_list (items : List Json) (instructions : List Instruction) :
    items.mapM decodeInstruction = .ok instructions ↔
      items.map decodedItem = instructions ∧
        ∀ item ∈ items, decodeInstruction item = .ok (decodedItem item) := by
  induction items generalizing instructions with
  | nil => simp [pure, Except.pure, eq_comm]
  | cons item rest ih =>
    cases decoded : decodeInstruction item with
    | error message =>
      simp [List.mapM_cons, bind, Except.bind, decoded]
    | ok decodedHead =>
      have head : decodedItem item = decodedHead := by simp [decodedItem, decoded, Except.toOption]
      simp only [List.mapM_cons, bind, Except.bind, decoded, List.map_cons, head]
      cases tail : rest.mapM decodeInstruction with
      | error message =>
        constructor
        · intro impossible
          cases impossible
        · rintro ⟨_, accepted⟩
          have impossible := (ih (rest.map decodedItem)).mpr
            ⟨rfl, fun json member => accepted json (List.mem_cons_of_mem _ member)⟩
          rw [tail] at impossible
          cases impossible
      | ok decodedTail =>
        have facts := (ih decodedTail).mp tail
        simp only [pure, Except.pure, Except.ok.injEq, facts.1]
        exact ⟨fun equal => ⟨equal, fun json member => by
          rcases List.mem_cons.mp member with rfl | member
          · simpa only [head] using decoded
          · exact facts.2 json member⟩, And.left⟩

private theorem decoded_assertionOperand? (item : Json) (operand : String)
    (instruction : Instruction) (recognized : assertionOperand? item = some operand)
    (decoded : decodeInstruction item = .ok instruction) :
    instruction = .assert (.reference operand) := by
  simp only [assertionOperand?, bind, Option.bind_eq_some_iff, option_guard_some,
    pure, Option.some.injEq] at recognized
  obtain ⟨object, objectEq, _, objectSize, opcode, opcodeEq, _, opcodeIsAssert,
    text, textEq, _, validText, textIsOperand⟩ := recognized
  have opcodeAsserts : opcode = "assert" := of_decide_eq_true opcodeIsAssert
  have opcodeDecode : (item.getObjVal? "op" >>= Json.getStr?) = .ok "assert" := by
    have h := toOption_some opcodeEq
    rw [opcodeAsserts] at h
    exact h
  have opcodeField : stringField item "op" = .ok "assert" := by
    simpa [stringField] using opcodeDecode
  have textDecode : (item.getObjVal? "cond" >>= Json.getStr?) = .ok text :=
    toOption_some textEq
  have condValue : item.getObjVal? "cond" = .ok (.str text) := by
    cases found : item.getObjVal? "cond" with
    | error message =>
      simp only [found, Bind.bind, Except.bind] at textDecode
      cases textDecode
    | ok value => cases value with
      | str value =>
        simp only [found, Bind.bind, Except.bind, Json.getStr?] at textDecode
        injection textDecode with equal
        subst value
        rfl
      | _ =>
        simp only [found, Bind.bind, Except.bind, Json.getStr?] at textDecode
        cases textDecode
  have validParts := validText
  simp only [Bool.and_eq_true] at validParts
  simp only [String.startsWith_char_eq_head?, beq_iff_eq] at validParts
  have bytePrefix : ['%'] <+: text.toList := by
    cases chars : text.toList with
    | nil => simp [chars] at validParts
    | cons first rest =>
      have firstIsPercent : first = '%' := by simpa [chars] using validParts.1.1
      subst first
      simp
  have valid : validIdentifier text = true := by
    simp [validIdentifier, bytePrefix, validParts.1.2, validParts.2]
  have starts : text.startsWith '%' = true := by
    simpa only [String.startsWith_char_eq_head?, beq_iff_eq] using validParts.1.1
  have noHex : text.startsWith "0x" = false := prefix_disjoint text (by
    exact starts)
  unfold decodeInstruction at decoded
  simp only [opcodeField, bind, Except.bind] at decoded
  cases fields : exactFields item ["op", "cond"] with
  | error message => simp [fields] at decoded
  | ok _ =>
    simp only [fields, decodeOperandField, bind, Except.bind] at decoded
    simp only [condValue, Json.getStr?, decodeOperand, bind, Except.bind, noHex, Bool.false_eq_true,
      ↓reduceIte, valid, ensure, pure, Except.pure] at decoded
    have decoded' : instruction = .assert (.reference text) := Except.ok.inj decoded.symm
    simpa [textIsOperand] using decoded'

/-- Inputs, Impact operations and outputs all occur among these ordered
instructions. Dropping range checks has no effect on their observations. -/
def nonRange : Instruction → Bool
  | .bits .. => false
  | _ => true

private theorem filter_map (items : List Json) :
    (items.map decodedItem).filter nonRange =
      items.flatMap fun item => if nonRange (decodedItem item) then [decodedItem item] else [] := by
  induction items with
  | nil => rfl
  | cons item rest ih =>
    by_cases kept : nonRange (decodedItem item) <;> simp [kept, ih]

def nonAssert : Instruction → Bool
  | .assert _ => false
  | _ => true

private theorem filter_decoded (items : List Json) :
    (items.map decodedItem).filter nonAssert =
      items.flatMap fun item =>
        if nonAssert (decodedItem item) then [decodedItem item] else [] := by
  induction items with
  | nil => rfl
  | cons item rest ih =>
    by_cases kept : nonAssert (decodedItem item) <;> simp [kept, ih]

/-- A native Copy binds the destination to the source SSA value.
Comparison reuse expresses this binding as equality over an assignment. -/
def copyHolds (witness : Assignment) (source destination : String) : Prop :=
  witness destination = witness source

/-- Read the Copy operand names. `comparisonCopyJson_decodes` applies this to
the exact object emitted by the comparison optimizer. -/
def comparisonCopyOperands? (instruction : Json) : Option (String × String) := do
  guard ((← (instruction.getObjVal? "op" >>= Json.getStr?).toOption) == "copy")
  let source ← (instruction.getObjVal? "val" >>= Json.getStr?).toOption
  let destination ← (instruction.getObjVal? "output" >>= Json.getStr?).toOption
  pure (source, destination)

/-- Model the reference Copy arms of pinned ZKIR 3.2.1 ir_vm.rs by storing the
resolved source value under the destination name. The VM checks freshness. -/
def vmCopyStore (witness : Assignment) (source destination : String) : Assignment :=
  fun name => if name == destination then witness source else witness name

def executeComparisonCopy (witness : Assignment) (instruction : Json) : Option Assignment := do
  let (source, destination) ← comparisonCopyOperands? instruction
  pure (vmCopyStore witness source destination)

theorem comparisonCopyJson_decodes (source destination : String) :
    comparisonCopyOperands? (comparisonCopyJson source destination) =
      some (source, destination) := by
  have opcode : (comparisonCopyJson source destination).getObjVal? "op" =
      .ok (.str "copy") := rfl
  have sourceField : (comparisonCopyJson source destination).getObjVal? "val" =
      .ok (.str source) := rfl
  have outputField : (comparisonCopyJson source destination).getObjVal? "output" =
      .ok (.str destination) := rfl
  simp [comparisonCopyOperands?, opcode, sourceField, outputField, guard,
    pure, failure, Bind.bind, Except.bind, Json.getStr?, Except.toOption, Except.pure]

theorem executeComparisonCopy_emitted (witness : Assignment) (source destination : String) :
    executeComparisonCopy witness (comparisonCopyJson source destination) =
      some (vmCopyStore witness source destination) := by
  simp [executeComparisonCopy, comparisonCopyJson_decodes]

theorem executeComparisonCopy_emitted_holds (witness result : Assignment)
    (source destination : String)
    (executed : executeComparisonCopy witness (comparisonCopyJson source destination) =
      some result) : copyHolds result source destination := by
  rw [executeComparisonCopy_emitted] at executed
  cases executed
  simp [copyHolds, vmCopyStore]

theorem vmCopyStore_unchanged (witness : Assignment) (source destination other : String)
    (otherIsNotOutput : other ≠ destination) :
    vmCopyStore witness source destination other = witness other := by
  simp [vmCopyStore, otherIsNotOutput]

/-- A retained comparison and the Copy emitted for its duplicate have exactly
the original duplicate comparison's arbitrary-witness constraint. Both input
bounds stay conditional in the same way in all three instructions. -/
theorem lessThanCopyPreserves (hash : Hash) (witness : Assignment)
    (left right : Operand) (width : Nat) (firstOutput duplicateOutput : String)
    (leftBound : (left.read witness).val < 2 ^ width)
    (rightBound : (right.read witness).val < 2 ^ width) :
    (Instruction.Holds hash witness
        (.lessThan left right width firstOutput) ∧
      copyHolds witness firstOutput duplicateOutput) ↔
      (Instruction.Holds hash witness
          (.lessThan left right width firstOutput) ∧
        Instruction.Holds hash witness (.lessThan left right width duplicateOutput)) := by
  constructor
  · rintro ⟨firstHolds, copied⟩
    refine ⟨firstHolds, ?_⟩
    intro _ _
    change witness duplicateOutput = witness firstOutput at copied
    rw [copied]
    exact firstHolds leftBound rightBound
  · rintro ⟨firstHolds, duplicateHolds⟩
    refine ⟨firstHolds, ?_⟩
    unfold copyHolds
    rw [firstHolds leftBound rightBound, duplicateHolds leftBound rightBound]

/-- The producer retains the original operand range checks. Under those checks,
replacing a second equal comparison with the emitted Copy preserves the full
constraint conjunction for every witness. -/
theorem lessThanCopyPreservesWithRanges (hash : Hash) (witness : Assignment)
    (left right : Operand) (width : Nat) (firstOutput duplicateOutput : String) :
    (Instruction.Holds hash witness (.bits left width) ∧
      Instruction.Holds hash witness (.bits right width) ∧
      Instruction.Holds hash witness (.lessThan left right width firstOutput) ∧
      copyHolds witness firstOutput duplicateOutput) ↔
    (Instruction.Holds hash witness (.bits left width) ∧
      Instruction.Holds hash witness (.bits right width) ∧
      Instruction.Holds hash witness (.lessThan left right width firstOutput) ∧
      Instruction.Holds hash witness (.lessThan left right width duplicateOutput)) := by
  constructor
  · rintro ⟨leftRange, rightRange, firstHolds, copied⟩
    have leftBound : (left.read witness).val < 2 ^ width := by
      simpa [Instruction.Holds] using leftRange
    have rightBound : (right.read witness).val < 2 ^ width := by
      simpa [Instruction.Holds] using rightRange
    obtain ⟨firstHolds, duplicateHolds⟩ :=
      (lessThanCopyPreserves hash witness left right width firstOutput duplicateOutput
        leftBound rightBound).mp ⟨firstHolds, copied⟩
    exact ⟨leftRange, rightRange, firstHolds, duplicateHolds⟩
  · rintro ⟨leftRange, rightRange, firstHolds, duplicateHolds⟩
    have leftBound : (left.read witness).val < 2 ^ width := by
      simpa [Instruction.Holds] using leftRange
    have rightBound : (right.read witness).val < 2 ^ width := by
      simpa [Instruction.Holds] using rightRange
    obtain ⟨firstHolds, copied⟩ :=
      (lessThanCopyPreserves hash witness left right width firstOutput duplicateOutput
        leftBound rightBound).mpr ⟨firstHolds, duplicateHolds⟩
    exact ⟨leftRange, rightRange, firstHolds, copied⟩

/-- The accepted relation represents a reference Copy as equality between its
source and destination operands. This is the same assignment condition used by
the optimizer's Copy model, up to equality symmetry. -/
theorem equalReferenceCopy_iff_copyHolds (hash : Hash) (witness : Assignment)
    (source destination : String) :
    Instruction.Holds hash witness
        (.equal (.reference source) (.reference destination)) ↔
      copyHolds witness source destination := by
  change witness source = witness destination ↔ witness destination = witness source
  exact ⟨Eq.symm, Eq.symm⟩

/-- Under the exact operand bit bounds retained before comparison reuse, a
decoded reference-equality Copy has the same relation as the duplicate
comparison it replaces. -/
theorem lessThanEqualCopyPreserves (hash : Hash) (witness : Assignment)
    (left right : Operand) (width : Nat) (firstOutput duplicateOutput : String)
    (leftBound : (left.read witness).val < 2 ^ width)
    (rightBound : (right.read witness).val < 2 ^ width) :
    (Instruction.Holds hash witness
        (.lessThan left right width firstOutput) ∧
      Instruction.Holds hash witness
        (.equal (.reference firstOutput) (.reference duplicateOutput))) ↔
      (Instruction.Holds hash witness
        (.lessThan left right width firstOutput) ∧
      Instruction.Holds hash witness
        (.lessThan left right width duplicateOutput)) := by
  constructor
  · rintro ⟨firstHolds, equalHolds⟩
    have copied : copyHolds witness firstOutput duplicateOutput :=
      (equalReferenceCopy_iff_copyHolds hash witness firstOutput duplicateOutput).mp equalHolds
    exact (lessThanCopyPreserves hash witness left right width firstOutput duplicateOutput
      leftBound rightBound).mp ⟨firstHolds, copied⟩
  · rintro ⟨firstHolds, duplicateHolds⟩
    obtain ⟨firstHolds, copied⟩ :=
      (lessThanCopyPreserves hash witness left right width firstOutput duplicateOutput
        leftBound rightBound).mpr ⟨firstHolds, duplicateHolds⟩
    exact ⟨firstHolds,
      (equalReferenceCopy_iff_copyHolds hash witness firstOutput duplicateOutput).mpr copied⟩

/-- Connect the actual two-item comparison fold to the decoded scalar
relation under the operand range constraints. The Copy contributes equality
between the destination and the retained result. -/
theorem reuseComparisons_pair_bridge_with_ranges (hash : Hash) (witness : Assignment)
    (earlier later : Json) (leftKey rightKey : String) (width : Nat)
    (firstOutput duplicateOutput : String) (left right : Operand)
    (earlierKey : comparison? earlier = some ((leftKey, rightKey, width), firstOutput))
    (laterKey : comparison? later = some ((leftKey, rightKey, width), duplicateOutput))
    (earlierDecoded : decodeInstruction earlier =
      .ok (.lessThan left right width firstOutput))
    (laterDecoded : decodeInstruction later =
      .ok (.lessThan left right width duplicateOutput))
    (leftRange : Instruction.Holds hash witness (.bits left width))
    (rightRange : Instruction.Holds hash witness (.bits right width)) :
    reuseComparisons #[earlier, later] =
        #[earlier, comparisonCopyJson firstOutput duplicateOutput] ∧
      (match decodeInstruction earlier, decodeInstruction later with
      | .ok first, .ok second =>
          (first.Holds hash witness ∧ copyHolds witness firstOutput duplicateOutput) ↔
          (first.Holds hash witness ∧ second.Holds hash witness)
      | _, _ => False) := by
  refine ⟨reuseComparisons_pair earlier later (leftKey, rightKey, width)
    firstOutput duplicateOutput earlierKey laterKey, ?_⟩
  rw [earlierDecoded, laterDecoded]
  exact lessThanCopyPreserves hash witness left right width firstOutput duplicateOutput
    (by simpa [Instruction.Holds] using leftRange)
    (by simpa [Instruction.Holds] using rightRange)

/-- Derive the shared typed operands and width from successful JSON decoding
and equal optimizer keys, then apply the range-constrained pair bridge. -/
theorem reuseComparisons_pair_bridge_from_decodes (hash : Hash) (witness : Assignment)
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
    (leftRange : Instruction.Holds hash witness (.bits left₁ width))
    (rightRange : Instruction.Holds hash witness (.bits right₁ width)) :
    reuseComparisons #[earlier, later] =
        #[earlier, comparisonCopyJson firstOutput duplicateOutput] ∧
      (match decodeInstruction earlier, decodeInstruction later with
      | .ok first, .ok second =>
          (first.Holds hash witness ∧ copyHolds witness firstOutput duplicateOutput) ↔
          (first.Holds hash witness ∧ second.Holds hash witness)
      | _, _ => False) := by
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
  have bridge := reuseComparisons_pair_bridge_with_ranges hash witness
    earlier later leftKey rightKey width firstOutput duplicateOutput left₁ right₁
    earlierKey laterKey earlierCanonical laterCanonical leftRange rightRange
  simpa only [earlierCanonical, laterCanonical] using bridge

/-- The decoded two-item optimization relation using the accepted native
`equal` form of Copy. The required bounds are exactly the preceding bit-range
constraints on both comparison operands. -/
theorem reuseComparisons_pair_bridge_from_decodes_equal (hash : Hash) (witness : Assignment)
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
    (leftRange : Instruction.Holds hash witness (.bits left₁ width))
    (rightRange : Instruction.Holds hash witness (.bits right₁ width)) :
    reuseComparisons #[earlier, later] =
        #[earlier, comparisonCopyJson firstOutput duplicateOutput] ∧
      (match decodeInstruction earlier, decodeInstruction later with
      | .ok first, .ok second =>
          (first.Holds hash witness ∧
            Instruction.Holds hash witness
              (.equal (.reference firstOutput) (.reference duplicateOutput))) ↔
          (first.Holds hash witness ∧ second.Holds hash witness)
      | _, _ => False) := by
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
  refine ⟨reuseComparisons_pair earlier later (leftKey, rightKey, width)
    firstOutput duplicateOutput earlierKey laterKey, ?_⟩
  rw [earlierCanonical, laterCanonical]
  exact lessThanEqualCopyPreserves hash witness left₁ right₁ width
    firstOutput duplicateOutput
    (by simpa [Instruction.Holds] using leftRange)
    (by simpa [Instruction.Holds] using rightRange)

/-- The actual JSON range pass preserves decode success, ordered non-range
instructions and field-level satisfaction for every assignment accepted or
rejected by the existing scalar relation model. -/
theorem preserves_decoded (instructions : Array Json) (original : List Instruction)
    (decoded : instructions.toList.mapM decodeInstruction = .ok original) :
    ∃ optimized,
      (run instructions).toList.mapM decodeInstruction = .ok optimized ∧
      optimized.filter nonRange = original.filter nonRange ∧
      ∀ hash witness,
        (∀ instruction ∈ optimized, instruction.Holds hash witness) ↔
        (∀ instruction ∈ original, instruction.Holds hash witness) := by
  obtain ⟨originalForm, admitted⟩ := (decode_list _ _).mp decoded
  subst original
  refine ⟨_, (decode_list _ _).mpr ⟨rfl, fun item member => admitted item ((sublist _).subset member)⟩, ?_, ?_⟩
  · let observe := fun item => if nonRange (decodedItem item) then [decodedItem item] else []
    have observed := preserves_observations instructions observe (by
      intro item member name width key
      simp [observe, key_instruction item _ name width key (admitted item member), nonRange])
    simpa only [filter_map, observe] using observed
  · intro hash witness
    simp only [List.forall_mem_map]
    exact preserves_satisfaction _ _ (fun name => (witness name).val) (by
      intro item member name width key
      rw [key_instruction item _ name width key (admitted item member)]
      rfl)

/-- Removing repeated direct reference assertions preserves decoded non-assert
order and the satisfying witnesses for every successful input decode. -/
theorem removeDuplicateAssertions_preserves_decoded (instructions : Array Json)
    (original : List Instruction)
    (decoded : instructions.toList.mapM decodeInstruction = .ok original) :
    ∃ optimized,
      (removeDuplicateAssertions instructions).toList.mapM decodeInstruction = .ok optimized ∧
      optimized.filter nonAssert = original.filter nonAssert ∧
      ∀ hash witness,
        (∀ instruction ∈ optimized, instruction.Holds hash witness) ↔
        (∀ instruction ∈ original, instruction.Holds hash witness) := by
  obtain ⟨originalForm, admitted⟩ := (decode_list _ _).mp decoded
  subst original
  let reduced := removeDuplicateAssertions instructions
  let optimized := reduced.toList.map decodedItem
  have reducedDecoded : reduced.toList.mapM decodeInstruction = .ok optimized :=
    (decode_list _ _).mpr ⟨rfl, fun item member =>
      admitted item ((removeDuplicateAssertions_sublist instructions).subset member)⟩
  let observe := fun item =>
    if nonAssert (decodedItem item) then [decodedItem item] else []
  have observed := removeDuplicateAssertions_preserves_observation instructions observe (by
    intro item member operand recognized
    have shape := decoded_assertionOperand? item operand (decodedItem item) recognized
      (admitted item member)
    simp [observe, shape, nonAssert])
  let observeUnrecognized := fun item =>
    if (assertionOperand? item).isNone then [item] else []
  have rawObserved := removeDuplicateAssertions_preserves_observation instructions
      observeUnrecognized (by
        intro item member operand recognized
        simp [observeUnrecognized, recognized])
  refine ⟨optimized, reducedDecoded, ?_, ?_⟩
  · let observe := fun item =>
      if nonAssert (decodedItem item) then [decodedItem item] else []
    simpa only [filter_decoded, observe, optimized, reduced] using observed
  · intro hash witness
    constructor
    · intro holds instruction member
      by_cases retained : nonAssert instruction = true
      · have filtered : instruction ∈
          (instructions.toList.map decodedItem).filter nonAssert :=
            List.mem_filter.mpr ⟨member, retained⟩
        have projection : optimized.filter nonAssert =
            (instructions.toList.map decodedItem).filter nonAssert := by
          simpa only [filter_decoded, observe, optimized, reduced] using observed
        have filtered' : instruction ∈ optimized.filter nonAssert := by
          rw [projection]
          exact filtered
        exact holds instruction (List.mem_filter.mp filtered').1
      · cases instruction with
        | assert condition =>
          have source := List.mem_map.mp member
          obtain ⟨item, sourceMember, decodedItemEq⟩ := source
          cases recognized : assertionOperand? item with
          | none =>
            have observedSource : item ∈ instructions.toList.flatMap observeUnrecognized := by
              apply List.mem_flatMap.mpr
              exact ⟨item, sourceMember, by simp [observeUnrecognized, recognized]⟩
            have observedReduced : item ∈ reduced.toList.flatMap observeUnrecognized := by
              rw [rawObserved]
              exact observedSource
            obtain ⟨retainedItem, retainedMember, itemIn⟩ :=
              List.mem_flatMap.mp observedReduced
            have sameItem : retainedItem = item := by
              cases retainedRecognition : assertionOperand? retainedItem with
              | none =>
                have eq : item = retainedItem := by
                  simpa [observeUnrecognized, retainedRecognition] using itemIn
                exact eq.symm
              | some other => simp [observeUnrecognized, retainedRecognition] at itemIn
            have optimizedMember : decodedItem item ∈ optimized := by
              change decodedItem item ∈ reduced.toList.map decodedItem
              rw [← sameItem]
              exact List.mem_map.mpr ⟨retainedItem, retainedMember, rfl⟩
            rw [← decodedItemEq]
            exact holds (decodedItem item) optimizedMember
          | some operand =>
            have shape := decoded_assertionOperand? item operand (decodedItem item)
              recognized (admitted item sourceMember)
            have conditionEq : condition = .reference operand := by
              have eq : Instruction.assert condition = Instruction.assert (.reference operand) :=
                decodedItemEq.symm.trans shape
              injection eq
            cases condition with
            | immediate value => simp at conditionEq
            | reference name =>
              have sameOperand : name = operand := by injection conditionEq
              subst name
              obtain ⟨retainedItem, retainedMember, retainedShape⟩ :=
                removeDuplicateAssertions_retains_operand instructions item sourceMember recognized
              have retainedDecoded :=
                admitted retainedItem ((removeDuplicateAssertions_sublist instructions).subset retainedMember)
              have retainedInstruction : decodedItem retainedItem = .assert (.reference operand) :=
                decoded_assertionOperand? retainedItem operand (decodedItem retainedItem)
                  retainedShape retainedDecoded
              have optimizedMember : decodedItem retainedItem ∈ optimized := by
                change decodedItem retainedItem ∈ reduced.toList.map decodedItem
                exact List.mem_map.mpr ⟨retainedItem, retainedMember, rfl⟩
              apply holds (.assert (.reference operand))
              rw [← retainedInstruction]
              exact optimizedMember
        | _ => simp [nonAssert] at retained
    · intro holds instruction member
      obtain ⟨item, reducedMember, decodedEq⟩ := List.mem_map.mp member
      have sourceMember := (removeDuplicateAssertions_sublist instructions).subset reducedMember
      have originalMember : decodedItem item ∈ instructions.toList.map decodedItem :=
        List.mem_map.mpr ⟨item, sourceMember, rfl⟩
      rw [← decodedEq]
      exact holds (decodedItem item) originalMember

/-- Keep bit checks and the host-observable instructions in their original order. -/
def stableOutsideComparisons : Instruction → Bool
  | .lessThan .. | .equal .. => false
  | _ => true

private theorem comparison_filter_map (items : List Json) :
    (items.map decodedItem).filter stableOutsideComparisons =
      items.flatMap fun item => if stableOutsideComparisons (decodedItem item)
        then [decodedItem item] else [] := by
  induction items with
  | nil => rfl
  | cons item rest ih =>
    by_cases keep : stableOutsideComparisons (decodedItem item) <;> simp [keep, ih]

private theorem decodedComparisonPair (earlier later : Json)
    (leftName rightName : String) (width : Nat) (first output : String)
    (earlierKey : comparison? earlier = some ((leftName, rightName, width), first))
    (laterKey : comparison? later = some ((leftName, rightName, width), output))
    (earlierDecoded : decodeInstruction earlier = .ok (decodedItem earlier))
    (laterDecoded : decodeInstruction later = .ok (decodedItem later)) :
    ∃ left right,
      decodedItem earlier = .lessThan left right width first ∧
      decodedItem later = .lessThan left right width output ∧
      decodeInstruction (comparisonCopyJson first output) =
        .ok (.equal (.reference first) (.reference output)) := by
  obtain ⟨left, right, earlierShape, leftParsed, rightParsed, firstValid⟩ :=
    exists_comparison_decode earlier leftName rightName first width _ earlierKey earlierDecoded
  obtain ⟨laterLeft, laterRight, laterShape, laterLeftParsed, laterRightParsed, outputValid⟩ :=
    exists_comparison_decode later leftName rightName output width _ laterKey laterDecoded
  have sameLeft := Except.ok.inj (laterLeftParsed.symm.trans leftParsed)
  have sameRight := Except.ok.inj (laterRightParsed.symm.trans rightParsed)
  refine ⟨left, right, earlierShape, ?_, ?_⟩
  · simpa only [sameLeft, sameRight] using laterShape
  · exact NativeRelationJson.decodeInstruction_copyJson first output firstValid outputValid

/-- A comparison operand's range follows from a literal or a retained bit check. -/
def ComparisonOperandRange (instructions : List Instruction) (operand : Operand)
    (width : Nat) : Prop :=
  (∃ narrow ≤ width, .bits operand narrow ∈ instructions) ∨
    (∃ literal, operand = .immediate literal ∧ literal.val < 2 ^ width)

/-- Arithmetic-derived producer bounds require a separate admission proof. -/
def ComparisonBitChecks (instructions : List Instruction) : Prop :=
  ∀ left right width output, .lessThan left right width output ∈ instructions →
    ComparisonOperandRange instructions left width ∧
    ComparisonOperandRange instructions right width

private theorem ComparisonOperandRange.bound {instructions : List Instruction}
    {operand : Operand} {width : Nat} (range : ComparisonOperandRange instructions operand width)
    (hash : Hash) (witness : Assignment)
    (bitRanges : ∀ operand width, .bits operand width ∈ instructions →
      Instruction.Holds hash witness (.bits operand width)) :
    (operand.read witness).val < 2 ^ width := by
  rcases range with ⟨narrow, smaller, member⟩ | ⟨literal, rfl, bounded⟩
  · exact Nat.lt_of_lt_of_le (bitRanges operand narrow member)
      (Nat.pow_le_pow_right (by decide) smaller)
  · exact bounded

/-- Apply the exact Copy relation throughout the real compiler fold. The range
hypothesis refers to constraints present in the decoded source relation. -/
theorem reuseComparisons_preserves_decoded (source : Array Json) (original : List Instruction)
    (decoded : source.toList.mapM decodeInstruction = .ok original)
    (ranges : ComparisonBitChecks original) :
    ∃ optimized,
      (reuseComparisons source).toList.mapM decodeInstruction = .ok optimized ∧
      optimized.filter stableOutsideComparisons = original.filter stableOutsideComparisons ∧
      ∀ hash witness,
        (∀ instruction ∈ optimized, instruction.Holds hash witness) ↔
        (∀ instruction ∈ original, instruction.Holds hash witness) := by
  obtain ⟨originalForm, admitted⟩ := (decode_list _ _).mp decoded
  let reduced := reuseComparisons source
  let optimized := reduced.toList.map decodedItem
  have pairs : ∀ earlier ∈ source.toList, ∀ later ∈ source.toList,
      ∀ key first output,
      comparison? earlier = some (key, first) → comparison? later = some (key, output) →
      ∃ left right,
        decodedItem earlier = .lessThan left right key.2.2 first ∧
        decodedItem later = .lessThan left right key.2.2 output ∧
        decodeInstruction (comparisonCopyJson first output) =
          .ok (.equal (.reference first) (.reference output)) := by
    intro earlier earlierMember later laterMember key first output earlierKey laterKey
    rcases key with ⟨leftName, rightName, width⟩
    exact decodedComparisonPair earlier later leftName rightName width first output earlierKey
      laterKey (admitted earlier earlierMember) (admitted later laterMember)
  have admittedReduced : ∀ item ∈ reduced.toList,
      decodeInstruction item = .ok (decodedItem item) := by
    apply (reuseComparisons_preserves_source_satisfaction source
      (fun item => decodeInstruction item = .ok (decodedItem item)) ?_).mpr admitted
    intro earlier earlierMember later laterMember key first output earlierKey laterKey
    obtain ⟨_, _, _, _, copied⟩ := pairs earlier earlierMember later laterMember key first output
      earlierKey laterKey
    have actual : decodeInstruction (comparisonCopyJson first output) =
        .ok (decodedItem (comparisonCopyJson first output)) := by
      simp [decodedItem, copied, Except.toOption]
    exact ⟨fun facts => ⟨facts.1, admitted later laterMember⟩,
      fun facts => ⟨facts.1, actual⟩⟩
  have stable : optimized.filter stableOutsideComparisons =
      original.filter stableOutsideComparisons := by
    rw [← originalForm, comparison_filter_map, comparison_filter_map]
    apply reuseComparisons_preserves_observations source
    intro earlier earlierMember later laterMember key first output earlierKey laterKey
    obtain ⟨_, _, _, laterShape, copied⟩ := pairs earlier earlierMember later laterMember key first output
      earlierKey laterKey
    have copyShape : decodedItem (comparisonCopyJson first output) =
        .equal (.reference first) (.reference output) := by
      simp [decodedItem, copied, Except.toOption]
    simp [laterShape, copyShape, stableOutsideComparisons]
  refine ⟨optimized, (decode_list _ _).mpr ⟨rfl, admittedReduced⟩, stable, ?_⟩
  intro hash witness
  let satisfies (instructions : List Instruction) :=
    ∀ instruction ∈ instructions, Instruction.Holds hash witness instruction
  have fold (bitRanges : ∀ operand width, .bits operand width ∈ original →
        Instruction.Holds hash witness (.bits operand width)) :
      satisfies optimized ↔ satisfies original := by
    unfold satisfies
    change (∀ instruction ∈ reduced.toList.map decodedItem, _) ↔ _
    rw [← originalForm]
    simp only [List.forall_mem_map]
    apply reuseComparisons_preserves_source_satisfaction source
    intro earlier earlierMember later laterMember key first output earlierKey laterKey
    obtain ⟨left, right, earlierShape, laterShape, copied⟩ :=
      pairs earlier earlierMember later laterMember key first output earlierKey laterKey
    have copyShape : decodedItem (comparisonCopyJson first output) =
        .equal (.reference first) (.reference output) := by
      simp [decodedItem, copied, Except.toOption]
    have earlierInOriginal : .lessThan left right key.2.2 first ∈ original := by
      rw [← earlierShape, ← originalForm]
      exact List.mem_map_of_mem earlierMember
    obtain ⟨leftRange, rightRange⟩ := ranges left right key.2.2 first earlierInOriginal
    rw [earlierShape, laterShape, copyShape]
    exact lessThanEqualCopyPreserves hash witness left right key.2.2 first output
      (leftRange.bound hash witness bitRanges) (rightRange.bound hash witness bitRanges)
  refine ⟨fun optimizedHolds => ?_, fun originalHolds => (fold fun _ _ member =>
    originalHolds _ member).mpr originalHolds⟩
  apply (fold ?_).mp optimizedHolds
  intro operand width member
  have inStable : .bits operand width ∈ original.filter stableOutsideComparisons := by
    exact List.mem_filter.mpr ⟨member, rfl⟩
  rw [← stable] at inStable
  exact optimizedHolds _ (List.mem_filter.mp inStable).1

end Noctium.Verification.RangeDedup
