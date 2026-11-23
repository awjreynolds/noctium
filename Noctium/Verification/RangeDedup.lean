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

/-- Native `copy` carries the witness value of its source SSA name to its
destination. The typed instruction relation records this effect as equality. -/
def copyHolds (witness : Assignment) (source destination : String) : Prop :=
  witness destination = witness source

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

end Noctium.Verification.RangeDedup
