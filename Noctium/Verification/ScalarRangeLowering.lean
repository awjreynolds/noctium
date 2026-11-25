import Noctium.Verification.ScalarInstructionEncoding
import Noctium.Verification.ScalarWitness

namespace Noctium.Verification.ScalarRangeLowering

open Lean Backend NativeRelation ScalarInstructionEncoding ScalarWitness

theorem unsigned_width (maximum : Nat) (nonzero : maximum ≠ 0)
    (admitted : maximum ≤ ScalarPolicy.maxUint) :
    0 < maximum.log2 + 1 ∧ maximum.log2 + 1 ≤ ScalarPolicy.maxBits ∧
      maximum < 2 ^ (maximum.log2 + 1) := by
  have positive : 0 < 2 ^ ScalarPolicy.maxBits := Nat.pow_pos (by decide)
  have bounded : maximum < 2 ^ ScalarPolicy.maxBits := by
    unfold ScalarPolicy.maxUint at admitted
    omega
  have logarithm := (Nat.log2_lt nonzero).mpr bounded
  exact ⟨by omega, by omega, Nat.lt_log2_self⟩

theorem threshold_canonical (maximum : Nat) (admitted : maximum ≤ ScalarPolicy.maxUint) :
    maximum + 1 < Field.modulus := by
  have cap : ScalarPolicy.maxUint + 1 < Field.modulus := by decide
  omega

theorem threshold_fits (maximum : Nat)
    (nonpower : maximum + 1 ≠ 2 ^ (maximum.log2 + 1)) :
    maximum + 1 < 2 ^ (maximum.log2 + 1) := by
  have upper := Nat.lt_log2_self (n := maximum)
  omega

theorem zero_run (state : Zkir.LowerState) (text : String) :
    (Zkir.constrainUnsigned 0 text).run state =
      ((), {state with instructions := (state.instructions.push
        (Zkir.instruction "constrain_eq" [("a", toJson text), ("b", toJson ("0x00" : String))]))}) := by
  simp [Zkir.constrainUnsigned, Zkir.emit]
  rfl

theorem power_run (state : Zkir.LowerState) (maximum : Nat) (text : String)
    (nonzero : maximum ≠ 0) (power : maximum + 1 = 2 ^ (maximum.log2 + 1)) :
    (Zkir.constrainUnsigned maximum text).run state =
      ((), {state with instructions := (state.instructions.push
        (Zkir.instruction "constrain_bits" [("val", toJson text), ("bits", toJson (maximum.log2 + 1))]))}) := by
  simp [Zkir.constrainUnsigned, nonzero, power, Zkir.emit]
  rfl

theorem nonpower_run (state : Zkir.LowerState) (maximum : Nat) (text : String)
    (nonzero : maximum ≠ 0) (nonpower : maximum + 1 ≠ 2 ^ (maximum.log2 + 1)) :
    (Zkir.constrainUnsigned maximum text).run state =
      ((), {state with
        next := state.next + 1
        instructions := ((state.instructions.push
          (Zkir.instruction "constrain_bits" [("val", toJson text), ("bits", toJson (maximum.log2 + 1))])).push
          (Zkir.instruction "less_than" [("a", toJson text), ("b", toJson (Zkir.fieldImmediate (maximum + 1))),
            ("bits", toJson (maximum.log2 + 1)), ("output", toJson s!"%v{state.next}")])).push
          (Zkir.instruction "assert" [("cond", toJson s!"%v{state.next}")])}) := by
  simp [Zkir.constrainUnsigned, nonzero, nonpower, Zkir.emit, Zkir.fresh]
  rfl

theorem zero_decode (state : Zkir.LowerState) (text : String) (value : Operand)
    (prior : List Instruction)
    (operand : NativeRelationJson.decodeOperand (toJson text) = .ok value)
    (priorDecoded : state.instructions.toList.mapM NativeRelationJson.decodeInstruction = .ok prior) :
    ((Zkir.constrainUnsigned 0 text).run state).2.instructions.toList.mapM
      NativeRelationJson.decodeInstruction = .ok (prior ++ [.equal value (.immediate zero)]) := by
  rw [zero_run]
  simp only [Array.toList_push, List.mapM_append, priorDecoded, List.mapM_cons,
    decode_equal_instruction operand encoded_zero.decode, List.mapM_nil, Bind.bind, Except.bind]
  rfl

theorem power_decode (state : Zkir.LowerState) (maximum : Nat) (text : String) (value : Operand)
    (prior : List Instruction)
    (nonzero : maximum ≠ 0) (power : maximum + 1 = 2 ^ (maximum.log2 + 1))
    (admitted : maximum ≤ ScalarPolicy.maxUint)
    (operand : NativeRelationJson.decodeOperand (toJson text) = .ok value)
    (priorDecoded : state.instructions.toList.mapM NativeRelationJson.decodeInstruction = .ok prior) :
    ((Zkir.constrainUnsigned maximum text).run state).2.instructions.toList.mapM
      NativeRelationJson.decodeInstruction = .ok (prior ++ [.bits value (maximum.log2 + 1)]) := by
  have width := unsigned_width maximum nonzero admitted
  rw [power_run state maximum text nonzero power]
  simp only [Array.toList_push, List.mapM_append, priorDecoded, List.mapM_cons,
    decode_bits_instruction _ operand width.1 width.2.1, List.mapM_nil, Bind.bind, Except.bind]
  rfl

theorem nonpower_decode (state : Zkir.LowerState) (maximum : Nat) (text : String) (value : Operand)
    (prior : List Instruction)
    (nonzero : maximum ≠ 0) (nonpower : maximum + 1 ≠ 2 ^ (maximum.log2 + 1))
    (admitted : maximum ≤ ScalarPolicy.maxUint)
    (budget : state.next ≤ Native.maxInstructions * Native.maxVectorLength)
    (operand : NativeRelationJson.decodeOperand (toJson text) = .ok value)
    (priorDecoded : state.instructions.toList.mapM NativeRelationJson.decodeInstruction = .ok prior) :
    ((Zkir.constrainUnsigned maximum text).run state).2.instructions.toList.mapM
      NativeRelationJson.decodeInstruction = .ok (prior ++
        [.bits value (maximum.log2 + 1),
         .lessThan value (.immediate (scalar (maximum + 1))) (maximum.log2 + 1) s!"%v{state.next}",
         .assert (.reference s!"%v{state.next}")]) := by
  have width := unsigned_width maximum nonzero admitted
  have identifierLimit : Native.maxInstructions * Native.maxVectorLength < 10 ^ 8 := by decide
  have valid : NativeRelationJson.validIdentifier s!"%v{state.next}" = true := by
    apply NativeRelationJson.generatedIdentifier_valid
    omega
  have threshold := ScalarImmediate.decodeOperand_fieldImmediate_exact (maximum + 1)
    (threshold_canonical maximum admitted)
  have less := decode_lessThan_instruction _ operand threshold valid width.1 width.2.1
  have assertion := decode_assert_instruction (OperandEncoding.reference _ valid).decode
  rw [nonpower_run state maximum text nonzero nonpower]
  simp only [Array.toList_push, List.mapM_append, priorDecoded, List.mapM_cons,
    decode_bits_instruction _ operand width.1 width.2.1, less, assertion, List.mapM_nil, Bind.bind, Except.bind]
  apply congrArg Except.ok
  simp only [List.append_assoc, List.cons_append, List.nil_append]

theorem zero_holds (hash : Hash) (witness : Assignment) (value : Operand)
    (range : (value.read witness).val ≤ 0) :
    Instruction.Holds hash witness (.equal value (.immediate zero)) := by
  change value.read witness = zero
  apply Fin.ext
  change (value.read witness).val = 0
  omega

theorem bits_holds (hash : Hash) (witness : Assignment) (value : Operand) (maximum : Nat)
    (range : (value.read witness).val ≤ maximum) :
    Instruction.Holds hash witness (.bits value (maximum.log2 + 1)) :=
  Nat.lt_of_le_of_lt range Nat.lt_log2_self

theorem nonpower_holds (hash : Hash) (witness : Assignment) (value : Operand) (maximum : Nat)
    (output : String) (admitted : maximum ≤ ScalarPolicy.maxUint)
    (range : (value.read witness).val ≤ maximum) (outputOne : witness output = one) :
    ∀ (instruction : Instruction), instruction ∈ [.bits value (maximum.log2 + 1),
      .lessThan value (.immediate (scalar (maximum + 1))) (maximum.log2 + 1) output,
      .assert (.reference output)] → instruction.Holds hash witness := by
  intro instruction member
  simp only [List.mem_cons, List.not_mem_nil, or_false] at member
  rcases member with rfl | rfl | rfl
  · exact bits_holds hash witness value maximum range
  · intro _ _
    change witness output = bit (decide ((value.read witness).val < (scalar (maximum + 1)).val))
    have canonical := threshold_canonical maximum admitted
    have threshold := scalar_no_wrap (maximum + 1) canonical
    rw [outputOne, threshold]
    simp only [Nat.lt_succ_of_le range, decide_true, bit, ↓reduceIte]
  · change witness output ≠ zero
    rw [outputOne]
    exact Ne.symm zero_ne_one

/-- Extend an arbitrary satisfying prefix through the actual unsigned constraint
emitter. Only its fresh comparison result is assigned, and only when emitted. -/
theorem constrainUnsigned_complete (hash : Hash) (witness : Assignment)
    (state : Zkir.LowerState) (maximum : Nat) (text : String) (value : Operand)
    (prior : List Instruction)
    (operand : NativeRelationJson.decodeOperand (toJson text) = .ok value)
    (priorDecoded : state.instructions.toList.mapM NativeRelationJson.decodeInstruction = .ok prior)
    (priorHolds : ∀ instruction ∈ prior, instruction.Holds hash witness)
    (range : (value.read witness).val ≤ maximum)
    (admitted : maximum ≤ ScalarPolicy.maxUint)
    (budget : state.next ≤ Native.maxInstructions * Native.maxVectorLength)
    (independent : OperandIndependent s!"%v{state.next}" value)
    (priorIndependent : ∀ instruction ∈ prior, InstructionIndependent s!"%v{state.next}" instruction) :
    ∃ afterWitness : Assignment, ∃ instructions : List Instruction,
      ((Zkir.constrainUnsigned maximum text).run state).2.instructions.toList.mapM
        NativeRelationJson.decodeInstruction = .ok instructions ∧
      (∀ instruction ∈ instructions, instruction.Holds hash afterWitness) ∧
      value.read afterWitness = value.read witness ∧
      (∀ name, name ≠ s!"%v{state.next}" → afterWitness name = witness name) ∧
      afterWitness = (if maximum = 0 ∨ maximum + 1 = 2 ^ (maximum.log2 + 1)
        then witness else assign witness s!"%v{state.next}" one) := by
  by_cases isZero : maximum = 0
  · subst maximum
    refine ⟨witness, prior ++ [.equal value (.immediate zero)],
      zero_decode state text value prior operand priorDecoded, ?_, rfl, ?_, ?_⟩
    · intro instruction member
      rcases List.mem_append.mp member with old | new
      · exact priorHolds instruction old
      · rcases List.mem_singleton.mp new with rfl
        exact zero_holds hash witness value range
    · intro name _
      rfl
    · simp
  · by_cases power : maximum + 1 = 2 ^ (maximum.log2 + 1)
    · refine ⟨witness, prior ++ [.bits value (maximum.log2 + 1)],
        power_decode state maximum text value prior isZero power admitted operand priorDecoded, ?_, rfl, ?_, ?_⟩
      · intro instruction member
        rcases List.mem_append.mp member with old | new
        · exact priorHolds instruction old
        · rcases List.mem_singleton.mp new with rfl
          exact bits_holds hash witness value maximum range
      · intro name _
        rfl
      · simp only [power, or_true, ↓reduceIte]
    · let afterWitness := assign witness s!"%v{state.next}" one
      have stable : value.read afterWitness = value.read witness :=
        ScalarWitness.Operand.read_assign witness s!"%v{state.next}" one value independent
      have oldHolds : ∀ instruction ∈ prior, instruction.Holds hash afterWitness := by
        intro instruction member
        exact (ScalarWitness.Instruction.Holds.assign_frame hash witness s!"%v{state.next}" one instruction
          (priorIndependent instruction member)).mpr (priorHolds instruction member)
      have newHolds := nonpower_holds hash afterWitness value maximum s!"%v{state.next}" admitted
        (by rw [stable]; exact range) (assign_same witness s!"%v{state.next}" one)
      refine ⟨afterWitness, prior ++ [.bits value (maximum.log2 + 1),
        .lessThan value (.immediate (scalar (maximum + 1))) (maximum.log2 + 1) s!"%v{state.next}",
        .assert (.reference s!"%v{state.next}")],
        nonpower_decode state maximum text value prior isZero power admitted budget operand priorDecoded,
        ?_, stable, ?_, ?_⟩
      · intro instruction member
        rcases List.mem_append.mp member with old | new
        · exact oldHolds instruction old
        · exact newHolds instruction new
      · intro name different
        exact assign_other witness s!"%v{state.next}" name one different
      · simp only [isZero, power, false_or, ↓reduceIte]
        rfl

end Noctium.Verification.ScalarRangeLowering
