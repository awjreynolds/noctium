import Noctium.Verification.ScalarImmediate

namespace Noctium.Verification.ScalarInstructionEncoding

open Lean Backend NativeRelation

/-- Operand spellings follow from a canonical emitted literal or a checked SSA
name. This relation assumes no decoder result or native semantic conclusion. -/
inductive OperandEncoding : String → Operand → Prop where
  | immediate (number : Nat) (canonical : number < Field.modulus) :
      OperandEncoding (Zkir.fieldImmediate number) (.immediate (scalar number))
  | reference (name : String) (valid : NativeRelationJson.validIdentifier name = true) :
      OperandEncoding name (.reference name)

theorem OperandEncoding.decode {text : String} {value : Operand}
    (encoding : OperandEncoding text value) :
    NativeRelationJson.decodeOperand (toJson text) = .ok value := by
  cases encoding with
  | immediate number canonical =>
    exact ScalarImmediate.decodeOperand_fieldImmediate_exact number canonical
  | reference name valid =>
    have starts : text.startsWith "%" = true :=
      (Bool.and_eq_true_iff.mp (Bool.and_eq_true_iff.mp valid).1).1
    have notImmediate := NativeRelationJson.reference_not_immediate starts
    unfold NativeRelationJson.decodeOperand
    change (if text.startsWith "0x" then
      (do return Operand.immediate (scalar (← NativeRelationJson.decodeImmediate text))) else
      (do NativeRelationJson.ensure (NativeRelationJson.validIdentifier text) "invalid native SSA reference"
          return Operand.reference text)) = _
    rw [notImmediate]
    simp only [Bool.false_eq_true, ↓reduceIte, valid, NativeRelationJson.ensure]
    rfl

def OperandsEncoding : List String → List Operand → Prop
  | [], [] => True
  | text :: texts, value :: values => OperandEncoding text value ∧ OperandsEncoding texts values
  | _, _ => False

theorem OperandsEncoding.decode {texts : List String} {values : List Operand}
    (encoding : OperandsEncoding texts values) :
    NativeRelationJson.decodeOperands (toJson texts) = .ok values := by
  unfold NativeRelationJson.decodeOperands
  change (do
    let values ← (Except.ok (texts.toArray.map toJson) : Except String (Array Json))
    values.toList.mapM NativeRelationJson.decodeOperand) = _
  change (texts.toArray.map toJson).toList.mapM NativeRelationJson.decodeOperand = _
  simp only [Array.toList_map, List.mapM_map, Function.comp_def]
  change texts.mapM (fun text => NativeRelationJson.decodeOperand (toJson text)) = .ok values
  induction texts generalizing values with
  | nil =>
    cases values <;> simp only [OperandsEncoding] at encoding
    rfl
  | cons text texts ih =>
    cases values with
    | nil => exact False.elim encoding
    | cons value values =>
      rcases encoding with ⟨head, tail⟩
      simp only [List.mapM_cons, head.decode, ih tail]
      rfl

theorem decode_binary_instruction_add {a b output : String} {left right : Operand}
    (aDecoded : NativeRelationJson.decodeOperand (toJson a) = .ok left) (bDecoded : NativeRelationJson.decodeOperand (toJson b) = .ok right)
    (valid : NativeRelationJson.validIdentifier output = true) :
    NativeRelationJson.decodeInstruction (Zkir.instruction "add"
      [("a", toJson a), ("b", toJson b), ("output", toJson output)]) =
      .ok (.add left right output) := by
  change (do
    let left ← NativeRelationJson.decodeOperand (toJson a)
    let right ← NativeRelationJson.decodeOperand (toJson b)
    NativeRelationJson.ensure (NativeRelationJson.validIdentifier output) "invalid native SSA definition"
    pure (Instruction.add left right output)) = _
  simp only [aDecoded, bDecoded, valid, NativeRelationJson.ensure,
    Bind.bind, Except.bind]
  rfl

theorem decode_binary_instruction_mul {a b output : String} {left right : Operand}
    (aDecoded : NativeRelationJson.decodeOperand (toJson a) = .ok left) (bDecoded : NativeRelationJson.decodeOperand (toJson b) = .ok right)
    (valid : NativeRelationJson.validIdentifier output = true) :
    NativeRelationJson.decodeInstruction (Zkir.instruction "mul"
      [("a", toJson a), ("b", toJson b), ("output", toJson output)]) =
      .ok (.mul left right output) := by
  change (do
    let left ← NativeRelationJson.decodeOperand (toJson a)
    let right ← NativeRelationJson.decodeOperand (toJson b)
    NativeRelationJson.ensure (NativeRelationJson.validIdentifier output) "invalid native SSA definition"
    pure (Instruction.mul left right output)) = _
  simp only [aDecoded, bDecoded, valid, NativeRelationJson.ensure,
    Bind.bind, Except.bind]
  rfl

theorem decode_binary_instruction_test_eq {a b output : String} {left right : Operand}
    (aDecoded : NativeRelationJson.decodeOperand (toJson a) = .ok left) (bDecoded : NativeRelationJson.decodeOperand (toJson b) = .ok right)
    (valid : NativeRelationJson.validIdentifier output = true) :
    NativeRelationJson.decodeInstruction (Zkir.instruction "test_eq"
      [("a", toJson a), ("b", toJson b), ("output", toJson output)]) =
      .ok (.testEq left right output) := by
  change (do
    let left ← NativeRelationJson.decodeOperand (toJson a)
    let right ← NativeRelationJson.decodeOperand (toJson b)
    NativeRelationJson.ensure (NativeRelationJson.validIdentifier output) "invalid native SSA definition"
    pure (Instruction.testEq left right output)) = _
  simp only [aDecoded, bDecoded, valid, NativeRelationJson.ensure,
    Bind.bind, Except.bind]
  rfl

theorem decode_unary_instruction_neg {a output : String} {value : Operand}
    (decoded : NativeRelationJson.decodeOperand (toJson a) = .ok value) (valid : NativeRelationJson.validIdentifier output = true) :
    NativeRelationJson.decodeInstruction (Zkir.instruction "neg"
      [("a", toJson a), ("output", toJson output)]) = .ok (.neg value output) := by
  change (do
    let value ← NativeRelationJson.decodeOperand (toJson a)
    NativeRelationJson.ensure (NativeRelationJson.validIdentifier output) "invalid native SSA definition"
    pure (Instruction.neg value output)) = _
  simp only [decoded, valid, NativeRelationJson.ensure, Bind.bind, Except.bind]
  rfl

theorem decode_unary_instruction_not {a output : String} {value : Operand}
    (decoded : NativeRelationJson.decodeOperand (toJson a) = .ok value) (valid : NativeRelationJson.validIdentifier output = true) :
    NativeRelationJson.decodeInstruction (Zkir.instruction "not"
      [("a", toJson a), ("output", toJson output)]) = .ok (.not value output) := by
  change (do
    let value ← NativeRelationJson.decodeOperand (toJson a)
    NativeRelationJson.ensure (NativeRelationJson.validIdentifier output) "invalid native SSA definition"
    pure (Instruction.not value output)) = _
  simp only [decoded, valid, NativeRelationJson.ensure, Bind.bind, Except.bind]
  rfl

theorem decode_select_instruction {condition a b output : String} {bit yes no : Operand}
    (conditionDecoded : NativeRelationJson.decodeOperand (toJson condition) = .ok bit)
    (aDecoded : NativeRelationJson.decodeOperand (toJson a) = .ok yes) (bDecoded : NativeRelationJson.decodeOperand (toJson b) = .ok no)
    (valid : NativeRelationJson.validIdentifier output = true) :
    NativeRelationJson.decodeInstruction (Zkir.instruction "cond_select"
      [("bit", toJson condition), ("a", toJson a), ("b", toJson b), ("output", toJson output)]) =
      .ok (.select bit yes no output) := by
  change (do
    let bit ← NativeRelationJson.decodeOperand (toJson condition)
    let yes ← NativeRelationJson.decodeOperand (toJson a)
    let no ← NativeRelationJson.decodeOperand (toJson b)
    NativeRelationJson.ensure (NativeRelationJson.validIdentifier output) "invalid native SSA definition"
    pure (Instruction.select bit yes no output)) = _
  simp only [conditionDecoded, aDecoded, bDecoded, valid,
    NativeRelationJson.ensure, Bind.bind, Except.bind]
  rfl

theorem decode_equal_instruction {a b : String} {left right : Operand}
    (aDecoded : NativeRelationJson.decodeOperand (toJson a) = .ok left) (bDecoded : NativeRelationJson.decodeOperand (toJson b) = .ok right) :
    NativeRelationJson.decodeInstruction (Zkir.instruction "constrain_eq"
      [("a", toJson a), ("b", toJson b)]) = .ok (.equal left right) := by
  change (do
    let left ← NativeRelationJson.decodeOperand (toJson a)
    let right ← NativeRelationJson.decodeOperand (toJson b)
    pure (Instruction.equal left right)) = _
  simp only [aDecoded, bDecoded, Bind.bind, Except.bind]
  rfl

theorem decode_boolean_instruction {text : String} {value : Operand} (decoded : NativeRelationJson.decodeOperand (toJson text) = .ok value) :
    NativeRelationJson.decodeInstruction (Zkir.instruction "constrain_to_boolean"
      [("val", toJson text)]) = .ok (.boolean value) := by
  change (do
    let value ← NativeRelationJson.decodeOperand (toJson text)
    pure (Instruction.boolean value)) = _
  simp only [decoded, Bind.bind, Except.bind]
  rfl

theorem decode_assert_instruction {text : String} {value : Operand} (decoded : NativeRelationJson.decodeOperand (toJson text) = .ok value) :
    NativeRelationJson.decodeInstruction (Zkir.instruction "assert"
      [("cond", toJson text)]) = .ok (.assert value) := by
  change (do
    let value ← NativeRelationJson.decodeOperand (toJson text)
    pure (Instruction.assert value)) = _
  simp only [decoded, Bind.bind, Except.bind]
  rfl

theorem decode_bits_instruction {text : String} {value : Operand} (bits : Nat)
    (decoded : NativeRelationJson.decodeOperand (toJson text) = .ok value) (positive : 0 < bits)
    (bounded : bits ≤ ScalarPolicy.maxBits) :
    NativeRelationJson.decodeInstruction (Zkir.instruction "constrain_bits"
      [("val", toJson text), ("bits", toJson bits)]) = .ok (.bits value bits) := by
  change (do
    NativeRelationJson.ensure (decide (0 < bits) && decide (bits ≤ ScalarPolicy.maxBits))
      "unsupported native bit width"
    let value ← NativeRelationJson.decodeOperand (toJson text)
    pure (Instruction.bits value bits)) = _
  simp only [positive, bounded, decide_true, Bool.true_and, NativeRelationJson.ensure,
    decoded, Bind.bind, Except.bind]
  rfl

theorem decode_lessThan_instruction {a b output : String} {left right : Operand} (bits : Nat)
    (aDecoded : NativeRelationJson.decodeOperand (toJson a) = .ok left) (bDecoded : NativeRelationJson.decodeOperand (toJson b) = .ok right)
    (valid : NativeRelationJson.validIdentifier output = true)
    (positive : 0 < bits) (bounded : bits ≤ ScalarPolicy.maxBits) :
    NativeRelationJson.decodeInstruction (Zkir.instruction "less_than"
      [("a", toJson a), ("b", toJson b), ("bits", toJson bits), ("output", toJson output)]) =
      .ok (.lessThan left right bits output) := by
  change (do
    NativeRelationJson.ensure (decide (0 < bits) && decide (bits ≤ ScalarPolicy.maxBits))
      "unsupported native bit width"
    let left ← NativeRelationJson.decodeOperand (toJson a)
    let right ← NativeRelationJson.decodeOperand (toJson b)
    NativeRelationJson.ensure (NativeRelationJson.validIdentifier output) "invalid native SSA definition"
    pure (Instruction.lessThan left right bits output)) = _
  simp only [positive, bounded, decide_true, Bool.true_and, NativeRelationJson.ensure,
    aDecoded, bDecoded, valid, Bind.bind, Except.bind]
  rfl

theorem decode_hash_instruction {texts : List String} {values : List Operand} {output : String}
    (decoded : NativeRelationJson.decodeOperands (toJson texts) = .ok values) (valid : NativeRelationJson.validIdentifier output = true) :
    NativeRelationJson.decodeInstruction (Zkir.instruction "transient_hash"
      [("inputs", toJson texts), ("output", toJson output)]) = .ok (.hash values output) := by
  change (do
    let values ← NativeRelationJson.decodeOperands (toJson texts)
    NativeRelationJson.ensure (NativeRelationJson.validIdentifier output) "invalid native SSA definition"
    pure (Instruction.hash values output)) = _
  simp only [decoded, valid, NativeRelationJson.ensure, Bind.bind, Except.bind]
  rfl

theorem decode_output_instruction {texts : List String} {values : List Operand}
    (decoded : NativeRelationJson.decodeOperands (toJson texts) = .ok values) :
    NativeRelationJson.decodeInstruction (Zkir.instruction "output"
      [("vals", toJson texts)]) = .ok (.output values) := by
  change (do
    let values ← NativeRelationJson.decodeOperands (toJson texts)
    pure (Instruction.output values)) = _
  simp only [decoded, Bind.bind, Except.bind]
  rfl

theorem encoded_zero : OperandEncoding "0x00" (.immediate zero) := by
  have encoded := OperandEncoding.immediate 0 (by decide)
  have spelling : Zkir.fieldImmediate 0 = "0x00" := by decide
  simpa only [spelling, show scalar 0 = zero from by decide] using encoded

theorem encoded_one : OperandEncoding "0x01" (.immediate one) := by
  have encoded := OperandEncoding.immediate 1 (by decide)
  have spelling : Zkir.fieldImmediate 1 = "0x01" := by decide
  simpa only [spelling, show scalar 1 = one from by decide] using encoded

theorem decode_impact_instruction {texts : List String} {values : List Operand}
    (decoded : NativeRelationJson.decodeOperands (toJson texts) = .ok values) :
    NativeRelationJson.decodeInstruction (Zkir.instruction "impact"
      [("guard", toJson ("0x01" : String)), ("inputs", toJson texts)]) =
      .ok (.impact (.immediate one) values) := by
  change (do
    let guard ← NativeRelationJson.decodeOperand (toJson ("0x01" : String))
    match guard with
    | .immediate active => do
      NativeRelationJson.ensure (decide (active = one)) "only literal-one always-active Impact is supported"
      let values ← NativeRelationJson.decodeOperands (toJson texts)
      pure (Instruction.impact guard values)
    | .reference _ => do
      throw "only literal-one always-active Impact is supported"
      let values ← NativeRelationJson.decodeOperands (toJson texts)
      pure (Instruction.impact guard values)) = _
  rw [encoded_one.decode]
  change (do
    let values ← NativeRelationJson.decodeOperands (toJson texts)
    pure (Instruction.impact (.immediate one) values)) = _
  simp only [decoded, Bind.bind, Except.bind]
  rfl

theorem decode_publicInput (output : String) (valid : NativeRelationJson.validIdentifier output = true) :
    NativeRelationJson.decodeInstruction (Zkir.instruction "public_input"
      [("guard", Json.null), ("type", toJson ("Scalar<BLS12-381>" : String)), ("output", toJson output)]) =
      .ok (.input .public output) := by
  change (do
    NativeRelationJson.ensure (NativeRelationJson.validIdentifier output) "invalid native SSA definition"
    pure (Instruction.input .public output)) = _
  rw [valid]
  rfl

theorem decode_privateInput (output : String) (valid : NativeRelationJson.validIdentifier output = true) :
    NativeRelationJson.decodeInstruction (Zkir.instruction "private_input"
      [("guard", Json.null), ("type", toJson ("Scalar<BLS12-381>" : String)), ("output", toJson output)]) =
      .ok (.input .private output) := by
  change (do
    NativeRelationJson.ensure (NativeRelationJson.validIdentifier output) "invalid native SSA definition"
    pure (Instruction.input .private output)) = _
  rw [valid]
  rfl

theorem decode_input (visibility : Visibility) (output : String)
    (valid : NativeRelationJson.validIdentifier output = true) :
    NativeRelationJson.decodeInstruction (Zkir.instruction
      (if visibility == .public then "public_input" else "private_input")
      [("guard", Json.null), ("type", toJson ("Scalar<BLS12-381>" : String)), ("output", toJson output)]) =
      .ok (.input visibility output) := by
  cases visibility
  · exact decode_publicInput output valid
  · exact decode_privateInput output valid

theorem fresh_name_injective {left right : Nat} (same : s!"%v{left}" = s!"%v{right}") :
    left = right := by
  change "%v" ++ left.repr = "%v" ++ right.repr at same
  exact Nat.repr_injective ((String.append_right_inj "%v").mp same)

/-- The actual producer's instruction budget bounds the generated SSA names. -/
theorem fresh_identifier (index : Nat) (bounded : index ≤ Native.maxInstructions) :
    NativeRelationJson.validIdentifier s!"%v{index}" = true := by
  apply NativeRelationJson.generatedIdentifier_valid
  have budget : Native.maxInstructions < 10 ^ 8 := by decide
  omega

end Noctium.Verification.ScalarInstructionEncoding
