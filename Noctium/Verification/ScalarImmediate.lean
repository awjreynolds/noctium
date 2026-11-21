import Noctium.Backend.Zkir
import Noctium.Verification.ScalarParserAgreement
import Noctium.Verification.ScalarTermMeaning

namespace Noctium.Verification.ScalarImmediate

open Backend Native

set_option maxRecDepth 4096

private def digits : Array Char := "0123456789abcdef".toList.toArray

/-- This finite table checks the emitter's actual indexed digit alphabet. -/
theorem digit_table : ∀ byte : Fin 256,
    Native.hexDigit digits[byte.val / 16]! = some (byte.val / 16) ∧
      Native.hexDigit digits[byte.val % 16]! = some (byte.val % 16) := by decide

def bytes (number : Nat) : Nat → List Nat
  | 0 => []
  | fuel + 1 => number % 256 :: bytes (number / 256) fuel

theorem bytes_length (number fuel : Nat) : (bytes number fuel).length = fuel := by
  induction fuel generalizing number with
  | zero => rfl
  | succ fuel ih => simp only [bytes, List.length_cons, ih]

theorem encoded_bytes (number fuel : Nat) :
    Native.hexBytes (Zkir.fieldImmediate.go number fuel).toList = some (bytes number fuel) := by
  induction fuel generalizing number with
  | zero => rfl
  | succ fuel ih =>
    have byteBound : number % 256 < 256 := Nat.mod_lt _ (by decide)
    have table := digit_table ⟨number % 256, byteBound⟩
    simp only [Zkir.fieldImmediate.go, String.toList_append, String.toList_singleton,
      List.cons_append, List.nil_append]
    change Native.hexBytes (digits[number % 256 / 16]! :: digits[number % 256 % 16]! ::
      (Zkir.fieldImmediate.go (number / 256) fuel).toList) = some (bytes number (fuel + 1))
    simp only [Native.hexBytes, table.1, table.2, ih]
    have reconstruction := Nat.mod_add_div (number % 256) 16
    change some ((number % 256 / 16 * 16 + number % 256 % 16) :: bytes (number / 256) fuel) =
      some (number % 256 :: bytes (number / 256) fuel)
    have byteValue : number % 256 / 16 * 16 + number % 256 % 16 = number % 256 := by omega
    rw [byteValue]

theorem bytes_value (number fuel : Nat) (fits : number < 256 ^ fuel) :
    Native.littleEndian (bytes number fuel) = number := by
  induction fuel generalizing number with
  | zero =>
    have numberZero : number = 0 := by simp at fits; omega
    subst number
    rfl
  | succ fuel ih =>
    have tailFits : number / 256 < 256 ^ fuel := by
      apply (Nat.div_lt_iff_lt_mul (by decide)).mpr
      simpa only [Nat.pow_succ] using fits
    simp only [bytes, Native.littleEndian, ih _ tailFits]
    exact Nat.mod_add_div number 256

theorem bytes_last (number fuel : Nat) :
    (bytes number (fuel + 1)).getLast? = some ((number / 256 ^ fuel) % 256) := by
  induction fuel generalizing number with
  | zero => simp [bytes]
  | succ fuel ih =>
    rw [bytes, bytes, List.getLast?_cons_cons]
    change (bytes (number / 256) (fuel + 1)).getLast? = _
    rw [ih, Nat.div_div_eq_div_mul]
    simp only [Nat.pow_succ, Nat.mul_comm]

theorem bytes_last_nonzero (number fuel : Nat)
    (upper : number < 256 ^ (fuel + 1)) (lower : 256 ^ fuel ≤ number) :
    (bytes number (fuel + 1)).getLast? ≠ some 0 := by
  rw [bytes_last]
  have quotientUpper : number / 256 ^ fuel < 256 := by
    apply (Nat.div_lt_iff_lt_mul (Nat.pow_pos (by decide))).mpr
    simpa only [Nat.pow_succ, Nat.mul_comm] using upper
  have quotientPositive : 0 < number / 256 ^ fuel :=
    Nat.div_pos lower (Nat.pow_pos (by decide))
  rw [Nat.mod_eq_of_lt quotientUpper]
  intro equal
  have zero := Option.some.inj equal
  omega

def byteCount (number : Nat) : Nat := number.log2 / 8 + 1

theorem pow256 (exponent : Nat) : 256 ^ exponent = 2 ^ (8 * exponent) := by
  calc
    256 ^ exponent = (2 ^ 8) ^ exponent := rfl
    _ = 2 ^ (8 * exponent) := (Nat.pow_mul 2 8 exponent).symm

theorem byteCount_fits (number : Nat) : number < 256 ^ byteCount number := by
  rw [pow256]
  apply Nat.lt_of_lt_of_le (Nat.lt_log2_self (n := number))
  apply Nat.pow_le_pow_right (by decide)
  unfold byteCount
  omega

theorem byteCount_minimal (number : Nat) (positive : number ≠ 0) :
    256 ^ (number.log2 / 8) ≤ number := by
  rw [pow256]
  exact Nat.le_trans (Nat.pow_le_pow_right (by decide) (Nat.mul_div_le number.log2 8))
    (Nat.log2_self_le positive)

theorem byteCount_width (number : Nat) (canonical : number < Field.modulus) :
    byteCount number ≤ 32 := by
  by_cases zero : number = 0
  · subst number
    decide
  · have fieldWidth : Field.modulus < 2 ^ 256 := by decide
    have logarithm : number.log2 < 256 :=
      (Nat.log2_lt zero).mpr (Nat.lt_trans canonical fieldWidth)
    unfold byteCount
    omega

theorem encoded_prefix (number : Nat) : (Zkir.fieldImmediate number).startsWith "0x" = true := by
  apply String.startsWith_string_iff.mpr
  rw [Zkir.fieldImmediate, String.toList_append]
  exact List.prefix_append _ _

theorem encoded_drop_prefix (number : Nat) :
    (Zkir.fieldImmediate number).toList.drop 2 =
      (Zkir.fieldImmediate.go number (byteCount number)).toList := by
  simp only [Zkir.fieldImmediate, String.toList_append]
  have prefixChars : "0x".toList = ['0', 'x'] := by decide
  rw [prefixChars]
  rfl

/-- The actual lowerer's immediate spelling denotes the original canonical
number. Parser agreement alone would not establish this encoding property. -/
theorem fieldImmediate_exact (number : Nat) (canonical : number < Field.modulus) :
    Native.immediate (Zkir.fieldImmediate number) = .ok number := by
  apply (ScalarParserAgreement.native_success (Zkir.fieldImmediate number) number).mpr
  refine ⟨encoded_prefix number, bytes number (byteCount number), ?_, ?_, ?_, ?_, ?_⟩
  · rw [encoded_drop_prefix]
    exact encoded_bytes number (byteCount number)
  · apply Bool.and_eq_true_iff.mpr
    constructor
    · simp only [byteCount, bytes, List.isEmpty_cons, Bool.not_false]
    · exact decide_eq_true (by rw [bytes_length]; exact byteCount_width number canonical)
  · by_cases single : byteCount number = 1
    · simp only [bytes_length, single, beq_self_eq_true, Bool.true_or]
    · have positive : number ≠ 0 := by
        intro zero
        subst number
        exact single (by decide)
      have nonzero := bytes_last_nonzero number (number.log2 / 8)
        (byteCount_fits number) (byteCount_minimal number positive)
      apply Bool.or_eq_true_iff.mpr
      exact Or.inr (by simpa only [bne_iff_ne, byteCount] using nonzero)
  · rw [bytes_value number (byteCount number) (byteCount_fits number)]
    exact canonical
  · exact bytes_value number (byteCount number) (byteCount_fits number)

theorem bytes32Low31FieldImmediate_exact (values : List Nat)
    (width : values.length = 32)
    (byteBound : ∀ value ∈ values, value < 256) :
    Native.immediate (Zkir.fieldImmediate (Native.littleEndian (values.take 31))) =
      .ok (Native.littleEndian (values.take 31)) := by
  apply fieldImmediate_exact
  exact ScalarTermMeaning.littleEndian_bytes32Low31_lt_modulus values width byteBound

theorem decode_fieldImmediate_exact (number : Nat) (canonical : number < Field.modulus) :
    NativeRelationJson.decodeImmediate (Zkir.fieldImmediate number) = .ok number :=
  (ScalarParserAgreement.producer_immediate_success _ number).mp (fieldImmediate_exact number canonical)

theorem operand_fieldImmediate_exact (state : Native.State) (number : Nat)
    (canonical : number < Field.modulus) :
    Native.operand state (Zkir.fieldImmediate number) =
      .ok {term := .constant number, maximum := number} := by
  unfold Native.operand
  rw [encoded_prefix]
  simp only [↓reduceIte, fieldImmediate_exact number canonical]
  rfl

theorem decodeOperand_fieldImmediate_exact (number : Nat) (canonical : number < Field.modulus) :
    NativeRelationJson.decodeOperand (Lean.toJson (Zkir.fieldImmediate number)) =
      .ok (.immediate (NativeRelation.scalar number)) := by
  unfold NativeRelationJson.decodeOperand
  change (do
    let text ← (Lean.Json.str (Zkir.fieldImmediate number)).getStr?
    if text.startsWith "0x" then
      return NativeRelation.Operand.immediate (NativeRelation.scalar (← NativeRelationJson.decodeImmediate text))
    NativeRelationJson.ensure (NativeRelationJson.validIdentifier text) "invalid native SSA reference"
    return NativeRelation.Operand.reference text) = _
  simp only [Lean.Json.getStr?]
  change (if (Zkir.fieldImmediate number).startsWith "0x" then
    (do return NativeRelation.Operand.immediate (NativeRelation.scalar (← NativeRelationJson.decodeImmediate (Zkir.fieldImmediate number))))
    else _) = _
  rw [encoded_prefix]
  simp only [↓reduceIte, decode_fieldImmediate_exact number canonical]
  rfl

end Noctium.Verification.ScalarImmediate
