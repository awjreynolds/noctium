import Noctium.Backend.NativeExpected
import Noctium.ScalarPolicy
import Noctium.Verification.NativeRelation

namespace Noctium.Verification.ScalarTermMeaning

open Backend.Native NativeRelation

/-- Interpret the scalar fragment of a native meaning term. Byte vectors and
unknown operations have no scalar interpretation. -/
def interpret? (hash : Hash) (inputs : Assignment) : Term → Option Scalar
  | .constant value => some (scalar value)
  | .input name => some (inputs name)
  | .unary opcode value => do
    let value ← interpret? hash inputs value
    if opcode == "neg" then some (scalar (Field.modulus - value.val))
    else if opcode == "not" then some (bit (decide (value = zero)))
    else none
  | .binary opcode left right => do
    let left ← interpret? hash inputs left
    let right ← interpret? hash inputs right
    if opcode == "add" then some (scalar (left.val + right.val))
    else if opcode == "mul" then some (scalar (left.val * right.val))
    else if opcode == "test_eq" then some (bit (decide (left = right)))
    else if opcode.startsWith "less_than:" then some (bit (decide (left.val < right.val)))
    else none
  | .select condition yes no => do
    let condition ← interpret? hash inputs condition
    if condition = one then interpret? hash inputs yes
    else interpret? hash inputs no
  | .hash values => do
    let values ← values.mapM (interpret? hash inputs)
    some (hash values)
  | _ => none

/-- A term belongs to the scalar meaning domain only when evaluation succeeds. -/
def Supported (hash : Hash) (inputs : Assignment) (term : Term) : Prop :=
  ∃ value, interpret? hash inputs term = some value

/-- Scalar bounds and assertions are meaningful only when every referenced term
has a scalar interpretation. -/
def Requirements (hash : Hash) (inputs : Assignment) (normalized : Normalized) : Prop :=
  (∀ requirement ∈ normalized.bounds,
    ∃ value, interpret? hash inputs requirement.1 = some value ∧ value.val ≤ requirement.2) ∧
  (∀ term ∈ normalized.assertions, interpret? hash inputs term = some one)

/-- A normalized scalar value carries its checked scalar interpretation and all
partial-operation obligations from normalization. -/
def Represents (hash : Hash) (inputs : Assignment) (normalized : Normalized)
    (value : Scalar) : Prop :=
  Requirements hash inputs normalized ∧ interpret? hash inputs normalized.term = some value

@[simp] theorem interpret_constant (hash : Hash) (inputs : Assignment) (value : Nat) :
    interpret? hash inputs (.constant value) = some (scalar value) := by simp [interpret?]

private theorem scalar_add_mod (left right : Nat) :
    scalar ((scalar left).val + (scalar right).val) = scalar (left + right) := by
  apply Fin.ext
  change ((left % Field.modulus + right % Field.modulus) % Field.modulus) =
    ((left + right) % Field.modulus)
  exact (Nat.add_mod left right Field.modulus).symm

private theorem scalar_mul_mod (left right : Nat) :
    scalar ((scalar left).val * (scalar right).val) = scalar (left * right) := by
  apply Fin.ext
  change ((left % Field.modulus * (right % Field.modulus)) % Field.modulus) =
    ((left * right) % Field.modulus)
  exact (Nat.mul_mod left right Field.modulus).symm

/-- The raw recursive source packing term denotes the producer's little-endian
integer modulo the native field. -/
private theorem interpret_packByteTermsRaw_constants (hash : Hash) (inputs : Assignment)
    (values : List Nat) :
    interpret? hash inputs (Backend.Native.packByteTermsRaw (values.map Term.constant)) =
      some (scalar (Backend.Native.littleEndian values)) := by
  induction values with
  | nil => simp [Backend.Native.packByteTermsRaw, Backend.Native.littleEndian]
  | cons first rest ih =>
    cases rest with
    | nil => simp [Backend.Native.packByteTermsRaw, Backend.Native.littleEndian]
    | cons second rest =>
      change interpret? hash inputs
          (.binary "add" (.constant first)
            (.binary "mul" (.constant 256)
              (Backend.Native.packByteTermsRaw (List.map Term.constant (second :: rest))))) =
        some (scalar (first + 256 * Backend.Native.littleEndian (second :: rest)))
      have ih' : interpret? hash inputs
          (Backend.Native.packByteTermsRaw (Term.constant second :: List.map Term.constant rest)) =
          some (scalar (Backend.Native.littleEndian (second :: rest))) := by
        simpa only [List.map_cons] using ih
      simp [interpret?, ih', scalar_add_mod, scalar_mul_mod]

private theorem allLiteralZeroTerms_constants_iff (values : List Nat) :
    Backend.Native.allLiteralZeroTerms (values.map Term.constant) = true ↔
      ∀ value ∈ values, value = 0 := by
  induction values with
  | nil => simp [Backend.Native.allLiteralZeroTerms]
  | cons value rest ih =>
    cases value <;> simp [Backend.Native.allLiteralZeroTerms, ih]

private theorem littleEndian_eq_zero_of_all_zero (values : List Nat)
    (allZero : ∀ value ∈ values, value = 0) :
    Backend.Native.littleEndian values = 0 := by
  induction values with
  | nil => rfl
  | cons first rest ih =>
    have firstZero := allZero first (by simp)
    have restZero : ∀ value ∈ rest, value = 0 := by
      intro value member
      exact allZero value (List.Mem.tail first member)
    simp [Backend.Native.littleEndian, firstZero, ih restZero]

/-- Normalized all-zero chunks pack to zero. Other chunks retain the original
symbolic recurrence and its scalar meaning. -/
theorem interpret_packByteTerms_constants (hash : Hash) (inputs : Assignment)
    (values : List Nat) :
    interpret? hash inputs (Backend.Native.packByteTerms (values.map Term.constant)) =
      some (scalar (Backend.Native.littleEndian values)) := by
  by_cases allZero :
      Backend.Native.allLiteralZeroTerms (values.map Term.constant) = true
  · have zeroValues := (allLiteralZeroTerms_constants_iff values).mp allZero
    have endianZero := littleEndian_eq_zero_of_all_zero values zeroValues
    simp [Backend.Native.packByteTerms, allZero, endianZero]
  · have nonzero : Backend.Native.allLiteralZeroTerms (values.map Term.constant) = false := by
      cases result : Backend.Native.allLiteralZeroTerms (values.map Term.constant) with
      | false => rfl
      | true => exact False.elim (allZero result)
    simp only [Backend.Native.packByteTerms, nonzero, Bool.false_eq_true, ↓reduceIte]
    exact interpret_packByteTermsRaw_constants hash inputs values

theorem interpret_packedByteConstant_eq_terms (hash : Hash) (inputs : Assignment)
    (values : List Nat) :
    interpret? hash inputs (.constant (Backend.Native.littleEndian values)) =
      interpret? hash inputs (Backend.Native.packByteTerms (values.map Term.constant)) := by
  rw [interpret_constant, interpret_packByteTerms_constants]

/-- Bytewise little-endian packing stays below the radix for its list width. -/
theorem littleEndian_lt_pow_of_bytes (values : List Nat)
    (byteBound : ∀ value ∈ values, value < 256) :
    Backend.Native.littleEndian values < 256 ^ values.length := by
  induction values with
  | nil => simp [Backend.Native.littleEndian]
  | cons first rest ih =>
    have firstBound : first < 256 := byteBound first (by simp)
    have restBound : ∀ value ∈ rest, value < 256 := by
      intro value member
      exact byteBound value (List.Mem.tail first member)
    have restRange := ih restBound
    simp only [Backend.Native.littleEndian, List.length_cons, Nat.pow_succ]
    omega

/-- A canonical 31-byte little-endian chunk always fits the native field. -/
theorem littleEndian_31Byte_lt_modulus (values : List Nat)
    (width : values.length = 31)
    (byteBound : ∀ value ∈ values, value < 256) :
    Backend.Native.littleEndian values < Field.modulus := by
  have range := littleEndian_lt_pow_of_bytes values byteBound
  have radix : 256 ^ 31 = ScalarPolicy.maxUint + 1 := by
    decide
  have within : Backend.Native.littleEndian values ≤ ScalarPolicy.maxUint := by
    rw [width] at range
    rw [radix] at range
    omega
  exact Nat.lt_of_le_of_lt within ScalarPolicy.maxUint_lt_native

theorem littleEndian_bytes32Low31_lt_modulus (values : List Nat)
    (width : values.length = 32)
    (byteBound : ∀ value ∈ values, value < 256) :
    Backend.Native.littleEndian (values.take 31) < Field.modulus := by
  apply littleEndian_31Byte_lt_modulus
  · simp [List.length_take, width]
  · intro value member
    exact byteBound value (List.mem_of_mem_take member)

@[simp] theorem interpret_input (hash : Hash) (inputs : Assignment) (name : String) :
    interpret? hash inputs (.input name) = some (inputs name) := by simp [interpret?]

@[simp] theorem interpret_bytes (hash : Hash) (inputs : Assignment) (values : List Term) :
    interpret? hash inputs (.bytes values) = none := by simp [interpret?]

@[simp] theorem supported_add (hash : Hash) (inputs : Assignment) (left right : Term)
    (leftSupported : Supported hash inputs left) (rightSupported : Supported hash inputs right) :
    Supported hash inputs (.binary "add" left right) := by
  rcases leftSupported with ⟨leftValue, leftMeaning⟩
  rcases rightSupported with ⟨rightValue, rightMeaning⟩
  refine ⟨scalar (leftValue.val + rightValue.val), ?_⟩
  simp [interpret?, leftMeaning, rightMeaning]

theorem represents_constant (hash : Hash) (inputs : Assignment) (value : Nat) :
    Represents hash inputs {term := .constant value} (scalar value) := by
  constructor
  · simp [Requirements]
  · simp

/-- The old Native literal case uses the production normalizer and evaluator,
then discharges its result through the partial scalar relation. -/
theorem native_literal_normalization_sound (ctx : EvalContext) (hash : Hash)
    (inputs : Assignment) (aliases : AliasEnvironment) (value : Nat)
    (contextBound : value < ctx.modulus) (fieldBound : value < Field.modulus) :
    (value < Field.modulus ∧ Expr.eval ctx ([] : EvalEnv) (.native value) = .ok value) ∧
      ∃ normalized, Backend.Native.normalize aliases (.native value) = .ok normalized ∧
        Represents hash inputs normalized (scalar value) := by
  have normal : Backend.Native.normalize aliases (.native value) =
      .ok ({term := .constant value} : Normalized) := by
    simp [Backend.Native.normalize, pure, Except.pure]
  refine ⟨⟨fieldBound, ?_⟩, ⟨{term := .constant value}, normal, ?_⟩⟩
  · simp [Expr.eval, contextBound, pure, Except.pure]
  · exact represents_constant hash inputs value

theorem requirements_join (hash : Hash) (inputs : Assignment)
    (left right : Normalized) (term : Term)
    (leftRequirements : Requirements hash inputs left)
    (rightRequirements : Requirements hash inputs right) :
    Requirements hash inputs
      {term := term, bounds := left.bounds ++ right.bounds,
        assertions := left.assertions ++ right.assertions} := by
  constructor
  · intro requirement member
    rcases List.mem_append.mp member with member | member
    · exact leftRequirements.1 requirement member
    · exact rightRequirements.1 requirement member
  · intro assertion member
    rcases List.mem_append.mp member with member | member
    · exact leftRequirements.2 assertion member
    · exact rightRequirements.2 assertion member

end Noctium.Verification.ScalarTermMeaning
