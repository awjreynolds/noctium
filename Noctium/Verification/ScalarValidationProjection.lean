import Noctium.Backend.NativeProducer
import Noctium.Verification.NativeRelationJson
import Noctium.Verification.ScalarParserAgreement
import Noctium.Verification.ScalarNormalization

namespace Noctium.Verification.ScalarValidationProjection

open Lean Backend.Native NativeRelation ScalarNormalization

private theorem bind_ok {α β : Type} {value : Except String α} {next : α → Except String β}
    {result : β} : (value >>= next) = .ok result ↔
      ∃ found, value = .ok found ∧ next found = .ok result := by
  cases value <;> simp [Bind.bind, Except.bind]

/-- Native producer facts whose values have a scalar projection. Bytes,
Jubjub values, and foreign values stay outside this type. -/
inductive FactScalarType : NativeValueType → Prop where
  | native : FactScalarType .native
  | bool : FactScalarType .bool

/-- Explicit evidence that a fact's term denotes the assigned field value. -/
structure ScalarProjection (hash : Hash) (inputs witness : Assignment)
    (fact : Fact) (value : Scalar) : Prop where
  term : interpret hash inputs fact.term = some value
  bound : value.val ≤ fact.maximum
  comparison : ∀ name exclusive,
    fact.assertedLessThan = some (name, exclusive) → value ≠ zero →
      (witness name).val < exclusive

/-- State invariants carry scalar support only for facts whose producer type
admits a field projection. Other native facts impose no scalar interpretation. -/
def StateScalarProjection (hash : Hash) (inputs witness : Assignment) (state : State) : Prop :=
  ∀ identifier fact, (identifier, fact) ∈ state.definitions →
    FactScalarType fact.valueType → ScalarProjection hash inputs witness fact (witness identifier)

private theorem scalar_le (number : Nat) : (scalar number).val ≤ number := Nat.mod_le _ _

private theorem lookup_member {α β : Type} [BEq α] [LawfulBEq α]
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

/-- Convert the producer's checked native type test into scalar support. -/
theorem scalarType_of_nativeType {fact : Fact}
    (native : (fact.valueType == NativeValueType.native) = true) :
    FactScalarType fact.valueType := by
  cases valueType : fact.valueType with
  | native => exact .native
  | bool => have unequal : (NativeValueType.bool == NativeValueType.native) = false := by decide
            simp [valueType, unequal] at native
  | byte => have unequal : (NativeValueType.byte == NativeValueType.native) = false := by decide
            simp [valueType, unequal] at native
  | bytes32 => have unequal : (NativeValueType.bytes32 == NativeValueType.native) = false := by decide
               simp [valueType, unequal] at native
  | bytes length => have unequal : (NativeValueType.bytes length == NativeValueType.native) = false := by rfl
                    simp [valueType, unequal] at native
  | jubjubScalar => have unequal : (NativeValueType.jubjubScalar == NativeValueType.native) = false := by decide
                    simp [valueType, unequal] at native
  | jubjubPoint => have unequal : (NativeValueType.jubjubPoint == NativeValueType.native) = false := by decide
                   simp [valueType, unequal] at native
  | foreign kind => have unequal : (NativeValueType.foreign kind == NativeValueType.native) = false := by rfl
                    simp [valueType, unequal] at native

/-- Read the scalar selected by the producer's immediate parser or SSA lookup. -/
def operandValue (witness : Assignment) (text : String) : Scalar :=
  if text.startsWith "0x" then
    match immediate text with
    | .ok number => scalar number
    | .error _ => zero
  else witness text

theorem operand_meaning {hash : Hash} {inputs witness : Assignment} {state : State}
    {text : String} {fact : Fact}
    (invariant : StateScalarProjection hash inputs witness state)
    (accepted : operand state text = .ok fact)
    (scalarType : FactScalarType fact.valueType) :
    ScalarProjection hash inputs witness fact (operandValue witness text) := by
  unfold operand at accepted
  split at accepted
  next immediateText =>
    simp only [bind_ok] at accepted
    rcases accepted with ⟨number, parsed, result⟩
    cases result
    cases scalarType
    refine ⟨?_, ?_, ?_⟩
    · simp [operandValue, immediateText, parsed, interpret]
    · simpa [operandValue, immediateText, parsed] using scalar_le number
    · intro _ _ tag
      cases tag
  next referenceText =>
    simp only [bind_ok] at accepted
    rcases accepted with ⟨_, _, accepted⟩
    split at accepted
    next existing found =>
      cases accepted
      simpa only [operandValue, referenceText, Bool.false_eq_true, ↓reduceIte] using
        invariant text _ (lookup_member found) scalarType
    next => contradiction

def OperandAgreement (hash : Hash) (inputs witness : Assignment)
    (fact : Fact) (value : Operand) : Prop :=
  FactScalarType fact.valueType →
    ScalarProjection hash inputs witness fact (value.read witness)

theorem operand_decoded_meaning
    (immediateAgreement : ∀ text number, immediate text = .ok number ↔
      NativeRelationJson.decodeImmediate text = .ok number)
    {hash : Hash} {inputs witness : Assignment} {state : State}
    {json : Json} {text : String} {fact : Fact} {value : Operand}
    (invariant : StateScalarProjection hash inputs witness state)
    (textParsed : json.getStr? = .ok text)
    (accepted : operand state text = .ok fact)
    (decoded : NativeRelationJson.decodeOperand json = .ok value) :
    OperandAgreement hash inputs witness fact value := by
  unfold NativeRelationJson.decodeOperand at decoded
  simp only [bind_ok] at decoded
  rcases decoded with ⟨foundText, parsedText, decoded⟩
  rw [textParsed] at parsedText
  cases parsedText
  intro scalarType
  have meaning := operand_meaning invariant accepted scalarType
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
    cases scalarType
    simpa [operandValue, isImmediate, producerParsed, Operand.read, interpret] using meaning
  · have notPrefix : text.startsWith "0x" = false := by
      cases prefixResult : text.startsWith "0x" <;> simp_all
    simp only [notPrefix, Bool.false_eq_true, ↓reduceIte, bind_ok] at decoded
    rcases decoded with ⟨_, _, result⟩
    cases result
    simpa only [operandValue, notPrefix, Bool.false_eq_true, ↓reduceIte, Operand.read] using meaning

/-- An accepted producer argument and the decoder's matching field share the
same parsed operand. This transports the partial scalar projection. -/
theorem argument_decoded_meaning
    (immediateAgreement : ∀ text number, immediate text = .ok number ↔
      NativeRelationJson.decodeImmediate text = .ok number)
    {hash : Hash} {inputs witness : Assignment} {state : State}
    {instruction : Json} {name : String} {fact : Fact} {value : Operand}
    (invariant : StateScalarProjection hash inputs witness state)
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

/-- Exact producer/decoder seam. The pair is the result of
`Backend.Native.nativeArgument_parts`, so the scalar type follows from the
producer's `requireNative` check. -/
theorem nativeArgument_decoded_meaning
    (immediateAgreement : ∀ text number, immediate text = .ok number ↔
      NativeRelationJson.decodeImmediate text = .ok number)
    {hash : Hash} {inputs witness : Assignment} {state : State}
    {instruction : Json} {name : String} {fact : Fact} {value : Operand}
    (invariant : StateScalarProjection hash inputs witness state)
    (producerParts : argument state instruction name = .ok fact ∧
      (fact.valueType == NativeValueType.native) = true)
    (decoded : NativeRelationJson.decodeOperandField instruction name = .ok value) :
    ScalarProjection hash inputs witness fact (value.read witness) := by
  have agreement := argument_decoded_meaning immediateAgreement invariant producerParts.1 decoded
  exact agreement (scalarType_of_nativeType producerParts.2)

end Noctium.Verification.ScalarValidationProjection
