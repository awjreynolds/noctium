import Noctium.Backend.NativeProducer
import Noctium.Verification.NativeRelationJson
import Noctium.Verification.ScalarParserAgreement
import Noctium.Verification.ScalarNormalization
import Noctium.Verification.ScalarValidationMeaning
import Noctium.Verification.ScalarValidationArithmeticLoop

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

/-- Native producer meaning and typing jointly imply the partial scalar
projection invariant for every definition in the state. -/
theorem stateScalarProjection_of_meaning_and_nativeDefinitions
    {hash : Hash} {inputs witness : Assignment} {state : State}
    (meaning : ScalarValidationMeaning.StateMeaning hash inputs witness state)
    (definitions : ScalarValidationArithmeticLoop.NativeDefinitions state) :
    StateScalarProjection hash inputs witness state := by
  intro identifier fact member scalarType
  have native : fact.valueType = NativeValueType.native := definitions identifier fact member
  have meaning := meaning identifier fact member
  rw [native] at scalarType
  cases scalarType
  exact ⟨meaning.term, meaning.bound, meaning.comparison⟩

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

/-- The executable validator seeds Native raw-call inputs before it checks the
instruction stream. Keep both states in the projection so consumers start the
instruction proof from the state the producer actually built. -/
structure NativeValidationDriverFacts (expected : Expected) (program : Json)
    (instructions rawInputs : Array Json) (seed final : State) : Prop where
  instructionsParsed : arrayField program "instructions" = .ok instructions
  rawInputsParsed : arrayField program "inputs" = .ok rawInputs
  rawInputCount : rawInputs.size = expected.rawInputs.length
  seedInputCount : seed.inputCount = 0
  emptyRawSeed : expected.rawInputs = [] → seed = {}
  finalOutput : requireFinalOutput instructions.toList = .ok ()
  instructionTrace : validateInstructionLoop expected instructions.toList.zipIdx seed = .ok final
  inputCount : final.inputCount = expected.inputs.length
  groupCount : final.groupCount = expected.groups.length
  assertionCount : final.assertionCount = expected.assertions.length
  bounds : ∀ requirement ∈ expected.bounds,
    checkBound final requirement.1 requirement.2 = .ok ()

private theorem ensure_ok {condition : Bool} {message : String} :
    Backend.Native.ensure condition message = .ok () ↔ condition = true := by
  cases condition <;> simp [Backend.Native.ensure] <;> rfl

private theorem forIn_checks {α : Type} {items : List α} {check : α → Except String Unit}
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

/-- Project the real `NativeProducer.validate` driver. In particular, the
instruction trace starts from the validated raw-input seed, not an empty state. -/
theorem validate_driver_result {expected : Expected} {program : Json}
    (accepted : validate expected program = .ok ()) :
    ∃ instructions : Array Json, ∃ rawInputs : Array Json, ∃ seed final : State,
      NativeValidationDriverFacts expected program instructions rawInputs seed final := by
  unfold validate at accepted
  simp only [bind_ok] at accepted
  rcases accepted with ⟨guardValue, guardParsed, programFields, programFieldsParsed,
    versionJson, versionParsed, versionFields, versionFieldsParsed,
    major, majorParsed, minor, minorParsed, versionCheck, versionCheckParsed,
    instructions, parsedInstructions, resources, resourceParsed,
    rawInputs, rawInputsParsed, rawInputCount, rawInputCountParsed,
    inputNames, inputNamesParsed, seedState, seedStateParsed,
    returns, returnsParsed, returnCount, returnCountParsed,
    outputTypes, outputTypesParsed,
    commitmentJson, commitmentParsed, commitment, commitmentParsedBool,
    commitmentCheck, commitmentCheckParsed, finalOutput, finalOutputParsed,
    finalState, instructionTrace,
    inputCount, inputCountParsed, groupCount, groupCountParsed,
    assertionCount, assertionCountParsed,
    inputChecks, inputChecksParsed, coordinateChecks, coordinateChecksParsed,
    boundChecks, boundChecksParsed, result⟩
  have seedInputCount : seedState.inputCount = 0 := by
    change seedRawInputs expected rawInputs = .ok seedState at seedStateParsed
    exact seedRawInputs_inputCount seedStateParsed
  refine ⟨instructions, rawInputs, seedState, finalState, ?_⟩
  refine ⟨parsedInstructions, rawInputsParsed, ?_, ?_, ?_, finalOutputParsed, instructionTrace,
    ?_, ?_, ?_, ?_⟩
  · exact eq_of_beq (ensure_ok.mp rawInputCountParsed)
  · exact seedInputCount
  · intro noRawInputs
    have rawCount := eq_of_beq (ensure_ok.mp rawInputCountParsed)
    have rawSize : rawInputs.size = 0 := by rw [noRawInputs] at rawCount; simpa using rawCount
    have rawListLength : rawInputs.toList.length = 0 := by simpa using rawSize
    have rawListNil : rawInputs.toList = [] := by
      cases rawList : rawInputs.toList <;> simp_all
    unfold seedRawInputs at seedStateParsed
    rw [rawListNil] at seedStateParsed
    simp only [List.zipIdx_nil, List.forIn_nil] at seedStateParsed
    exact (Except.ok.inj seedStateParsed).symm
  · exact eq_of_beq (ensure_ok.mp inputCountParsed)
  · exact eq_of_beq (ensure_ok.mp groupCountParsed)
  · exact eq_of_beq (ensure_ok.mp assertionCountParsed)
  · have acceptedBounds : forIn expected.bounds PUnit.unit
        (fun (requirement : Backend.Native.Term × Nat) (_ : PUnit) => do
          checkBound finalState requirement.1 requirement.2
          pure (.yield PUnit.unit)) = .ok PUnit.unit := by
      simpa only [Bind.bind, Except.bind, Pure.pure, Except.pure] using boundChecksParsed
    exact forIn_checks acceptedBounds

/-- The old empty-state consumer is valid precisely when the actual validator
has no raw call inputs to seed. -/
theorem validate_driver_result_empty_seed {expected : Expected} {program : Json}
    (accepted : validate expected program = .ok ())
    (noRawInputs : expected.rawInputs = []) :
    ∃ instructions : Array Json, ∃ rawInputs : Array Json, ∃ final : State,
      NativeValidationDriverFacts expected program instructions rawInputs {} final := by
  obtain ⟨instructions, rawInputs, seed, final, facts⟩ := validate_driver_result accepted
  cases facts.emptyRawSeed noRawInputs
  exact ⟨instructions, rawInputs, final, facts⟩

/-- An independently parsed empty header establishes the empty initial
state through the actual producer's raw-input count and seeding checks. -/
theorem validate_driver_result_empty_header {expected : Expected} {program : Json}
    (accepted : validate expected program = .ok ())
    (header : arrayField program "inputs" = .ok #[]) :
    expected.rawInputs = [] ∧
      ∃ instructions : Array Json, ∃ final : State,
        NativeValidationDriverFacts expected program instructions #[] {} final := by
  obtain ⟨instructions, rawInputs, seed, final, facts⟩ := validate_driver_result accepted
  have rawEmpty := Except.ok.inj (facts.rawInputsParsed.symm.trans header)
  have requiredEmpty : expected.rawInputs = [] := List.length_eq_zero_iff.mp (by
    simpa [rawEmpty] using facts.rawInputCount.symm)
  have seedEmpty := facts.emptyRawSeed requiredEmpty
  subst rawInputs seed
  exact ⟨requiredEmpty, instructions, final, facts⟩

end Noctium.Verification.ScalarValidationProjection
