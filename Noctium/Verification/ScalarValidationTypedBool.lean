import Noctium.Verification.ScalarValidationMeaning

namespace Noctium.Verification.ScalarValidationTypedBool

open Lean Backend.Native
open Noctium.Verification.ScalarValidationMeaning

/-- Interpret only canonical typed Bool constants and binary gates. Unknown
terms stay outside the typed Bool proof domain. -/
def interpretTypedBoolTerm? : Backend.Native.Term → Option Bool
  | .unary "bool_constant" (.constant 0) => some false
  | .unary "bool_constant" (.constant 1) => some true
  | .unary opcode (.hash [left, right]) => do
    let left ← interpretTypedBoolTerm? left
    let right ← interpretTypedBoolTerm? right
    if opcode == "typed_bool_and" then some (left && right)
    else if opcode == "typed_bool_or" then some (left || right)
    else if opcode == "typed_bool_xor" then some (left.xor right)
    else none
  | _ => none

/-- Bool encoding maps the checked Boolean result to its canonical field bit. -/
def interpretTypedBoolNative? (term : Backend.Native.Term) : Option NativeRelation.Scalar :=
  match term with
  | .unary "bool_to_native" value =>
    (interpretTypedBoolTerm? value).map NativeRelation.bit
  | _ => none

def typedBoolResult (opcode : String) (left right : Bool) : Bool :=
  if opcode == "and" then left && right
  else if opcode == "or" then left || right
  else left.xor right

def asTypedBoolFact (fact : Fact) : Fact := {fact with valueType := .bool}

def typedBoolConstantFact (value : Nat) : Fact :=
  {term := typedBoolConstantTerm value, maximum := value, valueType := .bool}

theorem interpretTypedBoolGate2Constants (opcode : String) (left right : Bool)
    (opcodeValid : opcode = "and" ∨ opcode = "or" ∨ opcode = "xor") :
    interpretTypedBoolTerm?
      (typedBoolGateTerm opcode
        [typedBoolConstantTerm (if left then 1 else 0),
          typedBoolConstantTerm (if right then 1 else 0)]) =
      some (typedBoolResult opcode left right) := by
  rcases opcodeValid with rfl | rfl | rfl <;>
    cases left <;> cases right <;>
    simp [interpretTypedBoolTerm?, typedBoolResult, typedBoolGateTerm,
      typedBoolConstantTerm]

theorem interpretTypedBoolEncodedGate2Constants (opcode : String) (left right : Bool)
    (opcodeValid : opcode = "and" ∨ opcode = "or" ∨ opcode = "xor") :
    interpretTypedBoolNative?
      (boolToNativeTerm
        (typedBoolGateTerm opcode
          [typedBoolConstantTerm (if left then 1 else 0),
            typedBoolConstantTerm (if right then 1 else 0)])) =
      some (NativeRelation.bit (typedBoolResult opcode left right)) := by
  rcases opcodeValid with rfl | rfl | rfl <;>
    cases left <;> cases right <;>
    simp [interpretTypedBoolNative?, interpretTypedBoolTerm?, typedBoolResult,
      boolToNativeTerm, typedBoolGateTerm, typedBoolConstantTerm]

/-- The Boolean projection stays separate from Native-only arithmetic facts. -/
def BooleanDefinitions (state : State) : Prop :=
  ∀ identifier fact, (identifier, fact) ∈ state.definitions →
    fact.valueType = .bool → fact.maximum ≤ 1

theorem defineResult_booleanDefinitions {state next : State} {instruction : Json}
    {fact : Fact} (prior : BooleanDefinitions state)
    (factBound : fact.valueType = .bool → fact.maximum ≤ 1)
    (accepted : defineResult state instruction fact = .ok next) :
    BooleanDefinitions next := by
  unfold defineResult at accepted
  simp only [bind_ok] at accepted
  rcases accepted with ⟨identifier, _, defined⟩
  unfold define at defined
  simp only [bind_ok] at defined
  rcases defined with ⟨_, _, _, _, result⟩
  cases result
  intro name found member foundBool
  simp only [List.mem_append, List.mem_singleton, Prod.mk.injEq] at member
  rcases member with member | ⟨sameName, sameFact⟩
  · exact prior name found member foundBool
  · subst name
    subst found
    exact factBound foundBool

/-- A successful Bool load_constant has the exact canonical immediate fact
that NativeProducer checked. -/
theorem accepted_bool_constant_components {expected : Expected} {state next : State}
    {instruction : Json}
    (opcode : stringField instruction "op" = .ok "load_constant")
    (boolType : stringField instruction "type" = .ok "Bool")
    (accepted : validateInstruction expected state instruction = .ok next) :
    ∃ value, value ≤ 1 ∧
      defineResult state instruction
        {term := typedBoolConstantTerm value, maximum := value, valueType := .bool} =
          .ok next := by
  unfold validateInstruction at accepted
  simp only [bind_ok] at accepted
  rcases accepted with ⟨opcodeName, opcodeParsed, descriptor, descriptorParsed,
    supported, fieldsParsed, accepted⟩
  have opcodeEq : opcodeName = "load_constant" :=
    Except.ok.inj (opcodeParsed.symm.trans opcode)
  subst opcodeName
  simp only [bind_ok] at accepted
  rcases accepted with ⟨typeName, typeParsed, encoding, encodingParsed, accepted⟩
  have typeEq : typeName = "Bool" := Except.ok.inj (typeParsed.symm.trans boolType)
  subst typeName
  simp only [beq_self_eq_true, ↓reduceIte, bind_ok] at accepted
  rcases accepted with ⟨_, sizeChecked, text, textParsed, value, immediateParsed, checked⟩
  rcases checked with ⟨_unit, rangeChecked, defined⟩
  have valueBound := ensure_ok.mp rangeChecked
  exact ⟨value, of_decide_eq_true valueBound, by
    simpa [Backend.Native.typedBoolConstantTerm] using defined⟩

/-- The constant meaning follows from the exact Bool `load_constant` branch
accepted by NativeProducer, including its canonical 0/1 range check. -/
theorem accepted_bool_constant_scoped_meaning {expected : Expected} {state next : State}
    {instruction : Json}
    (opcode : stringField instruction "op" = .ok "load_constant")
    (boolType : stringField instruction "type" = .ok "Bool")
    (accepted : validateInstruction expected state instruction = .ok next) :
    ∃ value, value ≤ 1 ∧
      interpretTypedBoolTerm? (typedBoolConstantTerm value) = some (value == 1) ∧
      defineResult state instruction
        {term := typedBoolConstantTerm value, maximum := value, valueType := .bool} =
          .ok next := by
  obtain ⟨value, valueBound, defined⟩ :=
    accepted_bool_constant_components opcode boolType accepted
  refine ⟨value, valueBound, ?_, defined⟩
  have valueCases : value = 0 ∨ value = 1 := by omega
  rcases valueCases with zero | one
  · simp [zero, interpretTypedBoolTerm?, typedBoolConstantTerm]
  · simp [one, interpretTypedBoolTerm?, typedBoolConstantTerm]

private theorem defineResult_appends_fact {state next : State} {instruction : Json}
    {fact : Fact} {output : String}
    (outputField : stringField instruction "output" = .ok output)
    (accepted : defineResult state instruction fact = .ok next) :
    next.definitions = state.definitions ++ [(output, fact)] ∧
    state.definitions.lookup output = none := by
  unfold defineResult at accepted
  simp only [bind_ok] at accepted
  rcases accepted with ⟨foundOutput, outputParsed, defined⟩
  have sameOutput : foundOutput = output := Except.ok.inj (outputParsed.symm.trans outputField)
  subst foundOutput
  unfold define at defined
  simp only [bind_ok] at defined
  rcases defined with ⟨_, _valid, _, result⟩
  rcases result with ⟨absent, result⟩
  have absent := ensure_ok.mp absent
  have lookupAbsent : state.definitions.lookup output = none := by
    cases lookup : state.definitions.lookup output <;> simp [lookup] at absent ⊢
  cases result
  exact ⟨rfl, lookupAbsent⟩

/-- An input operand naming the fresh output of an accepted definition resolves
to the exact fact inserted by that transition. -/
private theorem argument_after_defineResult {state next : State}
    {definition consumer : Json} {fact : Fact} {name : String}
    (outputField : stringField definition "output" = .ok name)
    (inputField : stringField consumer "input" = .ok name)
    (nameIsReference : name.startsWith "0x" = false)
    (defined : defineResult state definition fact = .ok next) :
    argument next consumer "input" = .ok fact := by
  obtain ⟨nextDefinitions, priorAbsent⟩ :=
    defineResult_appends_fact outputField defined
  unfold defineResult at defined
  rw [outputField] at defined
  simp only [bind_ok] at defined
  rcases defined with ⟨foundName, parsedName, defined⟩
  have sameName : foundName = name := (Except.ok.inj parsedName).symm
  subst foundName
  unfold define at defined
  simp only [bind_ok] at defined
  rcases defined with ⟨_, identifierValid, _, _⟩
  have identifierValid := ensure_ok.mp identifierValid
  have factLookup : next.definitions.lookup name = some fact := by
    rw [nextDefinitions]
    simp [List.lookup_append, priorAbsent]
  have operandAccepted : operand next name = .ok fact := by
    simp [Backend.Native.operand, nameIsReference, factLookup, identifierValid,
      Backend.Native.ensure, Bind.bind, Except.bind, Pure.pure, Except.pure]
  unfold argument
  rw [inputField]
  simpa [Bind.bind, Except.bind, Pure.pure, Except.pure] using operandAccepted

/-- Two accepted canonical Bool constants survive their actual ordered
`defineResult` insertions and resolve through the producer's input parser. -/
theorem accepted_bool_constant_pair_arguments {expected : Expected}
    {initial afterLeft afterRight : State}
    {leftInstruction rightInstruction gateInstruction : Json}
    {leftValue rightValue : Nat}
    (leftOpcode : stringField leftInstruction "op" = .ok "load_constant")
    (leftType : stringField leftInstruction "type" = .ok "Bool")
    (leftAccepted : validateInstruction expected initial leftInstruction = .ok afterLeft)
    (leftOutput : stringField leftInstruction "output" = .ok "%bool_left")
    (rightOpcode : stringField rightInstruction "op" = .ok "load_constant")
    (rightType : stringField rightInstruction "type" = .ok "Bool")
    (rightAccepted : validateInstruction expected afterLeft rightInstruction = .ok afterRight)
    (rightOutput : stringField rightInstruction "output" = .ok "%bool_right")
    (gateInputs : arrayField gateInstruction "inputs" =
      .ok #[Json.str "%bool_left", Json.str "%bool_right"])
    (leftExact : ∀ value, value ≤ 1 →
      defineResult initial leftInstruction (typedBoolConstantFact value) = .ok afterLeft →
      value = leftValue)
    (rightExact : ∀ value, value ≤ 1 →
      defineResult afterLeft rightInstruction (typedBoolConstantFact value) = .ok afterRight →
      value = rightValue) :
    arguments afterRight gateInstruction "inputs" =
      .ok [typedBoolConstantFact leftValue, typedBoolConstantFact rightValue] := by
  obtain ⟨actualLeft, leftBound, leftDefined⟩ :=
    accepted_bool_constant_components leftOpcode leftType leftAccepted
  have leftValueEq := leftExact actualLeft leftBound leftDefined
  subst actualLeft
  obtain ⟨actualRight, rightBound, rightDefined⟩ :=
    accepted_bool_constant_components rightOpcode rightType rightAccepted
  have rightValueEq := rightExact actualRight rightBound rightDefined
  subst actualRight
  obtain ⟨afterLeftDefs, leftFresh⟩ := defineResult_appends_fact leftOutput leftDefined
  obtain ⟨afterRightDefs, rightFresh⟩ := defineResult_appends_fact rightOutput rightDefined
  unfold defineResult at leftDefined rightDefined
  rw [leftOutput] at leftDefined
  rw [rightOutput] at rightDefined
  simp only [bind_ok] at leftDefined rightDefined
  rcases leftDefined with ⟨foundLeft, parsedLeft, leftDefine⟩
  have foundLeftEq : foundLeft = "%bool_left" := (Except.ok.inj parsedLeft).symm
  subst foundLeft
  rcases rightDefined with ⟨foundRight, parsedRight, rightDefine⟩
  have foundRightEq : foundRight = "%bool_right" := (Except.ok.inj parsedRight).symm
  subst foundRight
  unfold define at leftDefine rightDefine
  simp only [bind_ok] at leftDefine rightDefine
  rcases leftDefine with ⟨_, leftValid, _, _⟩
  rcases rightDefine with ⟨_, rightValid, _, _⟩
  have leftValidBool := ensure_ok.mp leftValid
  have rightValidBool := ensure_ok.mp rightValid
  have leftLookup : afterRight.definitions.lookup "%bool_left" =
      some (typedBoolConstantFact leftValue) := by
    rw [afterRightDefs, afterLeftDefs]
    simp [List.lookup_append, leftFresh, typedBoolConstantFact]
  have rightLookup : afterRight.definitions.lookup "%bool_right" =
      some (typedBoolConstantFact rightValue) := by
    rw [afterRightDefs]
    simp [List.lookup_append, rightFresh, typedBoolConstantFact]
  have leftOperand : operand afterRight "%bool_left" =
      .ok (typedBoolConstantFact leftValue) := by
    simp [Backend.Native.operand, leftLookup, leftValidBool,
      Backend.Native.ensure, Bind.bind, Except.bind, Pure.pure, Except.pure]
  have rightOperand : operand afterRight "%bool_right" =
      .ok (typedBoolConstantFact rightValue) := by
    simp [Backend.Native.operand, rightLookup, rightValidBool,
      Backend.Native.ensure, Bind.bind, Except.bind, Pure.pure, Except.pure]
  have leftText : (Json.str "%bool_left").getStr? = .ok "%bool_left" := rfl
  have rightText : (Json.str "%bool_right").getStr? = .ok "%bool_right" := rfl
  unfold arguments
  rw [gateInputs]
  simp [Bind.bind, Except.bind, Pure.pure, Except.pure, List.mapM_cons,
    List.mapM_nil, Backend.Native.ensure, leftText, rightText,
    leftOperand, rightOperand, typedBoolConstantFact,
    Backend.Native.maxVectorLength, Noctium.fabHashNativeOperandLimit] <;>
    (simp [Backend.Native.ensure, Except.map] <;> rfl)

/-- One accepted two-input `and` gate exposes the reducer fact and its Bool
output definition. NativeProducer's checked branch also validates each input
type and range before returning this equation. -/
theorem accepted_bool_and_components {expected : Expected} {state next : State}
    {instruction : Json}
    (opcode : stringField instruction "op" = .ok "and")
    (accepted : validateInstruction expected state instruction = .ok next) :
    ∃ values fact,
      arguments state instruction "inputs" = .ok values ∧
      values ≠ [] ∧
      combine (typedBoolGateTerm "and" (values.map Fact.term)) 1 values = .ok fact ∧
      defineResult state instruction {fact with valueType := .bool} = .ok next := by
  unfold validateInstruction at accepted
  simp only [bind_ok] at accepted
  rcases accepted with ⟨opcodeName, opcodeParsed, descriptor, descriptorParsed,
    supported, fieldsParsed, accepted⟩
  have opcodeEq : opcodeName = "and" := Except.ok.inj (opcodeParsed.symm.trans opcode)
  subst opcodeName
  simp only [bind_ok] at accepted
  rcases accepted with ⟨values, valuesParsed, _, nonempty, _, typedInputs, fact,
    combined, defined⟩
  exact ⟨values, fact, valuesParsed, by
    intro empty
    subst values
    simp [Backend.Native.ensure] at nonempty, combined, defined⟩

/-- Compose actual `NativeProducer.validateInstruction` acceptance for a
binary gate with the canonical Bool term result. The caller supplies the two
already-defined load_constant facts selected by the checked argument parser. -/
theorem accepted_bool_and_term_meaning {expected : Expected} {state next : State}
    {instruction : Json} {left right : Fact} (leftValue rightValue : Bool)
    (opcode : stringField instruction "op" = .ok "and")
    (accepted : validateInstruction expected state instruction = .ok next)
    (inputs : arguments state instruction "inputs" = .ok [left, right])
    (leftTerm : left.term = typedBoolConstantTerm (if leftValue then 1 else 0))
    (rightTerm : right.term = typedBoolConstantTerm (if rightValue then 1 else 0)) :
    ∃ fact : Fact,
      defineResult state instruction {fact with valueType := .bool} = .ok next ∧
      fact.maximum = 1 ∧
      interpretTypedBoolTerm? (({fact with valueType := .bool}).term) =
        some (leftValue && rightValue) ∧
      interpretTypedBoolNative? (boolToNativeTerm (({fact with valueType := .bool}).term)) =
        some (NativeRelation.bit (leftValue && rightValue)) := by
  obtain ⟨values, fact, argumentsAccepted, _nonempty, combined, defined⟩ :=
    accepted_bool_and_components opcode accepted
  have valuesEq : values = [left, right] := Except.ok.inj (argumentsAccepted.symm.trans inputs)
  have factMaximum : fact.maximum = 1 := by
    unfold combine at combined
    dsimp [Backend.Native.ensure] at combined
    split at combined
    · simp only [Pure.pure, Except.pure] at combined
      have same := Except.ok.inj combined
      simpa using (congrArg Fact.maximum same).symm
    · contradiction
  have factTerm : fact.term = typedBoolGateTerm "and" [left.term, right.term] := by
    unfold combine at combined
    dsimp [Backend.Native.ensure] at combined
    split at combined
    · simp only [Pure.pure, Except.pure] at combined
      have same := Except.ok.inj combined
      simpa [valuesEq] using (congrArg Fact.term same).symm
    · contradiction
  have typedMeaning : interpretTypedBoolTerm? (({fact with valueType := .bool}).term) =
      some (leftValue && rightValue) := by
    rw [factTerm, leftTerm, rightTerm]
    exact interpretTypedBoolGate2Constants "and" leftValue rightValue (Or.inl rfl)
  have encodedMeaning : interpretTypedBoolNative?
      (boolToNativeTerm (({fact with valueType := .bool}).term)) =
        some (NativeRelation.bit (leftValue && rightValue)) := by
    rw [factTerm, leftTerm, rightTerm]
    exact interpretTypedBoolEncodedGate2Constants "and" leftValue rightValue (Or.inl rfl)
  exact ⟨fact, defined, factMaximum, typedMeaning, encodedMeaning⟩

/-- An accepted Bool `encode` instruction creates exactly one Native fact by
combining the selected Bool input with the canonical Bool-to-Native bridge.
The output name and fact come from the actual checked producer transition. -/
theorem accepted_bool_encode_components {expected : Expected} {state next : State}
    {instruction : Json} {input : Fact}
    (opcode : stringField instruction "op" = .ok "encode")
    (inputAccepted : argument state instruction "input" = .ok input)
    (inputBool : input.valueType = .bool)
    (accepted : validateInstruction expected state instruction = .ok next) :
    ∃ outputs output fact,
      arrayField instruction "outputs" = .ok outputs ∧ outputs.size = 1 ∧
      outputs[0]!.getStr? = .ok output ∧ input.maximum ≤ 1 ∧
      combine (boolToNativeTerm input.term) 1 [input] = .ok fact ∧
      define state output fact = .ok next := by
  unfold validateInstruction at accepted
  simp only [bind_ok] at accepted
  rcases accepted with ⟨opcodeName, opcodeParsed, descriptor, descriptorParsed,
    supported, fieldsParsed, accepted⟩
  have opcodeEq : opcodeName = "encode" := Except.ok.inj (opcodeParsed.symm.trans opcode)
  subst opcodeName
  simp only [bind_ok] at accepted
  rcases accepted with ⟨foundInput, foundInputAccepted, outputs, outputsAccepted, reducer⟩
  have inputEq : foundInput = input := Except.ok.inj (foundInputAccepted.symm.trans inputAccepted)
  subst foundInput
  simp [inputBool] at reducer
  rcases bind_ok.mp reducer with ⟨_, outputsCount, reducer⟩
  have outputsSize : outputs.size = 1 := eq_of_beq (ensure_ok.mp outputsCount)
  rcases bind_ok.mp reducer with ⟨_, inputRange, reducer⟩
  have inputBound : input.maximum ≤ 1 := of_decide_eq_true (ensure_ok.mp inputRange)
  rcases bind_ok.mp reducer with ⟨output, outputParsed, reducer⟩
  rcases bind_ok.mp reducer with ⟨foundFact, combined, defined⟩
  exact ⟨outputs, output, foundFact, outputsAccepted, outputsSize, outputParsed,
    inputBound, combined, defined⟩

/-- Compose an accepted typed Bool gate with its accepted `encode` handoff.
The result is the exact one-output Native producer fact, and its scoped Bool
meaning is the canonical field bit for the gate result. -/
theorem accepted_bool_and_encode_meaning {expected : Expected}
    {state gateState encodedState : State} {gateInstruction encodeInstruction : Json}
    {gateOutputName : String}
    {left right : Fact} (leftValue rightValue : Bool)
    (gateOpcode : stringField gateInstruction "op" = .ok "and")
    (gateAccepted : validateInstruction expected state gateInstruction = .ok gateState)
    (gateInputs : arguments state gateInstruction "inputs" = .ok [left, right])
    (leftTerm : left.term = typedBoolConstantTerm (if leftValue then 1 else 0))
    (rightTerm : right.term = typedBoolConstantTerm (if rightValue then 1 else 0))
    (encodeOpcode : stringField encodeInstruction "op" = .ok "encode")
    (gateOutput : stringField gateInstruction "output" = .ok gateOutputName)
    (encodeInputField : stringField encodeInstruction "input" = .ok gateOutputName)
    (gateOutputIsReference : gateOutputName.startsWith "0x" = false)
    (encodeAccepted : validateInstruction expected gateState encodeInstruction =
      .ok encodedState) :
    ∃ outputs output nativeFact,
      arrayField encodeInstruction "outputs" = .ok outputs ∧ outputs.size = 1 ∧
      outputs[0]!.getStr? = .ok output ∧
      define gateState output nativeFact = .ok encodedState ∧
      interpretTypedBoolNative? nativeFact.term =
        some (NativeRelation.bit (leftValue && rightValue)) := by
  obtain ⟨gateFact, gateDefined, gateMaximum, _gateMeaning, gateEncodedMeaning⟩ :=
    accepted_bool_and_term_meaning leftValue rightValue gateOpcode gateAccepted
      gateInputs leftTerm rightTerm
  have encodedInput := argument_after_defineResult gateOutput encodeInputField
    gateOutputIsReference gateDefined
  obtain ⟨outputs, output, nativeFact, outputsAccepted, outputsSize,
      outputName, inputBound, combined, defined⟩ :=
    accepted_bool_encode_components encodeOpcode encodedInput (by rfl) encodeAccepted
  have nativeFactTerm : nativeFact.term = boolToNativeTerm gateFact.term := by
    unfold combine at combined
    simp [Bind.bind, Except.bind] at combined
    split at combined
    · simp only [Pure.pure, Except.pure] at combined
      cases combined
      rfl
    · contradiction
  have encodedMeaning : interpretTypedBoolNative? nativeFact.term =
      some (NativeRelation.bit (leftValue && rightValue)) := by
    rw [nativeFactTerm]
    simpa only [Bool.true_and] using gateEncodedMeaning
  exact ⟨outputs, output, nativeFact, outputsAccepted, outputsSize, outputName,
    defined, encodedMeaning⟩

/-- Consume the accepted gate and encode handoff at the strict scalar output
boundary. The caller supplies the decoded output identity and its satisfying
witness value. This theorem scopes Bool meaning to the exact accepted slice. -/
theorem accepted_bool_and_encode_output_boundary {expected : Expected}
    {witness : NativeRelation.Assignment}
    {state gateState encodedState outputState : State}
    {gateInstruction encodeInstruction outputInstruction : Json}
    {gateOutputName outputName : String}
    {left right : Fact} (leftValue rightValue : Bool)
    (gateOpcode : stringField gateInstruction "op" = .ok "and")
    (gateAccepted : validateInstruction expected state gateInstruction = .ok gateState)
    (gateInputs : arguments state gateInstruction "inputs" = .ok [left, right])
    (leftTerm : left.term = typedBoolConstantTerm (if leftValue then 1 else 0))
    (rightTerm : right.term = typedBoolConstantTerm (if rightValue then 1 else 0))
    (encodeOpcode : stringField encodeInstruction "op" = .ok "encode")
    (gateOutput : stringField gateInstruction "output" = .ok gateOutputName)
    (encodeInputField : stringField encodeInstruction "input" = .ok gateOutputName)
    (gateOutputIsReference : gateOutputName.startsWith "0x" = false)
    (encodeAccepted : validateInstruction expected gateState encodeInstruction =
      .ok encodedState)
    (encodedOutput : arrayField encodeInstruction "outputs" =
      .ok #[Json.str outputName])
    (outputAccepted : validateInstruction expected encodedState outputInstruction =
      .ok outputState)
    (decodedOutput : NativeRelationJson.decodeInstruction outputInstruction =
      .ok (.output [.reference outputName]))
    (outputSatisfied : witness outputName =
      NativeRelation.bit (leftValue && rightValue)) :
    ∃ (nativeFact : Fact),
      validateInstruction expected encodedState outputInstruction = .ok outputState ∧
      NativeRelationJson.decodeInstruction outputInstruction =
        .ok (.output [.reference outputName]) ∧
      interpretTypedBoolNative? nativeFact.term =
        some (NativeRelation.bit (leftValue && rightValue)) ∧
      [NativeRelation.Operand.read witness (.reference outputName)] =
        [NativeRelation.bit (leftValue && rightValue)] := by
  obtain ⟨outputs, encodedName, (nativeFact : Fact), outputsAccepted, outputsSize,
    outputParsed, defined, encodedMeaning⟩ :=
    accepted_bool_and_encode_meaning leftValue rightValue gateOpcode gateAccepted
      gateInputs leftTerm rightTerm encodeOpcode gateOutput encodeInputField
      gateOutputIsReference encodeAccepted
  have outputsEq : outputs = #[Json.str outputName] :=
    Except.ok.inj (outputsAccepted.symm.trans encodedOutput)
  have sameOutput : encodedName = outputName := by
    rw [outputsEq] at outputParsed
    exact (Except.ok.inj outputParsed).symm
  subst encodedName
  have decodedValue : NativeRelation.Operand.read witness (.reference outputName) =
      NativeRelation.bit (leftValue && rightValue) := outputSatisfied
  exact ⟨nativeFact, outputAccepted, decodedOutput, encodedMeaning, by simp [decodedValue]⟩

/-- Exact accepted slice from two canonical Bool `load_constant` operations
through the actual gate argument parser, Bool encode, and strict output decode.
The witness equality remains an explicit decoded satisfaction assumption. -/
theorem accepted_bool_constants_gate_encode_output {expected : Expected}
    {witness : NativeRelation.Assignment}
    {initial afterLeft afterConstants gateState encodedState outputState : State}
    {leftInstruction rightInstruction gateInstruction encodeInstruction outputInstruction : Json}
    {gateOutputName outputName : String} (leftValue rightValue : Bool)
    (leftOpcode : stringField leftInstruction "op" = .ok "load_constant")
    (leftType : stringField leftInstruction "type" = .ok "Bool")
    (leftAccepted : validateInstruction expected initial leftInstruction = .ok afterLeft)
    (leftOutput : stringField leftInstruction "output" = .ok "%bool_left")
    (rightOpcode : stringField rightInstruction "op" = .ok "load_constant")
    (rightType : stringField rightInstruction "type" = .ok "Bool")
    (rightAccepted : validateInstruction expected afterLeft rightInstruction = .ok afterConstants)
    (rightOutput : stringField rightInstruction "output" = .ok "%bool_right")
    (gateInputsJson : arrayField gateInstruction "inputs" =
      .ok #[Json.str "%bool_left", Json.str "%bool_right"])
    (leftValueExact : ∀ value, value ≤ 1 →
      defineResult initial leftInstruction (typedBoolConstantFact value) = .ok afterLeft →
      value = if leftValue then 1 else 0)
    (rightValueExact : ∀ value, value ≤ 1 →
      defineResult afterLeft rightInstruction (typedBoolConstantFact value) = .ok afterConstants →
      value = if rightValue then 1 else 0)
    (gateOpcode : stringField gateInstruction "op" = .ok "and")
    (gateAccepted : validateInstruction expected afterConstants gateInstruction = .ok gateState)
    (encodeOpcode : stringField encodeInstruction "op" = .ok "encode")
    (gateOutput : stringField gateInstruction "output" = .ok gateOutputName)
    (encodeInputField : stringField encodeInstruction "input" = .ok gateOutputName)
    (gateOutputIsReference : gateOutputName.startsWith "0x" = false)
    (encodeAccepted : validateInstruction expected gateState encodeInstruction = .ok encodedState)
    (encodedOutput : arrayField encodeInstruction "outputs" = .ok #[Json.str outputName])
    (outputAccepted : validateInstruction expected encodedState outputInstruction = .ok outputState)
    (decodedOutput : NativeRelationJson.decodeInstruction outputInstruction =
      .ok (.output [.reference outputName]))
    (outputSatisfied : witness outputName = NativeRelation.bit (leftValue && rightValue)) :
    ∃ nativeFact : Fact,
      validateInstruction expected encodedState outputInstruction = .ok outputState ∧
      NativeRelationJson.decodeInstruction outputInstruction = .ok (.output [.reference outputName]) ∧
      interpretTypedBoolNative? nativeFact.term =
        some (NativeRelation.bit (leftValue && rightValue)) ∧
      [NativeRelation.Operand.read witness (.reference outputName)] =
        [NativeRelation.bit (leftValue && rightValue)] := by
  have inputsAccepted := accepted_bool_constant_pair_arguments
    leftOpcode leftType leftAccepted leftOutput rightOpcode rightType rightAccepted rightOutput
    gateInputsJson leftValueExact rightValueExact
  exact accepted_bool_and_encode_output_boundary
    (expected := expected) (witness := witness) (state := afterConstants)
    (gateState := gateState) (encodedState := encodedState) (outputState := outputState)
    (gateInstruction := gateInstruction) (encodeInstruction := encodeInstruction)
    (outputInstruction := outputInstruction) (gateOutputName := gateOutputName)
    (outputName := outputName)
    (left := typedBoolConstantFact (if leftValue then 1 else 0))
    (right := typedBoolConstantFact (if rightValue then 1 else 0))
    leftValue rightValue gateOpcode gateAccepted inputsAccepted rfl rfl encodeOpcode
    gateOutput encodeInputField gateOutputIsReference encodeAccepted encodedOutput
    outputAccepted decodedOutput outputSatisfied

end Noctium.Verification.ScalarValidationTypedBool
