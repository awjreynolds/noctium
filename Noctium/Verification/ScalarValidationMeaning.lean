import Noctium.Backend.NativeProducer
import Noctium.Verification.NativeRelationJson
import Noctium.Verification.ScalarParserAgreement
import Noctium.Verification.ScalarNormalization

namespace Noctium.Verification.ScalarValidationMeaning

open Backend.Native NativeRelation ScalarNormalization

/-- A producer fact has a meaning only when the partial scalar interpreter
returns that exact value. -/
structure FactMeaning (hash : Hash) (inputs witness : Assignment) (fact : Fact)
    (value : Scalar) : Prop where
  term : interpret hash inputs fact.term = some value
  bound : value.val ≤ fact.maximum
  comparison : ∀ identifier exclusive,
    fact.assertedLessThan = some (identifier, exclusive) → value ≠ zero →
      (witness identifier).val < exclusive

def StateMeaning (hash : Hash) (inputs witness : Assignment) (state : State) : Prop :=
  ∀ identifier fact, (identifier, fact) ∈ state.definitions →
    FactMeaning hash inputs witness fact (witness identifier)

theorem bind_ok {α β : Type} {value : Except String α} {next : α → Except String β}
    {result : β} : (value >>= next) = .ok result ↔
      ∃ found, value = .ok found ∧ next found = .ok result := by
  cases value <;> simp [Bind.bind, Except.bind]

theorem ensure_ok {condition : Bool} {message : String} :
    Backend.Native.ensure condition message = .ok () ↔ condition = true := by
  cases condition <;> simp [Backend.Native.ensure] <;> rfl

theorem lookup_member {α β : Type} [BEq α] [LawfulBEq α]
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

theorem empty_meaning (hash : Hash) (inputs witness : Assignment) :
    StateMeaning hash inputs witness {} := by
  intro identifier fact found
  simp at found

theorem scalar_le (number : Nat) : (scalar number).val ≤ number := Nat.mod_le _ _

/-- Accepted producer operands retain scalar meaning through either a checked
canonical immediate or an existing definition in the state. -/
theorem operand_meaning {hash : Hash} {inputs witness : Assignment} {state : State}
    {text : String} {fact : Fact}
    (invariant : StateMeaning hash inputs witness state)
    (accepted : operand state text = .ok fact) :
    ∃ value, FactMeaning hash inputs witness fact value := by
  unfold operand at accepted
  split at accepted
  next immediateText =>
    simp only [bind_ok] at accepted
    rcases accepted with ⟨number, parsed, result⟩
    cases result
    refine ⟨scalar number, ?_⟩
    refine ⟨?_, ?_, ?_⟩
    · simp [interpret]
    · simpa [interpret] using scalar_le number
    · intro _ _ tag
      cases tag
  next referenceText =>
    simp only [bind_ok] at accepted
    rcases accepted with ⟨_, _, accepted⟩
    split at accepted
    next existing found =>
      cases accepted
      exact ⟨witness text, by simpa only [referenceText, Bool.false_eq_true,
        ↓reduceIte] using invariant text _ (lookup_member found)⟩
    next => contradiction

/-- The actual argument helper preserves the same checked meaning, including
its canonical immediate parser. -/
theorem argument_meaning {hash : Hash} {inputs witness : Assignment} {state : State}
    {instruction : Lean.Json} {name : String} {fact : Fact}
    (invariant : StateMeaning hash inputs witness state)
    (accepted : argument state instruction name = .ok fact) :
    ∃ value, FactMeaning hash inputs witness fact value := by
  unfold argument at accepted
  simp only [bind_ok] at accepted
  rcases accepted with ⟨text, _, operandAccepted⟩
  exact operand_meaning invariant operandAccepted

/-- The producer operand parser and native JSON operand decoder agree on the
scalar assigned to each accepted operand. -/
theorem operand_decoded_meaning
    {hash : Hash} {inputs witness : Assignment} {state : State}
    {json : Lean.Json} {text : String} {fact : Fact} {value : Operand}
    (invariant : StateMeaning hash inputs witness state)
    (textParsed : json.getStr? = .ok text)
    (accepted : operand state text = .ok fact)
    (decoded : NativeRelationJson.decodeOperand json = .ok value) :
    FactMeaning hash inputs witness fact (value.read witness) := by
  unfold NativeRelationJson.decodeOperand at decoded
  simp only [bind_ok] at decoded
  rcases decoded with ⟨foundText, parsedText, decoded⟩
  rw [textParsed] at parsedText
  cases parsedText
  have meaning := operand_meaning invariant accepted
  by_cases isImmediate : text.startsWith "0x"
  · simp only [isImmediate, ↓reduceIte] at decoded meaning
    simp only [bind_ok] at decoded
    rcases decoded with ⟨number, parsed, result⟩
    have producerParsed :=
      (ScalarParserAgreement.producer_immediate_success text number).mpr parsed
    unfold operand at accepted
    simp only [isImmediate, ↓reduceIte, bind_ok] at accepted
    rcases accepted with ⟨sameNumber, sameParsed, resultFact⟩
    rw [producerParsed] at sameParsed
    cases sameParsed
    cases resultFact
    cases result
    exact ⟨by simp [Operand.read, interpret], scalar_le _, by intro _ _ tag; cases tag⟩
  · simp only [isImmediate, Bool.false_eq_true, ↓reduceIte] at decoded meaning
    simp only [bind_ok] at decoded
    rcases decoded with ⟨name, valid, result⟩
    cases result
    unfold operand at accepted
    simp only [isImmediate, Bool.false_eq_true, ↓reduceIte, bind_ok] at accepted
    rcases accepted with ⟨_, _, accepted⟩
    split at accepted
    next existing found =>
      cases accepted
      exact invariant text _ (lookup_member found)
    next => contradiction

/-- The argument wrapper preserves that same agreement for named instruction
fields. -/
theorem argument_decoded_meaning
    {hash : Hash} {inputs witness : Assignment} {state : State}
    {instruction : Lean.Json} {name : String} {fact : Fact} {value : Operand}
    (invariant : StateMeaning hash inputs witness state)
    (accepted : argument state instruction name = .ok fact)
    (decoded : NativeRelationJson.decodeOperandField instruction name = .ok value) :
    FactMeaning hash inputs witness fact (value.read witness) := by
  unfold argument stringField at accepted
  unfold NativeRelationJson.decodeOperandField at decoded
  simp only [bind_ok] at accepted decoded
  rcases accepted with ⟨text, ⟨json, parsed, textParsed⟩, accepted⟩
  rcases decoded with ⟨same, sameParsed, decoded⟩
  rw [parsed] at sameParsed
  cases sameParsed
  exact operand_decoded_meaning invariant textParsed accepted decoded

theorem nativeJson_stringField_eq (value : Lean.Json) (name : String) :
    NativeRelationJson.stringField value name = stringField value name := rfl

theorem decoded_add_arguments {raw : Lean.Json} {a b : Operand} {output : String}
    (opcodeParsed : stringField raw "op" = .ok "add")
    (decoded : NativeRelationJson.decodeInstruction raw = .ok (.add a b output)) :
    NativeRelationJson.decodeOperandField raw "a" = .ok a ∧
    NativeRelationJson.decodeOperandField raw "b" = .ok b ∧
    stringField raw "output" = .ok output := by
  unfold NativeRelationJson.decodeInstruction at decoded
  simp only [bind_ok, nativeJson_stringField_eq] at decoded
  rcases decoded with ⟨opcode, opParsed, body⟩
  have opcodeEq : opcode = "add" := Except.ok.inj (opParsed.symm.trans opcodeParsed)
  subst opcode
  simp only [bind_ok] at body
  simp [NativeRelationJson.ensure] at body
  rcases body with ⟨_, _, aDecoded, foundB, bDecoded, _, rest⟩
  rcases rest with ⟨outputParsed, _, result⟩
  simp only [Pure.pure, Except.pure] at result
  cases result
  exact ⟨aDecoded, bDecoded, outputParsed⟩

theorem decoded_mul_arguments {raw : Lean.Json} {a b : Operand} {output : String}
    (opcodeParsed : stringField raw "op" = .ok "mul")
    (decoded : NativeRelationJson.decodeInstruction raw = .ok (.mul a b output)) :
    NativeRelationJson.decodeOperandField raw "a" = .ok a ∧
    NativeRelationJson.decodeOperandField raw "b" = .ok b ∧
    stringField raw "output" = .ok output := by
  unfold NativeRelationJson.decodeInstruction at decoded
  simp only [bind_ok, nativeJson_stringField_eq] at decoded
  rcases decoded with ⟨opcode, opParsed, body⟩
  have opcodeEq : opcode = "mul" := Except.ok.inj (opParsed.symm.trans opcodeParsed)
  subst opcode
  simp only [bind_ok] at body
  simp [NativeRelationJson.ensure] at body
  rcases body with ⟨_, _, aDecoded, foundB, bDecoded, _, rest⟩
  rcases rest with ⟨outputParsed, _, result⟩
  simp only [Pure.pure, Except.pure] at result
  cases result
  exact ⟨aDecoded, bDecoded, outputParsed⟩

theorem decoded_neg_argument {raw : Lean.Json} {a : Operand} {output : String}
    (opcodeParsed : stringField raw "op" = .ok "neg")
    (decoded : NativeRelationJson.decodeInstruction raw = .ok (.neg a output)) :
    NativeRelationJson.decodeOperandField raw "a" = .ok a ∧
    stringField raw "output" = .ok output := by
  unfold NativeRelationJson.decodeInstruction at decoded
  simp only [bind_ok, nativeJson_stringField_eq] at decoded
  rcases decoded with ⟨opcode, opParsed, body⟩
  have opcodeEq : opcode = "neg" := Except.ok.inj (opParsed.symm.trans opcodeParsed)
  subst opcode
  simp only [bind_ok] at body
  simp [NativeRelationJson.ensure] at body
  rcases body with ⟨_, _, aDecoded, rest⟩
  rcases rest with ⟨_, outputParsed, _, result⟩
  simp only [Pure.pure, Except.pure] at result
  cases result
  exact ⟨aDecoded, outputParsed⟩

theorem decoded_not_argument {raw : Lean.Json} {a : Operand} {output : String}
    (opcodeParsed : stringField raw "op" = .ok "not")
    (decoded : NativeRelationJson.decodeInstruction raw = .ok (.not a output)) :
    NativeRelationJson.decodeOperandField raw "a" = .ok a ∧
    stringField raw "output" = .ok output := by
  unfold NativeRelationJson.decodeInstruction at decoded
  simp only [bind_ok, nativeJson_stringField_eq] at decoded
  rcases decoded with ⟨opcode, opParsed, body⟩
  have opcodeEq : opcode = "not" := Except.ok.inj (opParsed.symm.trans opcodeParsed)
  subst opcode
  simp only [bind_ok] at body
  simp [NativeRelationJson.ensure] at body
  rcases body with ⟨_, _, aDecoded, rest⟩
  rcases rest with ⟨_, outputParsed, _, result⟩
  simp only [Pure.pure, Except.pure] at result
  cases result
  exact ⟨aDecoded, outputParsed⟩

/-- The ordinary public/private input fact has a scalar meaning exactly when
the satisfying witness agrees with the declared input assignment. -/
theorem input_fact_meaning {hash : Hash} {inputs witness : Assignment}
    {identifier : String} (inputAgreement : witness identifier = inputs identifier) :
    FactMeaning hash inputs witness
      ({term := .input identifier, maximum := Field.modulus - 1} : Fact)
      (witness identifier) := by
  refine ⟨?_, ?_, ?_⟩
  · rw [inputAgreement]
    exact interpret_input hash inputs identifier
  · change (witness identifier).val ≤ Field.modulus - 1
    have canonical := (witness identifier).isLt
    omega
  · intro _ _ tag
    cases tag

/-- A producer `define` step extends the meaning invariant only with a fact
whose partial interpretation has already succeeded. -/
theorem define_meaning {hash : Hash} {inputs witness : Assignment} {state next : State}
    {identifier : String} {fact : Fact}
    (invariant : StateMeaning hash inputs witness state)
    (meaning : FactMeaning hash inputs witness fact (witness identifier))
    (accepted : define state identifier fact = .ok next) :
    StateMeaning hash inputs witness next := by
  unfold define at accepted
  simp only [bind_ok] at accepted
  rcases accepted with ⟨_, _, _, fresh, result⟩
  cases result
  intro name found member
  simp only [List.mem_append, List.mem_singleton, Prod.mk.injEq] at member
  rcases member with member | ⟨sameName, sameFact⟩
  · exact invariant name found member
  · subst name
    subst found
    exact meaning

/-- This is the semantic step used by the validator's input branch: the
checked input fact is inserted by the real producer definition function. -/
theorem define_input_meaning {hash : Hash} {inputs witness : Assignment}
    {state next : State} {identifier : String}
    (invariant : StateMeaning hash inputs witness state)
    (inputAgreement : witness identifier = inputs identifier)
    (accepted : define state identifier
      ({term := .input identifier, maximum := Field.modulus - 1} : Fact) = .ok next) :
    StateMeaning hash inputs witness next := by
  exact define_meaning invariant (input_fact_meaning inputAgreement) accepted

/-- The actual public-input reducer arm preserves scalar meaning. Its only
source assumption is agreement for the required public input. -/
theorem public_input_step_meaning {hash : Hash} {inputs witness : Assignment}
    {expected : Expected} {state next : State} {raw : Lean.Json}
    {requirement : InputRequirement}
    (invariant : StateMeaning hash inputs witness state)
    (selected : expected.inputs[state.inputCount]? = some requirement)
    (nonforeignInput : requirement.ty.isForeign = false)
    (unguarded : requirement.activityGuard = none)
    (inputAgreement : witness requirement.identifier = inputs requirement.identifier)
    (opcodeParsed : stringField raw "op" = .ok "public_input")
    (accepted : validateInstruction expected state raw = .ok next) :
    StateMeaning hash inputs witness next := by
  unfold validateInstruction at accepted
  simp only [bind_ok] at accepted
  rcases accepted with ⟨opcode, op, descriptor, registry, _, fields, accepted⟩
  have opcodeEq : opcode = "public_input" := Except.ok.inj (op.symm.trans opcodeParsed)
  simp only [opcodeEq, selected] at accepted
  split at accepted
  · simp_all [Ty.isForeign]
  ·
    simp only [unguarded] at accepted
    simp only [bind_ok] at accepted
    rcases accepted with ⟨typeJson, typeParsed, _, typeChecked, valueType, valueParsed,
      guardJson, guardParsed, _, guardChecked, output, outputParsed, _, schema,
      definedState, defined, result⟩
    cases valueParsed
    have outputEq : output = requirement.identifier := eq_of_beq
      (Bool.and_eq_true_iff.mp (ensure_ok.mp schema)).1
    have inputEq : witness output = inputs output := by
      rw [outputEq]
      exact inputAgreement
    let nextState : State := { definedState with inputCount := definedState.inputCount + 1 }
    have nextEq : nextState = next := by
      change Except.ok nextState = .ok next at result
      exact Except.ok.inj result
    subst next
    change StateMeaning hash inputs witness definedState
    exact define_meaning invariant (input_fact_meaning inputEq) defined

/-- A validated private input installs its source term for every witness that
matches the externally supplied private transcript value. -/
theorem private_input_step_meaning {hash : Hash} {inputs witness : Assignment}
    {expected : Expected} {state next : State} {raw : Lean.Json}
    {requirement : InputRequirement}
    (invariant : StateMeaning hash inputs witness state)
    (selected : expected.inputs[state.inputCount]? = some requirement)
    (nonforeignInput : requirement.ty.isForeign = false)
    (unguarded : requirement.activityGuard = none)
    (inputAgreement : witness requirement.identifier = inputs requirement.identifier)
    (opcodeParsed : stringField raw "op" = .ok "private_input")
    (accepted : validateInstruction expected state raw = .ok next) :
    StateMeaning hash inputs witness next := by
  unfold validateInstruction at accepted
  simp only [bind_ok] at accepted
  rcases accepted with ⟨opcode, op, descriptor, registry, _, fields, accepted⟩
  have opcodeEq : opcode = "private_input" := Except.ok.inj (op.symm.trans opcodeParsed)
  simp only [opcodeEq, selected] at accepted
  split at accepted
  · simp_all [Ty.isForeign]
  ·
    simp only [unguarded] at accepted
    simp only [bind_ok] at accepted
    rcases accepted with ⟨typeJson, typeParsed, _, typeChecked, valueType, valueParsed,
      guardJson, guardParsed, _, guardChecked, output, outputParsed, _, schema,
      definedState, defined, result⟩
    cases valueParsed
    have outputEq : output = requirement.identifier := eq_of_beq
      (Bool.and_eq_true_iff.mp (ensure_ok.mp schema)).1
    have inputEq : witness output = inputs output := by
      rw [outputEq]
      exact inputAgreement
    let nextState : State := { definedState with inputCount := definedState.inputCount + 1 }
    have nextEq : nextState = next := by
      change Except.ok nextState = .ok next at result
      exact Except.ok.inj result
    subst next
    change StateMeaning hash inputs witness definedState
    exact define_meaning invariant (input_fact_meaning inputEq) defined

/-- A conditional source-bound ledger input installs the same input term as an
unconditional one. The producer separately checks that its declared guard is
the already-defined Boolean term selected by the source. -/
theorem guarded_public_input_step_meaning {hash : Hash} {inputs witness : Assignment}
    {expected : Expected} {state next : State} {raw : Lean.Json}
    {requirement : InputRequirement} {guardTerm : Term}
    (invariant : StateMeaning hash inputs witness state)
    (selected : expected.inputs[state.inputCount]? = some requirement)
    (nonforeignInput : requirement.ty.isForeign = false)
    (guarded : requirement.activityGuard = some guardTerm)
    (inputAgreement : witness requirement.identifier = inputs requirement.identifier)
    (opcodeParsed : stringField raw "op" = .ok "public_input")
    (accepted : validateInstruction expected state raw = .ok next) :
    StateMeaning hash inputs witness next := by
  unfold validateInstruction at accepted
  simp only [bind_ok] at accepted
  rcases accepted with ⟨opcode, op, descriptor, registry, _, fields, accepted⟩
  have opcodeEq : opcode = "public_input" := Except.ok.inj (op.symm.trans opcodeParsed)
  simp only [opcodeEq, selected] at accepted
  split at accepted
  · simp_all [Ty.isForeign]
  · simp only [guarded] at accepted
    simp only [bind_ok] at accepted
    rcases accepted with ⟨typeJson, typeParsed, _, typeChecked, valueType, valueParsed,
      _, _, guardJson, guardParsed, _, guardChecked, _, _, _, _, output, outputParsed,
      _, schema, definedState, defined, result⟩
    cases valueParsed
    have outputEq : output = requirement.identifier := eq_of_beq
      (Bool.and_eq_true_iff.mp (ensure_ok.mp schema)).1
    have inputEq : witness output = inputs output := by
      rw [outputEq]
      exact inputAgreement
    let nextState : State := { definedState with inputCount := definedState.inputCount + 1 }
    have nextEq : nextState = next := by
      change Except.ok nextState = .ok next at result
      exact Except.ok.inj result
    subst next
    change StateMeaning hash inputs witness definedState
    exact define_meaning invariant (input_fact_meaning inputEq) defined

theorem combine_meaning {hash : Hash} {inputs witness : Assignment}
    {term : Term} {maximum : Nat} {children : List Fact} {fact : Fact}
    {value : Scalar}
    (accepted : combine term maximum children = .ok fact)
    (meaning : interpret hash inputs term = some value)
    (bound : value.val ≤ maximum) :
    FactMeaning hash inputs witness fact value := by
  unfold combine at accepted
  dsimp [Backend.Native.ensure] at accepted
  split at accepted
  · simp only [Pure.pure, Except.pure] at accepted
    cases accepted
    refine ⟨meaning, bound, ?_⟩
    intro _ _ tag
    cases tag
  · contradiction

theorem defineResult_meaning {hash : Hash} {inputs witness : Assignment}
    {state next : State} {instruction : Lean.Json} {fact : Fact}
    (invariant : StateMeaning hash inputs witness state)
    (meaning : ∀ identifier, stringField instruction "output" = .ok identifier →
      FactMeaning hash inputs witness fact (witness identifier))
    (accepted : defineResult state instruction fact = .ok next) :
    StateMeaning hash inputs witness next := by
  unfold defineResult at accepted
  simp only [bind_ok] at accepted
  rcases accepted with ⟨identifier, parsed, accepted⟩
  exact define_meaning invariant (meaning identifier parsed) accepted

theorem modular_add_bound (left right : Scalar) (leftMaximum rightMaximum : Nat)
    (leftBound : left.val ≤ leftMaximum) (rightBound : right.val ≤ rightMaximum) :
    (scalar (left.val + right.val)).val ≤
      if leftMaximum + rightMaximum < Field.modulus then leftMaximum + rightMaximum
      else Field.modulus - 1 := by
  split
  · exact Nat.le_trans (scalar_le _) (Nat.add_le_add leftBound rightBound)
  · have canonical := (scalar (left.val + right.val)).isLt
    omega

theorem modular_mul_bound (left right : Scalar) (leftMaximum rightMaximum : Nat)
    (leftBound : left.val ≤ leftMaximum) (rightBound : right.val ≤ rightMaximum) :
    (scalar (left.val * right.val)).val ≤
      if leftMaximum * rightMaximum < Field.modulus then leftMaximum * rightMaximum
      else Field.modulus - 1 := by
  split
  · exact Nat.le_trans (scalar_le _) (Nat.mul_le_mul leftBound rightBound)
  · have canonical := (scalar (left.val * right.val)).isLt
    omega

/-- The accepted producer reducer for native addition uses the same facts and
bound passed to `combine`, then defines its output with `defineResult`. -/
theorem accepted_native_add_define
    {expected : Expected} {state next : State} {raw : Lean.Json}
    {left right fact : Fact}
    (opcodeParsed : stringField raw "op" = .ok "add")
    (leftAccepted : argument state raw "a" = .ok left)
    (rightAccepted : argument state raw "b" = .ok right)
    (leftNative : left.valueType = .native) (rightNative : right.valueType = .native)
    (combined : combine (.binary "add" left.term right.term)
      (if left.maximum + right.maximum < Field.modulus then left.maximum + right.maximum
        else Field.modulus - 1) [left, right] = .ok fact)
    (accepted : validateInstruction expected state raw = .ok next) :
    defineResult state raw fact = .ok next := by
  unfold validateInstruction at accepted
  simp only [bind_ok] at accepted
  rcases accepted with ⟨opcode, op, descriptor, support, fields, accepted⟩
  have opcodeEq : opcode = "add" := Except.ok.inj (op.symm.trans opcodeParsed)
  subst opcode
  simp only [bind_ok] at accepted
  simp_all [Backend.Native.ensure]
  have notPoint : (NativeValueType.native == NativeValueType.jubjubPoint) = false := by decide
  rw [notPoint] at accepted
  rcases accepted with ⟨fieldsAccepted, sameTypeAccepted, reducerAccepted⟩
  change (do
    let _ ← Backend.Native.ensure (left.valueType == NativeValueType.native)
      "native instruction operand must have Native type"
    let _ ← Backend.Native.ensure (right.valueType == NativeValueType.native)
      "native instruction operand must have Native type"
    let acceptedFact ← (Except.ok fact : Except String Fact)
    defineResult state raw acceptedFact) = .ok next at reducerAccepted
  simp [leftNative, rightNative, Backend.Native.ensure] at reducerAccepted
  exact reducerAccepted

theorem accepted_native_mul_define
    {expected : Expected} {state next : State} {raw : Lean.Json}
    {left right fact : Fact}
    (opcodeParsed : stringField raw "op" = .ok "mul")
    (leftAccepted : argument state raw "a" = .ok left)
    (rightAccepted : argument state raw "b" = .ok right)
    (leftNative : left.valueType = .native) (rightNative : right.valueType = .native)
    (combined : combine (.binary "mul" left.term right.term)
      (if left.maximum * right.maximum < Field.modulus then left.maximum * right.maximum
        else Field.modulus - 1) [left, right] = .ok fact)
    (accepted : validateInstruction expected state raw = .ok next) :
    defineResult state raw fact = .ok next := by
  unfold validateInstruction at accepted
  simp only [bind_ok] at accepted
  rcases accepted with ⟨opcode, op, descriptor, support, fields, accepted⟩
  have opcodeEq : opcode = "mul" := Except.ok.inj (op.symm.trans opcodeParsed)
  subst opcode
  simp only [bind_ok] at accepted
  simp_all [Backend.Native.ensure]
  rcases accepted with ⟨_, reducer⟩
  change (do
    let _ ← Backend.Native.ensure (left.valueType == NativeValueType.native)
      "native instruction operand must have Native type"
    let _ ← Backend.Native.ensure (right.valueType == NativeValueType.native)
      "native instruction operand must have Native type"
    let acceptedFact ← (Except.ok fact : Except String Fact)
    defineResult state raw acceptedFact) = .ok next at reducer
  simp [leftNative, rightNative, Backend.Native.ensure] at reducer
  exact reducer

theorem accepted_native_neg_define
    {expected : Expected} {state next : State} {raw : Lean.Json}
    {value fact : Fact}
    (opcodeParsed : stringField raw "op" = .ok "neg")
    (valueAccepted : argument state raw "a" = .ok value)
    (valueNative : value.valueType = .native)
    (combined : combine (.unary "neg" value.term)
      (if value.maximum == 0 then 0 else Field.modulus - 1) [value] = .ok fact)
    (accepted : validateInstruction expected state raw = .ok next) :
    defineResult state raw fact = .ok next := by
  unfold validateInstruction at accepted
  simp only [bind_ok] at accepted
  rcases accepted with ⟨opcode, op, descriptor, support, fields, accepted⟩
  have opcodeEq : opcode = "neg" := Except.ok.inj (op.symm.trans opcodeParsed)
  subst opcode
  simp only [bind_ok] at accepted
  simp_all
  rcases accepted with ⟨_, reducer⟩
  change (do
    let _ ← Backend.Native.ensure (value.valueType == NativeValueType.native)
      "native instruction operand must have Native type"
    let acceptedFact ← (Except.ok fact : Except String Fact)
    defineResult state raw acceptedFact) = .ok next at reducer
  simp [valueNative, Backend.Native.ensure] at reducer
  exact reducer

/-- Native addition preserves meanings for every accepted definition and the
matching decoded instruction relation. -/
theorem native_add_step_meaning
    {hash : Hash} {inputs witness : Assignment} {expected : Expected}
    {state next : State} {raw : Lean.Json} {output : String}
    {left right : Fact} {a b : Operand} {fact : Fact}
    (invariant : StateMeaning hash inputs witness state)
    (opcodeParsed : stringField raw "op" = .ok "add")
    (leftAccepted : argument state raw "a" = .ok left)
    (rightAccepted : argument state raw "b" = .ok right)
    (leftNative : left.valueType = .native) (rightNative : right.valueType = .native)
    (decoded : NativeRelationJson.decodeInstruction raw = .ok (.add a b output))
    (holds : Instruction.Holds hash witness (.add a b output))
    (combined : combine (.binary "add" left.term right.term)
      (if left.maximum + right.maximum < Field.modulus then left.maximum + right.maximum
        else Field.modulus - 1) [left, right] = .ok fact)
    (accepted : validateInstruction expected state raw = .ok next) :
    StateMeaning hash inputs witness next := by
  have decodedFields := decoded_add_arguments opcodeParsed decoded
  have leftMeaning := argument_decoded_meaning invariant leftAccepted decodedFields.1
  have rightMeaning := argument_decoded_meaning invariant rightAccepted decodedFields.2.1
  have holdsEquation : witness output = scalar ((a.read witness).val + (b.read witness).val) := by
    simpa [Instruction.Holds] using holds
  have resultMeaning : interpret hash inputs (.binary "add" left.term right.term) =
      some (witness output) := by
    simp [interpret, leftMeaning.term, rightMeaning.term, holdsEquation]
  have resultBound : (witness output).val ≤
      if left.maximum + right.maximum < Field.modulus then left.maximum + right.maximum
      else Field.modulus - 1 := by
    rw [holdsEquation]
    exact modular_add_bound (a.read witness) (b.read witness)
      left.maximum right.maximum leftMeaning.bound rightMeaning.bound
  have factMeaning : FactMeaning hash inputs witness fact (witness output) :=
    combine_meaning combined resultMeaning resultBound
  have defined := accepted_native_add_define opcodeParsed leftAccepted rightAccepted
    leftNative rightNative combined accepted
  apply defineResult_meaning invariant ?_ defined
  intro identifier parsed
  have same : identifier = output := Except.ok.inj (parsed.symm.trans decodedFields.2.2)
  subst identifier
  exact factMeaning

theorem native_mul_step_meaning
    {hash : Hash} {inputs witness : Assignment} {expected : Expected}
    {state next : State} {raw : Lean.Json} {output : String}
    {left right : Fact} {a b : Operand} {fact : Fact}
    (invariant : StateMeaning hash inputs witness state)
    (opcodeParsed : stringField raw "op" = .ok "mul")
    (leftAccepted : argument state raw "a" = .ok left)
    (rightAccepted : argument state raw "b" = .ok right)
    (leftNative : left.valueType = .native) (rightNative : right.valueType = .native)
    (decoded : NativeRelationJson.decodeInstruction raw = .ok (.mul a b output))
    (holds : Instruction.Holds hash witness (.mul a b output))
    (combined : combine (.binary "mul" left.term right.term)
      (if left.maximum * right.maximum < Field.modulus then left.maximum * right.maximum
        else Field.modulus - 1) [left, right] = .ok fact)
    (accepted : validateInstruction expected state raw = .ok next) :
    StateMeaning hash inputs witness next := by
  have decodedFields := decoded_mul_arguments opcodeParsed decoded
  have leftMeaning := argument_decoded_meaning invariant leftAccepted decodedFields.1
  have rightMeaning := argument_decoded_meaning invariant rightAccepted decodedFields.2.1
  have holdsEquation : witness output = scalar ((a.read witness).val * (b.read witness).val) := by
    simpa [Instruction.Holds] using holds
  have resultMeaning : interpret hash inputs (.binary "mul" left.term right.term) =
      some (witness output) := by
    simp [interpret, leftMeaning.term, rightMeaning.term, holdsEquation]
  have resultBound : (witness output).val ≤
      if left.maximum * right.maximum < Field.modulus then left.maximum * right.maximum
      else Field.modulus - 1 := by
    rw [holdsEquation]
    exact modular_mul_bound (a.read witness) (b.read witness)
      left.maximum right.maximum leftMeaning.bound rightMeaning.bound
  have factMeaning : FactMeaning hash inputs witness fact (witness output) :=
    combine_meaning combined resultMeaning resultBound
  have defined := accepted_native_mul_define opcodeParsed leftAccepted rightAccepted
    leftNative rightNative combined accepted
  apply defineResult_meaning invariant ?_ defined
  intro identifier parsed
  have same : identifier = output := Except.ok.inj (parsed.symm.trans decodedFields.2.2)
  subst identifier
  exact factMeaning

/-- Native negation preserves the producer's bound, including its zero-only
case, under the decoded witness equation. -/
theorem native_neg_step_meaning
    {hash : Hash} {inputs witness : Assignment} {expected : Expected}
    {state next : State} {raw : Lean.Json} {output : String}
    {value : Fact} {a : Operand} {fact : Fact}
    (invariant : StateMeaning hash inputs witness state)
    (opcodeParsed : stringField raw "op" = .ok "neg")
    (valueAccepted : argument state raw "a" = .ok value)
    (valueNative : value.valueType = .native)
    (decoded : NativeRelationJson.decodeInstruction raw = .ok (.neg a output))
    (holds : Instruction.Holds hash witness (.neg a output))
    (combined : combine (.unary "neg" value.term)
      (if value.maximum == 0 then 0 else Field.modulus - 1) [value] = .ok fact)
    (accepted : validateInstruction expected state raw = .ok next) :
    StateMeaning hash inputs witness next := by
  have decodedFields := decoded_neg_argument opcodeParsed decoded
  have valueMeaning := argument_decoded_meaning invariant valueAccepted decodedFields.1
  have holdsEquation : witness output = scalar (Field.modulus - (a.read witness).val) := by
    simpa [Instruction.Holds] using holds
  have resultMeaning : interpret hash inputs (.unary "neg" value.term) =
      some (witness output) := by
    simp [interpret, valueMeaning.term, holdsEquation]
  have resultBound : (witness output).val ≤
      if value.maximum == 0 then 0 else Field.modulus - 1 := by
    cases zeroMax : value.maximum == 0
    · have canonical := (witness output).isLt
      simp only [Bool.false_eq_true, ↓reduceIte]
      omega
    · have valueZero : (a.read witness).val = 0 := by
        have bound := valueMeaning.bound
        have maxZero : value.maximum = 0 := of_decide_eq_true zeroMax
        omega
      rw [holdsEquation]
      simp [valueZero, scalar]
  have factMeaning : FactMeaning hash inputs witness fact (witness output) :=
    combine_meaning combined resultMeaning resultBound
  have defined := accepted_native_neg_define opcodeParsed valueAccepted valueNative
    combined accepted
  apply defineResult_meaning invariant ?_ defined
  intro identifier parsed
  have same : identifier = output := Except.ok.inj (parsed.symm.trans decodedFields.2)
  subst identifier
  exact factMeaning

end Noctium.Verification.ScalarValidationMeaning
