import Noctium.Verification.ScalarStateExtensions
import Noctium.Verification.ScalarCircuit
import Noctium.Verification.ScalarAdmission
import Noctium.Verification.ScalarAllocationOutputFrame
import Noctium.Verification.ScalarExpressionArithmetic

namespace Noctium.Verification.ScalarCircuitLowering
open Lean Backend NativeRelation NativeRelationJson ScalarWitness ScalarNormalization ScalarLowering

/-- Source input admission and the actual native identifier checks establish the
initial wire/normalizer alias relation. No source constraint is assumed. -/
theorem initial_aliases (circuit : Circuit) (values : EvalEnv) (inputs : NativeRelation.Assignment)
    (hash : Hash) (admitted : CanonicalInputs circuit values inputs)
    (identifiers : ∀ input ∈ circuit.inputs, validIdentifier ("%input_" ++ input.name) = true) :
    LowerAliasAgreement hash inputs inputs (circuitAliases circuit) [] values := by
  intro name ty raw value lookup typed
  obtain ⟨canonical, term, termLookup, meaning⟩ :=
    (admitted.typedEnvironment circuit values inputs hash).aliases name ty raw value lookup typed
  obtain ⟨input, member, inputName⟩ := admitted.declared name raw (ScalarValidation.lookup_member lookup)
  have known : (circuitAliases circuit).lookup name = some (.input ("%input_" ++ name)) :=
    aliases_lookup circuit.inputs name ⟨input, member, inputName⟩
  have termIs : term = .input ("%input_" ++ name) := Option.some.inj (termLookup.symm.trans known)
  have nativeValid : validIdentifier ("%input_" ++ name) = true := by
    simpa only [inputName] using identifiers input member
  refine ⟨term, termLookup, .reference ("%input_" ++ name), ?_, ?_⟩
  · exact (ScalarInstructionEncoding.OperandEncoding.reference _ nativeValid).decode
  · simp only [termIs, interpret_input, Operand.read]

/-- A declared input is a scoped field, while its declared source type is
constrained by the following actual constrainType computation. -/
theorem emit_input (hash : Hash) (witness : NativeRelation.Assignment)
    (state : Zkir.LowerState) (meaning : LowerStateMeaning hash witness state)
    (input : Input) (valid : validIdentifier ("%input_" ++ input.name) = true) :
    LowerStateMeaning hash witness
      ((Zkir.emit (if input.visibility == .«public» then "public_input" else "private_input")
        [("guard", Json.null), ("type", toJson ("Scalar<BLS12-381>" : String)),
          ("output", toJson ("%input_" ++ input.name))]).run state).2 := by
  change LowerStateMeaning hash witness {state with instructions := state.instructions.push _}
  apply meaning.append
  · exact ScalarInstructionEncoding.decode_input _ _ valid
  · trivial
  · intro name member
    simp only [instructionIdentifiers, List.mem_singleton] at member
    subst name
    exact Or.inl ⟨input.name, rfl⟩

theorem scoped_operands (next : Nat) (texts : List String)
    (scopes : ∀ text ∈ texts, TextScope next text) :
    ∃ operands, decodeOperands (toJson texts) = .ok operands ∧
      ∀ name ∈ operands.flatMap operandIdentifiers, InScope next name := by
  have listResult : ∃ operands, texts.mapM (fun text => decodeOperand (toJson text)) = .ok operands ∧
      ∀ name ∈ operands.flatMap operandIdentifiers, InScope next name := by
    induction texts with
    | nil => exact ⟨[], rfl, by simp⟩
    | cons text texts ih =>
      obtain ⟨operand, parsed, scope⟩ := scopes text (by simp)
      obtain ⟨operands, tailParsed, tailScope⟩ := ih (by intro value member; exact scopes value (by simp [member]))
      refine ⟨operand :: operands, ?_, ?_⟩
      · simp only [List.mapM_cons, parsed, tailParsed, Bind.bind, Except.bind]
        rfl
      · intro name member
        simp only [List.flatMap_cons, List.mem_append] at member
        exact member.elim (scope name) (tailScope name)
  obtain ⟨operands, parsed, scope⟩ := listResult
  refine ⟨operands, ?_, scope⟩
  unfold decodeOperands
  change ((texts.toArray.map toJson).toList.mapM decodeOperand) = .ok operands
  simpa only [Array.toList_map, List.toList_toArray, List.mapM_map, Function.comp_def] using parsed

theorem emit_impact (hash : Hash) (witness : NativeRelation.Assignment)
    (state : Zkir.LowerState) (meaning : LowerStateMeaning hash witness state)
    (texts : List String) (scopes : ∀ text ∈ texts, TextScope state.next text) :
    LowerStateMeaning hash witness ((Zkir.bindPublic texts).run state).2 := by
  obtain ⟨operands, parsed, scope⟩ := scoped_operands state.next texts scopes
  change LowerStateMeaning hash witness {state with instructions := state.instructions.push _}
  exact LowerStateMeaning.append hash witness state meaning _ _ (ScalarInstructionEncoding.decode_impact_instruction parsed) rfl
    (by simpa only [instructionIdentifiers, operandIdentifiers, List.nil_append] using scope)

theorem emit_output (hash : Hash) (witness : NativeRelation.Assignment)
    (state : Zkir.LowerState) (meaning : LowerStateMeaning hash witness state)
    (texts : List String) (scopes : ∀ text ∈ texts, TextScope state.next text) :
    LowerStateMeaning hash witness ((Zkir.emit "output" [("vals", toJson texts)]).run state).2 := by
  obtain ⟨operands, parsed, scope⟩ := scoped_operands state.next texts scopes
  change LowerStateMeaning hash witness {state with instructions := state.instructions.push _}
  exact LowerStateMeaning.append hash witness state meaning _ _ (ScalarInstructionEncoding.decode_output_instruction parsed) True.intro scope

theorem emit_assert (hash : Hash) (witness : NativeRelation.Assignment)
    (state : Zkir.LowerState) (meaning : LowerStateMeaning hash witness state)
    (text : String) (scope : TextScope state.next text)
    (value : ∃ operand, decodeOperand (toJson text) = .ok operand ∧ operand.read witness = one) :
    LowerStateMeaning hash witness ((Zkir.emit "assert" [("cond", toJson text)]).run state).2 := by
  obtain ⟨operand, parsed, value⟩ := value
  obtain ⟨found, decoded, identifiers⟩ := scope
  rw [parsed] at decoded
  cases decoded
  change LowerStateMeaning hash witness {state with instructions := state.instructions.push _}
  apply LowerStateMeaning.append hash witness state meaning _ _ (ScalarInstructionEncoding.decode_assert_instruction parsed)
  · change operand.read witness ≠ zero
    rw [value]
    decide
  · exact identifiers

structure PrefixExtension (hash : Hash) (beforeWitness : NativeRelation.Assignment)
    (before after : Zkir.LowerState) where
  witness : NativeRelation.Assignment
  meaning : LowerStateMeaning hash witness after
  aliases : after.aliases = before.aliases
  frame : ∀ name, InScope before.next name → witness name = beforeWitness name

def InputFrame (inputs witness : NativeRelation.Assignment) : Prop :=
  ∀ name, witness ("%input_" ++ name) = inputs ("%input_" ++ name)

def Completes (hash : Hash) (inputs : NativeRelation.Assignment) (operation : StateM Zkir.LowerState α) : Prop :=
  ∀ witness state, LowerStateMeaning hash witness state → InputFrame inputs witness → state.aliases = [] →
    (operation.run state).2.next ≤ Native.maxInstructions * Native.maxVectorLength →
    Nonempty (PrefixExtension hash witness state (operation.run state).2)

theorem completes_pure (hash : Hash) (inputs : NativeRelation.Assignment) (value : α) : Completes hash inputs (pure value) := by
  intro witness state meaning inputFrame aliases budget
  exact ⟨{witness, meaning, aliases := rfl, frame := by intro name _; rfl}⟩

theorem completes_bind (hash : Hash) (inputs : NativeRelation.Assignment) (first : StateM Zkir.LowerState α)
    (next : α → StateM Zkir.LowerState β)
    (firstFrame : ScalarAllocation.PreservesFrame first)
    (nextFrame : ∀ value, ScalarAllocation.PreservesFrame (next value))
    (firstComplete : Completes hash inputs first) (nextComplete : ∀ value, Completes hash inputs (next value)) :
    Completes hash inputs (first >>= next) := by
  intro witness state meaning inputFrame aliases budget
  have runBudget : ((next (first.run state).1).run (first.run state).2).2.next ≤ Native.maxInstructions * Native.maxVectorLength := budget
  have middleBudget : (first.run state).2.next ≤ Native.maxInstructions * Native.maxVectorLength :=
    Nat.le_trans (nextFrame _ _).next runBudget
  obtain ⟨left⟩ := firstComplete witness state meaning inputFrame aliases middleBudget
  have nextInput : InputFrame inputs left.witness := fun name =>
    (left.frame _ (Or.inl ⟨name, rfl⟩)).trans (inputFrame name)
  obtain ⟨right⟩ := nextComplete _ left.witness _ left.meaning nextInput (left.aliases.trans aliases) runBudget
  refine ⟨{witness := right.witness, meaning := right.meaning, aliases := right.aliases.trans left.aliases, frame := ?_}⟩
  intro name scope
  exact (right.frame name (InScope.mono (firstFrame state).next scope)).trans (left.frame name scope)

theorem state_ite_bind (condition : Prop) [Decidable condition]
    (yes no : StateM Zkir.LowerState α) (next : α → StateM Zkir.LowerState β) :
    ((if condition then yes else no) >>= next) =
      (if condition then yes >>= next else no >>= next) := by split <;> rfl

theorem completes_forIn (hash : Hash) (inputs : NativeRelation.Assignment) (items : List α)
    (initial : β) (body : α → StateM Zkir.LowerState Unit)
    (frames : ∀ item, ScalarAllocation.PreservesFrame (body item))
    (complete : ∀ item ∈ items, Completes hash inputs (body item)) :
    Completes hash inputs (forIn items initial (fun item _ => do body item; pure (.yield initial))) := by
  induction items with
  | nil => exact completes_pure hash inputs initial
  | cons item items ih =>
    rw [List.forIn_cons]
    simp only [bind_assoc, pure_bind]
    change Completes hash inputs (body item >>= fun _ => forIn items initial (fun item _ => do body item; pure (.yield initial)))
    apply completes_bind hash inputs _ _ (frames item)
    · intro value
      exact ScalarAllocation.forIn_preserves items initial _ (fun item _ =>
        ScalarAllocation.bind_preserves _ _ (frames item) (fun _ => ScalarAllocation.pure_preserves _))
    · exact complete item (by simp)
    · intro value
      exact ih (by intro item member; exact complete item (by simp [member]))

theorem constrain_type_complete (hash : Hash) (inputs witness : NativeRelation.Assignment)
    (state : Zkir.LowerState) (ty : Ty) (value : ty.Denote) (text : String) (term : Native.Term)
    (canonical : Canonical ty value) (termValue : interpret hash inputs term = scalar (number ty value))
    (meaning : LowerStateMeaning hash witness state)
    (operand : OperandMeaning hash inputs witness text term) (scope : TextScope state.next text)
    (budget : ((Zkir.constrainType ty text).run state).2.next ≤ Native.maxInstructions * Native.maxVectorLength) :
    Nonempty (PrefixExtension hash witness state ((Zkir.constrainType ty text).run state).2) := by
  cases ty with
  | native => exact ⟨{witness, meaning, aliases := rfl, frame := by intro name _; rfl}⟩
  | bool =>
    obtain ⟨native, parsed, read⟩ := operand
    obtain ⟨found, foundParsed, identifiers⟩ := scope
    rw [parsed] at foundParsed
    cases foundParsed
    have boolean : native.read witness = zero ∨ native.read witness = one := by
      rw [read, termValue]
      cases value <;> simp [number, scalar_zero, scalar_one]
    refine ⟨{witness, meaning := ?_, aliases := rfl, frame := by intro name _; rfl}⟩
    change LowerStateMeaning hash witness {state with instructions := state.instructions.push _}
    exact LowerStateMeaning.append hash witness state meaning _ _
      (ScalarInstructionEncoding.decode_boolean_instruction parsed) boolean identifiers
  | uint maximum =>
    have range : (interpret hash inputs term).val ≤ maximum := by
      rw [termValue]
      change number (.uint maximum) value % Field.modulus ≤ maximum
      rw [Nat.mod_eq_of_lt canonical.1]
      exact canonical.2.2
    obtain ⟨result⟩ := ScalarExpressionArithmetic.constrainUnsigned_step hash inputs witness state
      maximum text term meaning operand scope range canonical.2.1 budget
    have stateEqual := congrArg Prod.snd result.run
    change ((Zkir.constrainType (.uint maximum) text).run state).2 = result.finalState at stateEqual
    exact ⟨{witness := result.finalWitness, meaning := by rw [stateEqual]; exact result.stateMeaning, aliases := by rw [stateEqual]; exact result.aliasesPreserved, frame := result.frame}⟩

theorem completes_emit_input (hash : Hash) (inputs : NativeRelation.Assignment) (input : Input)
    (valid : validIdentifier ("%input_" ++ input.name) = true) :
    Completes hash inputs (Zkir.emit (if input.visibility == .«public» then "public_input" else "private_input")
      [("guard", Json.null), ("type", toJson ("Scalar<BLS12-381>" : String)),
        ("output", toJson ("%input_" ++ input.name))]) := by
  intro witness state meaning inputFrame aliases budget
  exact ⟨{witness, meaning := emit_input hash witness state meaning input valid, aliases := rfl, frame := by intro name _; rfl}⟩

theorem completes_input_type (hash : Hash) (inputs : NativeRelation.Assignment) (input : Input)
    (value : input.ty.Denote) (canonical : Canonical input.ty value)
    (binding : inputs ("%input_" ++ input.name) = scalar (number input.ty value))
    (valid : validIdentifier ("%input_" ++ input.name) = true) :
    Completes hash inputs (Zkir.constrainType input.ty ("%input_" ++ input.name)) := by
  intro witness state meaning inputFrame aliases budget
  have decoded := (ScalarInstructionEncoding.OperandEncoding.reference _ valid).decode
  apply constrain_type_complete hash inputs witness state input.ty value _ (.input ("%input_" ++ input.name)) canonical
  · simpa only [interpret_input] using binding
  · exact meaning
  · exact ⟨_, decoded, by simpa only [Operand.read, interpret_input] using inputFrame input.name⟩
  · exact ⟨_, decoded, by intro name member; simp only [operandIdentifiers, List.mem_singleton] at member; subst name; exact Or.inl ⟨input.name, rfl⟩⟩
  · exact budget

theorem completes_input_impact (hash : Hash) (inputs : NativeRelation.Assignment) (input : Input)
    (valid : validIdentifier ("%input_" ++ input.name) = true) :
    Completes hash inputs (if input.visibility == .«public» then Zkir.bindPublic ["%input_" ++ input.name] else pure ()) := by
  split
  · intro witness state meaning inputFrame aliases budget
    have scopedInput : TextScope state.next ("%input_" ++ input.name) :=
      ⟨_, (ScalarInstructionEncoding.OperandEncoding.reference _ valid).decode,
        by intro name member; simp only [operandIdentifiers, List.mem_singleton] at member; subst name; exact Or.inl ⟨input.name, rfl⟩⟩
    exact ⟨{witness, meaning := emit_impact hash witness state meaning _ (by intro text member; simpa only [List.mem_singleton.mp member] using scopedInput), aliases := rfl, frame := by intro name _; rfl}⟩
  · exact completes_pure hash inputs ()

theorem completes_input (hash : Hash) (inputs : NativeRelation.Assignment) (input : Input)
    (value : input.ty.Denote) (canonical : Canonical input.ty value)
    (binding : inputs ("%input_" ++ input.name) = scalar (number input.ty value))
    (valid : validIdentifier ("%input_" ++ input.name) = true) :
    Completes hash inputs (do
      let output := "%input_" ++ input.name
      Zkir.emit (if input.visibility == .«public» then "public_input" else "private_input")
        [("guard", Json.null), ("type", toJson ("Scalar<BLS12-381>" : String)), ("output", toJson output)]
      Zkir.constrainType input.ty output
      if input.visibility == .«public» then Zkir.bindPublic [output]) := by
  apply completes_bind hash inputs _ _ (ScalarAllocation.emit_preserves _ _)
  · intro ignored
    apply ScalarAllocation.bind_preserves _ _ (ScalarAllocation.constrainType_preserves _ _)
    intro ignored
    split
    · exact ScalarAllocation.bindPublic_preserves _
    · exact ScalarAllocation.pure_preserves _
  · exact completes_emit_input hash inputs input valid
  · intro ignored
    apply completes_bind hash inputs _ _ (ScalarAllocation.constrainType_preserves _ _)
    · intro ignored
      split
      · exact ScalarAllocation.bindPublic_preserves _
      · exact ScalarAllocation.pure_preserves _
    · exact completes_input_type hash inputs input value canonical binding valid
    · intro ignored
      exact completes_input_impact hash inputs input valid

theorem current_aliases (hash : Hash) (inputs witness : NativeRelation.Assignment)
    (circuit : Circuit) (values : EvalEnv) (state : Zkir.LowerState)
    (admitted : CanonicalInputs circuit values inputs)
    (identifiers : ∀ input ∈ circuit.inputs, validIdentifier ("%input_" ++ input.name) = true)
    (inputFrame : InputFrame inputs witness) (aliases : state.aliases = []) :
    LowerAliasAgreement hash inputs witness (circuitAliases circuit) state.aliases values := by
  rw [aliases]
  apply LowerAliasAgreement.of_frame hash inputs inputs witness 0 (circuitAliases circuit) [] values
    (initial_aliases circuit values inputs hash admitted identifiers)
  · simp
  · intro name scope
    rcases scope with ⟨source, rfl⟩ | ⟨index, impossible, _⟩
    · exact inputFrame source
    · omega

theorem completes_condition (ctx : EvalContext) (hash : Hash) (implementation : HashAgreement ctx hash)
    (complete : ∀ ty (expression : Expr ty), ExprComplete expression)
    (circuit : Circuit) (values : EvalEnv) (inputs : NativeRelation.Assignment)
    (admitted : CanonicalInputs circuit values inputs)
    (identifiers : ∀ input ∈ circuit.inputs, validIdentifier ("%input_" ++ input.name) = true)
    (condition : Expr .bool)
    (valid : condition.validate {poseidon2 := true} (circuit.inputs.map (fun input => (input.name, input.ty))) = .ok ())
    (success : condition.eval ctx values = .ok true) :
    Completes hash inputs (do let text ← Zkir.lowerExpr condition; Zkir.emit "assert" [("cond", toJson text)]) := by
  intro witness state meaning inputFrame aliases budget
  have exprBudget : ((Zkir.lowerExpr condition).run state).2.next ≤ Native.maxInstructions * Native.maxVectorLength := budget
  obtain ⟨result⟩ := complete _ condition ctx hash implementation inputs witness state
    (circuitAliases circuit) values _ true valid success
    (admitted.typedEnvironment circuit values inputs hash).aliases
    (current_aliases hash inputs witness circuit values state admitted identifiers inputFrame aliases) meaning exprBudget
  have readOne : ∃ operand, decodeOperand (toJson result.text) = .ok operand ∧ operand.read result.finalWitness = one := by
    obtain ⟨operand, parsed, read⟩ := result.operandMeaning
    exact ⟨operand, parsed, read.trans (by simpa [number, scalar_one] using result.represents.2.2)⟩
  have actualState : ((do let text ← Zkir.lowerExpr condition; Zkir.emit "assert" [("cond", toJson text)]).run state).2 =
      ((Zkir.emit "assert" [("cond", toJson result.text)]).run result.finalState).2 := by
    change ((Zkir.emit "assert" [("cond", toJson ((Zkir.lowerExpr condition).run state).1)]).run
      ((Zkir.lowerExpr condition).run state).2).2 = _
    rw [result.run]
  refine ⟨{witness := result.finalWitness, meaning := ?_, aliases := ?_, frame := result.frame}⟩
  · rw [actualState]
    exact emit_assert hash result.finalWitness result.finalState result.stateMeaning result.text result.textScope readOne
  · rw [actualState]
    exact result.aliasesPreserved

theorem constraints_members (ctx : EvalContext) (circuit : Circuit) (values : EvalEnv)
    (valid : validateConstraints {poseidon2 := true} (circuit.inputs.map (fun input => (input.name, input.ty))) circuit.span circuit.constraints = .ok ())
    (success : runConstraints ctx values circuit.constraints = .ok ()) :
    ∀ condition ∈ circuit.constraints,
      condition.validate {poseidon2 := true} (circuit.inputs.map (fun input => (input.name, input.ty))) = .ok () ∧
      condition.eval ctx values = .ok true := by
  generalize circuit.constraints = conditions at *
  induction conditions with
  | nil => simp
  | cons condition rest ih =>
    cases checked : condition.validate {poseidon2 := true} (circuit.inputs.map (fun input => (input.name, input.ty))) with
    | error message => simp [validateConstraints, checked] at valid
    | ok checkedUnit =>
      cases checkedUnit
      simp only [validateConstraints, checked] at valid
      cases evaluated : condition.eval ctx values with
      | error message => simp [runConstraints, evaluated] at success
      | ok value =>
        cases value
        · simp [runConstraints, evaluated] at success
        · simp only [runConstraints, evaluated] at success
          intro found member
          rcases List.mem_cons.mp member with rfl | member
          · exact ⟨checked, evaluated⟩
          · exact ih valid success found member

theorem output_eval_members (ctx : EvalContext) (values : EvalEnv) (outputs : List Output) (result : EvalEnv)
    (success : outputs.mapM (evalOutput ctx values) = .ok result) :
    ∀ output ∈ outputs, ∃ value, output.value.eval ctx values = .ok value := by
  induction outputs generalizing result with
  | nil => simp
  | cons output outputs ih =>
    cases evaluated : output.value.eval ctx values with
    | error message => simp [List.mapM_cons, evalOutput, evaluated, Bind.bind, Except.bind] at success
    | ok value =>
      cases tail : outputs.mapM (evalOutput ctx values) with
      | error message => simp [List.mapM_cons, evalOutput, evaluated, tail, Bind.bind, Except.bind, pure, Except.pure] at success
      | ok tailResult =>
        intro found member
        rcases List.mem_cons.mp member with rfl | member
        · exact ⟨value, evaluated⟩
        · exact ih tailResult tail found member

theorem outputs_complete (ctx : EvalContext) (hash : Hash) (implementation : HashAgreement ctx hash)
    (complete : ∀ ty (expression : Expr ty), ExprComplete expression)
    (circuit : Circuit) (values : EvalEnv) (inputs : NativeRelation.Assignment)
    (admitted : CanonicalInputs circuit values inputs)
    (identifiers : ∀ input ∈ circuit.inputs, validIdentifier ("%input_" ++ input.name) = true)
    (outputs : List Output)
    (valid : ∀ output ∈ outputs, output.value.validate {poseidon2 := true}
      (circuit.inputs.map (fun input => (input.name, input.ty))) = .ok ())
    (success : ∀ output ∈ outputs, ∃ value, output.value.eval ctx values = .ok value)
    (witness : NativeRelation.Assignment) (state : Zkir.LowerState) (texts : List String)
    (meaning : LowerStateMeaning hash witness state) (inputFrame : InputFrame inputs witness)
    (aliases : state.aliases = []) (scopes : ∀ text ∈ texts, TextScope state.next text)
    (budget : ((forIn outputs texts (fun (output : Output) (accumulated : List String) => do
      let text ← Zkir.lowerExpr output.value
      pure (.yield (accumulated ++ [text])))).run state).2.next ≤ Native.maxInstructions * Native.maxVectorLength) :
    Nonempty (PrefixExtension hash witness state ((forIn outputs texts (fun (output : Output) (accumulated : List String) => do
      let text ← Zkir.lowerExpr output.value
      pure (.yield (accumulated ++ [text])))).run state).2) ∧
    ∀ text ∈ ((forIn outputs texts (fun (output : Output) (accumulated : List String) => do
      let text ← Zkir.lowerExpr output.value
      pure (.yield (accumulated ++ [text])))).run state).1,
      TextScope ((forIn outputs texts (fun (output : Output) (accumulated : List String) => do
        let text ← Zkir.lowerExpr output.value
        pure (.yield (accumulated ++ [text])))).run state).2.next text := by
  induction outputs generalizing witness state texts with
  | nil => exact ⟨⟨{witness, meaning, aliases := rfl, frame := by intro name _; rfl}⟩, scopes⟩
  | cons output outputs ih =>
    obtain ⟨value, evaluated⟩ := success output (by simp)
    let tail := fun accumulated => forIn outputs accumulated (fun (output : Output) (accumulated : List String) => do
      let text ← Zkir.lowerExpr output.value
      pure (.yield (accumulated ++ [text])))
    have tailFrame : ∀ accumulated, ScalarAllocation.PreservesFrame (tail accumulated) := by
      intro accumulated
      apply ScalarAllocation.forIn_preserves
      intro output accumulated
      exact ScalarAllocation.bind_preserves _ _ (ScalarAllocation.lowerExpr_preserves _) (fun _ => ScalarAllocation.pure_preserves _)
    have runEq : (forIn (output :: outputs) texts (fun (output : Output) (accumulated : List String) => do
        let text ← Zkir.lowerExpr output.value
        pure (.yield (accumulated ++ [text])))) =
        (Zkir.lowerExpr output.value >>= fun text => tail (texts ++ [text])) := by
      rw [List.forIn_cons]
      simp only [bind_assoc, pure_bind]
      rfl
    rw [runEq] at budget ⊢
    have middleBudget : ((Zkir.lowerExpr output.value).run state).2.next ≤ Native.maxInstructions * Native.maxVectorLength :=
      Nat.le_trans (tailFrame _ _).next budget
    obtain ⟨step⟩ := complete _ output.value ctx hash implementation inputs witness state (circuitAliases circuit)
      values _ value (valid output (by simp)) evaluated (admitted.typedEnvironment circuit values inputs hash).aliases
      (current_aliases hash inputs witness circuit values state admitted identifiers inputFrame aliases) meaning middleBudget
    have continuedBudget : ((tail (texts ++ [step.text])).run step.finalState).2.next ≤ Native.maxInstructions * Native.maxVectorLength := by
      change ((tail (texts ++ [((Zkir.lowerExpr output.value).run state).1])).run
        ((Zkir.lowerExpr output.value).run state).2).2.next ≤ _ at budget
      simpa only [step.run] using budget
    have nextInputs : InputFrame inputs step.finalWitness := fun name =>
      (step.frame _ (Or.inl ⟨name, rfl⟩)).trans (inputFrame name)
    have nextScopes : ∀ text ∈ texts ++ [step.text], TextScope step.finalState.next text := by
      intro text member
      rcases List.mem_append.mp member with old | new
      · have monotone := ScalarAllocation.lowerExpr_next output.value state
        rw [step.run] at monotone
        exact (scopes text old).mono monotone
      · exact List.mem_singleton.mp new ▸ step.textScope
    obtain ⟨⟨rest⟩, finalScopes⟩ := ih
      (by intro found member; exact valid found (by simp [member]))
      (by intro found member; exact success found (by simp [member]))
      step.finalWitness step.finalState (texts ++ [step.text]) step.stateMeaning nextInputs
      (step.aliasesPreserved.trans aliases) nextScopes continuedBudget
    have finalStateEq : ((Zkir.lowerExpr output.value >>= fun text => tail (texts ++ [text])).run state).2 =
        ((tail (texts ++ [step.text])).run step.finalState).2 := by
      change ((tail (texts ++ [((Zkir.lowerExpr output.value).run state).1])).run
        ((Zkir.lowerExpr output.value).run state).2).2 = _
      rw [step.run]
    constructor
    · refine ⟨{witness := rest.witness, meaning := ?_, aliases := ?_, frame := ?_}⟩
      · rw [finalStateEq]; exact rest.meaning
      · rw [finalStateEq]; exact rest.aliases.trans step.aliasesPreserved
      · intro name scope
        exact (rest.frame name (InScope.mono (by simpa only [step.run] using ScalarAllocation.lowerExpr_next output.value state) scope)).trans (step.frame name scope)
    · change ∀ text ∈ ((tail (texts ++ [((Zkir.lowerExpr output.value).run state).1])).run
        ((Zkir.lowerExpr output.value).run state).2).1, TextScope
        ((tail (texts ++ [((Zkir.lowerExpr output.value).run state).1])).run
          ((Zkir.lowerExpr output.value).run state).2).2.next text
      rw [step.run]
      exact finalScopes

theorem completes_outputs (ctx : EvalContext) (hash : Hash) (implementation : HashAgreement ctx hash)
    (complete : ∀ ty (expression : Expr ty), ExprComplete expression)
    (circuit : Circuit) (values : EvalEnv) (inputs : NativeRelation.Assignment)
    (admitted : CanonicalInputs circuit values inputs)
    (identifiers : ∀ input ∈ circuit.inputs, validIdentifier ("%input_" ++ input.name) = true)
    (valid : ∀ output ∈ circuit.outputs, output.value.validate {poseidon2 := true}
      (circuit.inputs.map (fun input => (input.name, input.ty))) = .ok ())
    (success : ∀ output ∈ circuit.outputs, ∃ value, output.value.eval ctx values = .ok value) :
    Completes hash inputs (do
      let texts ← forIn circuit.outputs ([] : List String) (fun (output : Output) accumulated => do
        let text ← Zkir.lowerExpr output.value
        pure (.yield (accumulated ++ [text])))
      if !texts.isEmpty then Zkir.bindPublic texts
      Zkir.emit "output" [("vals", toJson texts)]) := by
  intro witness state meaning inputFrame aliases budget
  let loop := forIn circuit.outputs ([] : List String) (fun (output : Output) accumulated => do
    let text ← Zkir.lowerExpr output.value
    pure (.yield (accumulated ++ [text])))
  let footer := fun (texts : List String) => do
    if !texts.isEmpty then Zkir.bindPublic texts
    Zkir.emit "output" [("vals", toJson texts)]
  have footerFrame : ∀ texts, ScalarAllocation.PreservesFrame (footer texts) := by
    intro texts
    dsimp only [footer]
    split
    · exact ScalarAllocation.bind_preserves _ _ (ScalarAllocation.bindPublic_preserves _) (fun _ => ScalarAllocation.emit_preserves _ _)
    · exact ScalarAllocation.emit_preserves _ _
  have loopBudget : (loop.run state).2.next ≤ Native.maxInstructions * Native.maxVectorLength :=
    ScalarAllocation.bind_middle_budget loop footer state footerFrame _ budget
  obtain ⟨⟨result⟩, scopes⟩ := outputs_complete ctx hash implementation complete circuit values inputs
    admitted identifiers circuit.outputs valid success witness state [] meaning inputFrame aliases (by simp) loopBudget
  have footerMeaning : LowerStateMeaning hash result.witness ((footer (loop.run state).1).run (loop.run state).2).2 := by
    dsimp only [footer]
    split
    · exact emit_output hash result.witness _ (emit_impact hash result.witness _ result.meaning _ scopes) _ scopes
    · exact emit_output hash result.witness _ result.meaning _ scopes
  refine ⟨{witness := result.witness, meaning := footerMeaning, aliases := ?_, frame := result.frame}⟩
  change ((footer (loop.run state).1).run (loop.run state).2).2.aliases = state.aliases
  dsimp only [footer]
  split <;> exact result.aliases

theorem lowerBody_complete_with_expressions (ctx : EvalContext) (hash : Hash) (implementation : HashAgreement ctx hash)
    (complete : ∀ ty (expression : Expr ty), ExprComplete expression)
    (circuit : Circuit) (values result : EvalEnv) (inputs : NativeRelation.Assignment)
    (admitted : CanonicalInputs circuit values inputs)
    (identifiers : ∀ input ∈ circuit.inputs, validIdentifier ("%input_" ++ input.name) = true)
    (validation : circuit.validate {poseidon2 := true} = .ok ())
    (success : circuit.run ctx values = .ok result) : Completes hash inputs (Zkir.lowerBody circuit) := by
  obtain ⟨constraintValidation, outputValidation⟩ := circuit_validation_parts circuit validation
  obtain ⟨constraintSuccess, outputSuccess⟩ := circuit_run_steps ctx circuit values result success
  have conditions := constraints_members ctx circuit values constraintValidation constraintSuccess
  unfold Zkir.lowerBody
  apply completes_bind hash inputs
  · apply ScalarAllocation.forIn_preserves
    intro input accumulator
    apply ScalarAllocation.bind_preserves _ _ (ScalarAllocation.emit_preserves _ _)
    intro ignored
    apply ScalarAllocation.bind_preserves _ _ (ScalarAllocation.constrainType_preserves _ _)
    intro ignored
    split
    · apply ScalarAllocation.bind_preserves _ _ (ScalarAllocation.bindPublic_preserves _)
      intro ignored
      exact ScalarAllocation.pure_preserves _
    · exact ScalarAllocation.pure_preserves _
  · intro ignored
    apply ScalarAllocation.bind_preserves
    · apply ScalarAllocation.forIn_preserves
      intro condition accumulator
      apply ScalarAllocation.bind_preserves _ _ (ScalarAllocation.lowerExpr_preserves _)
      intro text
      apply ScalarAllocation.bind_preserves _ _ (ScalarAllocation.emit_preserves _ _)
      intro ignored
      exact ScalarAllocation.pure_preserves _
    · intro ignored
      apply ScalarAllocation.bind_preserves
      · apply ScalarAllocation.forIn_preserves
        intro output accumulator
        exact ScalarAllocation.bind_preserves _ _ (ScalarAllocation.lowerExpr_preserves _) (fun _ => ScalarAllocation.pure_preserves _)
      · intro texts
        dsimp only
        split
        · exact ScalarAllocation.bind_preserves _ _ (ScalarAllocation.bindPublic_preserves _) (fun _ => ScalarAllocation.emit_preserves _ _)
        · exact ScalarAllocation.emit_preserves _ _
  · let inputBody : Input → StateM Zkir.LowerState Unit := fun input => do
      let output := "%input_" ++ input.name
      Zkir.emit (if input.visibility == .«public» then "public_input" else "private_input")
        [("guard", Json.null), ("type", toJson ("Scalar<BLS12-381>" : String)), ("output", toJson output)]
      Zkir.constrainType input.ty output
      if input.visibility == .«public» then Zkir.bindPublic [output]
    have frames : ∀ input, ScalarAllocation.PreservesFrame (inputBody input) := by
      intro input
      apply ScalarAllocation.bind_preserves _ _ (ScalarAllocation.emit_preserves _ _)
      intro ignored
      apply ScalarAllocation.bind_preserves _ _ (ScalarAllocation.constrainType_preserves _ _)
      intro ignored
      split
      · exact ScalarAllocation.bindPublic_preserves _
      · exact ScalarAllocation.pure_preserves _
    have construction : ∀ input ∈ circuit.inputs, Completes hash inputs (inputBody input) := by
      intro input member
      obtain ⟨value, lookup, canonical⟩ := admitted.complete input member
      exact completes_input hash inputs input value canonical (admitted.binding input member value lookup) (identifiers input member)
    simpa only [inputBody, Zkir.nativeType_eq, bind_assoc, state_ite_bind, pure_bind] using
      (completes_forIn hash inputs circuit.inputs PUnit.unit inputBody frames construction)
  · intro ignored
    apply completes_bind hash inputs
    · apply ScalarAllocation.forIn_preserves
      intro condition accumulator
      apply ScalarAllocation.bind_preserves _ _ (ScalarAllocation.lowerExpr_preserves _)
      intro text
      apply ScalarAllocation.bind_preserves _ _ (ScalarAllocation.emit_preserves _ _)
      intro ignored
      exact ScalarAllocation.pure_preserves _
    · intro ignored
      apply ScalarAllocation.bind_preserves
      · apply ScalarAllocation.forIn_preserves
        intro output accumulator
        exact ScalarAllocation.bind_preserves _ _ (ScalarAllocation.lowerExpr_preserves _) (fun _ => ScalarAllocation.pure_preserves _)
      · intro texts
        dsimp only
        split
        · exact ScalarAllocation.bind_preserves _ _ (ScalarAllocation.bindPublic_preserves _) (fun _ => ScalarAllocation.emit_preserves _ _)
        · exact ScalarAllocation.emit_preserves _ _
    · let conditionBody : Expr .bool → StateM Zkir.LowerState Unit := fun condition => do
        let text ← Zkir.lowerExpr condition
        Zkir.emit "assert" [("cond", toJson text)]
      have frames : ∀ condition, ScalarAllocation.PreservesFrame (conditionBody condition) := by
        intro condition
        exact ScalarAllocation.bind_preserves _ _ (ScalarAllocation.lowerExpr_preserves _) (fun _ => ScalarAllocation.emit_preserves _ _)
      have construction : ∀ condition ∈ circuit.constraints, Completes hash inputs (conditionBody condition) := by
        intro condition member
        exact completes_condition ctx hash implementation complete circuit values inputs admitted identifiers condition
          (conditions condition member).1 (conditions condition member).2
      simpa only [conditionBody, bind_assoc] using
        (completes_forIn hash inputs circuit.constraints PUnit.unit conditionBody frames construction)
    · intro ignored
      exact completes_outputs ctx hash implementation complete circuit values inputs admitted identifiers outputValidation
        (output_eval_members ctx values circuit.outputs result outputSuccess)

theorem lowerCircuit_witness_with_expressions (ctx : EvalContext) (hash : Hash)
    (implementation : HashAgreement ctx hash)
    (complete : ∀ ty (expression : Expr ty), ExprComplete expression)
    (circuit : Circuit) (values result : EvalEnv) (inputs : NativeRelation.Assignment)
    (json : Json) (program : Program) (admitted : CanonicalInputs circuit values inputs)
    (lowered : Zkir.lowerCircuit circuit = .ok json) (decoded : NativeRelationJson.decode json = .ok program)
    (success : circuit.run ctx values = .ok result) :
    ∃ witness, InputFrame inputs witness ∧ ∀ instruction ∈ program.instructions, instruction.Holds hash witness := by
  obtain ⟨expected, expectedAccepted, nativeAccepted⟩ := Zkir.lowerCircuit_validated circuit json lowered
  obtain ⟨validation, _⟩ := expectedCircuit_parts (Passes.pruneCircuit circuit) expected expectedAccepted
  have prunedInputs : CanonicalInputs (Passes.pruneCircuit circuit) values inputs :=
    ⟨admitted.unique, admitted.declared, admitted.complete, admitted.binding⟩
  have identifiers := (ScalarAdmission.lowerCircuit_admission circuit json program lowered decoded).2.2
  have prunedSuccess : (Passes.pruneCircuit circuit).run ctx values = .ok result := by
    simpa only [Passes.pruneCircuit_run] using success
  have construction := lowerBody_complete_with_expressions ctx hash implementation complete
    (Passes.pruneCircuit circuit) values result inputs prunedInputs identifiers validation prunedSuccess
  obtain ⟨extension⟩ := construction inputs {} (empty_state hash inputs) (by intro name; rfl) rfl
    (ScalarAllocationOutputFrame.lowerCircuit_names_fit_producerCapacity circuit lowered)
  refine ⟨extension.witness, ?_, ?_⟩
  · intro name
    exact extension.frame _ (Or.inl ⟨name, rfl⟩)
  · obtain ⟨raw, parsed, trace⟩ := ScalarValidation.decode_result decoded
    rw [Zkir.lowerCircuit_instructions circuit json lowered] at parsed
    cases parsed
    exact extension.meaning.holds program.instructions trace

end Noctium.Verification.ScalarCircuitLowering
