import Noctium.Verification.ScalarValidationArithmeticLoop
import Noctium.Verification.ScalarValidationNativeLoop

namespace Noctium.Verification.ScalarValidationNativeDefinitions

open Lean Backend.Native NativeRelation NativeRelationJson
open Noctium.Verification.ScalarValidationArithmeticLoop
open Noctium.Verification.ScalarValidationNativeLoop

private theorem bind_ok {α β : Type} {value : Except String α} {next : α → Except String β}
    {result : β} : (value >>= next) = .ok result ↔
      ∃ found, value = .ok found ∧ next found = .ok result := by
  cases value <;> simp [Bind.bind, Except.bind]

private theorem refine_nativeDefinitions {state next : State} {text : String} {maximum : Nat}
    (nativeDefinitions : NativeDefinitions state)
    (accepted : refine state text maximum = .ok next) :
    NativeDefinitions next := by
  unfold refine at accepted
  simp only [bind_ok] at accepted
  rcases accepted with ⟨fact, _, accepted⟩
  split at accepted
  next referenceText =>
    rcases accepted with ⟨_, _, result⟩
    have stateEq := Except.ok.inj result
    subst next
    intro name value member
    simp only [List.mem_map] at member
    rcases member with ⟨⟨oldName, oldValue⟩, member, equal⟩
    simp only [Prod.mk.injEq] at equal
    rcases equal with ⟨nameEq, valueEq⟩
    subst name
    subst value
    have oldNative := nativeDefinitions oldName oldValue member
    cases same : oldName == text <;> simp [oldNative]
  next =>
    rcases accepted with ⟨_, _, accepted⟩
    simp only [bind_ok] at accepted
    rcases accepted with ⟨_, _, result⟩
    have stateEq := Except.ok.inj result
    cases stateEq
    exact nativeDefinitions

theorem accepted_copy_nativeDefinitions {expected : Expected} {state next : State} {raw : Json}
    (nativeDefinitions : NativeDefinitions state)
    (opcode : Backend.Native.stringField raw "op" = .ok "copy")
    (accepted : validateInstruction expected state raw = .ok next) :
    NativeDefinitions next := by
  obtain ⟨value, _, valueNative, defined⟩ :=
    accepted_copy_components nativeDefinitions opcode accepted
  exact defineResult_nativeDefinitions nativeDefinitions valueNative defined

theorem accepted_add_nativeDefinitions {expected : Expected} {state next : State} {raw : Json}
    (nativeDefinitions : NativeDefinitions state)
    (opcode : Backend.Native.stringField raw "op" = .ok "add")
    (accepted : validateInstruction expected state raw = .ok next) :
    NativeDefinitions next := by
  obtain ⟨_, _, _, _, _, _, _, combined, defined⟩ :=
    accepted_add_components nativeDefinitions opcode accepted
  exact defineResult_nativeDefinitions nativeDefinitions (combine_native combined) defined

theorem accepted_testEq_nativeDefinitions {expected : Expected} {state next : State} {raw : Json}
    (nativeDefinitions : NativeDefinitions state)
    (opcode : Backend.Native.stringField raw "op" = .ok "test_eq")
    (accepted : validateInstruction expected state raw = .ok next) :
    NativeDefinitions next := by
  obtain ⟨_, _, _, _, _, _, _, combined, defined⟩ :=
    accepted_testEq_components nativeDefinitions opcode accepted
  exact defineResult_nativeDefinitions nativeDefinitions (combine_native combined) defined

theorem accepted_constrainEq_nativeDefinitions {expected : Expected} {state next : State} {raw : Json}
    (nativeDefinitions : NativeDefinitions state)
    (opcode : Backend.Native.stringField raw "op" = .ok "constrain_eq")
    (accepted : validateInstruction expected state raw = .ok next) :
    NativeDefinitions next := by
  unfold validateInstruction at accepted
  simp only [bind_ok] at accepted
  rcases accepted with ⟨found, op, descriptor, registry, _, fields, accepted⟩
  have opcodeEq := Except.ok.inj (op.symm.trans opcode)
  subst found
  simp only [bind_ok] at accepted
  rcases accepted with ⟨leftText, leftTextParsed, rightText, rightTextParsed,
    leftFact, leftParsed, rightFact, rightParsed, middle, leftRefined, rightRefined⟩
  have leftArgument : argument state raw "a" = .ok leftFact := by
    unfold argument
    rw [leftTextParsed]
    exact leftParsed
  have leftNative := argument_native_of_state nativeDefinitions leftArgument
  simp only [leftNative, Backend.Native.ensure] at rightRefined
  simp only [Bind.bind, Except.bind] at rightRefined
  rcases bind_ok.mp rightRefined with ⟨middleState, leftRefined, rest⟩
  rcases bind_ok.mp rest with ⟨nextState, rightRefine, final⟩
  have nextStateNative :=
    refine_nativeDefinitions (refine_nativeDefinitions nativeDefinitions leftRefined) rightRefine
  simp only [Pure.pure, Except.pure] at final
  have finalEq := Except.ok.inj final
  subst next
  intro name fact member
  change (name, fact) ∈ nextState.definitions at member
  exact nextStateNative name fact member

/-- The supported opcode profile for this trace fragment. Copy and constrain_eq
both decode to `.equal`, so the profile records which producer opcode was used. -/
inductive SupportedScalarOpcode (raw : Json) : Instruction → Prop where
  | publicInput (output : String)
      (opcode : Backend.Native.stringField raw "op" = .ok "public_input") :
      SupportedScalarOpcode raw (.input .public output)
  | privateInput (output : String)
      (opcode : Backend.Native.stringField raw "op" = .ok "private_input") :
      SupportedScalarOpcode raw (.input .private output)
  | add (a b : Operand) (output : String)
      (opcode : Backend.Native.stringField raw "op" = .ok "add") :
      SupportedScalarOpcode raw (.add a b output)
  | mul (a b : Operand) (output : String)
      (opcode : Backend.Native.stringField raw "op" = .ok "mul") :
      SupportedScalarOpcode raw (.mul a b output)
  | neg (a : Operand) (output : String)
      (opcode : Backend.Native.stringField raw "op" = .ok "neg") :
      SupportedScalarOpcode raw (.neg a output)
  | testEq (a b : Operand) (output : String)
      (opcode : Backend.Native.stringField raw "op" = .ok "test_eq") :
      SupportedScalarOpcode raw (.testEq a b output)
  | copy (source destination : String)
      (opcode : Backend.Native.stringField raw "op" = .ok "copy") :
      SupportedScalarOpcode raw (.equal (.reference source) (.reference destination))
  | constrainEq (a b : Operand)
      (opcode : Backend.Native.stringField raw "op" = .ok "constrain_eq") :
      SupportedScalarOpcode raw (.equal a b)

structure NativeDefinitionStep (raw : Json) (instruction : Instruction) : Prop where
  supported : SupportedScalarOpcode raw instruction
  decoded : NativeRelationJson.decodeInstruction raw = .ok instruction

inductive NativeDefinitionTrace : List (Json × Nat) → List Instruction → Prop where
  | nil : NativeDefinitionTrace [] []
  | cons {raw : Json} {index : Nat} {instruction : Instruction}
      {items : List (Json × Nat)} {instructions : List Instruction}
      (head : NativeDefinitionStep raw instruction)
      (tail : NativeDefinitionTrace items instructions) :
      NativeDefinitionTrace ((raw, index) :: items) (instruction :: instructions)

inductive SupportedScalarOpcodeTrace : List (Json × Nat) → List Instruction → Prop where
  | nil : SupportedScalarOpcodeTrace [] []
  | cons {raw : Json} {index : Nat} {instruction : Instruction}
      {items : List (Json × Nat)} {instructions : List Instruction}
      (head : SupportedScalarOpcode raw instruction)
      (tail : SupportedScalarOpcodeTrace items instructions) :
      SupportedScalarOpcodeTrace ((raw, index) :: items) (instruction :: instructions)

/-- Attach the exact per-instruction decoder proofs from a successful mapM to
an explicit supported-opcode trace. No other opcode is inferred or admitted. -/
theorem NativeDefinitionTrace.ofDecodedSupportedOpcodes
    {items : List (Json × Nat)} {instructions : List Instruction}
    (supported : SupportedScalarOpcodeTrace items instructions)
    (decoded : (items.map Prod.fst).mapM NativeRelationJson.decodeInstruction = .ok instructions) :
    NativeDefinitionTrace items instructions := by
  induction supported with
  | nil => exact .nil
  | @cons raw index instruction tailItems tailInstructions head tail ih =>
    simp only [List.map_cons, List.mapM_cons, bind_ok] at decoded
    rcases decoded with ⟨decodedInstruction, decodedHead, decodedTailInstructions,
      decodedTail, listEquality⟩
    simp only [Pure.pure, Except.pure] at listEquality
    rcases List.cons.inj (Except.ok.inj listEquality) with ⟨instructionEq, instructionsEq⟩
    cases instructionEq
    cases instructionsEq
    exact .cons ⟨head, decodedHead⟩ (ih decodedTail)

theorem NativeDefinitionTrace.decodes {items : List (Json × Nat)}
    {instructions : List Instruction} (trace : NativeDefinitionTrace items instructions) :
    (items.map Prod.fst).mapM NativeRelationJson.decodeInstruction = .ok instructions := by
  induction trace with
  | nil => simp [List.mapM_nil, Pure.pure, Except.pure]
  | @cons raw index instruction tailItems tailInstructions head tail ih =>
    simp [List.mapM_cons, head.decoded, ih, Bind.bind, Except.bind, Pure.pure, Except.pure]

theorem empty_nativeDefinitions : NativeDefinitions ({} : State) := by
  intro identifier fact found
  simp at found

private theorem nativeDefinitions_step {expected : Expected} {state next : State}
    {raw : Json} {instruction : Instruction}
    (inputSchema : ∀ requirement ∈ expected.inputs, requirement.ty.isForeign = false)
    (nativeDefinitions : NativeDefinitions state)
    (step : NativeDefinitionStep raw instruction)
    (accepted : validateInstruction expected state raw = .ok next) :
    NativeDefinitions next := by
  cases step.supported with
  | publicInput output opcode =>
    have parsedOpcode : Backend.Native.stringField raw "op" =
        .ok (inputOpcode .public) := by simpa [inputOpcode] using opcode
    obtain ⟨requirement, selected⟩ := accepted_input_requirement_selected
      (visibility := .public) parsedOpcode accepted
    have member : requirement ∈ expected.inputs := List.mem_of_getElem? selected
    have nonforeignInput := inputSchema requirement member
    cases guarded : requirement.activityGuard with
    | none =>
      exact input_nativeDefinitions_step (visibility := .public) nativeDefinitions selected
        nonforeignInput guarded parsedOpcode accepted
    | some guardTerm =>
      exact guarded_public_input_nativeDefinitions_step nativeDefinitions selected
        nonforeignInput guarded parsedOpcode accepted
  | privateInput output opcode =>
    have parsedOpcode : Backend.Native.stringField raw "op" =
        .ok (inputOpcode .private) := by simpa [inputOpcode] using opcode
    obtain ⟨requirement, selected⟩ := accepted_input_requirement_selected
      (visibility := .private) parsedOpcode accepted
    have member : requirement ∈ expected.inputs := List.mem_of_getElem? selected
    have nonforeignInput := inputSchema requirement member
    have unguarded := accepted_private_input_unguarded selected parsedOpcode accepted
    exact input_nativeDefinitions_step (visibility := .private) nativeDefinitions selected
      nonforeignInput unguarded parsedOpcode accepted
  | add _ _ _ opcode => exact accepted_add_nativeDefinitions nativeDefinitions opcode accepted
  | mul _ _ _ opcode =>
      obtain ⟨_, _, _, _, _, _, _, combined, defined⟩ :=
        accepted_mul_components nativeDefinitions opcode accepted
      exact defineResult_nativeDefinitions nativeDefinitions (combine_native combined) defined
  | neg _ _ opcode =>
      obtain ⟨_, _, _, _, combined, defined⟩ :=
        accepted_neg_components nativeDefinitions opcode accepted
      exact defineResult_nativeDefinitions nativeDefinitions (combine_native combined) defined
  | testEq _ _ _ opcode => exact accepted_testEq_nativeDefinitions nativeDefinitions opcode accepted
  | copy _ _ opcode => exact accepted_copy_nativeDefinitions nativeDefinitions opcode accepted
  | constrainEq _ _ opcode =>
      exact accepted_constrainEq_nativeDefinitions nativeDefinitions opcode accepted

/-- Derive the final native-definition invariant from the actual decoded
instruction list and the producer's ordered validation fold. -/
theorem validateInstructionLoop_nativeDefinitions_of_trace
    {expected : Expected} {items : List (Json × Nat)} {instructions : List Instruction}
    {initial final : State}
    (inputSchema : ∀ requirement ∈ expected.inputs, requirement.ty.isForeign = false)
    (initialNativeDefinitions : NativeDefinitions initial)
    (trace : NativeDefinitionTrace items instructions)
    (accepted : validateInstructionLoop expected items initial = .ok final) :
    NativeDefinitions final := by
  induction trace generalizing initial final with
  | nil =>
    have initialEq : initial = final := by injection accepted
    subst final
    exact initialNativeDefinitions
  | @cons raw index instruction tailItems tailInstructions head tail ih =>
    rw [validateInstructionLoop, List.forIn_cons] at accepted
    cases checked : validateInstruction expected initial raw with
    | error message => simp [checked, Bind.bind, Except.bind] at accepted
    | ok next =>
      simp only [checked, bind_pure_comp] at accepted
      have nextNativeDefinitions := nativeDefinitions_step inputSchema
        initialNativeDefinitions head checked
      exact ih nextNativeDefinitions accepted

theorem validateInstructionLoop_supportedScalar_nativeDefinitions
    {expected : Expected} {items : List (Json × Nat)} {instructions : List Instruction}
    {final : State}
    (inputSchema : ∀ requirement ∈ expected.inputs, requirement.ty.isForeign = false)
    (supported : SupportedScalarOpcodeTrace items instructions)
    (decoded : (items.map Prod.fst).mapM NativeRelationJson.decodeInstruction = .ok instructions)
    (accepted : validateInstructionLoop expected items ({} : State) = .ok final) :
    NativeDefinitions final :=
  validateInstructionLoop_nativeDefinitions_of_trace inputSchema empty_nativeDefinitions
    (NativeDefinitionTrace.ofDecodedSupportedOpcodes supported decoded) accepted

end Noctium.Verification.ScalarValidationNativeDefinitions
