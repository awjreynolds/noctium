import Noctium.Backend.NativeProducer
import Noctium.Verification.NativeRelationJson
import Noctium.Verification.ScalarValidationMeaning

namespace Noctium.Verification.ScalarValidationArithmeticLoop

open Lean Backend.Native NativeRelation NativeRelationJson
open Noctium.Verification.ScalarValidationMeaning

def NativeDefinitions (state : State) : Prop :=
  ∀ identifier fact, (identifier, fact) ∈ state.definitions → fact.valueType = .native

theorem argument_native_of_state {state : State} {raw : Json} {name : String}
    {fact : Fact}
    (nativeDefinitions : NativeDefinitions state)
    (accepted : argument state raw name = .ok fact) :
    fact.valueType = .native := by
  unfold argument at accepted
  simp only [bind_ok] at accepted
  rcases accepted with ⟨text, _, accepted⟩
  unfold operand at accepted
  split at accepted
  · simp only [bind_ok] at accepted
    rcases accepted with ⟨number, _, result⟩
    cases result
    rfl
  · simp only [bind_ok] at accepted
    rcases accepted with ⟨_, _, accepted⟩
    split at accepted
    · next found =>
      cases accepted
      exact nativeDefinitions text _ (lookup_member found)
    · contradiction

theorem accepted_add_components {expected : Expected} {state next : State}
    {raw : Json}
    (nativeDefinitions : NativeDefinitions state)
    (opcodeParsed : Backend.Native.stringField raw "op" = .ok "add")
    (accepted : validateInstruction expected state raw = .ok next) :
    ∃ left right fact,
      argument state raw "a" = .ok left ∧ argument state raw "b" = .ok right ∧
      left.valueType = .native ∧ right.valueType = .native ∧
      combine (.binary "add" left.term right.term)
        (if left.maximum + right.maximum < Field.modulus then left.maximum + right.maximum
          else Field.modulus - 1) [left, right] = .ok fact ∧
      defineResult state raw fact = .ok next := by
  unfold validateInstruction at accepted
  simp only [bind_ok] at accepted
  rcases accepted with ⟨opcode, op, descriptor, support, fields, accepted⟩
  have opcodeEq : opcode = "add" := Except.ok.inj (op.symm.trans opcodeParsed)
  subst opcode
  simp [bind_ok] at accepted
  rcases accepted with ⟨_, left, leftAccepted, right, rightAccepted, _, reducer⟩
  have leftNative := argument_native_of_state nativeDefinitions leftAccepted
  have rightNative := argument_native_of_state nativeDefinitions rightAccepted
  have notPoint : (NativeValueType.native == NativeValueType.jubjubPoint) = false := by decide
  rw [leftNative] at reducer
  simp only [notPoint, Bool.false_eq_true, ite_false] at reducer
  change (do
    let _ ← Backend.Native.ensure (left.valueType == NativeValueType.native)
      "native instruction operand must have Native type"
    let _ ← Backend.Native.ensure (right.valueType == NativeValueType.native)
      "native instruction operand must have Native type"
    let found ← combine (.binary "add" left.term right.term)
      (if left.maximum + right.maximum < Field.modulus then left.maximum + right.maximum
        else Field.modulus - 1) [left, right]
    defineResult state raw found) = .ok next at reducer
  simp [leftNative, rightNative, Backend.Native.ensure] at reducer
  rcases bind_ok.mp reducer with ⟨_, _, reducer⟩
  rcases bind_ok.mp reducer with ⟨_, _, reducer⟩
  rcases bind_ok.mp reducer with ⟨fact, combined, defined⟩
  exact ⟨left, right, fact, leftAccepted, rightAccepted, leftNative, rightNative,
    combined, defined⟩

theorem combine_native {term : Backend.Native.Term} {maximum : Nat}
    {children : List Fact} {fact : Fact}
    (accepted : combine term maximum children = .ok fact) :
    fact.valueType = .native := by
  unfold combine at accepted
  dsimp [Backend.Native.ensure] at accepted
  split at accepted
  · simp only [Pure.pure, Except.pure] at accepted
    cases accepted
    rfl
  · contradiction

theorem defineResult_nativeDefinitions {state next : State} {raw : Json} {fact : Fact}
    (nativeDefinitions : NativeDefinitions state)
    (factNative : fact.valueType = .native)
    (accepted : defineResult state raw fact = .ok next) :
    NativeDefinitions next := by
  unfold defineResult at accepted
  simp only [bind_ok] at accepted
  rcases accepted with ⟨identifier, _, defined⟩
  unfold define at defined
  simp only [bind_ok] at defined
  rcases defined with ⟨_, _, _, _, result⟩
  cases result
  intro name found member
  simp only [List.mem_append, List.mem_singleton, Prod.mk.injEq] at member
  rcases member with member | ⟨sameName, sameFact⟩
  · exact nativeDefinitions name found member
  · subst name
    subst found
    exact factNative

/-- An accepted add step preserves meanings and the native typing of every
definition. Operand facts, their native types, and the combine result all come
from the accepted reducer and the input state's typing invariant. -/
theorem accepted_native_add_step_meaning
    {hash : Hash} {inputs witness : Assignment} {expected : Expected}
    {state next : State} {raw : Json} {output : String}
    {a b : Operand}
    (invariant : StateMeaning hash inputs witness state)
    (nativeDefinitions : NativeDefinitions state)
    (opcodeParsed : Backend.Native.stringField raw "op" = .ok "add")
    (accepted : validateInstruction expected state raw = .ok next)
    (decoded : NativeRelationJson.decodeInstruction raw = .ok (.add a b output))
    (holds : Instruction.Holds hash witness (.add a b output)) :
    StateMeaning hash inputs witness next ∧ NativeDefinitions next := by
  obtain ⟨left, right, fact, leftAccepted, rightAccepted, leftNative, rightNative,
    combined, defined⟩ := accepted_add_components nativeDefinitions opcodeParsed accepted
  have meaning := native_add_step_meaning invariant opcodeParsed leftAccepted rightAccepted
    leftNative rightNative decoded holds combined accepted
  have factNative := combine_native combined
  have typed := defineResult_nativeDefinitions nativeDefinitions factNative defined
  exact ⟨meaning, typed⟩

theorem accepted_mul_components {expected : Expected} {state next : State}
    {raw : Json}
    (nativeDefinitions : NativeDefinitions state)
    (opcodeParsed : Backend.Native.stringField raw "op" = .ok "mul")
    (accepted : validateInstruction expected state raw = .ok next) :
    ∃ left right fact,
      argument state raw "a" = .ok left ∧ argument state raw "b" = .ok right ∧
      left.valueType = .native ∧ right.valueType = .native ∧
      combine (.binary "mul" left.term right.term)
        (if left.maximum * right.maximum < Field.modulus then left.maximum * right.maximum
          else Field.modulus - 1) [left, right] = .ok fact ∧
      defineResult state raw fact = .ok next := by
  unfold validateInstruction at accepted
  simp only [bind_ok] at accepted
  rcases accepted with ⟨opcode, op, descriptor, support, fields, accepted⟩
  have opcodeEq : opcode = "mul" := Except.ok.inj (op.symm.trans opcodeParsed)
  subst opcode
  simp [bind_ok] at accepted
  rcases accepted with ⟨_, left, leftAccepted, right, rightAccepted, reducer⟩
  have leftNative := argument_native_of_state nativeDefinitions leftAccepted
  have rightNative := argument_native_of_state nativeDefinitions rightAccepted
  rw [leftNative] at reducer
  change (do
    let _ ← Backend.Native.ensure (left.valueType == NativeValueType.native)
      "native instruction operand must have Native type"
    let _ ← Backend.Native.ensure (right.valueType == NativeValueType.native)
      "native instruction operand must have Native type"
    let bound := left.maximum * right.maximum
    let maximum := if bound < Field.modulus then bound else Field.modulus - 1
    let found ← combine (.binary "mul" left.term right.term) maximum [left, right]
    defineResult state raw found) = .ok next at reducer
  simp [leftNative, rightNative, Backend.Native.ensure] at reducer
  rcases bind_ok.mp reducer with ⟨_, _, reducer⟩
  rcases bind_ok.mp reducer with ⟨_, _, reducer⟩
  rcases bind_ok.mp reducer with ⟨fact, combined, defined⟩
  exact ⟨left, right, fact, leftAccepted, rightAccepted, leftNative, rightNative,
    combined, defined⟩

theorem accepted_native_mul_step_meaning
    {hash : Hash} {inputs witness : Assignment} {expected : Expected}
    {state next : State} {raw : Json} {output : String}
    {a b : Operand}
    (invariant : StateMeaning hash inputs witness state)
    (nativeDefinitions : NativeDefinitions state)
    (opcodeParsed : Backend.Native.stringField raw "op" = .ok "mul")
    (accepted : validateInstruction expected state raw = .ok next)
    (decoded : NativeRelationJson.decodeInstruction raw = .ok (.mul a b output))
    (holds : Instruction.Holds hash witness (.mul a b output)) :
    StateMeaning hash inputs witness next ∧ NativeDefinitions next := by
  obtain ⟨left, right, fact, leftAccepted, rightAccepted, leftNative, rightNative,
    combined, defined⟩ := accepted_mul_components nativeDefinitions opcodeParsed accepted
  have meaning := native_mul_step_meaning invariant opcodeParsed leftAccepted rightAccepted
    leftNative rightNative decoded holds combined accepted
  have factNative := combine_native combined
  have typed := defineResult_nativeDefinitions nativeDefinitions factNative defined
  exact ⟨meaning, typed⟩

theorem accepted_neg_components {expected : Expected} {state next : State}
    {raw : Json}
    (nativeDefinitions : NativeDefinitions state)
    (opcodeParsed : Backend.Native.stringField raw "op" = .ok "neg")
    (accepted : validateInstruction expected state raw = .ok next) :
    ∃ value fact,
      argument state raw "a" = .ok value ∧ value.valueType = .native ∧
      combine (.unary "neg" value.term)
        (if value.maximum == 0 then 0 else Field.modulus - 1) [value] = .ok fact ∧
      defineResult state raw fact = .ok next := by
  unfold validateInstruction at accepted
  simp only [bind_ok] at accepted
  rcases accepted with ⟨opcode, op, descriptor, support, fields, accepted⟩
  have opcodeEq : opcode = "neg" := Except.ok.inj (op.symm.trans opcodeParsed)
  subst opcode
  simp [bind_ok] at accepted
  rcases accepted with ⟨_, value, valueAccepted, reducer⟩
  have valueNative := argument_native_of_state nativeDefinitions valueAccepted
  rw [valueNative] at reducer
  have notPoint : (NativeValueType.native == NativeValueType.jubjubPoint) = false := by decide
  simp only [notPoint, Bool.false_eq_true, ite_false] at reducer
  change (do
    let _ ← Backend.Native.ensure (value.valueType == NativeValueType.native)
      "native instruction operand must have Native type"
    let maximum := if value.maximum = 0 then 0 else Field.modulus - 1
    let found ← combine (.unary "neg" value.term) maximum [value]
    defineResult state raw found) = .ok next at reducer
  simp [valueNative, Backend.Native.ensure] at reducer
  rcases bind_ok.mp reducer with ⟨_, _, reducer⟩
  rcases bind_ok.mp reducer with ⟨fact, combined, defined⟩
  have combinedBool : combine (.unary "neg" value.term)
      (if value.maximum == 0 then 0 else Field.modulus - 1) [value] = .ok fact := by
    simpa only [beq_iff_eq] using combined
  exact ⟨value, fact, valueAccepted, valueNative, combinedBool, defined⟩

theorem accepted_native_neg_step_meaning
    {hash : Hash} {inputs witness : Assignment} {expected : Expected}
    {state next : State} {raw : Json} {output : String}
    {a : Operand}
    (invariant : StateMeaning hash inputs witness state)
    (nativeDefinitions : NativeDefinitions state)
    (opcodeParsed : Backend.Native.stringField raw "op" = .ok "neg")
    (accepted : validateInstruction expected state raw = .ok next)
    (decoded : NativeRelationJson.decodeInstruction raw = .ok (.neg a output))
    (holds : Instruction.Holds hash witness (.neg a output)) :
    StateMeaning hash inputs witness next ∧ NativeDefinitions next := by
  obtain ⟨value, fact, valueAccepted, valueNative, combined, defined⟩ :=
    accepted_neg_components nativeDefinitions opcodeParsed accepted
  have meaning := native_neg_step_meaning invariant opcodeParsed valueAccepted valueNative
    decoded holds combined accepted
  have factNative := combine_native combined
  have typed := defineResult_nativeDefinitions nativeDefinitions factNative defined
  exact ⟨meaning, typed⟩

/-- Exact decoding and satisfaction for an instruction in the Native arithmetic
subset. The producer still checks operands, definitions, and instruction order. -/
inductive NativeArithmeticHolds (hash : Hash) (witness : Assignment) (raw : Json) : Prop where
  | add (a b : Operand) (output : String)
      (opcode : Backend.Native.stringField raw "op" = .ok "add")
      (decoded : NativeRelationJson.decodeInstruction raw = .ok (.add a b output))
      (holds : Instruction.Holds hash witness (.add a b output))
  | mul (a b : Operand) (output : String)
      (opcode : Backend.Native.stringField raw "op" = .ok "mul")
      (decoded : NativeRelationJson.decodeInstruction raw = .ok (.mul a b output))
      (holds : Instruction.Holds hash witness (.mul a b output))
  | neg (a : Operand) (output : String)
      (opcode : Backend.Native.stringField raw "op" = .ok "neg")
      (decoded : NativeRelationJson.decodeInstruction raw = .ok (.neg a output))
      (holds : Instruction.Holds hash witness (.neg a output))

/-- The accepted producer loop preserves meaning and native types when each
indexed instruction decodes as satisfied Native arithmetic. -/
theorem accepted_arithmetic_loop_meaning
    {hash : Hash} {inputs witness : Assignment} {expected : Expected}
    {items : List (Json × Nat)} {initial final : State}
    (invariant : StateMeaning hash inputs witness initial)
    (nativeDefinitions : NativeDefinitions initial)
    (steps : ∀ item ∈ items, NativeArithmeticHolds hash witness item.1)
    (accepted : validateInstructionLoop expected items initial = .ok final) :
    StateMeaning hash inputs witness final ∧ NativeDefinitions final := by
  induction items generalizing initial final with
  | nil =>
    have initialEq : initial = final := by injection accepted
    subst final
    exact ⟨invariant, nativeDefinitions⟩
  | cons head tail ih =>
    rw [validateInstructionLoop, List.forIn_cons] at accepted
    cases checked : validateInstruction expected initial head.1 with
    | error message => simp [checked, Bind.bind, Except.bind] at accepted
    | ok next =>
      simp only [checked, bind_pure_comp] at accepted
      have nextInvariant : StateMeaning hash inputs witness next ∧ NativeDefinitions next := by
        cases steps head (by simp) with
        | add _ _ _ opcode decoded holds =>
          exact accepted_native_add_step_meaning invariant nativeDefinitions opcode checked
            decoded holds
        | mul _ _ _ opcode decoded holds =>
          exact accepted_native_mul_step_meaning invariant nativeDefinitions opcode checked
            decoded holds
        | neg _ _ opcode decoded holds =>
          exact accepted_native_neg_step_meaning invariant nativeDefinitions opcode checked
            decoded holds
      exact ih nextInvariant.1 nextInvariant.2
        (fun item member => steps item (List.mem_cons_of_mem _ member)) accepted

end Noctium.Verification.ScalarValidationArithmeticLoop
