import Noctium.Verification.ScalarCache
import Noctium.Verification.ScalarRangeLowering
import Noctium.Verification.ScalarStateExtensions

namespace Noctium.Verification.ScalarWitnessConstruction

open Lean Backend NativeRelation NativeRelationJson ScalarNormalization ScalarLowering
open ScalarInstructionEncoding ScalarWitness ScalarValidationMeaning

structure NativeStepResult (hash : Hash) (inputs initialWitness : NativeRelation.Assignment)
    (initialState : Zkir.LowerState) (operation : StateM Zkir.LowerState String)
    (term : Native.Term) where
  text : String
  finalState : Zkir.LowerState
  finalWitness : NativeRelation.Assignment
  run : operation.run initialState = (text, finalState)
  operandMeaning : OperandMeaning hash inputs finalWitness text term
  textScope : TextScope finalState.next text
  stateMeaning : LowerStateMeaning hash finalWitness finalState
  budget : finalState.next ≤ Native.maxInstructions * Native.maxVectorLength
  aliasesPreserved : finalState.aliases = initialState.aliases
  frame : ∀ name, InScope initialState.next name → finalWitness name = initialWitness name

def NativeStepResult.chain
    {hash : Hash} {inputs witness : NativeRelation.Assignment} {state : Zkir.LowerState}
    {firstOperation : StateM Zkir.LowerState String} {firstTerm finalTerm : Native.Term}
    (first : NativeStepResult hash inputs witness state firstOperation firstTerm)
    (nextOperation : String → StateM Zkir.LowerState String)
    (second : NativeStepResult hash inputs first.finalWitness first.finalState
      (nextOperation first.text) finalTerm)
    (monotone : state.next ≤ first.finalState.next) :
    NativeStepResult hash inputs witness state (do let text ← firstOperation; nextOperation text) finalTerm := {
  text := second.text
  finalState := second.finalState
  finalWitness := second.finalWitness
  run := by rw [StateT.run_bind, first.run]; exact second.run
  operandMeaning := second.operandMeaning
  textScope := second.textScope
  stateMeaning := second.stateMeaning
  budget := second.budget
  aliasesPreserved := second.aliasesPreserved.trans first.aliasesPreserved
  frame := by
    intro name namesScoped
    rw [second.frame name (InScope.mono monotone namesScoped), first.frame name namesScoped]
}

theorem TextScope.identifiers {next : Nat} {text : String} {operand : Operand}
    (scope : TextScope next text) (decoded : decodeOperand (toJson text) = .ok operand) :
    ∀ name ∈ operandIdentifiers operand, InScope next name := by
  obtain ⟨found, parsed, namesScoped⟩ := scope
  have equal : found = operand := Except.ok.inj (parsed.symm.trans decoded)
  subst found
  exact namesScoped

theorem cached_text_scope (hash : Hash) (witness : NativeRelation.Assignment)
    (state : Zkir.LowerState) (invariant : LowerStateMeaning hash witness state)
    (key : ExpressionKey) (output : String)
    (hit : state.expressions.lookup key = some output) : TextScope state.next output := by
  obtain ⟨instructions, decoded, instruction, member, correspondence⟩ :=
    invariant.cacheTrace key output (ScalarValidationMeaning.lookup_member hit)
  have outputValid : validIdentifier output = true := by
    cases instruction <;> simp_all [CacheCorresponds] <;> grind
  have outputMember : output ∈ instructionIdentifiers instruction := by
    cases instruction <;> simp_all [CacheCorresponds, instructionIdentifiers]
    case equal source destination =>
      obtain ⟨_, _, _, rfl, rfl, _, _⟩ := correspondence
      exact Or.inr (by simp [operandIdentifiers])
  refine ⟨.reference output, (OperandEncoding.reference output outputValid).decode, ?_⟩
  intro name names
  have equal : name = output := by simpa only [operandIdentifiers, List.mem_singleton] using names
  subst name
  exact invariant.scope instructions decoded instruction member output outputMember

/-- Reuse a previously checked instruction result and keep the entire witness frame. -/
theorem cached_step (hash : Hash) (inputs witness : NativeRelation.Assignment)
    (state : Zkir.LowerState) (operation : StateM Zkir.LowerState String) (term : Native.Term)
    (key : ExpressionKey) (output : String)
    (stateMeaning : LowerStateMeaning hash witness state)
    (hit : state.expressions.lookup key = some output)
    (run : operation.run state = (output, state))
    (meaning : OperandMeaning hash inputs witness output term)
    (budget : (operation.run state).2.next ≤ Native.maxInstructions * Native.maxVectorLength) :
    Nonempty (NativeStepResult hash inputs witness state operation term) := by
  refine ⟨{
    text := output
    finalState := state
    finalWitness := witness
    run := run
    operandMeaning := meaning
    textScope := cached_text_scope hash witness state stateMeaning key output hit
    stateMeaning := stateMeaning
    budget := ?_
    aliasesPreserved := rfl
    frame := ?_
  }⟩
  · rw [run] at budget
    exact budget
  · intro name _
    rfl

/-- Extend the scoped assignment for one emitted and decoded cached result. -/
theorem fresh_step (hash : Hash) (inputs witness : NativeRelation.Assignment)
    (state : Zkir.LowerState) (operation : StateM Zkir.LowerState String) (term : Native.Term)
    (raw : Json) (key : ExpressionKey) (instruction : Instruction) (value : Scalar)
    (stateMeaning : LowerStateMeaning hash witness state)
    (run : operation.run state =
      (freshName state.next, appendFreshState state raw key (freshName state.next)))
    (decoded : decodeInstruction raw = .ok instruction)
    (cacheMatch : CacheCorresponds key (freshName state.next) instruction)
    (scope : ∀ name ∈ instructionIdentifiers instruction, InScope (state.next + 1) name)
    (holds : instruction.Holds hash (assign witness (freshName state.next) value))
    (valueMeaning : interpret hash inputs term = some value)
    (budget : (operation.run state).2.next ≤ Native.maxInstructions * Native.maxVectorLength) :
    Nonempty (NativeStepResult hash inputs witness state operation term) := by
  have finalBudget : state.next + 1 ≤ Native.maxInstructions * Native.maxVectorLength := by
    rw [run] at budget
    exact budget
  have valid : validIdentifier (freshName state.next) = true :=
    NativeRelationJson.generatedIdentifier_fits_output_capacity state.next (by omega)
  obtain ⟨instructions, priorDecoded⟩ := stateMeaning.decoded
  refine ⟨{
    text := freshName state.next
    finalState := appendFreshState state raw key (freshName state.next)
    finalWitness := assign witness (freshName state.next) value
    run := run
    operandMeaning := ?_
    textScope := ?_
    stateMeaning := ?_
    budget := finalBudget
    aliasesPreserved := rfl
    frame := ?_
  }⟩
  · exact ⟨.reference (freshName state.next), (OperandEncoding.reference _ valid).decode,
      by simpa only [Operand.read, assign_same] using valueMeaning⟩
  · refine ⟨.reference (freshName state.next), (OperandEncoding.reference _ valid).decode, ?_⟩
    intro name member
    have equal : name = freshName state.next := by simpa only [operandIdentifiers, List.mem_singleton] using member
    subst name
    exact Or.inr ⟨state.next, by simp [appendFreshState], rfl⟩
  · exact LowerStateMeaning.appendFresh hash witness state instructions priorDecoded stateMeaning raw key _ instruction
      decoded cacheMatch rfl valid scope value holds
  · intro name namesScoped
    apply assign_other
    intro equal
    rw [equal] at namesScoped
    exact fresh_not_inScope state.next namesScoped

private theorem fresh_binary_scope (next : Nat) (left right : Operand)
    (leftScope : ∀ name ∈ operandIdentifiers left, InScope next name)
    (rightScope : ∀ name ∈ operandIdentifiers right, InScope next name) :
    ∀ name ∈ operandIdentifiers left ++ operandIdentifiers right ++ [freshName next], InScope (next + 1) name := by
  intro name member
  simp only [List.mem_append, List.mem_singleton] at member
  rcases member with (member | member) | rfl
  · exact InScope.mono (by omega) (leftScope name member)
  · exact InScope.mono (by omega) (rightScope name member)
  · exact Or.inr ⟨next, by omega, rfl⟩

private theorem fresh_unary_scope (next : Nat) (value : Operand)
    (scope : ∀ name ∈ operandIdentifiers value, InScope next name) :
    ∀ name ∈ operandIdentifiers value ++ [freshName next], InScope (next + 1) name := by
  intro name member
  simp only [List.mem_append, List.mem_singleton] at member
  rcases member with member | rfl
  · exact InScope.mono (by omega) (scope name member)
  · exact Or.inr ⟨next, by omega, rfl⟩

theorem binary_add_step (hash : Hash) (inputs witness : NativeRelation.Assignment)
    (state : Zkir.LowerState) (left right : String) (leftTerm rightTerm : Native.Term)
    (stateMeaning : LowerStateMeaning hash witness state)
    (leftMeaning : OperandMeaning hash inputs witness left leftTerm)
    (rightMeaning : OperandMeaning hash inputs witness right rightTerm)
    (leftScope : TextScope state.next left) (rightScope : TextScope state.next right)
    (budget : ((Zkir.binary "add" left right).run state).2.next ≤ Native.maxInstructions * Native.maxVectorLength) :
    Nonempty (NativeStepResult hash inputs witness state (Zkir.binary "add" left right)
      (.binary "add" leftTerm rightTerm)) := by
  rcases leftMeaning with ⟨leftOperand, leftDecoded, leftValue⟩
  rcases rightMeaning with ⟨rightOperand, rightDecoded, rightValue⟩
  have leftNames := TextScope.identifiers leftScope leftDecoded
  have rightNames := TextScope.identifiers rightScope rightDecoded
  cases hit : state.expressions.lookup ("add", [left, right], none) with
  | some output =>
    exact cached_step hash inputs witness state _ _ _ output stateMeaning hit
      (binary_cache_hit state "add" left right output hit)
      (cached_add_meaning hash inputs witness state stateMeaning left right output leftTerm rightTerm
        ⟨leftOperand, leftDecoded, leftValue⟩ ⟨rightOperand, rightDecoded, rightValue⟩ hit) budget
  | none =>
    have run := binary_cache_miss state "add" left right hit
    have counter : state.next + 1 ≤ Native.maxInstructions * Native.maxVectorLength := by rw [run] at budget; exact budget
    have valid : validIdentifier (freshName state.next) = true := NativeRelationJson.generatedIdentifier_fits_output_capacity state.next (by omega)
    apply fresh_step hash inputs witness state (Zkir.binary "add" left right)
      (.binary "add" leftTerm rightTerm)
      (Zkir.instruction "add" [("a", toJson left), ("b", toJson right), ("output", toJson (freshName state.next))])
      ("add", [left, right], none) (.add leftOperand rightOperand (freshName state.next))
      (scalar ((leftOperand.read witness).val + (rightOperand.read witness).val)) stateMeaning run
      (decode_binary_instruction_add leftDecoded rightDecoded valid)
    · exact ⟨rfl, left, right, rfl, leftDecoded, rightDecoded, valid⟩
    · exact fresh_binary_scope state.next leftOperand rightOperand leftNames rightNames
    · exact add_output_holds hash witness (freshName state.next) leftOperand rightOperand
        (Operand.independent_of_scope state.next leftOperand leftNames)
        (Operand.independent_of_scope state.next rightOperand rightNames)
    · simp [interpret_add, leftValue, rightValue]
    · exact budget

theorem binary_mul_step (hash : Hash) (inputs witness : NativeRelation.Assignment)
    (state : Zkir.LowerState) (left right : String) (leftTerm rightTerm : Native.Term)
    (stateMeaning : LowerStateMeaning hash witness state)
    (leftMeaning : OperandMeaning hash inputs witness left leftTerm)
    (rightMeaning : OperandMeaning hash inputs witness right rightTerm)
    (leftScope : TextScope state.next left) (rightScope : TextScope state.next right)
    (budget : ((Zkir.binary "mul" left right).run state).2.next ≤ Native.maxInstructions * Native.maxVectorLength) :
    Nonempty (NativeStepResult hash inputs witness state (Zkir.binary "mul" left right)
      (.binary "mul" leftTerm rightTerm)) := by
  rcases leftMeaning with ⟨leftOperand, leftDecoded, leftValue⟩
  rcases rightMeaning with ⟨rightOperand, rightDecoded, rightValue⟩
  have leftNames := TextScope.identifiers leftScope leftDecoded
  have rightNames := TextScope.identifiers rightScope rightDecoded
  cases hit : state.expressions.lookup ("mul", [left, right], none) with
  | some output =>
    exact cached_step hash inputs witness state _ _ _ output stateMeaning hit
      (binary_cache_hit state "mul" left right output hit)
      (cached_mul_meaning hash inputs witness state stateMeaning left right output leftTerm rightTerm
        ⟨leftOperand, leftDecoded, leftValue⟩ ⟨rightOperand, rightDecoded, rightValue⟩ hit) budget
  | none =>
    have run := binary_cache_miss state "mul" left right hit
    have counter : state.next + 1 ≤ Native.maxInstructions * Native.maxVectorLength := by rw [run] at budget; exact budget
    have valid : validIdentifier (freshName state.next) = true := NativeRelationJson.generatedIdentifier_fits_output_capacity state.next (by omega)
    apply fresh_step hash inputs witness state (Zkir.binary "mul" left right)
      (.binary "mul" leftTerm rightTerm)
      (Zkir.instruction "mul" [("a", toJson left), ("b", toJson right), ("output", toJson (freshName state.next))])
      ("mul", [left, right], none) (.mul leftOperand rightOperand (freshName state.next))
      (scalar ((leftOperand.read witness).val * (rightOperand.read witness).val)) stateMeaning run
      (decode_binary_instruction_mul leftDecoded rightDecoded valid)
    · exact ⟨rfl, left, right, rfl, leftDecoded, rightDecoded, valid⟩
    · exact fresh_binary_scope state.next leftOperand rightOperand leftNames rightNames
    · exact mul_output_holds hash witness (freshName state.next) leftOperand rightOperand
        (Operand.independent_of_scope state.next leftOperand leftNames)
        (Operand.independent_of_scope state.next rightOperand rightNames)
    · simp [interpret_mul, leftValue, rightValue]
    · exact budget

theorem binary_testEq_step (hash : Hash) (inputs witness : NativeRelation.Assignment)
    (state : Zkir.LowerState) (left right : String) (leftTerm rightTerm : Native.Term)
    (stateMeaning : LowerStateMeaning hash witness state)
    (leftMeaning : OperandMeaning hash inputs witness left leftTerm)
    (rightMeaning : OperandMeaning hash inputs witness right rightTerm)
    (leftScope : TextScope state.next left) (rightScope : TextScope state.next right)
    (budget : ((Zkir.binary "test_eq" left right).run state).2.next ≤ Native.maxInstructions * Native.maxVectorLength) :
    Nonempty (NativeStepResult hash inputs witness state (Zkir.binary "test_eq" left right)
      (.binary "test_eq" leftTerm rightTerm)) := by
  rcases leftMeaning with ⟨leftOperand, leftDecoded, leftValue⟩
  rcases rightMeaning with ⟨rightOperand, rightDecoded, rightValue⟩
  have leftNames := TextScope.identifiers leftScope leftDecoded
  have rightNames := TextScope.identifiers rightScope rightDecoded
  cases hit : state.expressions.lookup ("test_eq", [left, right], none) with
  | some output =>
    exact cached_step hash inputs witness state _ _ _ output stateMeaning hit
      (binary_cache_hit state "test_eq" left right output hit)
      (ScalarCache.cached_testEq_meaning hash inputs witness state stateMeaning left right output leftTerm rightTerm
        ⟨leftOperand, leftDecoded, leftValue⟩ ⟨rightOperand, rightDecoded, rightValue⟩ hit) budget
  | none =>
    have run := binary_cache_miss state "test_eq" left right hit
    have counter : state.next + 1 ≤ Native.maxInstructions * Native.maxVectorLength := by rw [run] at budget; exact budget
    have valid : validIdentifier (freshName state.next) = true := NativeRelationJson.generatedIdentifier_fits_output_capacity state.next (by omega)
    apply fresh_step hash inputs witness state (Zkir.binary "test_eq" left right)
      (.binary "test_eq" leftTerm rightTerm)
      (Zkir.instruction "test_eq" [("a", toJson left), ("b", toJson right), ("output", toJson (freshName state.next))])
      ("test_eq", [left, right], none) (.testEq leftOperand rightOperand (freshName state.next))
      (bit (decide (leftOperand.read witness = rightOperand.read witness))) stateMeaning run
      (decode_binary_instruction_test_eq leftDecoded rightDecoded valid)
    · exact ⟨rfl, left, right, rfl, leftDecoded, rightDecoded, valid⟩
    · exact fresh_binary_scope state.next leftOperand rightOperand leftNames rightNames
    · exact testEq_output_holds hash witness (freshName state.next) leftOperand rightOperand
        (Operand.independent_of_scope state.next leftOperand leftNames)
        (Operand.independent_of_scope state.next rightOperand rightNames)
    · simp [interpret_testEq, leftValue, rightValue]
    · exact budget

theorem unary_neg_step (hash : Hash) (inputs witness : NativeRelation.Assignment)
    (state : Zkir.LowerState) (text : String) (term : Native.Term)
    (stateMeaning : LowerStateMeaning hash witness state)
    (meaning : OperandMeaning hash inputs witness text term)
    (scope : TextScope state.next text)
    (budget : ((Zkir.unary "neg" text).run state).2.next ≤ Native.maxInstructions * Native.maxVectorLength) :
    Nonempty (NativeStepResult hash inputs witness state (Zkir.unary "neg" text) (.unary "neg" term)) := by
  rcases meaning with ⟨operand, decoded, operandValue⟩
  have names := TextScope.identifiers scope decoded
  cases hit : state.expressions.lookup ("neg", [text], none) with
  | some output =>
    exact cached_step hash inputs witness state _ _ _ output stateMeaning hit
      (unary_cache_hit state "neg" text output hit)
      (ScalarCache.cached_neg_meaning hash inputs witness state stateMeaning text output term
        ⟨operand, decoded, operandValue⟩ hit) budget
  | none =>
    have run := unary_cache_miss state "neg" text hit
    have counter : state.next + 1 ≤ Native.maxInstructions * Native.maxVectorLength := by rw [run] at budget; exact budget
    have valid : validIdentifier (freshName state.next) = true := NativeRelationJson.generatedIdentifier_fits_output_capacity state.next (by omega)
    apply fresh_step hash inputs witness state (Zkir.unary "neg" text) (.unary "neg" term)
      (Zkir.instruction "neg" [("a", toJson text), ("output", toJson (freshName state.next))])
      ("neg", [text], none) (.neg operand (freshName state.next))
      (scalar (Field.modulus - (operand.read witness).val)) stateMeaning run (decode_unary_instruction_neg decoded valid)
    · exact ⟨rfl, text, rfl, decoded, valid⟩
    · exact fresh_unary_scope state.next operand names
    · exact neg_output_holds hash witness (freshName state.next) operand
        (Operand.independent_of_scope state.next operand names)
    · simp [interpret_neg, operandValue]
    · exact budget

theorem unary_not_step (hash : Hash) (inputs witness : NativeRelation.Assignment)
    (state : Zkir.LowerState) (text : String) (term : Native.Term)
    (stateMeaning : LowerStateMeaning hash witness state)
    (meaning : OperandMeaning hash inputs witness text term)
    (scope : TextScope state.next text)
    (boolean : interpret hash inputs term = zero ∨ interpret hash inputs term = one)
    (budget : ((Zkir.unary "not" text).run state).2.next ≤ Native.maxInstructions * Native.maxVectorLength) :
    Nonempty (NativeStepResult hash inputs witness state (Zkir.unary "not" text) (.unary "not" term)) := by
  rcases meaning with ⟨operand, decoded, operandValue⟩
  have names := TextScope.identifiers scope decoded
  have operandBoolean : operand.read witness = zero ∨ operand.read witness = one := by
    rcases boolean with isZero | isOne
    · exact Or.inl (Option.some.inj (operandValue.symm.trans isZero))
    · exact Or.inr (Option.some.inj (operandValue.symm.trans isOne))
  cases hit : state.expressions.lookup ("not", [text], none) with
  | some output =>
    exact cached_step hash inputs witness state _ _ _ output stateMeaning hit
      (unary_cache_hit state "not" text output hit)
      (ScalarCache.cached_not_meaning hash inputs witness state stateMeaning text output term
        ⟨operand, decoded, operandValue⟩ hit) budget
  | none =>
    have run := unary_cache_miss state "not" text hit
    have counter : state.next + 1 ≤ Native.maxInstructions * Native.maxVectorLength := by rw [run] at budget; exact budget
    have valid : validIdentifier (freshName state.next) = true := NativeRelationJson.generatedIdentifier_fits_output_capacity state.next (by omega)
    apply fresh_step hash inputs witness state (Zkir.unary "not" text) (.unary "not" term)
      (Zkir.instruction "not" [("a", toJson text), ("output", toJson (freshName state.next))])
      ("not", [text], none) (.not operand (freshName state.next))
      (if operand.read witness = zero then one else zero) stateMeaning run (decode_unary_instruction_not decoded valid)
    · exact ⟨rfl, text, rfl, decoded, valid⟩
    · exact fresh_unary_scope state.next operand names
    · exact not_output_holds hash witness (freshName state.next) operand
        (Operand.independent_of_scope state.next operand names)
        operandBoolean
    · simp [interpret_not, operandValue, bit]
    · exact budget


end Noctium.Verification.ScalarWitnessConstruction
