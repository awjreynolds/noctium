import Noctium.Verification.ScalarAllocation
import Noctium.Verification.ScalarCache
import Noctium.Verification.ScalarRangeLowering
import Noctium.Verification.ScalarStateExtensions

namespace Noctium.Verification.ScalarExpressionArithmetic

open Lean Backend NativeRelation NativeRelationJson ScalarNormalization ScalarLowering
open ScalarInstructionEncoding ScalarWitness

private def unchanged_result (hash : Hash) (inputs witness : NativeRelation.Assignment)
    (state : Zkir.LowerState) (normalAliases : Native.AliasEnvironment) (values : EvalEnv)
    (expression : Expr ty) (value : ty.Denote) (text : String) (normalized : Native.Normalized)
    (run : (Zkir.lowerExpr expression).run state = (text, state))
    (normalization : Native.normalize normalAliases expression = .ok normalized)
    (represents : Represents hash inputs ty normalized value)
    (meaning : OperandMeaning hash inputs witness text normalized.term)
    (scope : TextScope state.next text)
    (aliases : LowerAliasAgreement hash inputs witness normalAliases state.aliases values)
    (stateMeaning : LowerStateMeaning hash witness state)
    (budget : ((Zkir.lowerExpr expression).run state).2.next ≤ Native.maxInstructions * Native.maxVectorLength) :
    ExprStepResult hash inputs witness state normalAliases values expression value := {
  text, finalState := state, finalWitness := witness, normalized
  run, normalization, represents, operandMeaning := meaning, textScope := scope, stateMeaning
  budget := by rw [run] at budget; exact budget
  aliasAgreement := aliases
  aliasesPreserved := rfl
  frame := by intro name _; rfl
}

theorem complete_native (number : Nat) : ExprComplete (.native number) := by
  intro ctx hash implementation inputs witness state normalAliases values types value
    valid success aliases lowerAliases stateMeaning budget
  have sourceSuccess := success
  simp only [Expr.eval] at success
  split at success
  next canonical =>
    cases success
    have canonical : number < Field.modulus := by simpa only [implementation.modulus] using canonical
    obtain ⟨normalized, normalization, represents⟩ :=
      normalize_success ctx hash implementation inputs normalAliases values aliases (.native number) number sourceSuccess
    change Except.ok {term := .constant number : Native.Normalized} = .ok normalized at normalization
    cases normalization
    exact ⟨unchanged_result hash inputs witness state normalAliases values (.native number) number _ _
      (lowerExpr_native_run state number) rfl represents
      (OperandMeaning.fieldImmediate hash inputs witness number canonical) (TextScope.fieldImmediate state.next number canonical)
      lowerAliases stateMeaning budget⟩
  next => cases success

theorem complete_bool (boolean : Bool) : ExprComplete (.bool boolean) := by
  intro ctx hash implementation inputs witness state normalAliases values types value
    valid success aliases lowerAliases stateMeaning budget
  have sourceSuccess := success
  cases success
  obtain ⟨normalized, normalization, represents⟩ :=
    normalize_success ctx hash implementation inputs normalAliases values aliases (.bool boolean) boolean sourceSuccess
  cases boolean
  · change Except.ok {term := .constant 0, bounds := [(.constant 0, 1)] : Native.Normalized} =
      .ok normalized at normalization
    cases normalization
    have spelling : Zkir.fieldImmediate 0 = "0x00" := by decide
    exact ⟨unchanged_result hash inputs witness state normalAliases values (.bool false) false "0x00" {term := .constant 0, bounds := [(.constant 0, 1)]}
      (by simpa using lowerExpr_bool_run state false) rfl represents
      (by simpa only [spelling] using OperandMeaning.fieldImmediate hash inputs witness 0 (by decide))
      (by simpa only [spelling] using TextScope.fieldImmediate state.next 0 (by decide)) lowerAliases stateMeaning budget⟩
  · change Except.ok {term := .constant 1, bounds := [(.constant 1, 1)] : Native.Normalized} =
      .ok normalized at normalization
    cases normalization
    have spelling : Zkir.fieldImmediate 1 = "0x01" := by decide
    exact ⟨unchanged_result hash inputs witness state normalAliases values (.bool true) true "0x01" {term := .constant 1, bounds := [(.constant 1, 1)]}
      (by simpa using lowerExpr_bool_run state true) rfl represents
      (by simpa only [spelling] using OperandMeaning.fieldImmediate hash inputs witness 1 (by decide))
      (by simpa only [spelling] using TextScope.fieldImmediate state.next 1 (by decide)) lowerAliases stateMeaning budget⟩

theorem complete_uint (maximum number : Nat) : ExprComplete (.uint maximum number) := by
  intro ctx hash implementation inputs witness state normalAliases values types value
    valid success aliases lowerAliases stateMeaning budget
  have sourceSuccess := success
  simp only [Expr.eval] at success
  split at success
  next canonical =>
    cases success
    obtain ⟨normalized, normalization, represents⟩ :=
      normalize_success ctx hash implementation inputs normalAliases values aliases (.uint maximum number) number sourceSuccess
    simp only [Native.normalize, Native.requireSourceType_eq] at normalization
    cases normalization
    have fieldCanonical : number < Field.modulus := represents.1.1
    exact ⟨unchanged_result hash inputs witness state normalAliases values (.uint maximum number) number _ _
      (lowerExpr_uint_run state maximum number) rfl represents
      (OperandMeaning.fieldImmediate hash inputs witness number fieldCanonical) (TextScope.fieldImmediate state.next number fieldCanonical)
      lowerAliases stateMeaning budget⟩
  next => cases success

theorem complete_ref (ty : Ty) (name : String) : ExprComplete (.ref (ty := ty) name) := by
  intro ctx hash implementation inputs witness state normalAliases values types value
    valid success aliases lowerAliases stateMeaning budget
  have sourceSuccess := success
  simp only [Expr.eval] at success
  cases lookup : values.lookup name with
  | none => simp [lookup] at success
  | some raw =>
    simp only [lookup] at success
    cases typed : raw.as ty with
    | none => simp [typed] at success
    | some foundValue =>
      simp only [typed] at success
      split at success
      next => cases success
      next =>
        cases success
        obtain ⟨term, normalLookup, meaning⟩ := lowerAliases name ty raw value lookup typed
        obtain ⟨normalized, normalization, represents⟩ :=
          normalize_success ctx hash implementation inputs normalAliases values aliases (.ref (ty := ty) name) value sourceSuccess
        have termEq : normalized.term = term := by
          have normal := normalization
          simp only [Native.normalize, normalLookup] at normal
          cases normal
          simp only [Native.requireSourceType_eq]
        have scope : TextScope state.next (state.aliases.lookup name |>.getD ("%input_" ++ name)) := by
          obtain ⟨operand, parsed, _⟩ := meaning
          exact TextScope.lookup_default state.next state.aliases name operand parsed stateMeaning.aliases
        exact ⟨unchanged_result hash inputs witness state normalAliases values (.ref (ty := ty) name) value _ normalized
          (lowerExpr_ref_run state ty name) normalization represents (by rw [termEq]; exact meaning)
          scope lowerAliases stateMeaning budget⟩

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
    invariant.cacheTrace key output (ScalarValidation.lookup_member hit)
  have outputValid : validIdentifier output = true := by
    cases instruction <;> simp_all [CacheCorresponds] <;> grind
  have outputMember : output ∈ instructionIdentifiers instruction := by
    cases instruction <;> simp_all [CacheCorresponds, instructionIdentifiers]
  refine ⟨.reference output, (OperandEncoding.reference output outputValid).decode, ?_⟩
  intro name names
  have equal : name = output := by simpa only [operandIdentifiers, List.mem_singleton] using names
  subst name
  exact invariant.scope instructions decoded instruction member output outputMember

private theorem cached_step (hash : Hash) (inputs witness : NativeRelation.Assignment)
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

private theorem fresh_step (hash : Hash) (inputs witness : NativeRelation.Assignment)
    (state : Zkir.LowerState) (operation : StateM Zkir.LowerState String) (term : Native.Term)
    (raw : Json) (key : ExpressionKey) (instruction : Instruction) (value : Scalar)
    (stateMeaning : LowerStateMeaning hash witness state)
    (run : operation.run state =
      (freshName state.next, appendFreshState state raw key (freshName state.next)))
    (decoded : decodeInstruction raw = .ok instruction)
    (cacheMatch : CacheCorresponds key (freshName state.next) instruction)
    (scope : ∀ name ∈ instructionIdentifiers instruction, InScope (state.next + 1) name)
    (holds : instruction.Holds hash (assign witness (freshName state.next) value))
    (valueMeaning : value = interpret hash inputs term)
    (budget : (operation.run state).2.next ≤ Native.maxInstructions * Native.maxVectorLength) :
    Nonempty (NativeStepResult hash inputs witness state operation term) := by
  have finalBudget : state.next + 1 ≤ Native.maxInstructions * Native.maxVectorLength := by
    rw [run] at budget
    exact budget
  have valid : validIdentifier (freshName state.next) = true :=
    fresh_identifier state.next (by omega)
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
    have valid : validIdentifier (freshName state.next) = true := fresh_identifier state.next (by omega)
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
    · simp only [interpret_add, ← leftValue, ← rightValue]
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
    have valid : validIdentifier (freshName state.next) = true := fresh_identifier state.next (by omega)
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
    · simp only [interpret_mul, ← leftValue, ← rightValue]
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
    have valid : validIdentifier (freshName state.next) = true := fresh_identifier state.next (by omega)
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
    · simp only [interpret_testEq, ← leftValue, ← rightValue]
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
    have valid : validIdentifier (freshName state.next) = true := fresh_identifier state.next (by omega)
    apply fresh_step hash inputs witness state (Zkir.unary "neg" text) (.unary "neg" term)
      (Zkir.instruction "neg" [("a", toJson text), ("output", toJson (freshName state.next))])
      ("neg", [text], none) (.neg operand (freshName state.next))
      (scalar (Field.modulus - (operand.read witness).val)) stateMeaning run (decode_unary_instruction_neg decoded valid)
    · exact ⟨rfl, text, rfl, decoded, valid⟩
    · exact fresh_unary_scope state.next operand names
    · exact neg_output_holds hash witness (freshName state.next) operand
        (Operand.independent_of_scope state.next operand names)
    · simp only [interpret_neg, ← operandValue]
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
  cases hit : state.expressions.lookup ("not", [text], none) with
  | some output =>
    exact cached_step hash inputs witness state _ _ _ output stateMeaning hit
      (unary_cache_hit state "not" text output hit)
      (ScalarCache.cached_not_meaning hash inputs witness state stateMeaning text output term
        ⟨operand, decoded, operandValue⟩ hit) budget
  | none =>
    have run := unary_cache_miss state "not" text hit
    have counter : state.next + 1 ≤ Native.maxInstructions * Native.maxVectorLength := by rw [run] at budget; exact budget
    have valid : validIdentifier (freshName state.next) = true := fresh_identifier state.next (by omega)
    apply fresh_step hash inputs witness state (Zkir.unary "not" text) (.unary "not" term)
      (Zkir.instruction "not" [("a", toJson text), ("output", toJson (freshName state.next))])
      ("not", [text], none) (.not operand (freshName state.next))
      (if operand.read witness = zero then one else zero) stateMeaning run (decode_unary_instruction_not decoded valid)
    · exact ⟨rfl, text, rfl, decoded, valid⟩
    · exact fresh_unary_scope state.next operand names
    · exact not_output_holds hash witness (freshName state.next) operand
        (Operand.independent_of_scope state.next operand names)
        (by simpa only [operandValue] using boolean)
    · simp [interpret_not, ← operandValue, bit]
    · exact budget

theorem subtraction_preserves (left right : String) :
    ScalarAllocation.PreservesFrame (do let negated ← Zkir.unary "neg" right; Zkir.binary "add" left negated) :=
  ScalarAllocation.bind_preserves _ _ (ScalarAllocation.unary_preserves "neg" right ⟨by decide, by decide, by decide⟩)
    (fun negated => ScalarAllocation.binary_preserves "add" left negated ⟨by decide, by decide, by decide⟩)

theorem subtraction_step (hash : Hash) (inputs witness : NativeRelation.Assignment)
    (state : Zkir.LowerState) (left right : String) (leftTerm rightTerm : Native.Term)
    (stateMeaning : LowerStateMeaning hash witness state)
    (leftMeaning : OperandMeaning hash inputs witness left leftTerm)
    (rightMeaning : OperandMeaning hash inputs witness right rightTerm)
    (leftScope : TextScope state.next left) (rightScope : TextScope state.next right)
    (budget : ((do let negated ← Zkir.unary "neg" right; Zkir.binary "add" left negated).run state).2.next ≤ Native.maxInstructions * Native.maxVectorLength) :
    Nonempty (NativeStepResult hash inputs witness state
      (do let negated ← Zkir.unary "neg" right; Zkir.binary "add" left negated)
      (.binary "add" leftTerm (.unary "neg" rightTerm))) := by
  have unaryBudget := ScalarAllocation.bind_middle_budget (Zkir.unary "neg" right)
    (fun negated => Zkir.binary "add" left negated) state
    (fun negated => ScalarAllocation.binary_preserves "add" left negated ⟨by decide, by decide, by decide⟩) (Native.maxInstructions * Native.maxVectorLength) budget
  obtain ⟨negative⟩ := unary_neg_step hash inputs witness state right rightTerm stateMeaning rightMeaning rightScope unaryBudget
  have negativeNext : state.next ≤ negative.finalState.next := by
    have bound := (ScalarAllocation.unary_preserves "neg" right ⟨by decide, by decide, by decide⟩ state).next
    rw [negative.run] at bound
    exact bound
  have preservedLeft := OperandMeaning.of_frame hash inputs witness negative.finalWitness state.next left leftTerm
    leftMeaning leftScope negative.frame
  have preservedScope := TextScope.mono negativeNext leftScope
  have addBudget : ((Zkir.binary "add" left negative.text).run negative.finalState).2.next ≤ Native.maxInstructions * Native.maxVectorLength := by
    rw [StateT.run_bind, negative.run] at budget
    exact budget
  obtain ⟨added⟩ := binary_add_step hash inputs negative.finalWitness negative.finalState left negative.text
    leftTerm (.unary "neg" rightTerm) negative.stateMeaning preservedLeft negative.operandMeaning
    preservedScope negative.textScope addBudget
  exact ⟨negative.chain (fun negated => Zkir.binary "add" left negated) added negativeNext⟩

theorem boolean_cast_step (hash : Hash) (inputs witness : NativeRelation.Assignment)
    (state : Zkir.LowerState) (text : String) (term : Native.Term)
    (stateMeaning : LowerStateMeaning hash witness state)
    (meaning : OperandMeaning hash inputs witness text term) (scope : TextScope state.next text)
    (budget : ((do let compared ← Zkir.binary "test_eq" text "0x00"; Zkir.unary "not" compared).run state).2.next ≤ Native.maxInstructions * Native.maxVectorLength) :
    Nonempty (NativeStepResult hash inputs witness state
      (do let compared ← Zkir.binary "test_eq" text "0x00"; Zkir.unary "not" compared)
      (.unary "not" (.binary "test_eq" term (.constant 0)))) := by
  have compareBudget := ScalarAllocation.bind_middle_budget (Zkir.binary "test_eq" text "0x00")
    (fun compared => Zkir.unary "not" compared) state
    (fun compared => ScalarAllocation.unary_preserves "not" compared ⟨by decide, by decide, by decide⟩) (Native.maxInstructions * Native.maxVectorLength) budget
  have spelling : Zkir.fieldImmediate 0 = "0x00" := by decide
  obtain ⟨compared⟩ := binary_testEq_step hash inputs witness state text "0x00" term (.constant 0) stateMeaning meaning
    (by simpa only [spelling] using OperandMeaning.fieldImmediate hash inputs witness 0 (by decide)) scope
    (by simpa only [spelling] using TextScope.fieldImmediate state.next 0 (by decide)) compareBudget
  have compareNext : state.next ≤ compared.finalState.next := by
    have bound := (ScalarAllocation.binary_preserves "test_eq" text "0x00" ⟨by decide, by decide, by decide⟩ state).next
    rw [compared.run] at bound
    exact bound
  have boolean : interpret hash inputs (.binary "test_eq" term (.constant 0)) = zero ∨
      interpret hash inputs (.binary "test_eq" term (.constant 0)) = one := by
    rw [interpret_testEq]
    cases decide (interpret hash inputs term = interpret hash inputs (.constant 0)) <;> simp [bit]
  have notBudget : ((Zkir.unary "not" compared.text).run compared.finalState).2.next ≤ Native.maxInstructions * Native.maxVectorLength := by
    rw [StateT.run_bind, compared.run] at budget
    exact budget
  obtain ⟨negated⟩ := unary_not_step hash inputs compared.finalWitness compared.finalState compared.text
    (.binary "test_eq" term (.constant 0)) compared.stateMeaning compared.operandMeaning compared.textScope boolean notBudget
  exact ⟨compared.chain (fun compared => Zkir.unary "not" compared) negated compareNext⟩

private theorem state_from_suffix (hash : Hash) (witness afterWitness : NativeRelation.Assignment)
    (before after : Zkir.LowerState) (prior suffix : List Instruction)
    (meaning : LowerStateMeaning hash witness before)
    (priorDecoded : before.instructions.toList.mapM decodeInstruction = .ok prior)
    (afterDecoded : after.instructions.toList.mapM decodeInstruction = .ok (prior ++ suffix))
    (holds : ∀ instructions, after.instructions.toList.mapM decodeInstruction = .ok instructions →
      ∀ instruction ∈ instructions, instruction.Holds hash afterWitness)
    (next : before.next ≤ after.next) (aliasesSame : after.aliases = before.aliases)
    (cacheSame : after.expressions = before.expressions)
    (scope : ∀ instruction ∈ suffix, ∀ name ∈ instructionIdentifiers instruction, InScope after.next name) :
    LowerStateMeaning hash afterWitness after := by
  constructor
  · exact ⟨prior ++ suffix, afterDecoded⟩
  · exact holds
  · intro instructions checked instruction member name nameMember
    have equal : instructions = prior ++ suffix := Except.ok.inj (checked.symm.trans afterDecoded)
    subst instructions
    rcases List.mem_append.mp member with old | new
    · exact InScope.mono next (meaning.scope prior priorDecoded instruction old name nameMember)
    · exact scope instruction new name nameMember
  · intro name text member
    rw [aliasesSame] at member
    exact TextScope.mono next (meaning.aliases name text member)
  · intro key output member
    rw [cacheSame] at member
    obtain ⟨old, oldDecoded, instruction, instructionMember, correspondence⟩ := meaning.cacheTrace key output member
    have equal : old = prior := Except.ok.inj (oldDecoded.symm.trans priorDecoded)
    subst old
    exact ⟨prior ++ suffix, afterDecoded, instruction, List.mem_append_left _ instructionMember, correspondence⟩

theorem constrainUnsigned_step (hash : Hash) (inputs witness : NativeRelation.Assignment)
    (state : Zkir.LowerState) (maximum : Nat) (text : String) (term : Native.Term)
    (stateMeaning : LowerStateMeaning hash witness state)
    (meaning : OperandMeaning hash inputs witness text term) (scope : TextScope state.next text)
    (range : (interpret hash inputs term).val ≤ maximum) (admitted : maximum ≤ ScalarPolicy.maxUint)
    (budget : ((do Zkir.constrainUnsigned maximum text; pure text).run state).2.next ≤ Native.maxInstructions * Native.maxVectorLength) :
    Nonempty (NativeStepResult hash inputs witness state
      (do Zkir.constrainUnsigned maximum text; pure text) term) := by
  rcases meaning with ⟨operand, operandDecoded, operandValue⟩
  obtain ⟨prior, priorDecoded⟩ := stateMeaning.decoded
  have names := TextScope.identifiers scope operandDecoded
  let after := ((Zkir.constrainUnsigned maximum text).run state).2
  have next : state.next ≤ after.next := (ScalarAllocation.constrainUnsigned_preserves maximum text state).next
  have finalBudget : after.next ≤ Native.maxInstructions * Native.maxVectorLength := budget
  have beforeBudget : state.next ≤ Native.maxInstructions * Native.maxVectorLength := Nat.le_trans next finalBudget
  have independent := Operand.independent_of_scope state.next operand names
  have priorIndependent : ∀ instruction ∈ prior, InstructionIndependent (freshName state.next) instruction := by
    intro instruction member
    exact Instruction.independent_of_scope state.next instruction (stateMeaning.scope prior priorDecoded instruction member)
  obtain ⟨afterWitness, instructions, decoded, nativeHolds, stable, frame, extension⟩ :=
    ScalarRangeLowering.constrainUnsigned_complete hash witness state maximum text operand prior operandDecoded
      priorDecoded (stateMeaning.holds prior priorDecoded) (by rw [operandValue]; exact range)
      admitted beforeBudget independent priorIndependent
  have frameOld : ∀ name, InScope state.next name → afterWitness name = witness name := by
    intro name inScopeAt
    apply frame
    intro equal
    rw [equal] at inScopeAt
    exact fresh_not_inScope state.next inScopeAt
  have allHolds : ∀ found, after.instructions.toList.mapM decodeInstruction = .ok found →
      ∀ instruction ∈ found, instruction.Holds hash afterWitness := by
    intro found checked instruction member
    have equal : found = instructions := Except.ok.inj (checked.symm.trans decoded)
    subst found
    exact nativeHolds instruction member
  have aliasesSame : after.aliases = state.aliases := by
    dsimp only [after]
    by_cases isZero : maximum = 0
    · subst maximum
      rw [ScalarRangeLowering.zero_run]
    · by_cases power : maximum + 1 = 2 ^ (maximum.log2 + 1)
      · rw [ScalarRangeLowering.power_run state maximum text isZero power]
      · rw [ScalarRangeLowering.nonpower_run state maximum text isZero power]
  have cacheSame : after.expressions = state.expressions := by
    dsimp only [after]
    by_cases isZero : maximum = 0
    · subst maximum
      rw [ScalarRangeLowering.zero_run]
    · by_cases power : maximum + 1 = 2 ^ (maximum.log2 + 1)
      · rw [ScalarRangeLowering.power_run state maximum text isZero power]
      · rw [ScalarRangeLowering.nonpower_run state maximum text isZero power]
  have finalMeaning : LowerStateMeaning hash afterWitness after := by
    by_cases isZero : maximum = 0
    · subst maximum
      apply state_from_suffix hash witness afterWitness state after prior [.equal operand (.immediate zero)] stateMeaning
        priorDecoded (ScalarRangeLowering.zero_decode state text operand prior operandDecoded priorDecoded)
        allHolds next aliasesSame cacheSame
      intro instruction member name nameMember
      have equal := List.mem_singleton.mp member
      subst instruction
      have oldName : name ∈ operandIdentifiers operand := by
        simpa only [instructionIdentifiers, operandIdentifiers, List.append_nil] using nameMember
      exact InScope.mono next (names name oldName)
    · by_cases power : maximum + 1 = 2 ^ (maximum.log2 + 1)
      · apply state_from_suffix hash witness afterWitness state after prior [.bits operand (maximum.log2 + 1)] stateMeaning
          priorDecoded (ScalarRangeLowering.power_decode state maximum text operand prior isZero power admitted operandDecoded priorDecoded)
          allHolds next aliasesSame cacheSame
        intro instruction member name nameMember
        have equal := List.mem_singleton.mp member
        subst instruction
        exact InScope.mono next (names name nameMember)
      · apply state_from_suffix hash witness afterWitness state after prior
          [.bits operand (maximum.log2 + 1),
            .lessThan operand (.immediate (scalar (maximum + 1))) (maximum.log2 + 1) (freshName state.next),
            .assert (.reference (freshName state.next))] stateMeaning priorDecoded
          (ScalarRangeLowering.nonpower_decode state maximum text operand prior isZero power admitted beforeBudget operandDecoded priorDecoded)
          allHolds next aliasesSame cacheSame
        have nextEq : after.next = state.next + 1 := by
          dsimp only [after]
          rw [ScalarRangeLowering.nonpower_run state maximum text isZero power]
        intro instruction member name nameMember
        simp only [List.mem_cons, List.not_mem_nil, or_false] at member
        rcases member with rfl | rfl | rfl
        · exact InScope.mono next (names name nameMember)
        · rw [nextEq]
          exact fresh_binary_scope state.next operand (.immediate (scalar (maximum + 1))) names
            (by intro identifier absent; simp [operandIdentifiers] at absent) name nameMember
        · have equal : name = freshName state.next := by simpa only [instructionIdentifiers, operandIdentifiers, List.mem_singleton] using nameMember
          subst name
          rw [nextEq]
          exact Or.inr ⟨state.next, by omega, rfl⟩
  exact ⟨{
    text := text
    finalState := after
    finalWitness := afterWitness
    run := rfl
    operandMeaning := OperandMeaning.of_frame hash inputs witness afterWitness state.next text term
      ⟨operand, operandDecoded, operandValue⟩ scope frameOld
    textScope := TextScope.mono next scope
    stateMeaning := finalMeaning
    budget := finalBudget
    aliasesPreserved := aliasesSame
    frame := frameOld
  }⟩

theorem complete_add (left right : Expr .native) (ihLeft : ExprComplete left) (ihRight : ExprComplete right) :
    ExprComplete (.add left right) := by
  intro ctx hash implementation inputs witness state normalAliases values types value
    valid success aliases lowerAliases stateMeaning budget
  have validation := valid
  change (do left.validate {poseidon2 := true} types; right.validate {poseidon2 := true} types) = .ok () at validation
  simp only [ScalarValidation.bind_ok] at validation
  obtain ⟨leftUnit, leftValid, rightValid⟩ := validation
  cases leftUnit
  cases leftEval : left.eval ctx values with
  | error message => simp [Expr.eval, leftEval, implementation.modulus, Field.modulus, Bind.bind, Except.bind] at success
  | ok leftValue =>
    cases rightEval : right.eval ctx values with
    | error message => simp [Expr.eval, leftEval, rightEval, implementation.modulus, Field.modulus, Bind.bind, Except.bind] at success
    | ok rightValue =>
      have leftBudget := ScalarAllocation.bind_middle_budget (Zkir.lowerExpr left)
        (fun a => do let b ← Zkir.lowerExpr right; Zkir.binary "add" a b) state
        (fun a => ScalarAllocation.bind_preserves _ _ (ScalarAllocation.lowerExpr_preserves right)
          (fun b => ScalarAllocation.binary_preserves "add" a b ⟨by decide, by decide, by decide⟩)) (Native.maxInstructions * Native.maxVectorLength) budget
      obtain ⟨first⟩ := ihLeft ctx hash implementation inputs witness state normalAliases values types leftValue
        leftValid leftEval aliases lowerAliases stateMeaning leftBudget
      have remainingBudget : ((do let b ← Zkir.lowerExpr right; Zkir.binary "add" first.text b).run first.finalState).2.next ≤ Native.maxInstructions * Native.maxVectorLength := by
        have bound := budget
        change ((do let a ← Zkir.lowerExpr left; let b ← Zkir.lowerExpr right; Zkir.binary "add" a b).run state).2.next ≤ _ at bound
        rw [StateT.run_bind, first.run] at bound
        exact bound
      have rightBudget := ScalarAllocation.bind_middle_budget (Zkir.lowerExpr right)
        (fun b => Zkir.binary "add" first.text b) first.finalState
        (fun b => ScalarAllocation.binary_preserves "add" first.text b ⟨by decide, by decide, by decide⟩) (Native.maxInstructions * Native.maxVectorLength) remainingBudget
      obtain ⟨second⟩ := ihRight ctx hash implementation inputs first.finalWitness first.finalState normalAliases values types rightValue
        rightValid rightEval aliases first.aliasAgreement first.stateMeaning rightBudget
      have firstNext : state.next ≤ first.finalState.next := by
        have bound := ScalarAllocation.lowerExpr_next left state
        rw [first.run] at bound
        exact bound
      have secondNext : first.finalState.next ≤ second.finalState.next := by
        have bound := ScalarAllocation.lowerExpr_next right first.finalState
        rw [second.run] at bound
        exact bound
      have leftMeaning := OperandMeaning.of_frame hash inputs first.finalWitness second.finalWitness
        first.finalState.next first.text first.normalized.term first.operandMeaning first.textScope second.frame
      have leftScope := TextScope.mono secondNext first.textScope
      have nativeBudget : ((Zkir.binary "add" first.text second.text).run second.finalState).2.next ≤ Native.maxInstructions * Native.maxVectorLength := by
        rw [StateT.run_bind, second.run] at remainingBudget
        exact remainingBudget
      obtain ⟨native⟩ := binary_add_step hash inputs second.finalWitness second.finalState first.text second.text
        first.normalized.term second.normalized.term second.stateMeaning leftMeaning second.operandMeaning
        leftScope second.textScope nativeBudget
      obtain ⟨normalized, normalization, represents⟩ :=
        normalize_success ctx hash implementation inputs normalAliases values aliases (.add left right) value success
      have termEq : normalized.term = .binary "add" first.normalized.term second.normalized.term := by
        have normal := normalization
        simp only [Native.normalize, first.normalization, second.normalization] at normal
        cases normal
        simp only [Native.arithmetic_eq, Native.requireSourceType_eq]
      refine ⟨{
        text := native.text
        finalState := native.finalState
        finalWitness := native.finalWitness
        normalized := normalized
        run := ?_
        normalization := normalization
        represents := represents
        operandMeaning := by rw [termEq]; exact native.operandMeaning
        textScope := native.textScope
        stateMeaning := native.stateMeaning
        budget := native.budget
        aliasAgreement := ?_
        aliasesPreserved := native.aliasesPreserved.trans (second.aliasesPreserved.trans first.aliasesPreserved)
        frame := ?_
      }⟩
      · change ((do let a ← Zkir.lowerExpr left; let b ← Zkir.lowerExpr right; Zkir.binary "add" a b).run state) = _
        rw [StateT.run_bind, first.run]
        change ((do let b ← Zkir.lowerExpr right; Zkir.binary "add" first.text b).run first.finalState) = _
        rw [StateT.run_bind, second.run]
        exact native.run
      · rw [native.aliasesPreserved]
        exact LowerAliasAgreement.of_frame hash inputs second.finalWitness native.finalWitness second.finalState.next
          normalAliases second.finalState.aliases values second.aliasAgreement second.stateMeaning.aliases native.frame
      · intro name inScopeAt
        rw [native.frame name (InScope.mono secondNext (InScope.mono firstNext inScopeAt)),
          second.frame name (InScope.mono firstNext inScopeAt), first.frame name inScopeAt]

theorem complete_mul (left right : Expr .native) (ihLeft : ExprComplete left) (ihRight : ExprComplete right) :
    ExprComplete (.mul left right) := by
  intro ctx hash implementation inputs witness state normalAliases values types value
    valid success aliases lowerAliases stateMeaning budget
  have validation := valid
  change (do left.validate {poseidon2 := true} types; right.validate {poseidon2 := true} types) = .ok () at validation
  simp only [ScalarValidation.bind_ok] at validation
  obtain ⟨leftUnit, leftValid, rightValid⟩ := validation
  cases leftUnit
  cases leftEval : left.eval ctx values with
  | error message => simp [Expr.eval, leftEval, implementation.modulus, Field.modulus, Bind.bind, Except.bind] at success
  | ok leftValue =>
    cases rightEval : right.eval ctx values with
    | error message => simp [Expr.eval, leftEval, rightEval, implementation.modulus, Field.modulus, Bind.bind, Except.bind] at success
    | ok rightValue =>
      have leftBudget := ScalarAllocation.bind_middle_budget (Zkir.lowerExpr left)
        (fun a => do let b ← Zkir.lowerExpr right; Zkir.binary "mul" a b) state
        (fun a => ScalarAllocation.bind_preserves _ _ (ScalarAllocation.lowerExpr_preserves right)
          (fun b => ScalarAllocation.binary_preserves "mul" a b ⟨by decide, by decide, by decide⟩)) (Native.maxInstructions * Native.maxVectorLength) budget
      obtain ⟨first⟩ := ihLeft ctx hash implementation inputs witness state normalAliases values types leftValue
        leftValid leftEval aliases lowerAliases stateMeaning leftBudget
      have remainingBudget : ((do let b ← Zkir.lowerExpr right; Zkir.binary "mul" first.text b).run first.finalState).2.next ≤ Native.maxInstructions * Native.maxVectorLength := by
        have bound := budget
        change ((do let a ← Zkir.lowerExpr left; let b ← Zkir.lowerExpr right; Zkir.binary "mul" a b).run state).2.next ≤ _ at bound
        rw [StateT.run_bind, first.run] at bound
        exact bound
      have rightBudget := ScalarAllocation.bind_middle_budget (Zkir.lowerExpr right)
        (fun b => Zkir.binary "mul" first.text b) first.finalState
        (fun b => ScalarAllocation.binary_preserves "mul" first.text b ⟨by decide, by decide, by decide⟩) (Native.maxInstructions * Native.maxVectorLength) remainingBudget
      obtain ⟨second⟩ := ihRight ctx hash implementation inputs first.finalWitness first.finalState normalAliases values types rightValue
        rightValid rightEval aliases first.aliasAgreement first.stateMeaning rightBudget
      have firstNext : state.next ≤ first.finalState.next := by
        have bound := ScalarAllocation.lowerExpr_next left state
        rw [first.run] at bound
        exact bound
      have secondNext : first.finalState.next ≤ second.finalState.next := by
        have bound := ScalarAllocation.lowerExpr_next right first.finalState
        rw [second.run] at bound
        exact bound
      have leftMeaning := OperandMeaning.of_frame hash inputs first.finalWitness second.finalWitness
        first.finalState.next first.text first.normalized.term first.operandMeaning first.textScope second.frame
      have leftScope := TextScope.mono secondNext first.textScope
      have nativeBudget : ((Zkir.binary "mul" first.text second.text).run second.finalState).2.next ≤ Native.maxInstructions * Native.maxVectorLength := by
        rw [StateT.run_bind, second.run] at remainingBudget
        exact remainingBudget
      obtain ⟨native⟩ := binary_mul_step hash inputs second.finalWitness second.finalState first.text second.text
        first.normalized.term second.normalized.term second.stateMeaning leftMeaning second.operandMeaning
        leftScope second.textScope nativeBudget
      obtain ⟨normalized, normalization, represents⟩ :=
        normalize_success ctx hash implementation inputs normalAliases values aliases (.mul left right) value success
      have termEq : normalized.term = .binary "mul" first.normalized.term second.normalized.term := by
        have normal := normalization
        simp only [Native.normalize, first.normalization, second.normalization] at normal
        cases normal
        simp only [Native.arithmetic_eq, Native.requireSourceType_eq]
      refine ⟨{
        text := native.text
        finalState := native.finalState
        finalWitness := native.finalWitness
        normalized := normalized
        run := ?_
        normalization := normalization
        represents := represents
        operandMeaning := by rw [termEq]; exact native.operandMeaning
        textScope := native.textScope
        stateMeaning := native.stateMeaning
        budget := native.budget
        aliasAgreement := ?_
        aliasesPreserved := native.aliasesPreserved.trans (second.aliasesPreserved.trans first.aliasesPreserved)
        frame := ?_
      }⟩
      · change ((do let a ← Zkir.lowerExpr left; let b ← Zkir.lowerExpr right; Zkir.binary "mul" a b).run state) = _
        rw [StateT.run_bind, first.run]
        change ((do let b ← Zkir.lowerExpr right; Zkir.binary "mul" first.text b).run first.finalState) = _
        rw [StateT.run_bind, second.run]
        exact native.run
      · rw [native.aliasesPreserved]
        exact LowerAliasAgreement.of_frame hash inputs second.finalWitness native.finalWitness second.finalState.next
          normalAliases second.finalState.aliases values second.aliasAgreement second.stateMeaning.aliases native.frame
      · intro name inScopeAt
        rw [native.frame name (InScope.mono secondNext (InScope.mono firstNext inScopeAt)),
          second.frame name (InScope.mono firstNext inScopeAt), first.frame name inScopeAt]

theorem complete_uadd {m n : Nat} (left : Expr (.uint m)) (right : Expr (.uint n))
    (ihLeft : ExprComplete left) (ihRight : ExprComplete right) : ExprComplete (.uadd left right) := by
  intro ctx hash implementation inputs witness state normalAliases values types value
    valid success aliases lowerAliases stateMeaning budget
  let tail (a b : String) : StateM Zkir.LowerState String := do
    let output ← Zkir.binary "add" a b
    Zkir.constrainUnsigned (m + n) output
    pure output
  have tailPreserves (a b : String) : ScalarAllocation.PreservesFrame (tail a b) :=
    ScalarAllocation.bind_preserves _ _ (ScalarAllocation.binary_preserves "add" a b ⟨by decide, by decide, by decide⟩)
      (fun output => ScalarAllocation.bind_preserves _ _ (ScalarAllocation.constrainUnsigned_preserves (m + n) output)
        (fun _ => ScalarAllocation.pure_preserves output))
  change ((do let a ← Zkir.lowerExpr left; let b ← Zkir.lowerExpr right; tail a b).run state).2.next ≤ _ at budget
  have validation := valid
  change (do
    (Ty.uint (m + n)).validate {poseidon2 := true}
    left.validate {poseidon2 := true} types
    right.validate {poseidon2 := true} types) = .ok () at validation
  simp only [ScalarValidation.bind_ok] at validation
  obtain ⟨_, _, leftUnit, leftValid, rightValid⟩ := validation
  cases leftUnit
  cases leftEval : left.eval ctx values with
  | error message => simp [Expr.eval, leftEval, Bind.bind, Except.bind] at success
  | ok leftValue =>
    cases rightEval : right.eval ctx values with
    | error message => simp [Expr.eval, leftEval, rightEval, Bind.bind, Except.bind] at success
    | ok rightValue =>
      have leftBudget := ScalarAllocation.bind_middle_budget (Zkir.lowerExpr left)
        (fun a => do let b ← Zkir.lowerExpr right; tail a b) state
        (fun a => ScalarAllocation.bind_preserves _ _ (ScalarAllocation.lowerExpr_preserves right) (tailPreserves a))
        (Native.maxInstructions * Native.maxVectorLength) budget
      obtain ⟨first⟩ := ihLeft ctx hash implementation inputs witness state normalAliases values types leftValue
        leftValid leftEval aliases lowerAliases stateMeaning leftBudget
      have remainingBudget : ((do let b ← Zkir.lowerExpr right; tail first.text b).run first.finalState).2.next ≤ Native.maxInstructions * Native.maxVectorLength := by
        have bound := budget
        rw [StateT.run_bind, first.run] at bound
        exact bound
      have rightBudget := ScalarAllocation.bind_middle_budget (Zkir.lowerExpr right) (tail first.text) first.finalState
        (tailPreserves first.text) (Native.maxInstructions * Native.maxVectorLength) remainingBudget
      obtain ⟨second⟩ := ihRight ctx hash implementation inputs first.finalWitness first.finalState normalAliases values types rightValue
        rightValid rightEval aliases first.aliasAgreement first.stateMeaning rightBudget
      have firstNext : state.next ≤ first.finalState.next := by
        have bound := ScalarAllocation.lowerExpr_next left state
        rw [first.run] at bound
        exact bound
      have secondNext : first.finalState.next ≤ second.finalState.next := by
        have bound := ScalarAllocation.lowerExpr_next right first.finalState
        rw [second.run] at bound
        exact bound
      have leftMeaning := OperandMeaning.of_frame hash inputs first.finalWitness second.finalWitness
        first.finalState.next first.text first.normalized.term first.operandMeaning first.textScope second.frame
      have leftScope := TextScope.mono secondNext first.textScope
      have tailBudget : ((tail first.text second.text).run second.finalState).2.next ≤ Native.maxInstructions * Native.maxVectorLength := by
        rw [StateT.run_bind, second.run] at remainingBudget
        exact remainingBudget
      have binaryBudget := ScalarAllocation.bind_middle_budget (Zkir.binary "add" first.text second.text)
        (fun output => do Zkir.constrainUnsigned (m + n) output; pure output) second.finalState
        (fun output => ScalarAllocation.bind_preserves _ _ (ScalarAllocation.constrainUnsigned_preserves (m + n) output)
          (fun _ => ScalarAllocation.pure_preserves output)) (Native.maxInstructions * Native.maxVectorLength) tailBudget
      obtain ⟨binary⟩ := binary_add_step hash inputs second.finalWitness second.finalState first.text second.text
        first.normalized.term second.normalized.term second.stateMeaning leftMeaning second.operandMeaning
        leftScope second.textScope binaryBudget
      have binaryNext : second.finalState.next ≤ binary.finalState.next := by
        have bound := (ScalarAllocation.binary_preserves "add" first.text second.text ⟨by decide, by decide, by decide⟩ second.finalState).next
        rw [binary.run] at bound
        exact bound
      obtain ⟨normalized, normalization, represents⟩ :=
        normalize_success ctx hash implementation inputs normalAliases values aliases (.uadd left right) value success
      have termEq : normalized.term = .binary "add" first.normalized.term second.normalized.term := by
        have normal := normalization
        simp only [Native.normalize, first.normalization, second.normalization] at normal
        cases normal
        simp only [Native.arithmetic_eq, Native.requireSourceType_eq]
      have resultRange : (interpret hash inputs (.binary "add" first.normalized.term second.normalized.term)).val ≤ m + n := by
        rw [← termEq, represents.2.2]
        exact Nat.le_trans (Nat.mod_le value Field.modulus) represents.1.2.2
      have rangeBudget : ((do Zkir.constrainUnsigned (m + n) binary.text; pure binary.text).run binary.finalState).2.next ≤ Native.maxInstructions * Native.maxVectorLength := by
        change ((do let output ← Zkir.binary "add" first.text second.text; Zkir.constrainUnsigned (m + n) output; pure output).run second.finalState).2.next ≤ _ at tailBudget
        rw [StateT.run_bind, binary.run] at tailBudget
        exact tailBudget
      obtain ⟨bounded⟩ := constrainUnsigned_step hash inputs binary.finalWitness binary.finalState (m + n) binary.text
        (.binary "add" first.normalized.term second.normalized.term) binary.stateMeaning binary.operandMeaning binary.textScope
        resultRange represents.1.2.1 rangeBudget
      let native := binary.chain (fun output => do Zkir.constrainUnsigned (m + n) output; pure output) bounded binaryNext
      refine ⟨{
        text := native.text
        finalState := native.finalState
        finalWitness := native.finalWitness
        normalized := normalized
        run := ?_
        normalization := normalization
        represents := represents
        operandMeaning := by rw [termEq]; exact native.operandMeaning
        textScope := native.textScope
        stateMeaning := native.stateMeaning
        budget := native.budget
        aliasAgreement := ?_
        aliasesPreserved := native.aliasesPreserved.trans (second.aliasesPreserved.trans first.aliasesPreserved)
        frame := ?_
      }⟩
      · change ((do let a ← Zkir.lowerExpr left; let b ← Zkir.lowerExpr right; tail a b).run state) = _
        rw [StateT.run_bind, first.run]
        change ((do let b ← Zkir.lowerExpr right; tail first.text b).run first.finalState) = _
        rw [StateT.run_bind, second.run]
        exact native.run
      · rw [native.aliasesPreserved]
        exact LowerAliasAgreement.of_frame hash inputs second.finalWitness native.finalWitness second.finalState.next
          normalAliases second.finalState.aliases values second.aliasAgreement second.stateMeaning.aliases native.frame
      · intro name inScopeAt
        rw [native.frame name (InScope.mono secondNext (InScope.mono firstNext inScopeAt)),
          second.frame name (InScope.mono firstNext inScopeAt), first.frame name inScopeAt]

theorem complete_umul {m n : Nat} (left : Expr (.uint m)) (right : Expr (.uint n))
    (ihLeft : ExprComplete left) (ihRight : ExprComplete right) : ExprComplete (.umul left right) := by
  intro ctx hash implementation inputs witness state normalAliases values types value
    valid success aliases lowerAliases stateMeaning budget
  let tail (a b : String) : StateM Zkir.LowerState String := do
    let output ← Zkir.binary "mul" a b
    Zkir.constrainUnsigned (m * n) output
    pure output
  have tailPreserves (a b : String) : ScalarAllocation.PreservesFrame (tail a b) :=
    ScalarAllocation.bind_preserves _ _ (ScalarAllocation.binary_preserves "mul" a b ⟨by decide, by decide, by decide⟩)
      (fun output => ScalarAllocation.bind_preserves _ _ (ScalarAllocation.constrainUnsigned_preserves (m * n) output)
        (fun _ => ScalarAllocation.pure_preserves output))
  change ((do let a ← Zkir.lowerExpr left; let b ← Zkir.lowerExpr right; tail a b).run state).2.next ≤ _ at budget
  have validation := valid
  change (do
    (Ty.uint (m * n)).validate {poseidon2 := true}
    left.validate {poseidon2 := true} types
    right.validate {poseidon2 := true} types) = .ok () at validation
  simp only [ScalarValidation.bind_ok] at validation
  obtain ⟨_, _, leftUnit, leftValid, rightValid⟩ := validation
  cases leftUnit
  cases leftEval : left.eval ctx values with
  | error message => simp [Expr.eval, leftEval, Bind.bind, Except.bind] at success
  | ok leftValue =>
    cases rightEval : right.eval ctx values with
    | error message => simp [Expr.eval, leftEval, rightEval, Bind.bind, Except.bind] at success
    | ok rightValue =>
      have leftBudget := ScalarAllocation.bind_middle_budget (Zkir.lowerExpr left)
        (fun a => do let b ← Zkir.lowerExpr right; tail a b) state
        (fun a => ScalarAllocation.bind_preserves _ _ (ScalarAllocation.lowerExpr_preserves right) (tailPreserves a))
        (Native.maxInstructions * Native.maxVectorLength) budget
      obtain ⟨first⟩ := ihLeft ctx hash implementation inputs witness state normalAliases values types leftValue
        leftValid leftEval aliases lowerAliases stateMeaning leftBudget
      have remainingBudget : ((do let b ← Zkir.lowerExpr right; tail first.text b).run first.finalState).2.next ≤ Native.maxInstructions * Native.maxVectorLength := by
        have bound := budget
        rw [StateT.run_bind, first.run] at bound
        exact bound
      have rightBudget := ScalarAllocation.bind_middle_budget (Zkir.lowerExpr right) (tail first.text) first.finalState
        (tailPreserves first.text) (Native.maxInstructions * Native.maxVectorLength) remainingBudget
      obtain ⟨second⟩ := ihRight ctx hash implementation inputs first.finalWitness first.finalState normalAliases values types rightValue
        rightValid rightEval aliases first.aliasAgreement first.stateMeaning rightBudget
      have firstNext : state.next ≤ first.finalState.next := by
        have bound := ScalarAllocation.lowerExpr_next left state
        rw [first.run] at bound
        exact bound
      have secondNext : first.finalState.next ≤ second.finalState.next := by
        have bound := ScalarAllocation.lowerExpr_next right first.finalState
        rw [second.run] at bound
        exact bound
      have leftMeaning := OperandMeaning.of_frame hash inputs first.finalWitness second.finalWitness
        first.finalState.next first.text first.normalized.term first.operandMeaning first.textScope second.frame
      have leftScope := TextScope.mono secondNext first.textScope
      have tailBudget : ((tail first.text second.text).run second.finalState).2.next ≤ Native.maxInstructions * Native.maxVectorLength := by
        rw [StateT.run_bind, second.run] at remainingBudget
        exact remainingBudget
      have binaryBudget := ScalarAllocation.bind_middle_budget (Zkir.binary "mul" first.text second.text)
        (fun output => do Zkir.constrainUnsigned (m * n) output; pure output) second.finalState
        (fun output => ScalarAllocation.bind_preserves _ _ (ScalarAllocation.constrainUnsigned_preserves (m * n) output)
          (fun _ => ScalarAllocation.pure_preserves output)) (Native.maxInstructions * Native.maxVectorLength) tailBudget
      obtain ⟨binary⟩ := binary_mul_step hash inputs second.finalWitness second.finalState first.text second.text
        first.normalized.term second.normalized.term second.stateMeaning leftMeaning second.operandMeaning
        leftScope second.textScope binaryBudget
      have binaryNext : second.finalState.next ≤ binary.finalState.next := by
        have bound := (ScalarAllocation.binary_preserves "mul" first.text second.text ⟨by decide, by decide, by decide⟩ second.finalState).next
        rw [binary.run] at bound
        exact bound
      obtain ⟨normalized, normalization, represents⟩ :=
        normalize_success ctx hash implementation inputs normalAliases values aliases (.umul left right) value success
      have termEq : normalized.term = .binary "mul" first.normalized.term second.normalized.term := by
        have normal := normalization
        simp only [Native.normalize, first.normalization, second.normalization] at normal
        cases normal
        simp only [Native.arithmetic_eq, Native.requireSourceType_eq]
      have resultRange : (interpret hash inputs (.binary "mul" first.normalized.term second.normalized.term)).val ≤ m * n := by
        rw [← termEq, represents.2.2]
        exact Nat.le_trans (Nat.mod_le value Field.modulus) represents.1.2.2
      have rangeBudget : ((do Zkir.constrainUnsigned (m * n) binary.text; pure binary.text).run binary.finalState).2.next ≤ Native.maxInstructions * Native.maxVectorLength := by
        change ((do let output ← Zkir.binary "mul" first.text second.text; Zkir.constrainUnsigned (m * n) output; pure output).run second.finalState).2.next ≤ _ at tailBudget
        rw [StateT.run_bind, binary.run] at tailBudget
        exact tailBudget
      obtain ⟨bounded⟩ := constrainUnsigned_step hash inputs binary.finalWitness binary.finalState (m * n) binary.text
        (.binary "mul" first.normalized.term second.normalized.term) binary.stateMeaning binary.operandMeaning binary.textScope
        resultRange represents.1.2.1 rangeBudget
      let native := binary.chain (fun output => do Zkir.constrainUnsigned (m * n) output; pure output) bounded binaryNext
      refine ⟨{
        text := native.text
        finalState := native.finalState
        finalWitness := native.finalWitness
        normalized := normalized
        run := ?_
        normalization := normalization
        represents := represents
        operandMeaning := by rw [termEq]; exact native.operandMeaning
        textScope := native.textScope
        stateMeaning := native.stateMeaning
        budget := native.budget
        aliasAgreement := ?_
        aliasesPreserved := native.aliasesPreserved.trans (second.aliasesPreserved.trans first.aliasesPreserved)
        frame := ?_
      }⟩
      · change ((do let a ← Zkir.lowerExpr left; let b ← Zkir.lowerExpr right; tail a b).run state) = _
        rw [StateT.run_bind, first.run]
        change ((do let b ← Zkir.lowerExpr right; tail first.text b).run first.finalState) = _
        rw [StateT.run_bind, second.run]
        exact native.run
      · rw [native.aliasesPreserved]
        exact LowerAliasAgreement.of_frame hash inputs second.finalWitness native.finalWitness second.finalState.next
          normalAliases second.finalState.aliases values second.aliasAgreement second.stateMeaning.aliases native.frame
      · intro name inScopeAt
        rw [native.frame name (InScope.mono secondNext (InScope.mono firstNext inScopeAt)),
          second.frame name (InScope.mono firstNext inScopeAt), first.frame name inScopeAt]

theorem complete_sub (left right : Expr .native) (ihLeft : ExprComplete left) (ihRight : ExprComplete right) :
    ExprComplete (.sub left right) := by
  intro ctx hash implementation inputs witness state normalAliases values types value
    valid success aliases lowerAliases stateMeaning budget
  let tail (a b : String) : StateM Zkir.LowerState String := do
    let negated ← Zkir.unary "neg" b
    Zkir.binary "add" a negated
  have tailPreserves (a b : String) : ScalarAllocation.PreservesFrame (tail a b) :=
    ScalarAllocation.bind_preserves _ _ (ScalarAllocation.unary_preserves "neg" b ⟨by decide, by decide, by decide⟩)
      (fun negated => ScalarAllocation.binary_preserves "add" a negated ⟨by decide, by decide, by decide⟩)
  have validation := valid
  change (do left.validate {poseidon2 := true} types; right.validate {poseidon2 := true} types) = .ok () at validation
  simp only [ScalarValidation.bind_ok] at validation
  obtain ⟨leftUnit, leftValid, rightValid⟩ := validation
  cases leftUnit
  cases leftEval : left.eval ctx values with
  | error message => simp [Expr.eval, leftEval, implementation.modulus, Field.modulus, Bind.bind, Except.bind] at success
  | ok leftValue =>
    cases rightEval : right.eval ctx values with
    | error message => simp [Expr.eval, leftEval, rightEval, implementation.modulus, Field.modulus, Bind.bind, Except.bind] at success
    | ok rightValue =>
      have leftBudget := ScalarAllocation.bind_middle_budget (Zkir.lowerExpr left)
        (fun a => do let b ← Zkir.lowerExpr right; tail a b) state
        (fun a => ScalarAllocation.bind_preserves _ _ (ScalarAllocation.lowerExpr_preserves right)
          (fun b => tailPreserves a b)) (Native.maxInstructions * Native.maxVectorLength) budget
      obtain ⟨first⟩ := ihLeft ctx hash implementation inputs witness state normalAliases values types leftValue
        leftValid leftEval aliases lowerAliases stateMeaning leftBudget
      have remainingBudget : ((do let b ← Zkir.lowerExpr right; tail first.text b).run first.finalState).2.next ≤ Native.maxInstructions * Native.maxVectorLength := by
        have bound := budget
        change ((do let a ← Zkir.lowerExpr left; let b ← Zkir.lowerExpr right; tail a b).run state).2.next ≤ _ at bound
        rw [StateT.run_bind, first.run] at bound
        exact bound
      have rightBudget := ScalarAllocation.bind_middle_budget (Zkir.lowerExpr right)
        (fun b => tail first.text b) first.finalState
        (fun b => tailPreserves first.text b) (Native.maxInstructions * Native.maxVectorLength) remainingBudget
      obtain ⟨second⟩ := ihRight ctx hash implementation inputs first.finalWitness first.finalState normalAliases values types rightValue
        rightValid rightEval aliases first.aliasAgreement first.stateMeaning rightBudget
      have firstNext : state.next ≤ first.finalState.next := by
        have bound := ScalarAllocation.lowerExpr_next left state
        rw [first.run] at bound
        exact bound
      have secondNext : first.finalState.next ≤ second.finalState.next := by
        have bound := ScalarAllocation.lowerExpr_next right first.finalState
        rw [second.run] at bound
        exact bound
      have leftMeaning := OperandMeaning.of_frame hash inputs first.finalWitness second.finalWitness
        first.finalState.next first.text first.normalized.term first.operandMeaning first.textScope second.frame
      have leftScope := TextScope.mono secondNext first.textScope
      have nativeBudget : ((tail first.text second.text).run second.finalState).2.next ≤ Native.maxInstructions * Native.maxVectorLength := by
        rw [StateT.run_bind, second.run] at remainingBudget
        exact remainingBudget
      obtain ⟨native⟩ := subtraction_step hash inputs second.finalWitness second.finalState first.text second.text
        first.normalized.term second.normalized.term second.stateMeaning leftMeaning second.operandMeaning
        leftScope second.textScope nativeBudget
      obtain ⟨normalized, normalization, represents⟩ :=
        normalize_success ctx hash implementation inputs normalAliases values aliases (.sub left right) value success
      have termEq : normalized.term = .binary "add" first.normalized.term (.unary "neg" second.normalized.term) := by
        have normal := normalization
        simp only [Native.normalize, first.normalization, second.normalization] at normal
        cases normal
        simp only [Native.subtraction_eq, Native.requireSourceType_eq]
      refine ⟨{
        text := native.text
        finalState := native.finalState
        finalWitness := native.finalWitness
        normalized := normalized
        run := ?_
        normalization := normalization
        represents := represents
        operandMeaning := by rw [termEq]; exact native.operandMeaning
        textScope := native.textScope
        stateMeaning := native.stateMeaning
        budget := native.budget
        aliasAgreement := ?_
        aliasesPreserved := native.aliasesPreserved.trans (second.aliasesPreserved.trans first.aliasesPreserved)
        frame := ?_
      }⟩
      · change ((do let a ← Zkir.lowerExpr left; let b ← Zkir.lowerExpr right; tail a b).run state) = _
        rw [StateT.run_bind, first.run]
        change ((do let b ← Zkir.lowerExpr right; tail first.text b).run first.finalState) = _
        rw [StateT.run_bind, second.run]
        exact native.run
      · rw [native.aliasesPreserved]
        exact LowerAliasAgreement.of_frame hash inputs second.finalWitness native.finalWitness second.finalState.next
          normalAliases second.finalState.aliases values second.aliasAgreement second.stateMeaning.aliases native.frame
      · intro name inScopeAt
        rw [native.frame name (InScope.mono secondNext (InScope.mono firstNext inScopeAt)),
          second.frame name (InScope.mono firstNext inScopeAt), first.frame name inScopeAt]

theorem complete_usub {m n : Nat} (left : Expr (.uint m)) (right : Expr (.uint n))
    (ihLeft : ExprComplete left) (ihRight : ExprComplete right) : ExprComplete (.usub left right) := by
  intro ctx hash implementation inputs witness state normalAliases values types value
    valid success aliases lowerAliases stateMeaning budget
  let tail (a b : String) : StateM Zkir.LowerState String := do
    let output ← (do let negated ← Zkir.unary "neg" b; Zkir.binary "add" a negated)
    Zkir.constrainUnsigned (m) output
    pure output
  have tailPreserves (a b : String) : ScalarAllocation.PreservesFrame (tail a b) :=
    ScalarAllocation.bind_preserves _ _ (subtraction_preserves a b)
      (fun output => ScalarAllocation.bind_preserves _ _ (ScalarAllocation.constrainUnsigned_preserves (m) output)
        (fun _ => ScalarAllocation.pure_preserves output))
  change ((do let a ← Zkir.lowerExpr left; let b ← Zkir.lowerExpr right; tail a b).run state).2.next ≤ _ at budget
  have validation := valid
  change (do
    (Ty.uint (m)).validate {poseidon2 := true}
    left.validate {poseidon2 := true} types
    right.validate {poseidon2 := true} types) = .ok () at validation
  simp only [ScalarValidation.bind_ok] at validation
  obtain ⟨_, _, leftUnit, leftValid, rightValid⟩ := validation
  cases leftUnit
  cases leftEval : left.eval ctx values with
  | error message => simp [Expr.eval, leftEval, Bind.bind, Except.bind] at success
  | ok leftValue =>
    cases rightEval : right.eval ctx values with
    | error message => simp [Expr.eval, leftEval, rightEval, Bind.bind, Except.bind] at success
    | ok rightValue =>
      have leftBudget := ScalarAllocation.bind_middle_budget (Zkir.lowerExpr left)
        (fun a => do let b ← Zkir.lowerExpr right; tail a b) state
        (fun a => ScalarAllocation.bind_preserves _ _ (ScalarAllocation.lowerExpr_preserves right) (tailPreserves a))
        (Native.maxInstructions * Native.maxVectorLength) budget
      obtain ⟨first⟩ := ihLeft ctx hash implementation inputs witness state normalAliases values types leftValue
        leftValid leftEval aliases lowerAliases stateMeaning leftBudget
      have remainingBudget : ((do let b ← Zkir.lowerExpr right; tail first.text b).run first.finalState).2.next ≤ Native.maxInstructions * Native.maxVectorLength := by
        have bound := budget
        rw [StateT.run_bind, first.run] at bound
        exact bound
      have rightBudget := ScalarAllocation.bind_middle_budget (Zkir.lowerExpr right) (tail first.text) first.finalState
        (tailPreserves first.text) (Native.maxInstructions * Native.maxVectorLength) remainingBudget
      obtain ⟨second⟩ := ihRight ctx hash implementation inputs first.finalWitness first.finalState normalAliases values types rightValue
        rightValid rightEval aliases first.aliasAgreement first.stateMeaning rightBudget
      have firstNext : state.next ≤ first.finalState.next := by
        have bound := ScalarAllocation.lowerExpr_next left state
        rw [first.run] at bound
        exact bound
      have secondNext : first.finalState.next ≤ second.finalState.next := by
        have bound := ScalarAllocation.lowerExpr_next right first.finalState
        rw [second.run] at bound
        exact bound
      have leftMeaning := OperandMeaning.of_frame hash inputs first.finalWitness second.finalWitness
        first.finalState.next first.text first.normalized.term first.operandMeaning first.textScope second.frame
      have leftScope := TextScope.mono secondNext first.textScope
      have tailBudget : ((tail first.text second.text).run second.finalState).2.next ≤ Native.maxInstructions * Native.maxVectorLength := by
        rw [StateT.run_bind, second.run] at remainingBudget
        exact remainingBudget
      have binaryBudget := ScalarAllocation.bind_middle_budget (do let negated ← Zkir.unary "neg" second.text; Zkir.binary "add" first.text negated)
        (fun output => do Zkir.constrainUnsigned (m) output; pure output) second.finalState
        (fun output => ScalarAllocation.bind_preserves _ _ (ScalarAllocation.constrainUnsigned_preserves (m) output)
          (fun _ => ScalarAllocation.pure_preserves output)) (Native.maxInstructions * Native.maxVectorLength) tailBudget
      obtain ⟨binary⟩ := subtraction_step hash inputs second.finalWitness second.finalState first.text second.text
        first.normalized.term second.normalized.term second.stateMeaning leftMeaning second.operandMeaning
        leftScope second.textScope binaryBudget
      have binaryNext : second.finalState.next ≤ binary.finalState.next := by
        have bound := (subtraction_preserves first.text second.text second.finalState).next
        rw [binary.run] at bound
        exact bound
      obtain ⟨normalized, normalization, represents⟩ :=
        normalize_success ctx hash implementation inputs normalAliases values aliases (.usub left right) value success
      have termEq : normalized.term = .binary "add" first.normalized.term (.unary "neg" second.normalized.term) := by
        have normal := normalization
        simp only [Native.normalize, first.normalization, second.normalization] at normal
        cases normal
        simp only [Native.subtraction_eq, Native.requireSourceType_eq]
      have resultRange : (interpret hash inputs (.binary "add" first.normalized.term (.unary "neg" second.normalized.term))).val ≤ m := by
        rw [← termEq, represents.2.2]
        exact Nat.le_trans (Nat.mod_le value Field.modulus) represents.1.2.2
      have rangeBudget : ((do Zkir.constrainUnsigned (m) binary.text; pure binary.text).run binary.finalState).2.next ≤ Native.maxInstructions * Native.maxVectorLength := by
        change ((do let output ← (do let negated ← Zkir.unary "neg" second.text; Zkir.binary "add" first.text negated); Zkir.constrainUnsigned (m) output; pure output).run second.finalState).2.next ≤ _ at tailBudget
        rw [StateT.run_bind, binary.run] at tailBudget
        exact tailBudget
      obtain ⟨bounded⟩ := constrainUnsigned_step hash inputs binary.finalWitness binary.finalState (m) binary.text
        (.binary "add" first.normalized.term (.unary "neg" second.normalized.term)) binary.stateMeaning binary.operandMeaning binary.textScope
        resultRange represents.1.2.1 rangeBudget
      let native := binary.chain (fun output => do Zkir.constrainUnsigned (m) output; pure output) bounded binaryNext
      refine ⟨{
        text := native.text
        finalState := native.finalState
        finalWitness := native.finalWitness
        normalized := normalized
        run := ?_
        normalization := normalization
        represents := represents
        operandMeaning := by rw [termEq]; exact native.operandMeaning
        textScope := native.textScope
        stateMeaning := native.stateMeaning
        budget := native.budget
        aliasAgreement := ?_
        aliasesPreserved := native.aliasesPreserved.trans (second.aliasesPreserved.trans first.aliasesPreserved)
        frame := ?_
      }⟩
      · change ((do let a ← Zkir.lowerExpr left; let b ← Zkir.lowerExpr right; tail a b).run state) = _
        rw [StateT.run_bind, first.run]
        change ((do let b ← Zkir.lowerExpr right; tail first.text b).run first.finalState) = _
        rw [StateT.run_bind, second.run]
        exact native.run
      · rw [native.aliasesPreserved]
        exact LowerAliasAgreement.of_frame hash inputs second.finalWitness native.finalWitness second.finalState.next
          normalAliases second.finalState.aliases values second.aliasAgreement second.stateMeaning.aliases native.frame
      · intro name inScopeAt
        rw [native.frame name (InScope.mono secondNext (InScope.mono firstNext inScopeAt)),
          second.frame name (InScope.mono firstNext inScopeAt), first.frame name inScopeAt]

theorem complete_cast {sourceTy : Ty} (target : Ty) (expression : Expr sourceTy)
    (ih : ExprComplete expression) : ExprComplete (.cast target expression) := by
  intro ctx hash implementation inputs witness state normalAliases values types value
    valid success aliases lowerAliases stateMeaning budget
  let tail : String → StateM Zkir.LowerState String := (fun (kind : Ty) (text : String) => match kind with
    | .native => pure text
    | .bool => do let compared ← Zkir.binary "test_eq" text "0x00"; Zkir.unary "not" compared
    | .uint maximum => do Zkir.constrainUnsigned maximum text; pure text) target
  have tailPreserves (text : String) : ScalarAllocation.PreservesFrame (tail text) := by
    cases target with
    | native => exact ScalarAllocation.pure_preserves text
    | bool =>
      exact ScalarAllocation.bind_preserves _ _ (ScalarAllocation.binary_preserves "test_eq" text "0x00" ⟨by decide, by decide, by decide⟩)
        (fun compared => ScalarAllocation.unary_preserves "not" compared ⟨by decide, by decide, by decide⟩)
    | uint maximum =>
      exact ScalarAllocation.bind_preserves _ _ (ScalarAllocation.constrainUnsigned_preserves maximum text)
        (fun _ => ScalarAllocation.pure_preserves text)
  change ((do let text ← Zkir.lowerExpr expression; tail text).run state).2.next ≤ _ at budget
  have validation := valid
  change (do target.validate {poseidon2 := true}; expression.validate {poseidon2 := true} types) = .ok () at validation
  simp only [ScalarValidation.bind_ok] at validation
  obtain ⟨_, _, expressionValid⟩ := validation
  cases evaluated : expression.eval ctx values with
  | error message => simp [Expr.eval, evaluated, Bind.bind, Except.bind] at success
  | ok expressionValue =>
    have expressionBudget := ScalarAllocation.bind_middle_budget (Zkir.lowerExpr expression) tail state
      tailPreserves (Native.maxInstructions * Native.maxVectorLength) budget
    obtain ⟨child⟩ := ih ctx hash implementation inputs witness state normalAliases values types expressionValue
      expressionValid evaluated aliases lowerAliases stateMeaning expressionBudget
    have childNext : state.next ≤ child.finalState.next := by
      have bound := ScalarAllocation.lowerExpr_next expression state
      rw [child.run] at bound
      exact bound
    have tailBudget : ((tail child.text).run child.finalState).2.next ≤ Native.maxInstructions * Native.maxVectorLength := by
      rw [StateT.run_bind, child.run] at budget
      exact budget
    obtain ⟨normalized, normalization, represents⟩ :=
      normalize_success ctx hash implementation inputs normalAliases values aliases (.cast target expression) value success
    let targetTerm : Native.Term := (fun kind => match kind with
      | .bool => .unary "not" (.binary "test_eq" child.normalized.term (.constant 0))
      | _ => child.normalized.term) target
    have termEq : normalized.term = targetTerm := by
      have normal := normalization
      simp only [Native.normalize, child.normalization] at normal
      cases normal
      cases target <;> simp only [targetTerm, Native.requireSourceType_eq]
    have tailComplete : Nonempty (NativeStepResult hash inputs child.finalWitness child.finalState (tail child.text) targetTerm) := by
      cases target with
      | native =>
        exact ⟨{
          text := child.text
          finalState := child.finalState
          finalWitness := child.finalWitness
          run := rfl
          operandMeaning := child.operandMeaning
          textScope := child.textScope
          stateMeaning := child.stateMeaning
          budget := child.budget
          aliasesPreserved := rfl
          frame := by intro name _; rfl
        }⟩
      | bool =>
        exact boolean_cast_step hash inputs child.finalWitness child.finalState child.text child.normalized.term
          child.stateMeaning child.operandMeaning child.textScope tailBudget
      | uint maximum =>
        have resultRange : (interpret hash inputs child.normalized.term).val ≤ maximum := by
          change (interpret hash inputs targetTerm).val ≤ maximum
          rw [← termEq, represents.2.2]
          exact Nat.le_trans (Nat.mod_le value Field.modulus) represents.1.2.2
        exact constrainUnsigned_step hash inputs child.finalWitness child.finalState maximum child.text child.normalized.term
          child.stateMeaning child.operandMeaning child.textScope resultRange represents.1.2.1 tailBudget
    obtain ⟨native⟩ := tailComplete
    refine ⟨{
      text := native.text
      finalState := native.finalState
      finalWitness := native.finalWitness
      normalized := normalized
      run := ?_
      normalization := normalization
      represents := represents
      operandMeaning := by rw [termEq]; exact native.operandMeaning
      textScope := native.textScope
      stateMeaning := native.stateMeaning
      budget := native.budget
      aliasAgreement := ?_
      aliasesPreserved := native.aliasesPreserved.trans child.aliasesPreserved
      frame := ?_
    }⟩
    · change ((do let text ← Zkir.lowerExpr expression; tail text).run state) = _
      rw [StateT.run_bind, child.run]
      exact native.run
    · rw [native.aliasesPreserved]
      exact LowerAliasAgreement.of_frame hash inputs child.finalWitness native.finalWitness child.finalState.next
        normalAliases child.finalState.aliases values child.aliasAgreement child.stateMeaning.aliases native.frame
    · intro name inScopeAt
      rw [native.frame name (InScope.mono childNext inScopeAt), child.frame name inScopeAt]

theorem select_step (hash : Hash) (inputs witness : NativeRelation.Assignment)
    (state : Zkir.LowerState) (operation : StateM Zkir.LowerState String)
    (condition yes no : String) (conditionTerm yesTerm noTerm : Native.Term)
    (stateMeaning : LowerStateMeaning hash witness state)
    (conditionMeaning : OperandMeaning hash inputs witness condition conditionTerm)
    (yesMeaning : OperandMeaning hash inputs witness yes yesTerm)
    (noMeaning : OperandMeaning hash inputs witness no noTerm)
    (conditionScope : TextScope state.next condition) (yesScope : TextScope state.next yes)
    (noScope : TextScope state.next no)
    (boolean : interpret hash inputs conditionTerm = zero ∨ interpret hash inputs conditionTerm = one)
    (run : operation.run state = match state.expressions.lookup ("cond_select", [condition, yes, no], none) with
      | some output => (output, state)
      | none => (freshName state.next, appendFreshState state
          (Zkir.instruction "cond_select" [("bit", toJson condition), ("a", toJson yes), ("b", toJson no),
            ("output", toJson (freshName state.next))])
          ("cond_select", [condition, yes, no], none) (freshName state.next)))
    (budget : (operation.run state).2.next ≤ Native.maxInstructions * Native.maxVectorLength) :
    Nonempty (NativeStepResult hash inputs witness state operation (.select conditionTerm yesTerm noTerm)) := by
  rcases conditionMeaning with ⟨conditionOperand, conditionDecoded, conditionValue⟩
  rcases yesMeaning with ⟨yesOperand, yesDecoded, yesValue⟩
  rcases noMeaning with ⟨noOperand, noDecoded, noValue⟩
  have conditionNames := TextScope.identifiers conditionScope conditionDecoded
  have yesNames := TextScope.identifiers yesScope yesDecoded
  have noNames := TextScope.identifiers noScope noDecoded
  cases hit : state.expressions.lookup ("cond_select", [condition, yes, no], none) with
  | some output =>
    have actualRun : operation.run state = (output, state) := by rw [run, hit]
    exact cached_step hash inputs witness state operation _ _ output stateMeaning hit actualRun
      (ScalarCache.cached_select_meaning hash inputs witness state stateMeaning condition yes no output
        conditionTerm yesTerm noTerm ⟨conditionOperand, conditionDecoded, conditionValue⟩
        ⟨yesOperand, yesDecoded, yesValue⟩ ⟨noOperand, noDecoded, noValue⟩ hit) budget
  | none =>
    have actualRun : operation.run state = (freshName state.next, appendFreshState state
        (Zkir.instruction "cond_select" [("bit", toJson condition), ("a", toJson yes), ("b", toJson no),
          ("output", toJson (freshName state.next))])
        ("cond_select", [condition, yes, no], none) (freshName state.next)) := by rw [run, hit]
    have counter : state.next + 1 ≤ Native.maxInstructions * Native.maxVectorLength := by rw [actualRun] at budget; exact budget
    have valid : validIdentifier (freshName state.next) = true := fresh_identifier state.next (by omega)
    apply fresh_step hash inputs witness state operation (.select conditionTerm yesTerm noTerm)
      (Zkir.instruction "cond_select" [("bit", toJson condition), ("a", toJson yes), ("b", toJson no),
        ("output", toJson (freshName state.next))]) ("cond_select", [condition, yes, no], none)
      (.select conditionOperand yesOperand noOperand (freshName state.next))
      (if conditionOperand.read witness = one then yesOperand.read witness else noOperand.read witness)
      stateMeaning actualRun (decode_select_instruction conditionDecoded yesDecoded noDecoded valid)
    · exact ⟨rfl, condition, yes, no, rfl, conditionDecoded, yesDecoded, noDecoded, valid⟩
    · intro name member
      simp only [instructionIdentifiers, List.mem_append, List.mem_singleton] at member
      rcases member with ((member | member) | member) | rfl
      · exact InScope.mono (by omega) (conditionNames name member)
      · exact InScope.mono (by omega) (yesNames name member)
      · exact InScope.mono (by omega) (noNames name member)
      · exact Or.inr ⟨state.next, by omega, rfl⟩
    · exact select_output_holds hash witness (freshName state.next) conditionOperand yesOperand noOperand
        (Operand.independent_of_scope state.next conditionOperand conditionNames)
        (Operand.independent_of_scope state.next yesOperand yesNames)
        (Operand.independent_of_scope state.next noOperand noNames)
        (by simpa only [conditionValue] using boolean)
    · simp only [interpret_select, conditionValue, yesValue, noValue]
    · exact budget

end Noctium.Verification.ScalarExpressionArithmetic
