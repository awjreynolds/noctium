import Noctium.Backend.Zkir
import Noctium.Verification.ScalarImmediate
import Noctium.Verification.ScalarInstructionEncoding
import Noctium.Verification.ScalarValidation
import Noctium.Verification.ScalarNormalizationSoundness
import Noctium.Verification.ScalarAllocation
import Noctium.Verification.ScalarWitness
import Std.Data.String.ToNat

namespace Noctium.Verification.ScalarLowering

open Lean
open Noctium
open Noctium.Backend
open Noctium.Verification.NativeRelation
open Noctium.Verification.NativeRelationJson
open Noctium.Verification.ScalarWitness
open Noctium.Verification.ScalarNormalization
open Noctium.Verification.ScalarInstructionEncoding

abbrev Assignment := Noctium.Verification.NativeRelation.Assignment
abbrev ExpressionKey := Noctium.Backend.Zkir.ExpressionKey

def freshName (index : Nat) : String := s!"%v{index}"

def InScope (next : Nat) (name : String) : Prop :=
  (∃ source, name = "%input_" ++ source) ∨
    ∃ index, index < next ∧ name = freshName index

private theorem fresh_not_input (index : Nat) (source : String) :
    freshName index ≠ "%input_" ++ source := by
  intro equal
  have lists := congrArg String.toList equal
  simp only [freshName, Nat.toString_eq_repr, String.toList_append] at lists
  change ['%', 'v'] ++ (Nat.repr index).toList =
    ['%', 'i', 'n', 'p', 'u', 't', '_'] ++ source.toList at lists
  cases lists

theorem fresh_not_inScope (next : Nat) : ¬ InScope next (freshName next) := by
  rintro (⟨source, equal⟩ | ⟨index, before, equal⟩)
  · exact fresh_not_input next source equal
  · have same := ScalarInstructionEncoding.fresh_name_injective equal
    omega

theorem Operand.independent_of_scope (next : Nat) (operand : Operand)
    (inScopeAt : ∀ name ∈ operandIdentifiers operand, InScope next name) :
    OperandIndependent (freshName next) operand := by
  cases operand with
  | immediate _ => trivial
  | reference name =>
    intro equal
    have inScope := inScopeAt name (by simp [operandIdentifiers])
    rw [equal] at inScope
    exact (fresh_not_inScope next) inScope

theorem Instruction.independent_of_scope (next : Nat) (instruction : Instruction)
    (inScopeAt : ∀ name ∈ instructionIdentifiers instruction, InScope next name) :
    InstructionIndependent (freshName next) instruction := by
  intro member
  exact fresh_not_inScope next (inScopeAt (freshName next) member)

def TextScope (next : Nat) (text : String) : Prop :=
  ∃ operand, decodeOperand (toJson text) = .ok operand ∧
    ∀ name ∈ operandIdentifiers operand, InScope next name

theorem InScope.mono {before after : Nat} (le : before ≤ after) {name : String}
    (inScopeAt : InScope before name) : InScope after name := by
  rcases inScopeAt with ⟨source, equal⟩ | ⟨index, before, equal⟩
  · exact Or.inl ⟨source, equal⟩
  · exact Or.inr ⟨index, Nat.lt_of_lt_of_le before le, equal⟩

theorem TextScope.mono {before after : Nat} (le : before ≤ after) {text : String}
    (inScopeAt : TextScope before text) : TextScope after text := by
  rcases inScopeAt with ⟨operand, parsed, identifiers⟩
  exact ⟨operand, parsed, fun name member => InScope.mono le (identifiers name member)⟩

theorem TextScope.operand_independent (next : Nat) (text : String)
    (inScopeAt : TextScope next text) :
    ∃ operand, decodeOperand (toJson text) = .ok operand ∧
      OperandIndependent (freshName next) operand := by
  rcases inScopeAt with ⟨operand, parsed, identifiers⟩
  exact ⟨operand, parsed, Operand.independent_of_scope next operand identifiers⟩

def appendFreshState (state : Zkir.LowerState) (raw : Json)
    (key : ExpressionKey) (output : String) : Zkir.LowerState :=
  {state with
    next := state.next + 1
    instructions := state.instructions.push raw
    expressions := (key, output) :: state.expressions}

def OperandMeaning (hash : Hash) (inputs witness : Assignment) (text : String)
    (term : Backend.Native.Term) : Prop :=
  ∃ operand, decodeOperand (toJson text) = .ok operand ∧
    operand.read witness = interpret hash inputs term

def LowerAliasAgreement (hash : Hash) (inputs witness : Assignment)
    (normalAliases : Backend.Native.AliasEnvironment) (lowerAliases : List (String × String))
    (values : EvalEnv) : Prop :=
  ∀ name ty raw value, values.lookup name = some raw → raw.as ty = some value →
    ∃ term, normalAliases.lookup name = some term ∧
      OperandMeaning hash inputs witness
        (lowerAliases.lookup name |>.getD ("%input_" ++ name)) term

theorem OperandMeaning.assignFresh (hash : Hash) (inputs witness : Assignment)
    (next : Nat) (value : Scalar) (text : String) (term : Backend.Native.Term)
    (meaning : OperandMeaning hash inputs witness text term)
    (inScopeAt : TextScope next text) :
    OperandMeaning hash inputs (assign witness (freshName next) value) text term := by
  rcases meaning with ⟨operand, parsed, valueMeaning⟩
  rcases inScopeAt with ⟨scopedOperand, scopedParsed, identifiers⟩
  have same : scopedOperand = operand := Except.ok.inj (scopedParsed.symm.trans parsed)
  subst scopedOperand
  refine ⟨operand, parsed, ?_⟩
  rw [Operand.read_assign witness (freshName next) value operand
    (Operand.independent_of_scope next operand identifiers), valueMeaning]

theorem LowerAliasAgreement.cons (hash : Hash) (inputs witness : Assignment)
    (normalAliases : Backend.Native.AliasEnvironment) (lowerAliases : List (String × String))
    (values : EvalEnv) (name : String) (ty : Ty) (value : ty.Denote)
    (term : Backend.Native.Term) (text : String)
    (agreement : LowerAliasAgreement hash inputs witness normalAliases lowerAliases values)
    (meaning : OperandMeaning hash inputs witness text term) :
    LowerAliasAgreement hash inputs witness ((name, term) :: normalAliases)
      ((name, text) :: lowerAliases) ((name, Value.pack ty value) :: values) := by
  intro found foundTy raw foundValue lookup typed
  by_cases same : found = name
  · subst found
    simp only [List.lookup_cons, beq_self_eq_true] at lookup
    cases lookup
    cases ty <;> cases foundTy <;> simp_all [Value.pack, Value.as]
  · have unequal : (found == name) = false := by simp [same]
    simp only [List.lookup_cons, unequal] at lookup
    obtain ⟨existingTerm, normal, lower⟩ := agreement found foundTy raw foundValue lookup typed
    refine ⟨existingTerm, ?_, ?_⟩
    · simpa [List.lookup_cons, unequal] using normal
    · simpa [List.lookup_cons, unequal] using lower

def CacheCorresponds (key : ExpressionKey) (output : String) : Instruction → Prop
  | .add left right destination =>
      output = destination ∧ ∃ a b, key = ("add", [a, b], none) ∧
        decodeOperand (toJson a) = .ok left ∧ decodeOperand (toJson b) = .ok right ∧
        validIdentifier destination = true
  | .mul left right destination =>
      output = destination ∧ ∃ a b, key = ("mul", [a, b], none) ∧
        decodeOperand (toJson a) = .ok left ∧ decodeOperand (toJson b) = .ok right ∧
        validIdentifier destination = true
  | .testEq left right destination =>
      output = destination ∧ ∃ a b, key = ("test_eq", [a, b], none) ∧
        decodeOperand (toJson a) = .ok left ∧ decodeOperand (toJson b) = .ok right ∧
        validIdentifier destination = true
  | .neg value destination =>
      output = destination ∧ ∃ a, key = ("neg", [a], none) ∧
        decodeOperand (toJson a) = .ok value ∧ validIdentifier destination = true
  | .not value destination =>
      output = destination ∧ ∃ a, key = ("not", [a], none) ∧
        decodeOperand (toJson a) = .ok value ∧ validIdentifier destination = true
  | .select condition yes no destination =>
      output = destination ∧ ∃ c a b, key = ("cond_select", [c, a, b], none) ∧
        decodeOperand (toJson c) = .ok condition ∧ decodeOperand (toJson a) = .ok yes ∧
        decodeOperand (toJson b) = .ok no ∧ validIdentifier destination = true
  | .hash values destination =>
      output = destination ∧ ∃ (domain : Nat) (a b domainText : String) (left right : Operand),
        key = ("transient_hash", [a, b], some domain) ∧
        values = [.immediate (scalar domain), left, right] ∧
        decodeOperand (toJson domainText) = .ok (.immediate (scalar domain)) ∧
        decodeOperand (toJson a) = .ok left ∧ decodeOperand (toJson b) = .ok right ∧
        validIdentifier destination = true
  | .input .. | .boolean .. | .bits .. | .lessThan .. | .equal .. | .assert .. | .impact .. | .output .. => False

structure LowerStateMeaning (hash : Hash) (witness : Assignment)
    (state : Zkir.LowerState) : Prop where
  decoded : ∃ instructions,
    state.instructions.toList.mapM decodeInstruction = .ok instructions
  holds : ∀ instructions, state.instructions.toList.mapM decodeInstruction = .ok instructions →
    ∀ instruction ∈ instructions, Instruction.Holds hash witness instruction
  scope : ∀ instructions, state.instructions.toList.mapM decodeInstruction = .ok instructions →
    ∀ instruction ∈ instructions, ∀ name ∈ instructionIdentifiers instruction, InScope state.next name
  aliases : ∀ name text, (name, text) ∈ state.aliases → TextScope state.next text
  cacheTrace : ∀ key output, (key, output) ∈ state.expressions →
    ∃ instructions, state.instructions.toList.mapM decodeInstruction = .ok instructions ∧
      ∃ instruction ∈ instructions, CacheCorresponds key output instruction

theorem LowerStateMeaning.withAliases (hash : Hash) (witness : Assignment)
    (state : Zkir.LowerState) (invariant : LowerStateMeaning hash witness state)
    (aliases : List (String × String))
    (aliasesScoped : ∀ name text, (name, text) ∈ aliases → TextScope state.next text) :
    LowerStateMeaning hash witness {state with aliases := aliases} := by
  rcases invariant with ⟨decoded, holds, scope, oldAliases, cacheTrace⟩
  refine ⟨?_, ?_, ?_, aliasesScoped, ?_⟩
  · simpa using decoded
  · intro instructions decodedInstructions instruction member
    exact holds instructions decodedInstructions instruction member
  · intro instructions decodedInstructions instruction member name nameMember
    exact scope instructions decodedInstructions instruction member name nameMember
  · intro key output member
    obtain ⟨instructions, decodedInstructions, instruction, instructionMember, matching⟩ :=
      cacheTrace key output member
    exact ⟨instructions, by simpa using decodedInstructions, instruction, instructionMember, matching⟩

/-- One checked lowering step records both emitted syntax and its assignment
extension. Expression constructor proofs share this result without assuming an
honest, preconstructed witness. -/
structure ExprStepResult (hash : Hash) (inputs initialWitness : Assignment)
    (initialState : Zkir.LowerState) (normalAliases : Backend.Native.AliasEnvironment)
    (values : EvalEnv) (expression : Expr ty) (value : ty.Denote) where
  text : String
  finalState : Zkir.LowerState
  finalWitness : Assignment
  normalized : Backend.Native.Normalized
  run : (Zkir.lowerExpr expression).run initialState = (text, finalState)
  normalization : Backend.Native.normalize normalAliases expression = .ok normalized
  represents : Represents hash inputs ty normalized value
  operandMeaning : OperandMeaning hash inputs finalWitness text normalized.term
  textScope : TextScope finalState.next text
  stateMeaning : LowerStateMeaning hash finalWitness finalState
  budget : finalState.next ≤ Native.maxInstructions
  aliasAgreement : LowerAliasAgreement hash inputs finalWitness normalAliases finalState.aliases values
  aliasesPreserved : finalState.aliases = initialState.aliases
  frame : ∀ name, InScope initialState.next name → finalWitness name = initialWitness name

/-- Constructor closures share this contract. Its only resource premise is the
actual end counter of the expression's current lowerer run. -/
def ExprComplete (expression : Expr ty) : Prop :=
  ∀ (ctx : EvalContext) (hash : Hash) (implementation : HashAgreement ctx hash)
    (inputs witness : Assignment) (state : Zkir.LowerState)
    (normalAliases : Backend.Native.AliasEnvironment) (values : EvalEnv) (types : TypeEnv)
    (value : ty.Denote),
    expression.validate {poseidon2 := true} types = .ok () →
    expression.eval ctx values = .ok value →
    AliasAgreement hash inputs normalAliases values →
    LowerAliasAgreement hash inputs witness normalAliases state.aliases values →
    LowerStateMeaning hash witness state →
    ((Zkir.lowerExpr expression).run state).2.next ≤ Native.maxInstructions →
    Nonempty (ExprStepResult hash inputs witness state normalAliases values expression value)

private theorem lookup_member {key : α} {value : β} {entries : List (α × β)}
    [BEq α] [LawfulBEq α]
    (lookup : entries.lookup key = some value) : (key, value) ∈ entries := by
  obtain ⟨before, after, equal, _⟩ := List.lookup_eq_some_iff.mp lookup
  rw [equal]
  simp

theorem TextScope.fieldImmediate (next number : Nat) (canonical : number < Field.modulus) :
    TextScope next (Zkir.fieldImmediate number) := by
  refine ⟨.immediate (scalar number), ScalarImmediate.decodeOperand_fieldImmediate_exact number canonical, ?_⟩
  simp [operandIdentifiers]

theorem OperandMeaning.fieldImmediate (hash : Hash) (inputs witness : Assignment)
    (number : Nat) (canonical : number < Field.modulus) :
    OperandMeaning hash inputs witness (Zkir.fieldImmediate number) (.constant number) := by
  refine ⟨.immediate (scalar number), ScalarImmediate.decodeOperand_fieldImmediate_exact number canonical, ?_⟩
  simp [Operand.read]

theorem TextScope.validReference (next : Nat) (name : String)
    (valid : validIdentifier name = true) (nameScope : InScope next name) :
    TextScope next name := by
  refine ⟨.reference name, (OperandEncoding.reference name valid).decode, ?_⟩
  simp [operandIdentifiers, nameScope]

theorem OperandMeaning.reference (hash : Hash) (inputs witness : Assignment)
    (name : String) (valid : validIdentifier name = true) (term : Backend.Native.Term)
    (meaning : witness name = interpret hash inputs term) :
    OperandMeaning hash inputs witness name term := by
  refine ⟨.reference name, (OperandEncoding.reference name valid).decode, ?_⟩
  exact meaning

theorem LowerAliasAgreement.assignFresh (hash : Hash) (inputs witness : Assignment)
    (normalAliases : Backend.Native.AliasEnvironment) (lowerAliases : List (String × String))
    (values : EvalEnv) (next : Nat) (newValue : Scalar)
    (agreement : LowerAliasAgreement hash inputs witness normalAliases lowerAliases values)
    (aliasesScoped : ∀ name text, (name, text) ∈ lowerAliases → TextScope next text) :
    LowerAliasAgreement hash inputs (assign witness (freshName next) newValue)
      normalAliases lowerAliases values := by
  intro name ty raw value lookup typed
  obtain ⟨term, normal, meaning⟩ := agreement name ty raw value lookup typed
  have textScoped : TextScope next (lowerAliases.lookup name |>.getD ("%input_" ++ name)) := by
    cases found : lowerAliases.lookup name with
    | some text =>
      exact aliasesScoped name text (lookup_member found)
    | none =>
      have fallback : (lowerAliases.lookup name |>.getD ("%input_" ++ name)) =
          ("%input_" ++ name) := by simp [found]
      rcases meaning with ⟨operand, parsed, valueMeaning⟩
      have parsedFallback : decodeOperand (toJson ("%input_" ++ name)) = .ok operand := by
        simpa [found] using parsed
      refine ⟨operand, ?_, ?_⟩
      · exact parsedFallback
      · intro identifier member
        cases operand with
        | immediate _ => simp [operandIdentifiers] at member
        | reference ref =>
          simp only [operandIdentifiers, List.mem_singleton] at member
          subst identifier
          have startsPercent : ("%input_" ++ name).startsWith "%" = true := by simp
          have starts := ScalarValidation.reference_not_immediate startsPercent
          have parsedFallback' := parsedFallback
          unfold decodeOperand at parsedFallback'
          simp only [ScalarValidation.bind_ok] at parsedFallback'
          rcases parsedFallback' with ⟨found, foundParsed, decoded⟩
          change Except.ok ("%input_" ++ name) = Except.ok found at foundParsed
          have foundEq : found = "%input_" ++ name := (Except.ok.inj foundParsed).symm
          rw [foundEq, starts] at decoded
          simp only [Bool.false_eq_true, ↓reduceIte] at decoded
          have equal : ref = "%input_" ++ name := by
            cases valid : validIdentifier ("%input_" ++ name) with
            | false => simp [valid, ensure, Except.map, Functor.map] at decoded
            | true =>
              simp [valid, ensure, Except.map, Functor.map] at decoded
              exact decoded.symm
          subst ref
          exact Or.inl ⟨name, rfl⟩
  rcases meaning with ⟨operand, parsed, valueMeaning⟩
  refine ⟨term, normal, ?_⟩
  exact OperandMeaning.assignFresh hash inputs witness next newValue
    (lowerAliases.lookup name |>.getD ("%input_" ++ name)) term
    ⟨operand, parsed, valueMeaning⟩ textScoped

theorem cached_add_meaning (hash : Hash) (inputs witness : Assignment)
    (state : Zkir.LowerState) (invariant : LowerStateMeaning hash witness state)
    (left right result : String) (leftTerm rightTerm : Backend.Native.Term)
    (leftMeaning : OperandMeaning hash inputs witness left leftTerm)
    (rightMeaning : OperandMeaning hash inputs witness right rightTerm)
    (hit : state.expressions.lookup ("add", [left, right], none) = some result) :
    OperandMeaning hash inputs witness result (.binary "add" leftTerm rightTerm) := by
  rcases leftMeaning with ⟨leftMeaningOperand, leftMeaningDecoded, leftValue⟩
  rcases rightMeaning with ⟨rightMeaningOperand, rightMeaningDecoded, rightValue⟩
  have member := lookup_member hit
  obtain ⟨instructions, decoded, instruction, instructionMember, correspondence⟩ :=
    invariant.cacheTrace ("add", [left, right], none) result member
  cases instruction with
  | add leftOperand rightOperand output =>
    simp only [CacheCorresponds] at correspondence
    rcases correspondence with ⟨resultEq, a, b, keyEq, leftParsed, rightParsed, outputValid⟩
    cases keyEq
    subst result
    have leftParsedEq : leftOperand = leftMeaningOperand := by
      exact Except.ok.inj (leftParsed.symm.trans leftMeaningDecoded)
    have rightParsedEq : rightOperand = rightMeaningOperand := by
      exact Except.ok.inj (rightParsed.symm.trans rightMeaningDecoded)
    have holds := invariant.holds instructions decoded
      (.add leftOperand rightOperand output) instructionMember
    rw [leftParsedEq, rightParsedEq] at holds
    change witness output = scalar ((leftMeaningOperand.read witness).val +
      (rightMeaningOperand.read witness).val) at holds
    refine ⟨.reference output, ?_, ?_⟩
    · exact OperandEncoding.reference output outputValid |>.decode
    · simp only [Operand.read]
      rw [holds, interpret_add, leftValue, rightValue]
  | mul leftOperand rightOperand output => simp [CacheCorresponds] at correspondence
  | neg value output => simp [CacheCorresponds] at correspondence
  | testEq leftOperand rightOperand output => simp [CacheCorresponds] at correspondence
  | not value output => simp [CacheCorresponds] at correspondence
  | lessThan leftOperand rightOperand width output => simp [CacheCorresponds] at correspondence
  | boolean value => simp [CacheCorresponds] at correspondence
  | bits value width => simp [CacheCorresponds] at correspondence
  | equal leftOperand rightOperand => simp [CacheCorresponds] at correspondence
  | select condition yes no output => simp [CacheCorresponds] at correspondence
  | hash values output => simp [CacheCorresponds] at correspondence
  | assert condition => simp [CacheCorresponds] at correspondence
  | impact guard values => simp [CacheCorresponds] at correspondence
  | output values => simp [CacheCorresponds] at correspondence
  | input visibility output => simp [CacheCorresponds] at correspondence

theorem cached_mul_meaning (hash : Hash) (inputs witness : Assignment)
    (state : Zkir.LowerState) (invariant : LowerStateMeaning hash witness state)
    (left right result : String) (leftTerm rightTerm : Backend.Native.Term)
    (leftMeaning : OperandMeaning hash inputs witness left leftTerm)
    (rightMeaning : OperandMeaning hash inputs witness right rightTerm)
    (hit : state.expressions.lookup ("mul", [left, right], none) = some result) :
    OperandMeaning hash inputs witness result (.binary "mul" leftTerm rightTerm) := by
  rcases leftMeaning with ⟨leftMeaningOperand, leftMeaningDecoded, leftValue⟩
  rcases rightMeaning with ⟨rightMeaningOperand, rightMeaningDecoded, rightValue⟩
  have member := lookup_member hit
  obtain ⟨instructions, decoded, instruction, instructionMember, correspondence⟩ :=
    invariant.cacheTrace ("mul", [left, right], none) result member
  cases instruction with
  | mul leftOperand rightOperand output =>
    simp only [CacheCorresponds] at correspondence
    rcases correspondence with ⟨resultEq, a, b, keyEq, leftParsed, rightParsed, outputValid⟩
    cases keyEq
    subst result
    have leftParsedEq : leftOperand = leftMeaningOperand :=
      Except.ok.inj (leftParsed.symm.trans leftMeaningDecoded)
    have rightParsedEq : rightOperand = rightMeaningOperand :=
      Except.ok.inj (rightParsed.symm.trans rightMeaningDecoded)
    have holds := invariant.holds instructions decoded
      (.mul leftOperand rightOperand output) instructionMember
    rw [leftParsedEq, rightParsedEq] at holds
    change witness output = scalar ((leftMeaningOperand.read witness).val *
      (rightMeaningOperand.read witness).val) at holds
    refine ⟨.reference output, (OperandEncoding.reference output outputValid).decode, ?_⟩
    simp only [Operand.read]
    rw [holds, interpret_mul, leftValue, rightValue]
  | add leftOperand rightOperand output => simp [CacheCorresponds] at correspondence
  | neg value output => simp [CacheCorresponds] at correspondence
  | testEq leftOperand rightOperand output => simp [CacheCorresponds] at correspondence
  | not value output => simp [CacheCorresponds] at correspondence
  | lessThan leftOperand rightOperand width output => simp [CacheCorresponds] at correspondence
  | boolean value => simp [CacheCorresponds] at correspondence
  | bits value width => simp [CacheCorresponds] at correspondence
  | equal leftOperand rightOperand => simp [CacheCorresponds] at correspondence
  | select condition yes no output => simp [CacheCorresponds] at correspondence
  | hash values output => simp [CacheCorresponds] at correspondence
  | assert condition => simp [CacheCorresponds] at correspondence
  | impact guard values => simp [CacheCorresponds] at correspondence
  | output values => simp [CacheCorresponds] at correspondence
  | input visibility output => simp [CacheCorresponds] at correspondence

theorem LowerStateMeaning.appendFresh (hash : Hash) (witness : Assignment)
    (state : Zkir.LowerState) (instructions : List Instruction)
    (priorDecoded : state.instructions.toList.mapM decodeInstruction = .ok instructions)
    (priorMeaning : LowerStateMeaning hash witness state)
    (raw : Json) (key : ExpressionKey) (output : String) (instruction : Instruction)
    (decoded : decodeInstruction raw = .ok instruction)
    (cacheMatch : CacheCorresponds key output instruction)
    (outputName : output = freshName state.next)
    (freshValid : validIdentifier output = true)
    (newScope : ∀ name ∈ instructionIdentifiers instruction, InScope (state.next + 1) name)
    (value : Scalar)
    (newHolds : Instruction.Holds hash (assign witness output value) instruction) :
    LowerStateMeaning hash (assign witness output value)
      (appendFreshState state raw key output) := by
  have priorDifferent : ∀ old ∈ instructions,
      InstructionIndependent output old := by
    intro old member
    have scopedOld := priorMeaning.scope instructions priorDecoded old member
    subst output
    exact Instruction.independent_of_scope state.next old scopedOld
  have instructionsDecoded :
      (appendFreshState state raw key output).instructions.toList.mapM decodeInstruction =
        .ok (instructions ++ [instruction]) := by
    change (state.instructions.push raw).toList.mapM decodeInstruction =
      .ok (instructions ++ [instruction])
    rw [Array.toList_push, List.mapM_append, priorDecoded]
    simp [decoded]
    rfl
  constructor
  · exact ⟨instructions ++ [instruction], instructionsDecoded⟩
  · intro decodedInstructions decodedAll found member
    have same : decodedInstructions = instructions ++ [instruction] := by
      rw [instructionsDecoded] at decodedAll
      exact (Except.ok.inj decodedAll).symm
    subst decodedInstructions
    rcases List.mem_append.mp member with old | new
    · have oldHolds := priorMeaning.holds instructions priorDecoded found old
      exact (Instruction.Holds.assign_frame hash witness output value found
        (priorDifferent found old)).mpr oldHolds
    · have equal := List.mem_singleton.mp new
      cases equal
      exact newHolds
  · intro decodedInstructions decodedAll found member
    have same : decodedInstructions = instructions ++ [instruction] := by
      rw [instructionsDecoded] at decodedAll
      exact (Except.ok.inj decodedAll).symm
    subst decodedInstructions
    rcases List.mem_append.mp member with old | new
    · have oldScope := priorMeaning.scope instructions priorDecoded found old
      intro name nameMember
      exact InScope.mono (by simp [appendFreshState]) (oldScope name nameMember)
    · have equal := List.mem_singleton.mp new
      cases equal
      exact newScope
  · intro name text member
    exact TextScope.mono (by simp [appendFreshState]) (priorMeaning.aliases name text member)
  · intro foundKey foundOutput member
    change (foundKey, foundOutput) ∈ (key, output) :: state.expressions at member
    rcases List.mem_cons.mp member with equal | old
    · cases equal
      refine ⟨instructions ++ [instruction], instructionsDecoded, instruction, ?_, cacheMatch⟩
      exact List.mem_append_right _ (by simp)
    · obtain ⟨oldInstructions, oldDecoded, oldInstruction, oldMember, oldMatch⟩ :=
        priorMeaning.cacheTrace foundKey foundOutput old
      refine ⟨instructions ++ [instruction], instructionsDecoded, oldInstruction, ?_, oldMatch⟩
      have oldEq : instructions = oldInstructions := by
        apply Except.ok.inj
        rw [priorDecoded] at oldDecoded
        exact oldDecoded
      have same : oldInstructions = instructions := oldEq.symm
      subst oldInstructions
      exact List.mem_append_left _ oldMember

theorem add_output_holds (hash : Hash) (witness : Assignment) (name : String)
    (left right : Operand)
    (leftIndependent : OperandIndependent name left)
    (rightIndependent : OperandIndependent name right) :
    Instruction.Holds hash
      (assign witness name (scalar ((left.read witness).val + (right.read witness).val)))
      (.add left right name) := by
  simp only [Instruction.Holds, assign_same]
  rw [Operand.read_assign witness name _ left leftIndependent,
    Operand.read_assign witness name _ right rightIndependent]

theorem mul_output_holds (hash : Hash) (witness : Assignment) (name : String)
    (left right : Operand)
    (leftIndependent : OperandIndependent name left)
    (rightIndependent : OperandIndependent name right) :
    Instruction.Holds hash
      (assign witness name (scalar ((left.read witness).val * (right.read witness).val)))
      (.mul left right name) := by
  simp only [Instruction.Holds, assign_same]
  rw [Operand.read_assign witness name _ left leftIndependent,
    Operand.read_assign witness name _ right rightIndependent]

theorem testEq_output_holds (hash : Hash) (witness : Assignment) (name : String)
    (left right : Operand)
    (leftIndependent : OperandIndependent name left)
    (rightIndependent : OperandIndependent name right) :
    Instruction.Holds hash
      (assign witness name (bit (decide (left.read witness = right.read witness))))
      (.testEq left right name) := by
  simp only [Instruction.Holds, assign_same]
  rw [Operand.read_assign witness name _ left leftIndependent,
    Operand.read_assign witness name _ right rightIndependent]

theorem neg_output_holds (hash : Hash) (witness : Assignment) (name : String)
    (value : Operand) (independent : OperandIndependent name value) :
    Instruction.Holds hash
      (assign witness name (scalar (Field.modulus - (value.read witness).val)))
      (.neg value name) := by
  simp only [Instruction.Holds, assign_same]
  rw [Operand.read_assign witness name _ value independent]

theorem not_output_holds (hash : Hash) (witness : Assignment) (name : String)
    (value : Operand) (independent : OperandIndependent name value)
    (boolean : value.read witness = zero ∨ value.read witness = one) :
    Instruction.Holds hash
      (assign witness name (if value.read witness = zero then one else zero))
      (.not value name) := by
  simp only [Instruction.Holds, assign_same]
  rw [Operand.read_assign witness name _ value independent]
  exact ⟨boolean, rfl⟩

theorem select_output_holds (hash : Hash) (witness : Assignment) (name : String)
    (condition yes no : Operand)
    (conditionIndependent : OperandIndependent name condition)
    (yesIndependent : OperandIndependent name yes)
    (noIndependent : OperandIndependent name no)
    (boolean : condition.read witness = zero ∨ condition.read witness = one) :
    Instruction.Holds hash
      (assign witness name
        (if condition.read witness = one then yes.read witness else no.read witness))
      (.select condition yes no name) := by
  simp only [Instruction.Holds, assign_same]
  rw [Operand.read_assign witness name _ condition conditionIndependent,
    Operand.read_assign witness name _ yes yesIndependent,
    Operand.read_assign witness name _ no noIndependent]
  exact ⟨boolean, rfl⟩

theorem lessThan_output_holds (hash : Hash) (witness : Assignment) (name : String)
    (left right : Operand) (width : Nat)
    (leftIndependent : OperandIndependent name left)
    (rightIndependent : OperandIndependent name right) :
    Instruction.Holds hash
      (assign witness name (bit (decide ((left.read witness).val < (right.read witness).val))))
      (.lessThan left right width name) := by
  intro leftBound rightBound
  simp only [assign_same]
  rw [Operand.read_assign witness name _ left leftIndependent,
    Operand.read_assign witness name _ right rightIndependent]

theorem hash_output_holds (hash : Hash) (witness : Assignment) (name : String)
    (values : List Operand)
    (independent : ∀ value ∈ values, OperandIndependent name value) :
    Instruction.Holds hash
      (assign witness name (hash (values.map (·.read witness))))
      (.hash values name) := by
  simp only [Instruction.Holds, assign_same]
  congr 1
  apply List.map_congr_left
  intro value member
  rw [Operand.read_assign witness name _ value (independent value member)]

theorem lowerExpr_native_run (state : Zkir.LowerState) (value : Nat) :
    (Zkir.lowerExpr (.native value)).run state = (Zkir.fieldImmediate value, state) := by
  simp [Zkir.lowerExpr]
  rfl

theorem lowerExpr_uint_run (state : Zkir.LowerState) (maximum value : Nat) :
    (Zkir.lowerExpr (.uint maximum value)).run state = (Zkir.fieldImmediate value, state) := by
  simp [Zkir.lowerExpr]
  rfl

theorem lowerExpr_bool_run (state : Zkir.LowerState) (value : Bool) :
    (Zkir.lowerExpr (.bool value)).run state =
      (if value then "0x01" else "0x00", state) := by
  simp [Zkir.lowerExpr]
  rfl

theorem lowerExpr_ref_run (state : Zkir.LowerState) (ty : Ty) (name : String) :
    (Zkir.lowerExpr (ty := ty) (.ref (ty := ty) name)).run state =
      (state.aliases.lookup name |>.getD ("%input_" ++ name), state) := by
  simp [Zkir.lowerExpr]
  rfl

theorem binary_cache_hit (state : Zkir.LowerState) (opcode left right result : String)
    (hit : state.expressions.lookup (opcode, [left, right], none) = some result) :
    (Zkir.binary opcode left right).run state = (result, state) := by
  simp [Zkir.binary, hit]
  rfl

theorem unary_cache_hit (state : Zkir.LowerState) (opcode operand result : String)
    (hit : state.expressions.lookup (opcode, [operand], none) = some result) :
    (Zkir.unary opcode operand).run state = (result, state) := by
  simp [Zkir.unary, hit]
  rfl

theorem binary_cache_miss (state : Zkir.LowerState) (opcode left right : String)
    (miss : state.expressions.lookup (opcode, [left, right], none) = none) :
    (Zkir.binary opcode left right).run state =
      (freshName state.next, { state with
        next := state.next + 1,
        instructions := state.instructions.push (Zkir.instruction opcode
          [("a", toJson left), ("b", toJson right), ("output", toJson (freshName state.next))]),
        expressions := ((opcode, [left, right], none), freshName state.next) :: state.expressions }) := by
  simp [Zkir.binary, miss, Zkir.fresh, Zkir.emit, Zkir.instruction, freshName,
    StateT.run_get]
  rfl

theorem unary_cache_miss (state : Zkir.LowerState) (opcode operand : String)
    (miss : state.expressions.lookup (opcode, [operand], none) = none) :
    (Zkir.unary opcode operand).run state =
      (freshName state.next, { state with
        next := state.next + 1,
        instructions := state.instructions.push (Zkir.instruction opcode
          [("a", toJson operand), ("output", toJson (freshName state.next))]),
        expressions := ((opcode, [operand], none), freshName state.next) :: state.expressions }) := by
  simp [Zkir.unary, miss, Zkir.fresh, Zkir.emit, Zkir.instruction, freshName,
    StateT.run_get]
  rfl

end Noctium.Verification.ScalarLowering
