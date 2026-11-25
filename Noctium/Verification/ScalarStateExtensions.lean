import Noctium.Verification.ScalarLowering

namespace Noctium.Verification.ScalarLowering
open Lean Backend NativeRelation NativeRelationJson ScalarWitness ScalarNormalization

/-- Appending a constraint or observation changes neither the assignment nor
CSE/alias meanings. Its native semantics and namespace are checked explicitly. -/
theorem LowerStateMeaning.append (hash : Hash) (witness : Assignment)
    (state : Zkir.LowerState) (meaning : LowerStateMeaning hash witness state)
    (raw : Json) (instruction : Instruction)
    (decoded : decodeInstruction raw = .ok instruction)
    (holds : instruction.Holds hash witness)
    (scope : ∀ name ∈ instructionIdentifiers instruction, InScope state.next name) :
    LowerStateMeaning hash witness {state with instructions := state.instructions.push raw} := by
  obtain ⟨prior, priorDecoded⟩ := meaning.decoded
  have fullDecoded : (state.instructions.push raw).toList.mapM decodeInstruction = .ok (prior ++ [instruction]) := by
    rw [Array.toList_push, List.mapM_append, priorDecoded]
    simp [decoded]
    rfl
  constructor
  · exact ⟨prior ++ [instruction], fullDecoded⟩
  · intro instructions checked found member
    have same : instructions = prior ++ [instruction] := by
      rw [fullDecoded] at checked
      exact (Except.ok.inj checked).symm
    subst instructions
    rcases List.mem_append.mp member with old | new
    · exact meaning.holds prior priorDecoded found old
    · have equal := List.mem_singleton.mp new
      subst found
      exact holds
  · intro instructions checked found member
    have same : instructions = prior ++ [instruction] := by
      rw [fullDecoded] at checked
      exact (Except.ok.inj checked).symm
    subst instructions
    rcases List.mem_append.mp member with old | new
    · exact meaning.scope prior priorDecoded found old
    · have equal := List.mem_singleton.mp new
      subst found
      exact scope
  · exact meaning.aliases
  · intro key output member
    obtain ⟨old, oldDecoded, cached, cachedMember, matchKey⟩ := meaning.cacheTrace key output member
    have same : old = prior := by
      rw [priorDecoded] at oldDecoded
      exact (Except.ok.inj oldDecoded).symm
    subst old
    exact ⟨prior ++ [instruction], fullDecoded, cached, List.mem_append_left _ cachedMember, matchKey⟩

theorem empty_state (hash : Hash) (witness : Assignment) : LowerStateMeaning hash witness {} := by
  constructor
  · exact ⟨[], rfl⟩
  · intro instructions decoded instruction member
    cases decoded
    simp at member
  · intro instructions decoded instruction member
    cases decoded
    simp at member
  · intro name text member
    simp at member
  · intro key output member
    simp at member

theorem OperandMeaning.of_frame (hash : Hash) (inputs before after : Assignment)
    (next : Nat) (text : String) (term : Backend.Native.Term)
    (meaning : OperandMeaning hash inputs before text term)
    (scope : TextScope next text)
    (frame : ∀ name, InScope next name → after name = before name) :
    OperandMeaning hash inputs after text term := by
  obtain ⟨operand, parsed, value⟩ := meaning
  obtain ⟨scopedOperand, scopedParsed, identifiers⟩ := scope
  rw [parsed] at scopedParsed
  cases scopedParsed
  refine ⟨operand, parsed, ?_⟩
  cases operand with
  | immediate value => simpa [Operand.read] using value
  | reference name =>
    have same := frame name (identifiers name (by simp [operandIdentifiers]))
    simpa [Operand.read, same] using value

private theorem input_textScope (next : Nat) (name : String) (operand : Operand)
    (parsed : decodeOperand (toJson ("%input_" ++ name)) = .ok operand) :
    TextScope next ("%input_" ++ name) := by
  have percent : ("%input_" ++ name).startsWith "%" = true := by
    apply String.startsWith_string_iff.mpr
    rw [String.toList_append]
    exact ⟨['i', 'n', 'p', 'u', 't', '_'] ++ name.toList, rfl⟩
  have notImmediate := NativeRelationJson.reference_not_immediate percent
  have reference : operand = .reference ("%input_" ++ name) := by
    unfold decodeOperand at parsed
    change (if ("%input_" ++ name).startsWith "0x" then
      (do return Operand.immediate (scalar (← decodeImmediate ("%input_" ++ name)))) else
      (do ensure (validIdentifier ("%input_" ++ name)) "invalid native SSA reference"
          return Operand.reference ("%input_" ++ name))) = _ at parsed
    rw [notImmediate] at parsed
    simp only [Bool.false_eq_true, ↓reduceIte] at parsed
    cases valid : validIdentifier ("%input_" ++ name) with
    | false => simp [ensure, valid, Bind.bind, Except.bind] at parsed
    | true =>
      simp only [ensure, valid, ↓reduceIte] at parsed
      change Except.ok (.reference ("%input_" ++ name)) = Except.ok operand at parsed
      exact (Except.ok.inj parsed).symm
  subst operand
  refine ⟨_, parsed, ?_⟩
  intro found member
  simp only [operandIdentifiers, List.mem_singleton] at member
  subst found
  exact Or.inl ⟨name, rfl⟩

theorem TextScope.lookup_default (next : Nat) (aliases : List (String × String))
    (name : String) (operand : Operand)
    (parsed : decodeOperand (toJson (aliases.lookup name |>.getD ("%input_" ++ name))) = .ok operand)
    (aliasesScoped : ∀ name text, (name, text) ∈ aliases → TextScope next text) :
    TextScope next (aliases.lookup name |>.getD ("%input_" ++ name)) := by
  cases lookup : aliases.lookup name with
  | some text =>
    exact aliasesScoped name text (ScalarValidationMeaning.lookup_member lookup)
  | none =>
    apply input_textScope next name operand
    simpa only [lookup, Option.getD_none] using parsed

theorem LowerAliasAgreement.of_frame (hash : Hash) (inputs before after : Assignment)
    (next : Nat) (normalAliases : Backend.Native.AliasEnvironment)
    (aliases : List (String × String)) (values : EvalEnv)
    (agreement : LowerAliasAgreement hash inputs before normalAliases aliases values)
    (aliasesScoped : ∀ name text, (name, text) ∈ aliases → TextScope next text)
    (frame : ∀ name, InScope next name → after name = before name) :
    LowerAliasAgreement hash inputs after normalAliases aliases values := by
  intro name ty raw value lookup typed
  obtain ⟨term, termLookup, meaning⟩ := agreement name ty raw value lookup typed
  refine ⟨term, termLookup, OperandMeaning.of_frame hash inputs before after next _ term meaning ?_ frame⟩
  obtain ⟨operand, parsed, _⟩ := meaning
  exact TextScope.lookup_default next aliases name operand parsed aliasesScoped

end Noctium.Verification.ScalarLowering
