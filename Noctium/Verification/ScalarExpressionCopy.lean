import Noctium.Verification.ScalarExpressionNativeArithmetic
import Noctium.Verification.ScalarAllocationOutputFrame

namespace Noctium.Verification.ScalarWitnessConstruction

open Lean Backend NativeRelation NativeRelationJson ScalarNormalization ScalarLowering
open ScalarInstructionEncoding ScalarWitness ScalarAllocationOutputFrame

private theorem unary_copy_cache_hit (state : Zkir.LowerState) (operand output : String)
    (hit : state.expressions.lookup ("copy", [operand], none) = some output) :
    (Zkir.unary "copy" operand "val").run state = (output, state) := by
  simp [Zkir.unary, hit]
  rfl

private theorem unary_copy_cache_miss (state : Zkir.LowerState) (operand : String)
    (miss : state.expressions.lookup ("copy", [operand], none) = none) :
    (Zkir.unary "copy" operand "val").run state =
      (freshName state.next, appendFreshState state
        (Zkir.instruction "copy" [
          ("val", toJson operand), ("output", toJson (freshName state.next))])
        ("copy", [operand], none) (freshName state.next)) := by
  simp [Zkir.unary, miss, Zkir.fresh, Zkir.emit, Zkir.instruction,
    appendFreshState, freshName, StateT.run_get]
  rfl

private theorem lowerExpr_copyValue (value : Expr ty) :
    Zkir.lowerExpr (.copyValue value) =
      (do
        let text ← Zkir.lowerExpr value
        Zkir.unary "copy" text "val") := by
  simp only [Zkir.lowerExpr]

private theorem fresh_copy_scope (next : Nat) (value : Operand)
    (scope : ∀ name ∈ operandIdentifiers value, InScope next name) :
    ∀ name ∈ operandIdentifiers value ++ [freshName next], InScope (next + 1) name := by
  intro name member
  simp only [List.mem_append, List.mem_singleton] at member
  rcases member with member | rfl
  · exact InScope.mono (by omega) (scope name member)
  · exact Or.inr ⟨next, by omega, rfl⟩

private theorem copyCacheCorrespondence {text output : String} {instruction : Instruction}
    (correspondence : CacheCorresponds ("copy", [text], none) output instruction) :
    ∃ (source : Operand) (destination : String),
      instruction = .equal source (.reference destination) ∧ output = destination ∧
        validIdentifier destination = true ∧ decodeOperand (toJson text) = .ok source := by
  cases instruction with
  | input visibility output => simp [CacheCorresponds] at correspondence
  | boolean value => simp [CacheCorresponds] at correspondence
  | bits value width => simp [CacheCorresponds] at correspondence
  | lessThan left right width output => simp [CacheCorresponds] at correspondence
  | add left right output => simp [CacheCorresponds] at correspondence
  | mul left right output => simp [CacheCorresponds] at correspondence
  | neg value output => simp [CacheCorresponds] at correspondence
  | equal source target =>
    simp only [CacheCorresponds, Prod.mk.injEq, List.cons.injEq] at correspondence
    rcases correspondence with ⟨destination, cachedText, keyEq, targetEq,
      outputEq, outputValid, sourceDecoded⟩
    have textEq : text = cachedText := keyEq.2.1.1
    rw [← textEq] at sourceDecoded
    refine ⟨source, destination, ?_, outputEq, outputValid, sourceDecoded⟩
    rw [targetEq]
  | testEq left right output => simp [CacheCorresponds] at correspondence
  | not value output => simp [CacheCorresponds] at correspondence
  | select condition yes no output => simp [CacheCorresponds] at correspondence
  | hash values output => simp [CacheCorresponds] at correspondence
  | assert condition => simp [CacheCorresponds] at correspondence
  | impact guard values => simp [CacheCorresponds] at correspondence
  | output values => simp [CacheCorresponds] at correspondence

private theorem cached_copy_meaning (hash : Hash) (inputs witness : NativeRelation.Assignment)
    (state : Zkir.LowerState) (stateMeaning : LowerStateMeaning hash witness state)
    (text output : String) (term : Backend.Native.Term)
    (meaning : OperandMeaning hash inputs witness text term)
    (hit : state.expressions.lookup ("copy", [text], none) = some output) :
    OperandMeaning hash inputs witness output term := by
  rcases meaning with ⟨operand, operandDecoded, operandMeaning⟩
  have member := ScalarValidationMeaning.lookup_member hit
  obtain ⟨instructions, decoded, instruction, instructionMember, correspondence⟩ :=
    stateMeaning.cacheTrace ("copy", [text], none) output member
  obtain ⟨source, destination, instructionEq, outputEq, outputValid, sourceDecoded⟩ :=
    copyCacheCorrespondence correspondence
  rw [instructionEq] at instructionMember
  subst output
  have sourceEq : source = operand := Except.ok.inj (sourceDecoded.symm.trans operandDecoded)
  have holds := stateMeaning.holds instructions decoded
    (.equal source (.reference destination)) instructionMember
  rw [sourceEq] at holds
  have copied : operand.read witness = witness destination := by
    simpa [Instruction.Holds, Operand.read] using holds
  refine ⟨.reference destination, (OperandEncoding.reference destination outputValid).decode, ?_⟩
  simp only [Operand.read]
  exact operandMeaning.trans (congrArg some copied)

/-- Copy emits the native Copy operation. Its decoded equality preserves the
source term for both cache hits and fresh SSA outputs. -/
theorem unary_copy_step (hash : Hash) (inputs witness : NativeRelation.Assignment)
    (state : Zkir.LowerState) (text : String) (term : Backend.Native.Term)
    (stateMeaning : LowerStateMeaning hash witness state)
    (meaning : OperandMeaning hash inputs witness text term)
    (scope : TextScope state.next text)
    (budget : ((Zkir.unary "copy" text "val").run state).2.next ≤
      Native.maxInstructions * Native.maxVectorLength) :
    Nonempty (NativeStepResult hash inputs witness state
      (Zkir.unary "copy" text "val") term) := by
  rcases meaning with ⟨source, sourceDecoded, sourceMeaning⟩
  have sourceNames := TextScope.identifiers scope sourceDecoded
  cases hit : state.expressions.lookup ("copy", [text], none) with
  | some output =>
    exact cached_step hash inputs witness state _ _ _ output stateMeaning hit
      (unary_copy_cache_hit state text output hit)
      (cached_copy_meaning hash inputs witness state stateMeaning text output term
        ⟨source, sourceDecoded, sourceMeaning⟩ hit) budget
  | none =>
    have run := unary_copy_cache_miss state text hit
    have counter : state.next + 1 ≤ Native.maxInstructions * Native.maxVectorLength := by
      rw [run] at budget
      exact budget
    have valid : validIdentifier (freshName state.next) = true :=
      NativeRelationJson.generatedIdentifier_fits_output_capacity state.next (by omega)
    apply fresh_step hash inputs witness state (Zkir.unary "copy" text "val") term
      (Zkir.instruction "copy" [
        ("val", toJson text), ("output", toJson (freshName state.next))])
      ("copy", [text], none) (.equal source (.reference (freshName state.next)))
      (source.read witness) stateMeaning run
      (NativeRelationJson.decodeInstruction_copyOperandJson text source
        (freshName state.next) sourceDecoded valid)
    · exact ⟨freshName state.next, text, rfl, rfl, rfl, valid, sourceDecoded⟩
    · exact fresh_copy_scope state.next source sourceNames
    · have independent := Operand.independent_of_scope state.next source sourceNames
      change source.read (assign witness (freshName state.next) (source.read witness)) =
        (Operand.reference (freshName state.next)).read
          (assign witness (freshName state.next) (source.read witness))
      rw [Operand.read_assign witness (freshName state.next) (source.read witness)
        source independent]
      simp [Operand.read, assign_same]
    · exact sourceMeaning
    · exact budget

/-- A scalar-admitted copy is complete when its child expression is complete.
The emitted copy is checked against the same typed Native relation used by
other scalar expression constructors. -/
theorem complete_copyValue (value : Expr ty) (admission : ScalarExpression value)
    (complete : ExprComplete value) : ExprComplete (.copyValue value) := by
  intro ctx hash implementation inputs witness state normalAliases values types result
    valid success aliases lowerAliases stateMeaning budget
  have childValid : value.validate Capabilities.crypto types = .ok () := by
    simpa only [Expr.validate] using valid
  have childSuccess : value.eval ctx values = .ok result := by
    simpa only [Expr.eval] using success
  have copyFrame (text : String) :
      Zkir.PreservesOutputCapacityFrame (Zkir.unary "copy" text "val") :=
    Zkir.copyVal_preservesOutputCapacityFrame text
  have childBudget : ((Zkir.lowerExpr value).run state).2.next ≤
      Native.maxInstructions * Native.maxVectorLength := by
    rw [lowerExpr_copyValue, StateT.run_bind] at budget
    have remaining := (copyFrame ((Zkir.lowerExpr value).run state).1
      ((Zkir.lowerExpr value).run state).2).next
    exact Nat.le_trans remaining budget
  obtain ⟨child⟩ := complete ctx hash implementation inputs witness state normalAliases values
    types result childValid childSuccess aliases lowerAliases stateMeaning childBudget
  have copyBudget : ((Zkir.unary "copy" child.text "val").run child.finalState).2.next ≤
      Native.maxInstructions * Native.maxVectorLength := by
    have bound := budget
    rw [lowerExpr_copyValue, StateT.run_bind, child.run] at bound
    exact bound
  obtain ⟨copied⟩ := unary_copy_step hash inputs child.finalWitness child.finalState
    child.text child.normalized.term child.stateMeaning child.operandMeaning child.textScope copyBudget
  have childNext : state.next ≤ child.finalState.next := by
    simpa only [child.run] using
      (lowerExpr_admitted_preservesOutputCapacityFrame value admission state).next
  refine ⟨{
    text := copied.text
    finalState := copied.finalState
    finalWitness := copied.finalWitness
    normalized := child.normalized
    run := ?_
    normalization := ?_
    represents := child.represents
    operandMeaning := copied.operandMeaning
    textScope := copied.textScope
    stateMeaning := copied.stateMeaning
    budget := copied.budget
    aliasAgreement := ?_
    aliasesPreserved := copied.aliasesPreserved.trans child.aliasesPreserved
    frame := ?_
  }⟩
  · rw [lowerExpr_copyValue, StateT.run_bind, child.run]
    exact copied.run
  · simpa only [Backend.Native.normalize] using child.normalization
  · rw [copied.aliasesPreserved]
    exact LowerAliasAgreement.of_frame hash inputs child.finalWitness copied.finalWitness
      child.finalState.next normalAliases child.finalState.aliases values child.aliasAgreement
      child.stateMeaning.aliases copied.frame
  · intro name initialScope
    have afterChild := InScope.mono childNext initialScope
    exact (copied.frame name afterChild).trans (child.frame name initialScope)

end Noctium.Verification.ScalarWitnessConstruction
