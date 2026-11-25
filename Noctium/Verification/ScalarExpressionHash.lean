import Noctium.Verification.ScalarLowering
import Noctium.Verification.ScalarAllocation
import Noctium.Verification.ScalarCache
import Noctium.Verification.ScalarInstructionEncoding
import Noctium.Verification.ScalarImmediate
import Noctium.Verification.ScalarStateExtensions
import Noctium.Verification.ScalarExpressionArithmetic

namespace Noctium.Verification.ScalarExpressionHash

open Lean Backend NativeRelation NativeRelationJson ScalarNormalization
open ScalarLowering ScalarWitness ScalarInstructionEncoding ScalarAllocation
open ScalarExpressionArithmetic

abbrev Assignment := NativeRelation.Assignment

private def hashSuffix (domain : Nat) (left right : String) : StateM Zkir.LowerState String := do
  let key : ExpressionKey := ("transient_hash", [left, right], some domain)
  if let some existing := (← get).expressions.lookup key then return existing
  let output ← Zkir.fresh
  Zkir.emit "transient_hash" [("inputs", toJson [Zkir.fieldImmediate domain, left, right]),
    ("output", toJson output)]
  modify fun state => {state with expressions := (key, output) :: state.expressions}
  return output

private theorem lowerExpr_poseidon2_shape (domain : Nat) (left right : Expr .native) :
    Zkir.lowerExpr (.poseidon2 domain left right) = (do
      let leftText ← Zkir.lowerExpr left
      let rightText ← Zkir.lowerExpr right
      hashSuffix domain leftText rightText) := rfl

private theorem hashSuffix_preserves (domain : Nat) (left right : String) :
    PreservesFrame (hashSuffix domain left right) := by
  intro state
  cases hit : state.expressions.lookup ("transient_hash", [left, right], some domain) with
  | some output =>
    simp [hashSuffix, hit, StateT.run_bind, StateT.run_get, StateT.run_pure]
    exact Frame.refl _
  | none =>
    simp [hashSuffix, hit, Zkir.fresh, Zkir.emit, Zkir.instruction,
      StateT.run_bind, StateT.run_get, StateT.run_modify, StateT.run_set]
    constructor
    · exact Nat.le_add_right _ _
    · change state.instructions.size + (state.next + 1 - state.next) ≤
        (state.instructions.push _).size
      simp

private theorem hashSuffix_hit_run (domain : Nat) (left right output : String)
    (state : Zkir.LowerState)
    (hit : state.expressions.lookup ("transient_hash", [left, right], some domain) = some output) :
    (hashSuffix domain left right).run state = (output, state) := by
  simp [hashSuffix, hit]
  rfl

private theorem hashSuffix_miss_run (domain : Nat) (left right : String)
    (state : Zkir.LowerState)
    (miss : state.expressions.lookup ("transient_hash", [left, right], some domain) = none) :
    (hashSuffix domain left right).run state =
      (freshName state.next,
        appendFreshState state
          (Zkir.instruction "transient_hash"
            [("inputs", toJson [Zkir.fieldImmediate domain, left, right]),
              ("output", toJson (freshName state.next))])
          ("transient_hash", [left, right], some domain) (freshName state.next)) := by
  simp [hashSuffix, miss, Zkir.fresh, Zkir.emit, Zkir.instruction,
    appendFreshState, freshName, StateT.run_bind, StateT.run_get,
    StateT.run_modify, StateT.run_set]
  rfl

private theorem decodeOperands_of_texts {texts : List String} {operands : List Operand}
    (decoded : texts.mapM (fun text => decodeOperand (toJson text)) = .ok operands) :
    decodeOperands (toJson texts) = .ok operands := by
  unfold decodeOperands
  change (do
    let values ← (Except.ok (texts.toArray.map toJson) : Except String (Array Json))
    values.toList.mapM decodeOperand) = .ok operands
  change (texts.toArray.map toJson).toList.mapM decodeOperand = .ok operands
  simp only [Array.toList_map, List.mapM_map, Function.comp_def]
  change texts.mapM (fun text => decodeOperand (toJson text)) = .ok operands
  exact decoded

private theorem fresh_hash_scope (next domain : Nat) (left right : Operand)
    (leftNames : ∀ name ∈ operandIdentifiers left, InScope next name)
    (rightNames : ∀ name ∈ operandIdentifiers right, InScope next name) :
    ∀ name ∈ instructionIdentifiers
      (.hash [.immediate (scalar domain), left, right] (freshName next)),
      InScope (next + 1) name := by
  intro name member
  simp only [instructionIdentifiers, List.flatMap_cons, List.flatMap_nil,
    List.mem_append] at member
  rcases member with operandsMember | outputMember
  · rcases operandsMember with domainName | leftName | rightName | noFourth
    · simp [operandIdentifiers] at domainName
    · exact InScope.mono (by omega) (leftNames name leftName)
    · exact InScope.mono (by omega) (rightNames name rightName)
    · simp at noFourth
  · have same : name = freshName next := by simpa using outputMember
    rw [same]
    exact Or.inr ⟨next, by omega, rfl⟩

private theorem hashSuffix_step (hash : Hash) (inputs witness : Assignment)
    (state : Zkir.LowerState) (domain : Nat) (leftText rightText : String)
    (leftTerm rightTerm : Backend.Native.Term)
    (stateMeaning : LowerStateMeaning hash witness state)
    (leftMeaning : OperandMeaning hash inputs witness leftText leftTerm)
    (rightMeaning : OperandMeaning hash inputs witness rightText rightTerm)
    (leftScope : TextScope state.next leftText) (rightScope : TextScope state.next rightText)
    (domainCanonical : domain < Field.modulus)
    (budget : (hashSuffix domain leftText rightText).run state |>.2.next ≤ Native.maxInstructions * Native.maxVectorLength) :
    Nonempty (NativeStepResult hash inputs witness state (hashSuffix domain leftText rightText)
      (.hash [.constant domain, leftTerm, rightTerm])) := by
  rcases leftMeaning with ⟨leftOperand, leftDecoded, leftValue⟩
  rcases rightMeaning with ⟨rightOperand, rightDecoded, rightValue⟩
  have leftNames := TextScope.identifiers leftScope leftDecoded
  have rightNames := TextScope.identifiers rightScope rightDecoded
  let key : ExpressionKey := ("transient_hash", [leftText, rightText], some domain)
  cases hit : state.expressions.lookup key with
  | some output =>
    have run : (hashSuffix domain leftText rightText).run state = (output, state) := by
      simpa only [key] using hashSuffix_hit_run domain leftText rightText output state hit
    refine ⟨{
      text := output
      finalState := state
      finalWitness := witness
      run := run
      operandMeaning := ScalarCache.cached_hash_meaning hash inputs witness state stateMeaning
        domain leftText rightText output leftTerm rightTerm
        ⟨leftOperand, leftDecoded, leftValue⟩ ⟨rightOperand, rightDecoded, rightValue⟩ (by simpa only [key] using hit)
      textScope := ScalarExpressionArithmetic.cached_text_scope hash witness state stateMeaning key output hit
      stateMeaning := stateMeaning
      budget := ?_
      aliasesPreserved := rfl
      frame := fun _ _ => rfl
    }⟩
    rw [run] at budget
    exact budget
  | none =>
    let output := freshName state.next
    let raw := Zkir.instruction "transient_hash"
      [("inputs", toJson [Zkir.fieldImmediate domain, leftText, rightText]), ("output", toJson output)]
    let instruction := Instruction.hash
      [.immediate (scalar domain), leftOperand, rightOperand] output
    let outputValue := hash [scalar domain, leftOperand.read witness, rightOperand.read witness]
    have run : (hashSuffix domain leftText rightText).run state =
        (output, appendFreshState state raw key output) := by
      simpa only [key, output, raw] using hashSuffix_miss_run domain leftText rightText state hit
    have budgetAfter : (hashSuffix domain leftText rightText).run state |>.2.next ≤
        (Native.maxInstructions * Native.maxVectorLength) := budget
    rw [run] at budgetAfter
    have budgetFresh : state.next + 1 ≤ Native.maxInstructions * Native.maxVectorLength := by
      simpa only [appendFreshState] using budgetAfter
    have outputValid : validIdentifier output = true := by
      dsimp only [output]
      exact fresh_identifier state.next (by omega)
    have domainDecoded : decodeOperand (toJson (Zkir.fieldImmediate domain)) =
        .ok (.immediate (scalar domain)) :=
      ScalarImmediate.decodeOperand_fieldImmediate_exact domain domainCanonical
    have inputsDecoded : decodeOperands (toJson [Zkir.fieldImmediate domain, leftText, rightText]) =
        .ok [.immediate (scalar domain), leftOperand, rightOperand] := by
      apply decodeOperands_of_texts
      simp only [List.mapM_cons, domainDecoded, leftDecoded, rightDecoded,
        List.mapM_nil, pure, Except.pure]
      rfl
    have instructionDecoded : decodeInstruction raw = .ok instruction := by
      dsimp only [raw, instruction]
      exact decode_hash_instruction inputsDecoded outputValid
    have cacheMatch : CacheCorresponds key output instruction := by
      dsimp only [key, instruction, output]
      refine ⟨rfl, domain, leftText, rightText, Zkir.fieldImmediate domain,
        leftOperand, rightOperand, rfl, rfl, ?_, leftDecoded, rightDecoded, ?_⟩
      · exact domainDecoded
      · exact outputValid
    have newScope : ∀ name ∈ instructionIdentifiers instruction, InScope (state.next + 1) name := by
      simpa only [instruction] using fresh_hash_scope state.next domain
        leftOperand rightOperand leftNames rightNames
    have independent : ∀ operand ∈ ([.immediate (scalar domain), leftOperand, rightOperand] : List Operand),
        OperandIndependent output operand := by
      intro operand member
      rcases List.mem_cons.mp member with equal | rest
      · cases equal
        trivial
      · rcases List.mem_cons.mp rest with equal | rest
        · cases equal
          exact Operand.independent_of_scope state.next leftOperand leftNames
        · rcases List.mem_cons.mp rest with equal | impossible
          · cases equal
            exact Operand.independent_of_scope state.next rightOperand rightNames
          · simp at impossible
    have holds : Instruction.Holds hash (assign witness output outputValue) instruction := by
      have holdsBase := hash_output_holds hash witness (freshName state.next)
        [.immediate (scalar domain), leftOperand, rightOperand] independent
      have outputEq : outputValue =
          hash ([.immediate (scalar domain), leftOperand, rightOperand].map (·.read witness)) := by
        change hash [scalar domain, leftOperand.read witness, rightOperand.read witness] =
          hash [(Operand.immediate (scalar domain)).read witness,
            leftOperand.read witness, rightOperand.read witness]
        simp [Operand.read]
      rw [outputEq]
      simpa only [instruction, output] using holdsBase
    have meaning : outputValue = interpret hash inputs (.hash [.constant domain, leftTerm, rightTerm]) := by
      simp [outputValue, interpret_hash, interpret_constant, leftValue, rightValue]
    obtain ⟨prior, priorDecoded⟩ := stateMeaning.decoded
    have finalMeaning : LowerStateMeaning hash (assign witness output outputValue)
        (appendFreshState state raw key output) :=
      LowerStateMeaning.appendFresh hash witness state prior priorDecoded stateMeaning raw key output instruction
        instructionDecoded cacheMatch rfl outputValid newScope outputValue holds
    refine ⟨{
      text := output
      finalState := appendFreshState state raw key output
      finalWitness := assign witness output outputValue
      run := run
      operandMeaning := OperandMeaning.reference hash inputs (assign witness output outputValue)
        output outputValid (.hash [.constant domain, leftTerm, rightTerm]) (by
          simpa only [assign_same] using meaning)
      textScope := TextScope.validReference (state.next + 1) output outputValid
        (Or.inr ⟨state.next, by simp, rfl⟩)
      stateMeaning := finalMeaning
      budget := budgetFresh
      aliasesPreserved := rfl
      frame := ?_
    }⟩
    · intro name inScope
      have different : name ≠ output := by
        intro equal
        subst name
        have freshScope : InScope state.next (freshName state.next) := by
          simpa only [output] using inScope
        exact fresh_not_inScope state.next freshScope
      exact assign_other witness output name outputValue different

theorem exprComplete_poseidon2 (domain : Nat) (left right : Expr .native)
    (leftComplete : ExprComplete left) (rightComplete : ExprComplete right) :
    ExprComplete (.poseidon2 domain left right) := by
  intro ctx hash implementation inputs witness state normalAliases values types value
    valid success aliases lowerAliases stateMeaning budget
  have domainBound : domain < Field.modulus := by
    have evalDomain := success
    simp only [Expr.eval] at evalDomain
    split at evalDomain
    · cases evalDomain
    · rename_i validDomain
      have domainLessThanContext : domain < ctx.modulus := Nat.lt_of_not_ge validDomain
      simpa [implementation.modulus] using domainLessThanContext
  have domainNotInvalid : ¬ Field.modulus ≤ domain := by omega
  have childValidation :
      (do left.validate {poseidon2 := true} types; right.validate {poseidon2 := true} types) = .ok () := by
    simpa [Expr.validate, domainNotInvalid] using valid
  simp only [ScalarValidation.bind_ok] at childValidation
  rcases childValidation with ⟨leftUnit, leftValid, rightValid⟩
  cases leftUnit
  have successParts := success
  simp only [Expr.eval] at successParts
  split at successParts
  next invalid => cases successParts
  next domainOK =>
    cases leftEval : left.eval ctx values with
    | error message => simp [leftEval, Bind.bind, Except.bind] at successParts
    | ok leftValue =>
      cases rightEval : right.eval ctx values with
      | error message => simp [leftEval, rightEval, Bind.bind, Except.bind] at successParts
      | ok rightValue =>
        have suffixPreserves : ∀ text,
            PreservesFrame (do
              let rightText ← Zkir.lowerExpr right
              hashSuffix domain text rightText) := by
          intro text
          apply bind_preserves _ _ (lowerExpr_preserves right)
          intro rightText
          exact hashSuffix_preserves domain text rightText
        have leftBudget : ((Zkir.lowerExpr left).run state).2.next ≤ Native.maxInstructions * Native.maxVectorLength := by
          apply bind_middle_budget (Zkir.lowerExpr left)
            (fun text => do
              let rightText ← Zkir.lowerExpr right
              hashSuffix domain text rightText) state suffixPreserves (Native.maxInstructions * Native.maxVectorLength)
          simpa only [← lowerExpr_poseidon2_shape] using budget
        obtain ⟨first⟩ := leftComplete ctx hash implementation inputs witness state normalAliases
          values types leftValue leftValid leftEval aliases lowerAliases stateMeaning leftBudget
        have remainingBudget : ((do
            let rightText ← Zkir.lowerExpr right
            hashSuffix domain first.text rightText).run first.finalState).2.next ≤ Native.maxInstructions * Native.maxVectorLength := by
          have bound := budget
          change ((do
            let leftText ← Zkir.lowerExpr left
            let rightText ← Zkir.lowerExpr right
            hashSuffix domain leftText rightText).run state).2.next ≤ _ at bound
          rw [StateT.run_bind, first.run] at bound
          exact bound
        have rightBudget := bind_middle_budget (Zkir.lowerExpr right)
          (fun rightText => hashSuffix domain first.text rightText) first.finalState
          (fun rightText => hashSuffix_preserves domain first.text rightText)
          (Native.maxInstructions * Native.maxVectorLength) remainingBudget
        obtain ⟨second⟩ := rightComplete ctx hash implementation inputs first.finalWitness
          first.finalState normalAliases values types rightValue rightValid rightEval aliases
          first.aliasAgreement first.stateMeaning rightBudget
        have firstNext : state.next ≤ first.finalState.next := by
          have bound := ScalarAllocation.lowerExpr_next left state
          rw [first.run] at bound
          exact bound
        have secondNext : first.finalState.next ≤ second.finalState.next := by
          have bound := ScalarAllocation.lowerExpr_next right first.finalState
          rw [second.run] at bound
          exact bound
        have hashBudget : (hashSuffix domain first.text second.text).run second.finalState |>.2.next ≤
            (Native.maxInstructions * Native.maxVectorLength) := by
          have bound := remainingBudget
          change ((do
            let rightText ← Zkir.lowerExpr right
            hashSuffix domain first.text rightText).run first.finalState).2.next ≤ _ at bound
          rw [StateT.run_bind, second.run] at bound
          exact bound
        have leftMeaning := OperandMeaning.of_frame hash inputs first.finalWitness second.finalWitness
          first.finalState.next first.text first.normalized.term first.operandMeaning first.textScope second.frame
        have leftScope := TextScope.mono secondNext first.textScope
        obtain ⟨hashStep⟩ := hashSuffix_step hash inputs second.finalWitness second.finalState domain
          first.text second.text first.normalized.term second.normalized.term second.stateMeaning
          leftMeaning second.operandMeaning leftScope second.textScope domainBound hashBudget
        have childrenNext : state.next ≤ second.finalState.next := Nat.le_trans firstNext secondNext
        obtain ⟨normalized, normalization, represents⟩ :=
          normalize_success ctx hash implementation inputs normalAliases values aliases
            (.poseidon2 domain left right) value success
        have termEq : normalized.term =
            .hash [.constant domain, first.normalized.term, second.normalized.term] := by
          have normal := normalization
          simp only [Backend.Native.normalize, first.normalization, second.normalization] at normal
          cases normal
          rfl
        refine ⟨{
          text := hashStep.text
          finalState := hashStep.finalState
          finalWitness := hashStep.finalWitness
          normalized := normalized
          run := by
            change ((do
              let leftText ← Zkir.lowerExpr left
              let rightText ← Zkir.lowerExpr right
              hashSuffix domain leftText rightText).run state) = _
            rw [StateT.run_bind, first.run]
            change ((do
              let rightText ← Zkir.lowerExpr right
              hashSuffix domain first.text rightText).run first.finalState) = _
            rw [StateT.run_bind, second.run]
            exact hashStep.run
          normalization := normalization
          represents := represents
          operandMeaning := by rw [termEq]; exact hashStep.operandMeaning
          textScope := hashStep.textScope
          stateMeaning := hashStep.stateMeaning
          budget := hashStep.budget
          aliasAgreement := ?_
          aliasesPreserved := hashStep.aliasesPreserved.trans
            (second.aliasesPreserved.trans first.aliasesPreserved)
          frame := by
            intro name namesScoped
            rw [hashStep.frame name (InScope.mono childrenNext namesScoped)]
            rw [second.frame name (InScope.mono firstNext namesScoped)]
            exact first.frame name namesScoped
        }⟩
        ·
          have aliasCore : LowerAliasAgreement hash inputs hashStep.finalWitness normalAliases
              hashStep.finalState.aliases values := by
            rw [hashStep.aliasesPreserved]
            exact LowerAliasAgreement.of_frame hash inputs second.finalWitness hashStep.finalWitness
              second.finalState.next normalAliases second.finalState.aliases values
              second.aliasAgreement second.stateMeaning.aliases hashStep.frame
          exact aliasCore

end Noctium.Verification.ScalarExpressionHash
