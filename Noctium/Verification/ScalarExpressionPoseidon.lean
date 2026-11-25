import Noctium.Verification.ScalarAllocationOutputFrame
import Noctium.Verification.ScalarNativeWitnessSteps
import Noctium.Verification.ScalarLowering
import Noctium.Verification.ScalarCache
import Noctium.Verification.ScalarImmediate
import Noctium.Verification.ScalarInstructionEncoding
import Noctium.Verification.ScalarWitness

namespace Noctium.Verification.ScalarWitnessConstruction

open Lean Backend NativeRelation NativeRelationJson ScalarNormalization ScalarLowering
open ScalarInstructionEncoding ScalarImmediate ScalarValidationMeaning
open ScalarWitness
open ScalarAllocationOutputFrame

abbrev Assignment := NativeRelation.Assignment

private theorem stateRunBind {α β} (first : StateM Zkir.LowerState α)
    (next : α → StateM Zkir.LowerState β) (state : Zkir.LowerState) :
    (do let value ← first; next value).run state =
      (next (first.run state).1).run (first.run state).2 := rfl

private def hashSuffix (domain : Nat) (left right : String) : StateM Zkir.LowerState String := do
  let key : ExpressionKey := ("transient_hash", [Zkir.fieldImmediate domain, left, right], none)
  if let some existing := (← get).expressions.lookup key then return existing
  let output ← Zkir.fresh
  Zkir.emit "transient_hash" [("inputs", toJson [Zkir.fieldImmediate domain, left, right]),
    ("output", toJson output)]
  modify fun s => {s with expressions := (key, output) :: s.expressions}
  return output

private theorem lowerExpr_poseidon2_shape (domain : Nat) (left right : Expr .native) :
    Zkir.lowerExpr (.poseidon2 domain left right) = (do
      let leftText ← Zkir.lowerExpr left
      let rightText ← Zkir.lowerExpr right
      hashSuffix domain leftText rightText) := by
  simp only [Zkir.lowerExpr, hashSuffix]
  rfl

private theorem hashSuffix_hit_run (domain : Nat) (left right output : String)
    (state : Zkir.LowerState)
    (hit : state.expressions.lookup
      ("transient_hash", [Zkir.fieldImmediate domain, left, right], none) = some output) :
    (hashSuffix domain left right).run state = (output, state) := by
  simp [hashSuffix, hit]
  rfl

private theorem hashSuffix_miss_run (domain : Nat) (left right : String)
    (state : Zkir.LowerState)
    (miss : state.expressions.lookup
      ("transient_hash", [Zkir.fieldImmediate domain, left, right], none) = none) :
    (hashSuffix domain left right).run state =
      (freshName state.next,
        appendFreshState state
          (Zkir.instruction "transient_hash"
            [("inputs", toJson [Zkir.fieldImmediate domain, left, right]),
              ("output", toJson (freshName state.next))])
          ("transient_hash", [Zkir.fieldImmediate domain, left, right], none)
          (freshName state.next)) := by
  simp [hashSuffix, miss, Zkir.fresh, Zkir.emit, Zkir.instruction,
    appendFreshState, freshName, StateT.run_bind, StateT.run_get,
    StateT.run_modify, StateT.run_set]
  rfl

private theorem hashSuffix_preservesOutputCapacityFrame (domain : Nat) (left right : String) :
    Zkir.PreservesOutputCapacityFrame (hashSuffix domain left right) := by
  intro state
  let key : ExpressionKey := ("transient_hash", [Zkir.fieldImmediate domain, left, right], none)
  cases hit : state.expressions.lookup key with
  | some output =>
    have run : (hashSuffix domain left right).run state = (output, state) := by
      simpa only [key] using hashSuffix_hit_run domain left right output state hit
    rw [run]
    exact Zkir.OutputCapacityFrame.refl state
  | none =>
    let output := freshName state.next
    let raw := Zkir.instruction "transient_hash"
      [("inputs", toJson [Zkir.fieldImmediate domain, left, right]), ("output", toJson output)]
    have run : (hashSuffix domain left right).run state =
        (output, appendFreshState state raw key output) := by
      simpa only [key, output, raw] using hashSuffix_miss_run domain left right state hit
    rw [run]
    change Zkir.OutputCapacityFrame state (appendFreshState state raw key output)
    constructor
    · simp [appendFreshState]
    · have outputCount : Native.outputDefinitionsInInstruction raw = 1 := by
        have opcodeOk : Native.stringField raw "op" = .ok "transient_hash" := by
          change (Except.ok "transient_hash") = .ok "transient_hash"
          rfl
        have outputOk : (Native.stringField raw "output").isOk = true := by
          change (Except.ok output).isOk = true
          rfl
        unfold Native.outputDefinitionsInInstruction
        rw [opcodeOk]
        simp [outputOk]
      change state.outputDefinitions + (state.next + 1 - state.next) ≤
        ({state with instructions := state.instructions.push raw}).outputDefinitions
      rw [Zkir.LowerState.outputDefinitions_push, outputCount]
      omega

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
    (budget : (hashSuffix domain leftText rightText).run state |>.2.next ≤
      Native.maxInstructions * Native.maxVectorLength) :
    Nonempty (NativeStepResult hash inputs witness state (hashSuffix domain leftText rightText)
      (.hash [.constant domain, leftTerm, rightTerm])) := by
  rcases leftMeaning with ⟨leftOperand, leftDecoded, leftValue⟩
  rcases rightMeaning with ⟨rightOperand, rightDecoded, rightValue⟩
  have leftNames := TextScope.identifiers leftScope leftDecoded
  have rightNames := TextScope.identifiers rightScope rightDecoded
  let key : ExpressionKey := ("transient_hash", [Zkir.fieldImmediate domain, leftText, rightText], none)
  have domainDecoded : decodeOperand (toJson (Zkir.fieldImmediate domain)) =
      .ok (.immediate (scalar domain)) :=
    ScalarImmediate.decodeOperand_fieldImmediate_exact domain domainCanonical
  cases hit : state.expressions.lookup key with
  | some output =>
    have run : (hashSuffix domain leftText rightText).run state = (output, state) := by
      simpa only [key] using hashSuffix_hit_run domain leftText rightText output state hit
    have exactHit : state.expressions.lookup
        ("transient_hash", [Zkir.fieldImmediate domain, leftText, rightText], none) = some output := by
      simpa only [key] using hit
    exact cached_step hash inputs witness state _ _ key output stateMeaning hit run
      (ScalarCache.cached_hash_meaning hash inputs witness state stateMeaning domain
        (Zkir.fieldImmediate domain) leftText rightText output leftTerm rightTerm
        ⟨leftOperand, leftDecoded, leftValue⟩ ⟨rightOperand, rightDecoded, rightValue⟩
        domainDecoded exactHit) budget
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
        Native.maxInstructions * Native.maxVectorLength := budget
    rw [run] at budgetAfter
    have budgetFresh : state.next + 1 ≤ Native.maxInstructions * Native.maxVectorLength := by
      change state.next + 1 ≤ Native.maxInstructions * Native.maxVectorLength at budgetAfter
      exact budgetAfter
    have outputValid : validIdentifier output = true := by
      dsimp only [output]
      exact NativeRelationJson.generatedIdentifier_fits_output_capacity state.next (by omega)
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
      refine ⟨rfl, domain, Zkir.fieldImmediate domain, leftText, rightText,
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
    have meaning : interpret hash inputs (.hash [.constant domain, leftTerm, rightTerm]) =
        some outputValue := by
      simp [outputValue, interpret_hash, leftValue, rightValue]
    refine fresh_step hash inputs witness state (hashSuffix domain leftText rightText)
      (.hash [.constant domain, leftTerm, rightTerm]) raw key instruction outputValue stateMeaning run
      instructionDecoded cacheMatch newScope holds ?_ budget
    · simpa only [outputValue] using meaning

private theorem outputCapacity_first_stage_budget {α β : Type} (state : Zkir.LowerState)
    (first : StateM Zkir.LowerState α) (next : α → StateM Zkir.LowerState β)
    (nextFrame : ∀ value, Zkir.PreservesOutputCapacityFrame (next value))
    (limit : Nat) (budget : ((first >>= next).run state).2.next ≤ limit) :
    (first.run state).2.next ≤ limit := by
  have suffixBudget : ((next (first.run state).1).run (first.run state).2).2.next ≤ limit := by
          rw [stateRunBind] at budget
          exact budget
  exact Nat.le_trans (nextFrame (first.run state).1 (first.run state).2).next suffixBudget

/-- Poseidon2 completeness follows the exact three-operand `transient_hash`
lowering, including its domain immediate and CSE cache key. -/
theorem complete_poseidon2 (domain : Nat) (left right : Expr .native)
    (leftAdmitted : ScalarExpression left) (rightAdmitted : ScalarExpression right)
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
      (do left.validate Capabilities.crypto types; right.validate Capabilities.crypto types) = .ok () := by
    have cryptoHash : Capabilities.crypto.poseidon2 = true := rfl
    have cryptoModulus : Capabilities.crypto.nativeModulus = Field.modulus := rfl
    simpa [Expr.validate, cryptoHash, cryptoModulus, domainNotInvalid] using valid
  rcases ScalarValidationMeaning.bind_ok.mp childValidation with ⟨leftUnit, leftValid, rightValid⟩
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
        have expressionAdmission : ScalarExpression (.poseidon2 domain left right) :=
          .poseidon2 domain left right leftAdmitted rightAdmitted
        have leftFrame := lowerExpr_admitted_preservesOutputCapacityFrame left leftAdmitted
        have rightFrame := lowerExpr_admitted_preservesOutputCapacityFrame right rightAdmitted
        have suffixFrame (text : String) :
            Zkir.PreservesOutputCapacityFrame (do
              let rightText ← Zkir.lowerExpr right
              hashSuffix domain text rightText) := by
          apply Zkir.bind_preservesOutputCapacityFrame _ _ rightFrame
          intro rightText
          exact hashSuffix_preservesOutputCapacityFrame domain text rightText
        have wholeBudget : ((do
            let leftText ← Zkir.lowerExpr left
            let rightText ← Zkir.lowerExpr right
            hashSuffix domain leftText rightText).run state).2.next ≤
              Native.maxInstructions * Native.maxVectorLength := by
          simpa only [← lowerExpr_poseidon2_shape] using budget
        have leftBudget : ((Zkir.lowerExpr left).run state).2.next ≤
            Native.maxInstructions * Native.maxVectorLength :=
          outputCapacity_first_stage_budget state (Zkir.lowerExpr left)
            (fun leftText => do
              let rightText ← Zkir.lowerExpr right
              hashSuffix domain leftText rightText)
            suffixFrame (Native.maxInstructions * Native.maxVectorLength) wholeBudget
        obtain ⟨first⟩ := leftComplete ctx hash implementation inputs witness state normalAliases
          values types leftValue leftValid leftEval aliases lowerAliases stateMeaning leftBudget
        have remainingBudget : ((do
            let rightText ← Zkir.lowerExpr right
            hashSuffix domain first.text rightText).run first.finalState).2.next ≤
              Native.maxInstructions * Native.maxVectorLength := by
          have bound := wholeBudget
          rw [StateT.run_bind, first.run] at bound
          exact bound
        have rightBudget : ((Zkir.lowerExpr right).run first.finalState).2.next ≤
            Native.maxInstructions * Native.maxVectorLength :=
          outputCapacity_first_stage_budget first.finalState (Zkir.lowerExpr right)
            (fun rightText => hashSuffix domain first.text rightText)
            (fun rightText => hashSuffix_preservesOutputCapacityFrame domain first.text rightText)
            (Native.maxInstructions * Native.maxVectorLength) remainingBudget
        obtain ⟨second⟩ := rightComplete ctx hash implementation inputs first.finalWitness
          first.finalState normalAliases values types rightValue rightValid rightEval aliases
          first.aliasAgreement first.stateMeaning rightBudget
        have beforeSecond : state.next ≤ first.finalState.next := by
          simpa only [first.run] using (leftFrame state).next
        have beforeSuffix : first.finalState.next ≤ second.finalState.next := by
          simpa only [second.run] using (rightFrame first.finalState).next
        have leftMeaning := OperandMeaning.of_frame hash inputs first.finalWitness second.finalWitness
          first.finalState.next first.text first.normalized.term first.operandMeaning first.textScope second.frame
        have hashBudget : (hashSuffix domain first.text second.text).run second.finalState |>.2.next ≤
            Native.maxInstructions * Native.maxVectorLength := by
          have bound := remainingBudget
          rw [StateT.run_bind, second.run] at bound
          exact bound
        obtain ⟨hashStep⟩ := hashSuffix_step hash inputs second.finalWitness second.finalState domain
          first.text second.text first.normalized.term second.normalized.term second.stateMeaning
          leftMeaning second.operandMeaning (TextScope.mono beforeSuffix first.textScope)
          second.textScope domainBound hashBudget
        obtain ⟨normalized, normalization, represents⟩ := normalize_success ctx hash implementation inputs
          normalAliases values aliases (.poseidon2 domain left right) expressionAdmission value success
        have termEq : normalized.term =
            .hash [.constant domain, first.normalized.term, second.normalized.term] := by
          have normal := normalization
          simp only [Backend.Native.normalize, first.normalization, second.normalization] at normal
          cases normal
          rfl
        have childrenNext : state.next ≤ second.finalState.next := Nat.le_trans beforeSecond beforeSuffix
        have aliasesPreserved : hashStep.finalState.aliases = state.aliases := by
          rw [hashStep.aliasesPreserved, second.aliasesPreserved, first.aliasesPreserved]
        have secondAliases : second.finalState.aliases = state.aliases := by
          rw [second.aliasesPreserved, first.aliasesPreserved]
        have finalAliasAgreement : LowerAliasAgreement hash inputs hashStep.finalWitness
            normalAliases hashStep.finalState.aliases values := by
          rw [aliasesPreserved]
          rw [← secondAliases]
          exact LowerAliasAgreement.of_frame hash inputs second.finalWitness hashStep.finalWitness
            second.finalState.next normalAliases second.finalState.aliases values second.aliasAgreement
            second.stateMeaning.aliases hashStep.frame
        have rootFrame : ∀ name, InScope state.next name → hashStep.finalWitness name = witness name := by
          intro name inScope
          have firstScope : InScope first.finalState.next name := InScope.mono beforeSecond inScope
          have secondScope : InScope second.finalState.next name := InScope.mono beforeSuffix firstScope
          exact (hashStep.frame name (InScope.mono childrenNext inScope)).trans
            ((second.frame name firstScope).trans (first.frame name inScope))
        refine ⟨{
          text := hashStep.text
          finalState := hashStep.finalState
          finalWitness := hashStep.finalWitness
          normalized := normalized
          run := by
            rw [lowerExpr_poseidon2_shape, stateRunBind, first.run, stateRunBind, second.run]
            exact hashStep.run
          normalization := normalization
          represents := represents
          operandMeaning := by rw [termEq]; exact hashStep.operandMeaning
          textScope := hashStep.textScope
          stateMeaning := hashStep.stateMeaning
          budget := hashStep.budget
          aliasAgreement := finalAliasAgreement
          aliasesPreserved := aliasesPreserved
          frame := rootFrame
        }⟩

end Noctium.Verification.ScalarWitnessConstruction
