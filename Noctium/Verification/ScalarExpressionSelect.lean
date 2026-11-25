import Noctium.Verification.ScalarNativeWitnessSteps
import Noctium.Verification.ScalarAllocationOutputFrame
import Noctium.Verification.ScalarStateExtensions

namespace Noctium.Verification.ScalarWitnessConstruction

open Lean Backend NativeRelation NativeRelationJson ScalarNormalization ScalarLowering
open ScalarInstructionEncoding ScalarWitness ScalarAllocationOutputFrame

private def selectSuffix (condition yes no : String) : StateM Zkir.LowerState String := do
  if yes == no then return yes
  let key : ExpressionKey := ("cond_select", [condition, yes, no], none)
  if let some existing := (← get).expressions.lookup key then return existing
  let output ← Zkir.fresh
  Zkir.emit "cond_select" [
    ("bit", toJson condition), ("a", toJson yes), ("b", toJson no), ("output", toJson output)]
  modify fun state => {state with expressions := (("cond_select", [condition, yes, no], none), output) :: state.expressions}
  pure output

private theorem selectSuffix_run (condition yes no : String) (state : Zkir.LowerState) :
    (selectSuffix condition yes no).run state =
      if yes == no then (yes, state) else
        match state.expressions.lookup ("cond_select", [condition, yes, no], none) with
        | some output => (output, state)
        | none => (freshName state.next, appendFreshState state
            (Zkir.instruction "cond_select" [
              ("bit", toJson condition), ("a", toJson yes), ("b", toJson no),
              ("output", toJson (freshName state.next))])
            ("cond_select", [condition, yes, no], none) (freshName state.next)) := by
  by_cases equal : yes == no
  · simp [selectSuffix, equal, StateT.run_pure] <;> rfl
  · cases hit : state.expressions.lookup ("cond_select", [condition, yes, no], none) with
    | some output => simp [selectSuffix, equal, hit, StateT.run_pure] <;> rfl
    | none =>
      simp [selectSuffix, equal, hit, Zkir.fresh, Zkir.emit, appendFreshState,
        freshName, Zkir.instruction, StateT.run_bind, StateT.run_get,
        StateT.run_set, StateT.run_modify] <;> rfl

private theorem selectSuffix_next (condition yes no : String) (state : Zkir.LowerState) :
    state.next ≤ ((selectSuffix condition yes no).run state).2.next := by
  rw [selectSuffix_run]
  by_cases equal : yes == no
  · simp [equal]
  · cases hit : state.expressions.lookup ("cond_select", [condition, yes, no], none) with
    | some output => simp [equal]
    | none => simp [equal, appendFreshState]

private theorem bind_nextMonotone {α β : Type}
    (first : StateM Zkir.LowerState α) (next : α → StateM Zkir.LowerState β)
    (firstNext : ∀ state, state.next ≤ (first.run state).2.next)
    (nextNext : ∀ value state, state.next ≤ ((next value).run state).2.next)
    (state : Zkir.LowerState) :
    state.next ≤ ((do let value ← first; next value : StateM Zkir.LowerState β).run state).2.next := by
  rw [StateT.run_bind]
  exact Nat.le_trans (firstNext state) (nextNext _ _)

private theorem runBind {α β : Type} (first : StateM Zkir.LowerState α)
    (next : α → StateM Zkir.LowerState β) (state : Zkir.LowerState) :
    (do let value ← first; next value).run state =
      (next (first.run state).1).run (first.run state).2 := rfl

private theorem lowerSelect_eq {ty : Ty} (condition : Expr .bool) (yes no : Expr ty) :
    Zkir.lowerExpr (.select condition yes no) = (do
      let conditionText ← Zkir.lowerExpr condition
      let yesText ← Zkir.lowerExpr yes
      let noText ← Zkir.lowerExpr no
      selectSuffix conditionText yesText noText) := by
  simp only [Zkir.lowerExpr]
  rfl

private theorem fresh_select_scope (next : Nat) (condition yes no : Operand)
    (conditionScope : ∀ name ∈ operandIdentifiers condition, InScope next name)
    (yesScope : ∀ name ∈ operandIdentifiers yes, InScope next name)
    (noScope : ∀ name ∈ operandIdentifiers no, InScope next name) :
    ∀ name ∈ instructionIdentifiers (.select condition yes no (freshName next)),
      InScope (next + 1) name := by
  intro name member
  simp only [instructionIdentifiers, List.mem_append, List.mem_singleton] at member
  rcases member with ((member | member) | member) | rfl
  · exact InScope.mono (by omega) (conditionScope name member)
  · exact InScope.mono (by omega) (yesScope name member)
  · exact InScope.mono (by omega) (noScope name member)
  · exact Or.inr ⟨next, by omega, rfl⟩

private theorem selectSuffix_step (hash : Hash) (inputs witness : NativeRelation.Assignment)
    (state : Zkir.LowerState) (condition yes no : String)
    (conditionTerm yesTerm noTerm : Backend.Native.Term)
    (stateMeaning : LowerStateMeaning hash witness state)
    (conditionMeaning : OperandMeaning hash inputs witness condition conditionTerm)
    (yesMeaning : OperandMeaning hash inputs witness yes yesTerm)
    (noMeaning : OperandMeaning hash inputs witness no noTerm)
    (conditionScope : TextScope state.next condition)
    (yesScope : TextScope state.next yes) (noScope : TextScope state.next no)
    (boolean : interpret hash inputs conditionTerm = some zero ∨
      interpret hash inputs conditionTerm = some one)
    (budget : ((selectSuffix condition yes no).run state).2.next ≤
      Native.maxInstructions * Native.maxVectorLength) :
    Nonempty (NativeStepResult hash inputs witness state (selectSuffix condition yes no)
      (.select conditionTerm yesTerm noTerm)) := by
  rcases conditionMeaning with ⟨conditionOperand, conditionDecoded, conditionValue⟩
  rcases yesMeaning with ⟨yesOperand, yesDecoded, yesValue⟩
  rcases noMeaning with ⟨noOperand, noDecoded, noValue⟩
  have conditionNames := TextScope.identifiers conditionScope conditionDecoded
  have yesNames := TextScope.identifiers yesScope yesDecoded
  have noNames := TextScope.identifiers noScope noDecoded
  by_cases equal : yes == no
  · have textEqual : yes = no := eq_of_beq equal
    have noDecoded' : decodeOperand (toJson yes) = .ok noOperand := by
      simpa [textEqual] using noDecoded
    have operandsEqual : yesOperand = noOperand :=
      Except.ok.inj (yesDecoded.symm.trans noDecoded')
    have noValue' : interpret hash inputs noTerm = some (yesOperand.read witness) := by
      simpa [operandsEqual] using noValue
    have selectedMeaning : interpret hash inputs (.select conditionTerm yesTerm noTerm) =
        some (yesOperand.read witness) := by
      rcases boolean with conditionZero | conditionOne
      · have readZero : conditionOperand.read witness = zero :=
          Option.some.inj (conditionValue.symm.trans conditionZero)
        simp [interpret_select, conditionValue, yesValue, noValue', readZero]
      · have readOne : conditionOperand.read witness = one :=
          Option.some.inj (conditionValue.symm.trans conditionOne)
        simp [interpret_select, conditionValue, yesValue, noValue', readOne]
    have run : (selectSuffix condition yes no).run state = (yes, state) := by
      simp [selectSuffix_run, equal]
    refine ⟨{
      text := yes
      finalState := state
      finalWitness := witness
      run := run
      operandMeaning := ⟨yesOperand, yesDecoded, selectedMeaning⟩
      textScope := yesScope
      stateMeaning := stateMeaning
      budget := ?_
      aliasesPreserved := rfl
      frame := by intro name inScope; rfl
    }⟩
    rw [run] at budget
    exact budget
  · cases hit : state.expressions.lookup ("cond_select", [condition, yes, no], none) with
    | some output =>
      have run : (selectSuffix condition yes no).run state = (output, state) := by
        simp [selectSuffix_run, equal, hit]
      exact cached_step hash inputs witness state (selectSuffix condition yes no)
        (.select conditionTerm yesTerm noTerm) ("cond_select", [condition, yes, no], none)
        output stateMeaning hit run
        (ScalarCache.cached_select_meaning hash inputs witness state stateMeaning
          condition yes no output conditionTerm yesTerm noTerm
          ⟨conditionOperand, conditionDecoded, conditionValue⟩
          ⟨yesOperand, yesDecoded, yesValue⟩ ⟨noOperand, noDecoded, noValue⟩ hit)
        budget
    | none =>
      let raw := Zkir.instruction "cond_select" [
        ("bit", toJson condition), ("a", toJson yes), ("b", toJson no),
        ("output", toJson (freshName state.next))]
      let key : ExpressionKey := ("cond_select", [condition, yes, no], none)
      let output := freshName state.next
      let instruction : Instruction := .select conditionOperand yesOperand noOperand output
      let value := if conditionOperand.read witness = one then
        yesOperand.read witness else noOperand.read witness
      have run : (selectSuffix condition yes no).run state = (output,
          appendFreshState state raw key output) := by
        simp [selectSuffix_run, equal, hit, raw, key, output]
      have outputBound : state.next + 1 ≤ Native.maxInstructions * Native.maxVectorLength := by
        rw [run] at budget
        simpa [appendFreshState] using budget
      have valid : validIdentifier output = true :=
        NativeRelationJson.generatedIdentifier_fits_output_capacity state.next (by omega)
      have booleanOperand : conditionOperand.read witness = zero ∨
          conditionOperand.read witness = one := by
        rcases boolean with conditionZero | conditionOne
        · exact Or.inl (Option.some.inj (conditionValue.symm.trans conditionZero))
        · exact Or.inr (Option.some.inj (conditionValue.symm.trans conditionOne))
      have selectedMeaning : interpret hash inputs (.select conditionTerm yesTerm noTerm) =
          some value := by
        rcases booleanOperand with conditionZero | conditionOne
        · simp [interpret_select, conditionValue, yesValue, noValue, conditionZero, zero_ne_one,
            value]
        · simp [interpret_select, conditionValue, yesValue, noValue, conditionOne, value]
      apply fresh_step hash inputs witness state (selectSuffix condition yes no)
        (.select conditionTerm yesTerm noTerm) raw key instruction value stateMeaning run
        (decode_select_instruction conditionDecoded yesDecoded noDecoded valid)
      · exact ⟨rfl, condition, yes, no, rfl, conditionDecoded, yesDecoded, noDecoded, valid⟩
      · exact fresh_select_scope state.next conditionOperand yesOperand noOperand
          conditionNames yesNames noNames
      · exact select_output_holds hash witness output conditionOperand yesOperand noOperand
          (Operand.independent_of_scope state.next conditionOperand conditionNames)
          (Operand.independent_of_scope state.next yesOperand yesNames)
          (Operand.independent_of_scope state.next noOperand noNames) booleanOperand
      · exact selectedMeaning
      · exact budget

/-- Lower the condition and both source branches in order, then account for the
actual cached or fresh `cond_select` result from the current lowerer. -/
theorem exprComplete_select {ty : Ty} (condition : Expr .bool) (yes no : Expr ty)
    (sourceType : ScalarType ty)
    (conditionSupported : ScalarExpression condition)
    (yesSupported : ScalarExpression yes) (noSupported : ScalarExpression no)
    (conditionComplete : ExprComplete condition)
    (yesComplete : ExprComplete yes) (noComplete : ExprComplete no) :
    ExprComplete (.select condition yes no) := by
  intro ctx hash implementation inputs witness state normalAliases values types result
    valid success aliasAgreement lowerAliasAgreement lowerStateMeaning budget
  have validChildren : (do
      condition.validate Capabilities.crypto types
      yes.validate Capabilities.crypto types
      no.validate Capabilities.crypto types) = .ok () := by
    cases sourceType <;>
      simpa [Expr.validate, Ty.isBytes, Ty.isJubjub, Ty.isForeign,
        Capabilities.crypto, Backend.Native.ensure] using valid
  rcases ScalarValidationMeaning.bind_ok.mp validChildren with
    ⟨_, conditionValid, yesAndNoValid⟩
  rcases ScalarValidationMeaning.bind_ok.mp yesAndNoValid with
    ⟨_, yesValid, noValid⟩
  cases conditionEval : condition.eval ctx values with
  | error message => simp [Expr.eval, conditionEval, Bind.bind, Except.bind] at success
  | ok conditionValue =>
    cases yesEval : yes.eval ctx values with
    | error message => simp [Expr.eval, conditionEval, yesEval, Bind.bind, Except.bind] at success
    | ok yesValue =>
      cases noEval : no.eval ctx values with
      | error message => simp [Expr.eval, conditionEval, yesEval, noEval, Bind.bind, Except.bind] at success
      | ok noValue =>
        have conditionFrame :=
          lowerExpr_admitted_preservesOutputCapacityFrame condition conditionSupported
        have yesFrame := lowerExpr_admitted_preservesOutputCapacityFrame yes yesSupported
        have noFrame := lowerExpr_admitted_preservesOutputCapacityFrame no noSupported
        have tailNext : ∀ conditionText yesText noText state,
            state.next ≤ ((selectSuffix conditionText yesText noText).run state).2.next := by
          intro conditionText yesText noText state
          exact selectSuffix_next conditionText yesText noText state
        have noTailNext (conditionText yesText : String) : ∀ state,
            state.next ≤ ((do
              let noText ← Zkir.lowerExpr no
              selectSuffix conditionText yesText noText).run state).2.next := by
          intro state
          exact bind_nextMonotone (Zkir.lowerExpr no)
            (fun noText => selectSuffix conditionText yesText noText)
            (fun state => (noFrame state).next)
            (fun noText state => tailNext conditionText yesText noText state) state
        have yesTailNext (conditionText : String) : ∀ state,
            state.next ≤ ((do
              let yesText ← Zkir.lowerExpr yes
              let noText ← Zkir.lowerExpr no
              selectSuffix conditionText yesText noText).run state).2.next := by
          intro state
          exact bind_nextMonotone (Zkir.lowerExpr yes)
            (fun yesText => do
              let noText ← Zkir.lowerExpr no
              selectSuffix conditionText yesText noText)
            (fun state => (yesFrame state).next)
            (fun yesText state => noTailNext conditionText yesText state) state
        have wholeBudget : ((do
            let conditionText ← Zkir.lowerExpr condition
            let yesText ← Zkir.lowerExpr yes
            let noText ← Zkir.lowerExpr no
            selectSuffix conditionText yesText noText).run state).2.next ≤
              Native.maxInstructions * Native.maxVectorLength := by
          simpa only [lowerSelect_eq] using budget
        have conditionBudget : ((Zkir.lowerExpr condition).run state).2.next ≤
            Native.maxInstructions * Native.maxVectorLength := by
          have afterConditionBudget : ((do
              let yesText ← Zkir.lowerExpr yes
              let noText ← Zkir.lowerExpr no
              selectSuffix ((Zkir.lowerExpr condition).run state).1 yesText noText).run
                ((Zkir.lowerExpr condition).run state).2).2.next ≤
              Native.maxInstructions * Native.maxVectorLength := by
            rw [StateT.run_bind] at wholeBudget
            exact wholeBudget
          exact Nat.le_trans
            (yesTailNext ((Zkir.lowerExpr condition).run state).1
              ((Zkir.lowerExpr condition).run state).2)
            afterConditionBudget
        obtain ⟨first⟩ := conditionComplete ctx hash implementation inputs witness state
          normalAliases values types conditionValue conditionValid conditionEval aliasAgreement
          lowerAliasAgreement lowerStateMeaning conditionBudget
        have remainingBudget : ((do
            let yesText ← Zkir.lowerExpr yes
            let noText ← Zkir.lowerExpr no
            selectSuffix first.text yesText noText).run first.finalState).2.next ≤
              Native.maxInstructions * Native.maxVectorLength := by
          have bound := wholeBudget
          rw [StateT.run_bind, first.run] at bound
          exact bound
        have yesBudget : ((Zkir.lowerExpr yes).run first.finalState).2.next ≤
            Native.maxInstructions * Native.maxVectorLength := by
          have afterYesBudget : ((do
              let noText ← Zkir.lowerExpr no
              selectSuffix first.text ((Zkir.lowerExpr yes).run first.finalState).1 noText).run
                ((Zkir.lowerExpr yes).run first.finalState).2).2.next ≤
              Native.maxInstructions * Native.maxVectorLength := by
            rw [StateT.run_bind] at remainingBudget
            exact remainingBudget
          exact Nat.le_trans
            (noTailNext first.text ((Zkir.lowerExpr yes).run first.finalState).1
              ((Zkir.lowerExpr yes).run first.finalState).2)
            afterYesBudget
        obtain ⟨second⟩ := yesComplete ctx hash implementation inputs first.finalWitness
          first.finalState normalAliases values types yesValue yesValid yesEval aliasAgreement
          first.aliasAgreement first.stateMeaning yesBudget
        have afterYesBudget : ((do
            let noText ← Zkir.lowerExpr no
            selectSuffix first.text second.text noText).run second.finalState).2.next ≤
              Native.maxInstructions * Native.maxVectorLength := by
          have bound := remainingBudget
          rw [StateT.run_bind, second.run] at bound
          exact bound
        have noBudget : ((Zkir.lowerExpr no).run second.finalState).2.next ≤
            Native.maxInstructions * Native.maxVectorLength := by
          have tailBudget : ((selectSuffix first.text second.text
              ((Zkir.lowerExpr no).run second.finalState).1).run
              ((Zkir.lowerExpr no).run second.finalState).2).2.next ≤
              Native.maxInstructions * Native.maxVectorLength := by
            rw [StateT.run_bind] at afterYesBudget
            exact afterYesBudget
          exact Nat.le_trans
            (tailNext first.text second.text
              ((Zkir.lowerExpr no).run second.finalState).1
              ((Zkir.lowerExpr no).run second.finalState).2)
            tailBudget
        obtain ⟨third⟩ := noComplete ctx hash implementation inputs second.finalWitness
          second.finalState normalAliases values types noValue noValid noEval aliasAgreement
          second.aliasAgreement second.stateMeaning noBudget
        have nativeBudget : ((selectSuffix first.text second.text third.text).run
            third.finalState).2.next ≤ Native.maxInstructions * Native.maxVectorLength := by
          have bound := afterYesBudget
          rw [StateT.run_bind, third.run] at bound
          exact bound
        have firstNext : state.next ≤ first.finalState.next := by
          simpa only [first.run] using (conditionFrame state).next
        have secondNext : first.finalState.next ≤ second.finalState.next := by
          simpa only [second.run] using (yesFrame first.finalState).next
        have thirdNext : second.finalState.next ≤ third.finalState.next := by
          simpa only [third.run] using (noFrame second.finalState).next
        have conditionMeaning := OperandMeaning.of_frame hash inputs first.finalWitness
          second.finalWitness first.finalState.next first.text first.normalized.term
          first.operandMeaning first.textScope second.frame
        have conditionScope := first.textScope.mono secondNext
        have conditionMeaning := OperandMeaning.of_frame hash inputs second.finalWitness
          third.finalWitness second.finalState.next first.text first.normalized.term
          conditionMeaning conditionScope third.frame
        have yesMeaning := OperandMeaning.of_frame hash inputs second.finalWitness
          third.finalWitness second.finalState.next second.text second.normalized.term
          second.operandMeaning second.textScope third.frame
        have boolean : interpret hash inputs first.normalized.term = some zero ∨
            interpret hash inputs first.normalized.term = some one := by
          cases conditionValue
          · exact Or.inl (by simpa [sourceScalar?, sourceNumber?, number, scalar_zero] using first.represents.2.2)
          · exact Or.inr (by simpa [sourceScalar?, sourceNumber?, number, scalar_one] using first.represents.2.2)
        obtain ⟨native⟩ := selectSuffix_step hash inputs third.finalWitness third.finalState
          first.text second.text third.text first.normalized.term second.normalized.term
          third.normalized.term third.stateMeaning conditionMeaning yesMeaning third.operandMeaning
          (conditionScope.mono thirdNext) (second.textScope.mono thirdNext) third.textScope
          boolean nativeBudget
        obtain ⟨normalized, normalization, represents⟩ := normalize_success ctx hash
          implementation inputs normalAliases values aliasAgreement (.select condition yes no)
          (ScalarExpression.select condition yes no sourceType conditionSupported yesSupported noSupported)
          result success
        have termEq : normalized.term = Backend.Native.selectTerm first.normalized.term
            second.normalized.term third.normalized.term := by
          have actual := normalization
          simp only [Backend.Native.normalize, first.normalization, second.normalization,
            third.normalization] at actual
          cases actual
          rfl
        have conditionInterprets : ∃ value,
            ScalarTermMeaning.interpret? hash inputs first.normalized.term = .some value := by
          obtain ⟨operand, parsed, meaning⟩ := first.operandMeaning
          exact ⟨operand.read first.finalWitness, meaning⟩
        have outputMeaning : OperandMeaning hash inputs native.finalWitness native.text
            normalized.term := by
          rcases native.operandMeaning with ⟨operand, parsed, meaning⟩
          refine ⟨operand, parsed, ?_⟩
          change ScalarTermMeaning.interpret? hash inputs normalized.term =
            some (Operand.read native.finalWitness operand)
          rw [termEq, ScalarTermMeaning.interpret_selectTerm hash inputs
            first.normalized.term second.normalized.term third.normalized.term conditionInterprets]
          exact meaning
        have rootFrame : ∀ name, InScope state.next name →
            native.finalWitness name = witness name := by
          intro name inScope
          have firstScope : InScope first.finalState.next name := InScope.mono firstNext inScope
          have secondScope : InScope second.finalState.next name := InScope.mono secondNext firstScope
          have thirdScope : InScope third.finalState.next name := InScope.mono thirdNext secondScope
          exact (native.frame name thirdScope).trans
            ((third.frame name secondScope).trans
              ((second.frame name firstScope).trans (first.frame name inScope)))
        have aliasesPreserved : native.finalState.aliases = state.aliases := by
          rw [native.aliasesPreserved, third.aliasesPreserved,
            second.aliasesPreserved, first.aliasesPreserved]
        have finalLowerAliasAgreement : LowerAliasAgreement hash inputs native.finalWitness
            normalAliases native.finalState.aliases values := by
          rw [aliasesPreserved]
          exact LowerAliasAgreement.of_frame hash inputs witness native.finalWitness state.next
            normalAliases state.aliases values lowerAliasAgreement lowerStateMeaning.aliases rootFrame
        refine ⟨{
          text := native.text
          finalState := native.finalState
          finalWitness := native.finalWitness
          normalized := normalized
          run := ?_
          normalization := normalization
          represents := represents
          operandMeaning := outputMeaning
          textScope := native.textScope
          stateMeaning := native.stateMeaning
          budget := native.budget
          aliasAgreement := finalLowerAliasAgreement
          aliasesPreserved := aliasesPreserved
          frame := rootFrame
        }⟩
        · rw [lowerSelect_eq]
          rw [runBind, first.run]
          rw [runBind, second.run]
          rw [runBind, third.run]
          exact native.run

end Noctium.Verification.ScalarWitnessConstruction
