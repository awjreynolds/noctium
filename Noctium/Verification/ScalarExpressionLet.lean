import Noctium.Verification.ScalarLowering
import Noctium.Verification.ScalarStateExtensions
import Noctium.Verification.ScalarAllocationOutputFrame

namespace Noctium.Verification.ScalarExpressionLet

open Lean Backend NativeRelation NativeRelationJson ScalarNormalization ScalarLowering

private def outputCapacity : Nat := Native.maxInstructions * Native.maxVectorLength

private theorem bind_first_budget {α β : Type}
    (first : StateM Zkir.LowerState α) (next : α → StateM Zkir.LowerState β)
    (state : Zkir.LowerState) (limit : Nat)
    (nextFrame : ∀ value, Zkir.PreservesOutputCapacityFrame (next value))
    (budget : ((first >>= next).run state).2.next ≤ limit) :
    (first.run state).2.next ≤ limit := by
  rw [StateT.run_bind] at budget
  exact Nat.le_trans (nextFrame _ _).next budget

private theorem bind_suffix_budget {α β : Type}
    (first : StateM Zkir.LowerState α) (next : α → StateM Zkir.LowerState β)
    (state : Zkir.LowerState) (firstValue : α) (middle : Zkir.LowerState)
    (limit : Nat) (firstRun : first.run state = (firstValue, middle))
    (budget : ((first >>= next).run state).2.next ≤ limit) :
    ((next firstValue).run middle).2.next ≤ limit := by
  rw [StateT.run_bind, firstRun] at budget
  exact budget

private theorem runBind {α β : Type} (first : StateM Zkir.LowerState α)
    (next : α → StateM Zkir.LowerState β) (state : Zkir.LowerState) :
    (do let value ← first; next value).run state =
      (next (first.run state).1).run (first.run state).2 := rfl

private theorem stateGetFrame : Zkir.PreservesOutputCapacityFrame
    (get : StateM Zkir.LowerState Zkir.LowerState) := by
  intro state
  exact Zkir.OutputCapacityFrame.refl state

private theorem modifyAliasesFrame (aliases : List (String × String)) :
    Zkir.PreservesOutputCapacityFrame
      (modify fun state : Zkir.LowerState => {state with aliases := aliases}) := by
  exact Zkir.modify_preservesOutputCapacityFrame
    (fun state => {state with aliases := aliases})
    (by intro state; rfl) (by intro state; rfl)

/-- A scalar let lowers its value, binds the emitted operand under the source
name for its body, then restores the prior alias scope. The proof tracks the
source value, normalizer alias, lowerer alias, witness assignment, and emitted
state through that exact lowering sequence. -/
theorem exprComplete_letE {source target : Ty} (name : String)
    (expression : Expr source) (body : Expr target)
    (sourceScalar : ScalarType source)
    (expressionSupported : ScalarExpression expression)
    (bodySupported : ScalarExpression body)
    (valueComplete : ExprComplete expression) (bodyComplete : ExprComplete body) :
    ExprComplete (.letE name expression body) := by
  intro ctx hash implementation inputs witness state normalAliases values types result
    valid success aliasAgreement lowerAliasAgreement lowerStateMeaning budget
  have validation : (do
      expression.validate Capabilities.crypto types
      body.validate Capabilities.crypto ((name, source) :: types)) = .ok () := by
    simpa only [Expr.validate] using valid
  rcases ScalarValidationMeaning.bind_ok.mp validation with
    ⟨_, expressionValid, bodyValid⟩
  have rootSuccess := success
  cases expressionEval : expression.eval ctx values with
  | error message => simp [Expr.eval, expressionEval, Bind.bind, Except.bind] at success
  | ok sourceValue =>
    have bodySuccess : body.eval ctx ((name, Value.pack source sourceValue) :: values) = .ok result := by
      simpa only [Expr.eval, expressionEval, Bind.bind, Except.bind] using success
    let suffix (text : String) : StateM Zkir.LowerState String := do
      let snapshot ← (get : StateM Zkir.LowerState Zkir.LowerState)
      modify fun (current : Zkir.LowerState) =>
        {current with aliases := (name, text) :: snapshot.aliases}
      let bodyText ← Zkir.lowerExpr body
      modify fun (current : Zkir.LowerState) => {current with aliases := snapshot.aliases}
      pure bodyText
    have suffixFrame : ∀ text, Zkir.PreservesOutputCapacityFrame (suffix text) := by
      intro text
      dsimp only [suffix]
      apply Zkir.bind_preservesOutputCapacityFrame _ _ stateGetFrame
      intro snapshot
      apply Zkir.bind_preservesOutputCapacityFrame _ _ (modifyAliasesFrame ((name, text) :: snapshot.aliases))
      intro ignored
      apply Zkir.bind_preservesOutputCapacityFrame _ _
        (ScalarAllocationOutputFrame.lowerExpr_admitted_preservesOutputCapacityFrame body bodySupported)
      intro bodyText
      apply Zkir.bind_preservesOutputCapacityFrame _ _ (modifyAliasesFrame snapshot.aliases)
      intro ignored
      exact Zkir.pure_preservesOutputCapacityFrame bodyText
    have lowerLet : Zkir.lowerExpr (.letE name expression body) =
        Zkir.lowerExpr expression >>= suffix := by
      cases sourceScalar <;> simp [Zkir.lowerExpr, suffix]
    have wholeBudget : ((Zkir.lowerExpr expression >>= suffix).run state).2.next ≤ outputCapacity := by
      simpa only [lowerLet, outputCapacity] using budget
    have expressionBudget : (Zkir.lowerExpr expression).run state |>.2.next ≤ outputCapacity :=
      bind_first_budget (Zkir.lowerExpr expression) suffix state outputCapacity suffixFrame wholeBudget
    obtain ⟨first⟩ := valueComplete ctx hash implementation inputs witness state normalAliases values types
      sourceValue expressionValid expressionEval aliasAgreement lowerAliasAgreement lowerStateMeaning
      expressionBudget
    have afterExpressionBound : (suffix first.text).run first.finalState |>.2.next ≤ outputCapacity :=
      bind_suffix_budget (Zkir.lowerExpr expression) suffix state first.text first.finalState
        outputCapacity first.run wholeBudget
    let bodyState : Zkir.LowerState :=
      {first.finalState with aliases := (name, first.text) :: first.finalState.aliases}
    have afterSnapshotBound : ((do
        modify fun (current : Zkir.LowerState) =>
          {current with aliases := (name, first.text) :: first.finalState.aliases}
        let bodyText ← Zkir.lowerExpr body
        modify fun (current : Zkir.LowerState) => {current with aliases := first.finalState.aliases}
        pure bodyText).run first.finalState).2.next ≤ outputCapacity := by
      exact bind_suffix_budget (get : StateM Zkir.LowerState Zkir.LowerState)
        (fun snapshot => do
          modify fun (current : Zkir.LowerState) =>
            {current with aliases := (name, first.text) :: snapshot.aliases}
          let bodyText ← Zkir.lowerExpr body
          modify fun (current : Zkir.LowerState) => {current with aliases := snapshot.aliases}
          pure bodyText)
        first.finalState first.finalState first.finalState outputCapacity rfl afterExpressionBound
    have afterAliasBound : ((do
        let bodyText ← Zkir.lowerExpr body
        modify fun (current : Zkir.LowerState) => {current with aliases := first.finalState.aliases}
        pure bodyText).run bodyState).2.next ≤ outputCapacity := by
      exact bind_suffix_budget
        (modify fun (current : Zkir.LowerState) =>
          {current with aliases := (name, first.text) :: first.finalState.aliases})
        (fun _ => do
          let bodyText ← Zkir.lowerExpr body
          modify fun (current : Zkir.LowerState) => {current with aliases := first.finalState.aliases}
          pure bodyText)
        first.finalState () bodyState outputCapacity rfl afterSnapshotBound
    let bodyTail (text : String) : StateM Zkir.LowerState String := do
      modify fun (current : Zkir.LowerState) => {current with aliases := first.finalState.aliases}
      pure text
    have bodyTailFrame : ∀ text, Zkir.PreservesOutputCapacityFrame (bodyTail text) := by
      intro text
      dsimp only [bodyTail]
      apply Zkir.bind_preservesOutputCapacityFrame _ _ (modifyAliasesFrame first.finalState.aliases)
      intro ignored
      exact Zkir.pure_preservesOutputCapacityFrame text
    have bodyBudget : (Zkir.lowerExpr body).run bodyState |>.2.next ≤ outputCapacity :=
      bind_first_budget (Zkir.lowerExpr body) bodyTail bodyState outputCapacity bodyTailFrame afterAliasBound
    have normalAgreementBody : AliasAgreement hash inputs
        ((name, first.normalized.term) :: normalAliases)
        ((name, Value.pack source sourceValue) :: values) :=
      ScalarNormalization.aliasAgreement_cons hash inputs normalAliases values name source sourceValue
        first.normalized.term aliasAgreement first.represents.1 first.represents.2.2
    have lowerAgreementAfterFirst : LowerAliasAgreement hash inputs first.finalWitness
        normalAliases first.finalState.aliases values := by
      rw [first.aliasesPreserved]
      exact LowerAliasAgreement.of_frame hash inputs witness first.finalWitness state.next normalAliases
        state.aliases values lowerAliasAgreement lowerStateMeaning.aliases first.frame
    have lowerAgreementBody : LowerAliasAgreement hash inputs first.finalWitness
        ((name, first.normalized.term) :: normalAliases) bodyState.aliases
        ((name, Value.pack source sourceValue) :: values) := by
      change LowerAliasAgreement hash inputs first.finalWitness
        ((name, first.normalized.term) :: normalAliases)
        ((name, first.text) :: first.finalState.aliases)
        ((name, Value.pack source sourceValue) :: values)
      exact LowerAliasAgreement.cons hash inputs first.finalWitness normalAliases first.finalState.aliases values
        name source sourceValue first.normalized.term first.text lowerAgreementAfterFirst first.operandMeaning
    have aliasesScopedBody : ∀ found text,
        (found, text) ∈ bodyState.aliases → TextScope bodyState.next text := by
      intro found text member
      simp only [bodyState, List.mem_cons] at member
      rcases member with equal | old
      · cases equal
        exact first.textScope
      · exact first.stateMeaning.aliases found text old
    have bodyStateMeaning := first.stateMeaning.withAliases hash first.finalWitness first.finalState
      ((name, first.text) :: first.finalState.aliases) aliasesScopedBody
    obtain ⟨second⟩ := bodyComplete ctx hash implementation inputs first.finalWitness bodyState
      ((name, first.normalized.term) :: normalAliases)
      ((name, Value.pack source sourceValue) :: values) ((name, source) :: types)
      result bodyValid bodySuccess normalAgreementBody lowerAgreementBody bodyStateMeaning bodyBudget
    have firstNext : state.next ≤ first.finalState.next := by
      have frame := (ScalarAllocationOutputFrame.lowerExpr_admitted_preservesOutputCapacityFrame
        expression expressionSupported state).next
      simpa [first.run] using frame
    have bodyNext : bodyState.next ≤ second.finalState.next := by
      have frame := (ScalarAllocationOutputFrame.lowerExpr_admitted_preservesOutputCapacityFrame
        body bodySupported bodyState).next
      simpa [second.run, bodyState] using frame
    have aliasesScopedFinal : ∀ found text,
        (found, text) ∈ state.aliases → TextScope second.finalState.next text := by
      intro found text member
      have original : (found, text) ∈ first.finalState.aliases := by
        rw [first.aliasesPreserved]
        exact member
      exact TextScope.mono (by simpa [bodyState] using bodyNext)
        (first.stateMeaning.aliases found text original)
    let finalState : Zkir.LowerState := {second.finalState with aliases := state.aliases}
    have finalStateMeaning : LowerStateMeaning hash second.finalWitness finalState :=
      second.stateMeaning.withAliases hash second.finalWitness second.finalState state.aliases aliasesScopedFinal
    let normalized : Backend.Native.Normalized := {second.normalized with
      bounds := first.normalized.bounds ++ second.normalized.bounds
      assertions := first.normalized.assertions ++ second.normalized.assertions}
    have normalization : Backend.Native.normalize normalAliases (.letE name expression body) = .ok normalized := by
      simp only [Backend.Native.normalize, Bind.bind, Except.bind, first.normalization]
      rw [second.normalization]
      rfl
    have represents : Represents hash inputs target normalized result := by
      obtain ⟨actual, actualNorm, actualRepresents⟩ := ScalarNormalization.normalize_success
        ctx hash implementation inputs normalAliases values aliasAgreement
        (.letE name expression body)
        (ScalarExpression.letE name expression body sourceScalar expressionSupported bodySupported)
        result rootSuccess
      rw [normalization] at actualNorm
      cases actualNorm
      exact actualRepresents
    have rootFrame : ∀ found, InScope state.next found → second.finalWitness found = witness found := by
      intro found inScope
      have inFirst := InScope.mono firstNext inScope
      have inBody : InScope bodyState.next found := by simpa [bodyState] using inFirst
      rw [second.frame found inBody, first.frame found inScope]
    have rootAliasAgreement : LowerAliasAgreement hash inputs second.finalWitness normalAliases
        state.aliases values :=
      LowerAliasAgreement.of_frame hash inputs witness second.finalWitness state.next normalAliases
        state.aliases values lowerAliasAgreement lowerStateMeaning.aliases rootFrame
    refine ⟨{
      text := second.text
      finalState := finalState
      finalWitness := second.finalWitness
      normalized := normalized
      run := ?_
      normalization := normalization
      represents := represents
      operandMeaning := by simpa [normalized] using second.operandMeaning
      textScope := second.textScope
      stateMeaning := finalStateMeaning
      budget := by simpa [finalState] using second.budget
      aliasAgreement := by simpa [finalState] using rootAliasAgreement
      aliasesPreserved := rfl
      frame := rootFrame }⟩
    · rw [lowerLet]
      rw [StateT.run_bind, first.run]
      change (suffix first.text).run first.finalState = _
      dsimp only [suffix]
      rw [StateT.run_bind, StateT.run_get]
      change ((do
        modify fun (current : Zkir.LowerState) =>
          {current with aliases := (name, first.text) :: first.finalState.aliases}
        let bodyText ← Zkir.lowerExpr body
        modify fun (current : Zkir.LowerState) => {current with aliases := first.finalState.aliases}
        pure bodyText).run first.finalState) = _
      rw [StateT.run_bind, StateT.run_modify]
      change ((do
        let bodyText ← Zkir.lowerExpr body
        modify fun (current : Zkir.LowerState) => {current with aliases := first.finalState.aliases}
        pure bodyText).run bodyState) = _
      rw [StateT.run_bind, second.run]
      simp [StateT.run_map, StateT.run_modify, finalState, first.aliasesPreserved]
      rfl

end Noctium.Verification.ScalarExpressionLet
