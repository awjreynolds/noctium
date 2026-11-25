import Noctium.Verification.ScalarLowering
import Noctium.Verification.ScalarStateExtensions
import Noctium.Verification.ScalarCache
import Noctium.Verification.ScalarRangeLowering
import Noctium.Verification.ScalarInstructionEncoding
import Noctium.Verification.ScalarAllocation
import Noctium.Verification.ScalarExpressionArithmetic

namespace Noctium.Verification.ScalarExpressionControl

open Lean Backend NativeRelation NativeRelationJson ScalarNormalization
open ScalarLowering ScalarWitness ScalarInstructionEncoding
open ScalarAllocation

abbrev Assignment := NativeRelation.Assignment

private theorem eq_left_budget (left right : Expr ty) (state : Zkir.LowerState)
    (limit : Nat)
    (budget : ((Zkir.lowerExpr (.eq left right)).run state).2.next ≤ limit) :
    ((Zkir.lowerExpr left).run state).2.next ≤ limit := by
  have restPreserves : ∀ text, PreservesFrame
      (do
        let rightText ← Zkir.lowerExpr right
        Zkir.binary "test_eq" text rightText) := by
    intro text
    apply bind_preserves _ _ (lowerExpr_preserves right)
    intro rightText
    exact binary_preserves "test_eq" text rightText ⟨by decide, by decide, by decide⟩
  apply bind_middle_budget (Zkir.lowerExpr left)
    (fun text => do
      let rightText ← Zkir.lowerExpr right
      Zkir.binary "test_eq" text rightText) state restPreserves limit
  simpa only [Zkir.lowerExpr] using budget

private theorem except_unit_bind (first : Except ε Unit) (next : Except ε Unit) :
    Except.bind first (fun _ => next) = .ok () ↔ first = .ok () ∧ next = .ok () := by
  cases first <;> cases next <;> simp [Except.bind]

private theorem bind_suffix_bound {α β : Type} (first : StateM Zkir.LowerState α)
    (next : α → StateM Zkir.LowerState β) (state : Zkir.LowerState)
    (firstValue : α) (middle : Zkir.LowerState) (limit : Nat)
    (firstRun : first.run state = (firstValue, middle))
    (bound : ((first >>= next).run state).2.next ≤ limit) :
    ((next firstValue).run middle).2.next ≤ limit := by
  rw [StateT.run_bind, firstRun] at bound
  change ((next firstValue).run middle).2.next ≤ limit at bound
  exact bound

/-- Disclosure preserves the source evaluation and the actual lowerer run. -/
theorem exprComplete_disclose (span : SourceSpan) (expression : Expr ty)
    (complete : ExprComplete expression) :
    ExprComplete (.disclose span expression) := by
  intro ctx hash implementation inputs witness state normalAliases values types value
    valid success aliasAgreement lowerAliasAgreement lowerStateMeaning budget
  have childValid : expression.validate {poseidon2 := true} types = .ok () := by
    simpa only [Expr.validate] using valid
  have childSuccess : expression.eval ctx values = .ok value := by
    simpa only [Expr.eval] using success
  rcases complete ctx hash implementation inputs witness state normalAliases values types value
      childValid childSuccess aliasAgreement lowerAliasAgreement lowerStateMeaning
      (by simpa only [Zkir.lowerExpr] using budget) with ⟨result⟩
  refine ⟨?_⟩
  refine {
    text := result.text
    finalState := result.finalState
    finalWitness := result.finalWitness
    normalized := result.normalized
    run := ?_
    normalization := ?_
    represents := result.represents
    operandMeaning := result.operandMeaning
    textScope := result.textScope
    stateMeaning := result.stateMeaning
    budget := result.budget
    aliasAgreement := result.aliasAgreement
    aliasesPreserved := result.aliasesPreserved
    frame := result.frame }
  · simpa only [Zkir.lowerExpr] using result.run
  · simpa only [Backend.Native.normalize] using result.normalization

theorem exprComplete_letE (name : String) (expression : Expr source) (body : Expr ty)
    (valueComplete : ExprComplete expression) (bodyComplete : ExprComplete body) :
    ExprComplete (.letE name expression body) := by
  intro ctx hash implementation inputs witness state normalAliases values types result
    valid success aliasAgreement lowerAliasAgreement lowerStateMeaning budget
  have validation := valid
  change (do
    expression.validate {poseidon2 := true} types
    body.validate {poseidon2 := true} ((name, source) :: types)) = .ok () at validation
  simp only [ScalarValidation.bind_ok] at validation
  obtain ⟨value, expressionValid, bodyValid⟩ := validation
  cases value
  have rootSuccess := success
  cases expressionEval : expression.eval ctx values with
  | error message => simp [Expr.eval, expressionEval, Bind.bind, Except.bind] at success
  | ok sourceValue =>
    have bodySuccess : body.eval ctx ((name, Value.pack source sourceValue) :: values) = .ok result := by
      simpa only [Expr.eval, expressionEval, Bind.bind, Except.bind] using success
    have suffixPreserves (text : String) : PreservesFrame (do
      let snapshot ← (get : StateM Zkir.LowerState Zkir.LowerState)
      modify fun (current : Zkir.LowerState) => {current with aliases := (name, text) :: snapshot.aliases}
      let bodyText ← Zkir.lowerExpr body
      modify fun (current : Zkir.LowerState) => {current with aliases := snapshot.aliases}
      pure bodyText) := by
      apply bind_preserves _ _ get_preserves
      intro snapshot
      apply bind_preserves _ _ (aliases_preserves ((name, text) :: snapshot.aliases))
      intro ignored
      apply bind_preserves _ _ (lowerExpr_preserves body)
      intro bodyText
      apply bind_preserves _ _ (aliases_preserves snapshot.aliases)
      intro ignored
      exact pure_preserves _
    have expressionBudget := bind_middle_budget (Zkir.lowerExpr expression)
      (fun text => do
        let snapshot ← (get : StateM Zkir.LowerState Zkir.LowerState)
        modify fun (current : Zkir.LowerState) => {current with aliases := (name, text) :: snapshot.aliases}
        let bodyText ← Zkir.lowerExpr body
        modify fun (current : Zkir.LowerState) => {current with aliases := snapshot.aliases}
        pure bodyText) state suffixPreserves (Native.maxInstructions * Native.maxVectorLength) (by
          change ((do
            let text ← Zkir.lowerExpr expression
            let snapshot ← (get : StateM Zkir.LowerState Zkir.LowerState)
            modify fun (current : Zkir.LowerState) => {current with aliases := (name, text) :: snapshot.aliases}
            let bodyText ← Zkir.lowerExpr body
            modify fun (current : Zkir.LowerState) => {current with aliases := snapshot.aliases}
            pure bodyText).run state).2.next ≤ Native.maxInstructions * Native.maxVectorLength at budget
          exact budget)
    obtain ⟨first⟩ := valueComplete ctx hash implementation inputs witness state normalAliases values types
      sourceValue expressionValid expressionEval aliasAgreement lowerAliasAgreement lowerStateMeaning
      expressionBudget
    have afterExpressionBound : ((do
      let snapshot ← (get : StateM Zkir.LowerState Zkir.LowerState)
      modify fun (current : Zkir.LowerState) => {current with aliases := (name, first.text) :: snapshot.aliases}
      let bodyText ← Zkir.lowerExpr body
      modify fun (current : Zkir.LowerState) => {current with aliases := snapshot.aliases}
      pure bodyText).run first.finalState).2.next ≤ Native.maxInstructions * Native.maxVectorLength := by
      have bound := budget
      change ((do
        let text ← Zkir.lowerExpr expression
        let snapshot ← (get : StateM Zkir.LowerState Zkir.LowerState)
        modify fun (current : Zkir.LowerState) => {current with aliases := (name, text) :: snapshot.aliases}
        let bodyText ← Zkir.lowerExpr body
        modify fun (current : Zkir.LowerState) => {current with aliases := snapshot.aliases}
        pure bodyText).run state).2.next ≤ Native.maxInstructions * Native.maxVectorLength at bound
      rw [StateT.run_bind, first.run] at bound
      exact bound
    let bodyState : Zkir.LowerState :=
      {first.finalState with aliases := (name, first.text) :: first.finalState.aliases}
    have afterSnapshotBound : ((do
      modify fun (current : Zkir.LowerState) => {current with aliases := (name, first.text) :: first.finalState.aliases}
      let bodyText ← Zkir.lowerExpr body
      modify fun (current : Zkir.LowerState) => {current with aliases := first.finalState.aliases}
      pure bodyText).run first.finalState).2.next ≤ Native.maxInstructions * Native.maxVectorLength := by
      exact bind_suffix_bound get
        (fun snapshot => do
          modify fun (current : Zkir.LowerState) => {current with aliases := (name, first.text) :: snapshot.aliases}
          let bodyText ← Zkir.lowerExpr body
          modify fun (current : Zkir.LowerState) => {current with aliases := snapshot.aliases}
          pure bodyText)
        first.finalState first.finalState first.finalState (Native.maxInstructions * Native.maxVectorLength)
        (by rfl) afterExpressionBound
    have afterAliasBound : ((do
      let bodyText ← Zkir.lowerExpr body
      modify fun (current : Zkir.LowerState) => {current with aliases := first.finalState.aliases}
      pure bodyText).run bodyState).2.next ≤ Native.maxInstructions * Native.maxVectorLength := by
      exact bind_suffix_bound (modify fun (current : Zkir.LowerState) =>
          {current with aliases := (name, first.text) :: first.finalState.aliases})
        (fun _ => do
          let bodyText ← Zkir.lowerExpr body
          modify fun (current : Zkir.LowerState) => {current with aliases := first.finalState.aliases}
          pure bodyText)
        first.finalState () bodyState (Native.maxInstructions * Native.maxVectorLength) (by rfl) afterSnapshotBound
    have bodyTailPreserves : ∀ (text : String), PreservesFrame
        (do
          modify fun (current : Zkir.LowerState) => {current with aliases := first.finalState.aliases}
          pure text) := by
      intro text
      apply bind_preserves _ _ (aliases_preserves first.finalState.aliases)
      intro ignored
      exact pure_preserves _
    have bodyBudget := bind_middle_budget (Zkir.lowerExpr body)
      (fun bodyText => do
        modify fun (current : Zkir.LowerState) => {current with aliases := first.finalState.aliases}
        pure bodyText)
      bodyState bodyTailPreserves (Native.maxInstructions * Native.maxVectorLength) afterAliasBound
    have normalAgreementBody : AliasAgreement hash inputs
        ((name, first.normalized.term) :: normalAliases)
        ((name, Value.pack source sourceValue) :: values) :=
      ScalarNormalization.aliasAgreement_cons hash inputs normalAliases values name source sourceValue first.normalized.term
        aliasAgreement first.represents.1 first.represents.2.2
    have lowerAgreementAfterFirst : LowerAliasAgreement hash inputs first.finalWitness
        normalAliases state.aliases values :=
      LowerAliasAgreement.of_frame hash inputs witness first.finalWitness state.next normalAliases
        state.aliases values lowerAliasAgreement lowerStateMeaning.aliases first.frame
    have lowerAgreementBody : LowerAliasAgreement hash inputs first.finalWitness
        ((name, first.normalized.term) :: normalAliases) bodyState.aliases
        ((name, Value.pack source sourceValue) :: values) := by
      change LowerAliasAgreement hash inputs first.finalWitness
        ((name, first.normalized.term) :: normalAliases)
        ((name, first.text) :: first.finalState.aliases)
        ((name, Value.pack source sourceValue) :: values)
      rw [first.aliasesPreserved]
      exact LowerAliasAgreement.cons hash inputs first.finalWitness normalAliases state.aliases values
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
      result bodyValid bodySuccess normalAgreementBody
      lowerAgreementBody bodyStateMeaning bodyBudget
    have firstNext : state.next ≤ first.finalState.next := by
      have bound := lowerExpr_next expression state
      rw [first.run] at bound
      exact bound
    have bodyNext : bodyState.next ≤ second.finalState.next := by
      have bound := lowerExpr_next body bodyState
      rw [second.run] at bound
      exact bound
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
    have represents : Represents hash inputs ty normalized result := by
      obtain ⟨actual, actualNorm, actualRepresents⟩ := ScalarNormalization.normalize_success
        ctx hash implementation inputs normalAliases values aliasAgreement
        (.letE name expression body) result rootSuccess
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
    · change ((do
        let text ← Zkir.lowerExpr expression
        let snapshot ← (get : StateM Zkir.LowerState Zkir.LowerState)
        modify fun (current : Zkir.LowerState) => {current with aliases := (name, text) :: snapshot.aliases}
        let bodyText ← Zkir.lowerExpr body
        modify fun (current : Zkir.LowerState) => {current with aliases := snapshot.aliases}
        pure bodyText).run state) = _
      rw [StateT.run_bind, first.run]
      change ((do
        let snapshot ← (get : StateM Zkir.LowerState Zkir.LowerState)
        modify fun (current : Zkir.LowerState) => {current with aliases := (name, first.text) :: snapshot.aliases}
        let bodyText ← Zkir.lowerExpr body
        modify fun (current : Zkir.LowerState) => {current with aliases := snapshot.aliases}
        pure bodyText).run first.finalState) = _
      rw [StateT.run_bind, StateT.run_get]
      change ((do
        modify fun (current : Zkir.LowerState) => {current with aliases := (name, first.text) :: first.finalState.aliases}
        let bodyText ← Zkir.lowerExpr body
        modify fun (current : Zkir.LowerState) => {current with aliases := first.finalState.aliases}
        pure bodyText).run first.finalState) = _
      rw [StateT.run_bind, StateT.run_modify]
      change ((do
        let bodyText ← Zkir.lowerExpr body
        modify fun (current : Zkir.LowerState) => {current with aliases := first.finalState.aliases}
        pure bodyText).run bodyState) = _
      rw [StateT.run_bind, second.run]
      simp [StateT.run_map, StateT.run_modify, StateT.run_pure, finalState, first.aliasesPreserved]
      rfl

theorem exprComplete_eq (left right : Expr ty)
    (leftComplete : ExprComplete left) (rightComplete : ExprComplete right) :
    ExprComplete (.eq left right) := by
  intro ctx hash implementation inputs witness state normalAliases values types value
    valid success aliasAgreement lowerAliasAgreement lowerStateMeaning budget
  have validParts : left.validate {poseidon2 := true} types = .ok () ∧
      right.validate {poseidon2 := true} types = .ok () := by
    change Except.bind (left.validate {poseidon2 := true} types)
      (fun _ => right.validate {poseidon2 := true} types) = .ok () at valid
    exact (except_unit_bind _ _).mp valid
  have rootSuccess := success
  cases leftEval : left.eval ctx values with
  | error message => simp [Expr.eval, leftEval, Bind.bind, Except.bind] at success
  | ok leftValue =>
    cases rightEval : right.eval ctx values with
    | error message => simp [Expr.eval, leftEval, rightEval, Bind.bind, Except.bind] at success
    | ok rightValue =>
      have firstBudget : ((Zkir.lowerExpr left).run state).2.next ≤ Native.maxInstructions * Native.maxVectorLength :=
        eq_left_budget left right state (Native.maxInstructions * Native.maxVectorLength) budget
      rcases leftComplete ctx hash implementation inputs witness state normalAliases values types
          leftValue validParts.1 leftEval aliasAgreement lowerAliasAgreement lowerStateMeaning
          firstBudget with ⟨leftResult⟩
      let rightStart := leftResult.finalState
      have lowerAgreementLeft : LowerAliasAgreement hash inputs leftResult.finalWitness
          normalAliases rightStart.aliases values := by
        rw [leftResult.aliasesPreserved]
        exact LowerAliasAgreement.of_frame hash inputs witness leftResult.finalWitness state.next
          normalAliases state.aliases values lowerAliasAgreement lowerStateMeaning.aliases leftResult.frame
      have afterLeftBudget :
          (StateT.run (Zkir.lowerExpr right >>= fun rightText =>
            Zkir.binary "test_eq" leftResult.text rightText) rightStart).2.next ≤ Native.maxInstructions * Native.maxVectorLength := by
        have sequenceBound :
            ((Zkir.lowerExpr left >>= fun leftText => do
              let rightText ← Zkir.lowerExpr right
              Zkir.binary "test_eq" leftText rightText).run state).2.next ≤ Native.maxInstructions * Native.maxVectorLength := by
          simpa only [Zkir.lowerExpr] using budget
        exact bind_suffix_bound (Zkir.lowerExpr left)
          (fun leftText => do
            let rightText ← Zkir.lowerExpr right
            Zkir.binary "test_eq" leftText rightText)
          state leftResult.text leftResult.finalState (Native.maxInstructions * Native.maxVectorLength) leftResult.run sequenceBound
      have rightFrame : ∀ rightText, PreservesFrame (Zkir.binary "test_eq" leftResult.text rightText) := by
        intro rightText
        exact binary_preserves "test_eq" leftResult.text rightText ⟨by decide, by decide, by decide⟩
      have rightBudget : ((Zkir.lowerExpr right).run rightStart).2.next ≤ Native.maxInstructions * Native.maxVectorLength :=
        bind_middle_budget (Zkir.lowerExpr right)
          (fun rightText => Zkir.binary "test_eq" leftResult.text rightText)
          rightStart rightFrame (Native.maxInstructions * Native.maxVectorLength) afterLeftBudget
      rcases rightComplete ctx hash implementation inputs leftResult.finalWitness rightStart
          normalAliases values types rightValue validParts.2 rightEval aliasAgreement lowerAgreementLeft
          leftResult.stateMeaning rightBudget with ⟨rightResult⟩
      have rightMono : rightStart.next ≤ rightResult.finalState.next := by
        have mono := lowerExpr_next right rightStart
        rw [rightResult.run] at mono
        exact mono
      have lowerAgreementRight : LowerAliasAgreement hash inputs rightResult.finalWitness
          normalAliases rightResult.finalState.aliases values := by
        rw [rightResult.aliasesPreserved]
        exact LowerAliasAgreement.of_frame hash inputs leftResult.finalWitness rightResult.finalWitness
          rightStart.next normalAliases rightStart.aliases values lowerAgreementLeft
          leftResult.stateMeaning.aliases rightResult.frame
      have opBudget :
          ((Zkir.binary "test_eq" leftResult.text rightResult.text).run rightResult.finalState).2.next ≤
            (Native.maxInstructions * Native.maxVectorLength) := by
        have sequenceBound :
            ((Zkir.lowerExpr left >>= fun leftText => do
              let rightText ← Zkir.lowerExpr right
              Zkir.binary "test_eq" leftText rightText).run state).2.next ≤ Native.maxInstructions * Native.maxVectorLength := by
          simpa only [Zkir.lowerExpr] using budget
        have afterLeft := bind_suffix_bound (Zkir.lowerExpr left)
          (fun leftText => do
            let rightText ← Zkir.lowerExpr right
            Zkir.binary "test_eq" leftText rightText)
          state leftResult.text leftResult.finalState (Native.maxInstructions * Native.maxVectorLength) leftResult.run sequenceBound
        exact bind_suffix_bound (Zkir.lowerExpr right)
          (fun rightText => Zkir.binary "test_eq" leftResult.text rightText)
          rightStart rightResult.text rightResult.finalState (Native.maxInstructions * Native.maxVectorLength) rightResult.run
          (by simpa only [StateT.run_bind, Id.instMonad] using afterLeft)
      have leftScope : TextScope rightResult.finalState.next leftResult.text :=
        TextScope.mono (by simpa only [leftResult.run] using rightMono) leftResult.textScope
      have leftMeaningRight : OperandMeaning hash inputs rightResult.finalWitness
          leftResult.text leftResult.normalized.term :=
        OperandMeaning.of_frame hash inputs leftResult.finalWitness rightResult.finalWitness
          rightStart.next leftResult.text leftResult.normalized.term leftResult.operandMeaning
          leftResult.textScope rightResult.frame
      rcases ScalarExpressionArithmetic.binary_testEq_step hash inputs rightResult.finalWitness
          rightResult.finalState leftResult.text rightResult.text leftResult.normalized.term
          rightResult.normalized.term rightResult.stateMeaning leftMeaningRight
          rightResult.operandMeaning leftScope rightResult.textScope opBudget with ⟨step⟩
      let normalized : Backend.Native.Normalized := {
        term := .binary "test_eq" leftResult.normalized.term rightResult.normalized.term
        bounds := leftResult.normalized.bounds ++ rightResult.normalized.bounds ++
          [(.binary "test_eq" leftResult.normalized.term rightResult.normalized.term, 1)]
        assertions := leftResult.normalized.assertions ++ rightResult.normalized.assertions }
      have normalization : Backend.Native.normalize normalAliases (.eq left right) = .ok normalized := by
        simp only [Backend.Native.normalize, leftResult.normalization, rightResult.normalization,
          Bind.bind, Except.bind, Functor.map, Except.map, Backend.Native.arithmetic_eq,
          Backend.Native.requireSourceType_eq, Except.pure]
        rfl
      have represents : Represents hash inputs .bool normalized value := by
        obtain ⟨actual, actualNorm, actualRepresents⟩ := ScalarNormalization.normalize_success
          ctx hash implementation inputs normalAliases values aliasAgreement (.eq left right) value rootSuccess
        rw [normalization] at actualNorm
        cases actualNorm
        exact actualRepresents
      have rootFrame : ∀ name, InScope state.next name → step.finalWitness name = witness name := by
        intro name inScope
        have leftAt : InScope leftResult.finalState.next name :=
          InScope.mono (by
            have mono := lowerExpr_next left state
            rw [leftResult.run] at mono
            exact mono) inScope
        have rightAt : InScope rightResult.finalState.next name :=
          InScope.mono (by simpa only [leftResult.run] using rightMono) leftAt
        have stepFrame := step.frame name rightAt
        have rightFrame := rightResult.frame name leftAt
        have leftFrame := leftResult.frame name inScope
        exact stepFrame.trans (rightFrame.trans leftFrame)
      have aliasesPreserved : step.finalState.aliases = state.aliases := by
        rw [step.aliasesPreserved, rightResult.aliasesPreserved, leftResult.aliasesPreserved]
      have aliasAgreementFinal : LowerAliasAgreement hash inputs step.finalWitness
          normalAliases step.finalState.aliases values := by
        rw [aliasesPreserved]
        exact LowerAliasAgreement.of_frame hash inputs witness step.finalWitness state.next normalAliases
          state.aliases values lowerAliasAgreement lowerStateMeaning.aliases rootFrame
      refine ⟨{
        text := step.text
        finalState := step.finalState
        finalWitness := step.finalWitness
        normalized := normalized
        run := ?_
        normalization := normalization
        represents := represents
        operandMeaning := by simpa [normalized] using step.operandMeaning
        textScope := step.textScope
        stateMeaning := step.stateMeaning
        budget := step.budget
        aliasAgreement := aliasAgreementFinal
        aliasesPreserved := aliasesPreserved
        frame := rootFrame }⟩
      · change ((Zkir.lowerExpr left >>= fun leftText => do
          let rightText ← Zkir.lowerExpr right
          Zkir.binary "test_eq" leftText rightText).run state) = (step.text, step.finalState)
        rw [StateT.run_bind, leftResult.run]
        change (do
          let rightText ← Zkir.lowerExpr right
          Zkir.binary "test_eq" leftResult.text rightText).run rightStart = (step.text, step.finalState)
        rw [StateT.run_bind, rightResult.run]
        exact step.run

end Noctium.Verification.ScalarExpressionControl
