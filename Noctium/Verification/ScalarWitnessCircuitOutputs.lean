import Noctium.Verification.ScalarWitnessAliases
import Noctium.Verification.ScalarWitnessReturnProjection
import Noctium.Verification.ScalarAllocationOutputFrame
import Noctium.Verification.ScalarNormalizationSoundness
import Lean

namespace Noctium.Verification.ScalarWitnessConstruction

open Lean Backend NativeRelation NativeRelationJson ScalarLowering ScalarNormalization

private abbrev returnFieldsStep := Zkir.lowerReturnFieldStep

private abbrev returnFieldsLoopFrom := Zkir.lowerReturnFieldsFrom

private def returnFieldsLoop (outputs : List Output) : StateM Zkir.LowerState (List String) :=
  returnFieldsLoopFrom outputs []

private theorem stateRunBind {α β} (first : StateM Zkir.LowerState α)
    (next : α → StateM Zkir.LowerState β) (state : Zkir.LowerState) :
    (do let value ← first; next value).run state =
      (next (first.run state).1).run (first.run state).2 := rfl

private theorem returnFieldsLoop_eq (outputs : List Output) :
    returnFieldsLoop outputs = Zkir.lowerReturnFields outputs := by
  rfl

private theorem output_eval_member (ctx : EvalContext) (values : EvalEnv)
    (outputs : List Output) (result : List (String × Value))
    (success : outputs.mapM (evalOutput ctx values) = .ok result)
    (output : Output) (member : output ∈ outputs) :
    ∃ value, output.value.eval ctx values = .ok value := by
  induction outputs generalizing result with
  | nil => simp at member
  | cons head tail ih =>
    cases evaluated : head.value.eval ctx values with
    | error message =>
      simp only [List.mapM_cons, evalOutput, Bind.bind, Except.bind, evaluated] at success
      cases success
    | ok value =>
      cases tailSuccess : tail.mapM (evalOutput ctx values) with
      | error message =>
        simp only [List.mapM_cons, evalOutput, Bind.bind, Except.bind,
          evaluated, tailSuccess] at success
        cases success
      | ok tailResult =>
        rcases List.mem_cons.mp member with same | member
        · subst head
          exact ⟨value, evaluated⟩
        · exact ih tailResult tailSuccess member

private theorem scalarReturnField_evaluates (ctx : EvalContext) (hash : Hash)
    (implementation : HashAgreement ctx hash) (circuit : Circuit) (values : EvalEnv)
    (inputs : NativeRelation.Assignment) (admitted : CanonicalInputs circuit values inputs)
    (scalarAdmission : ScalarCircuitAdmission circuit) (output : Output)
    (member : output ∈ circuit.outputs) (sourceValue : output.ty.Denote)
    (sourceEvaluation : output.value.eval ctx values = .ok sourceValue)
    (field : Expr .native) (projection : output.nativeReturnFields = .ok [field]) :
    ∃ value, field.eval ctx values = .ok value := by
  obtain ⟨sourceType, expressionAdmission⟩ := scalarAdmission.outputs output member
  obtain ⟨normalized, _, represents⟩ := normalize_success ctx hash implementation inputs
    (circuitAliases circuit) values
    (admitted.typedEnvironment circuit values inputs hash).aliases
    output.value expressionAdmission sourceValue sourceEvaluation
  cases output with
  | mk name ty value span =>
    cases sourceType with
    | native =>
      have fieldEq : field = value := by
        change Except.ok [value] = Except.ok [field] at projection
        exact (List.cons.inj (Except.ok.inj projection)).1.symm
      subst field
      exact ⟨sourceValue, sourceEvaluation⟩
    | bool =>
      have fieldEq : field = .cast .native value := by
        change Except.ok [.cast .native value] = Except.ok [field] at projection
        exact (List.cons.inj (Except.ok.inj projection)).1.symm
      subst field
      have range : number ScalarType.bool sourceValue < ctx.modulus := by
        cases sourceValue <;> simp [number, implementation.modulus, Field.modulus]
      rw [eval_cast_scalar ctx values value ScalarType.bool ScalarType.native sourceValue sourceEvaluation]
      simp [scalarCast, range]
    | uint maximum =>
      have fieldEq : field = .cast .native value := by
        change Except.ok [.cast .native value] = Except.ok [field] at projection
        exact (List.cons.inj (Except.ok.inj projection)).1.symm
      subst field
      have sourceCanonical : Canonical (.uint maximum) sourceValue := by
        simpa [Canonical, sourceNumber?] using represents.1
      have range : number (ScalarType.uint maximum) sourceValue < ctx.modulus := by
        simpa [number, sourceNumber?, implementation.modulus] using sourceCanonical.1
      rw [eval_cast_scalar ctx values value (.uint maximum) ScalarType.native sourceValue sourceEvaluation]
      simp [scalarCast, range]

private theorem scalarReturnField_validates (circuit : Circuit) (output : Output)
    (member : output ∈ circuit.outputs) (scalarAdmission : ScalarCircuitAdmission circuit)
    (types : TypeEnv) (sourceValidation : output.value.validate Capabilities.crypto types = .ok ())
    (field : Expr .native) (projection : output.nativeReturnFields = .ok [field]) :
    field.validate Capabilities.crypto types = .ok () := by
  obtain ⟨sourceType, _⟩ := scalarAdmission.outputs output member
  cases output with
  | mk name ty value span =>
    cases sourceType with
    | native =>
      have fieldEq : field = value := by
        change Except.ok [value] = Except.ok [field] at projection
        exact (List.cons.inj (Except.ok.inj projection)).1.symm
      subst field
      exact sourceValidation
    | bool =>
      have fieldEq : field = .cast .native value := by
        change Except.ok [.cast .native value] = Except.ok [field] at projection
        exact (List.cons.inj (Except.ok.inj projection)).1.symm
      subst field
      simpa [Expr.validate, Ty.validate, Ty.scalarKind, Ty.isBytes, Ty.isOpaqueBytes,
        Ty.isOpaqueString, Ty.isJubjub, Ty.isForeign, ScalarPolicy.validate,
        Capabilities.crypto] using sourceValidation
    | uint maximum =>
      have fieldEq : field = .cast .native value := by
        change Except.ok [.cast .native value] = Except.ok [field] at projection
        exact (List.cons.inj (Except.ok.inj projection)).1.symm
      subst field
      simpa [Expr.validate, Ty.validate, Ty.scalarKind, Ty.isBytes, Ty.isOpaqueBytes,
        Ty.isOpaqueString, Ty.isJubjub, Ty.isForeign, ScalarPolicy.validate,
        Capabilities.crypto] using sourceValidation

private theorem returnFieldsStep_frame (circuit : Circuit)
    (scalarAdmission : ScalarCircuitAdmission circuit) (output : Output)
    (member : output ∈ circuit.outputs) (accumulated : List String) :
    Zkir.PreservesOutputCapacityFrame (returnFieldsStep output accumulated) := by
  obtain ⟨scalarType, expressionAdmission⟩ := scalarAdmission.outputs output member
  obtain ⟨field, projection, fieldAdmission⟩ :=
    scalarAdmission.nativeReturnFields circuit output member
  unfold returnFieldsStep
  apply Zkir.bind_preservesOutputCapacityFrame _ _
    (ScalarAllocationOutputFrame.scalarReturnPreflight_preservesOutputCapacityFrame output scalarType)
  intro ignored
  rw [projection]
  apply Zkir.bind_preservesOutputCapacityFrame _ _
  · apply Zkir.forIn_preservesOutputCapacityFrame_of_mem
    intro returned returnedMember accumulator
    have exactField : returned = field := by
      simpa only [List.mem_singleton] using returnedMember
    subst returned
    apply Zkir.bind_preservesOutputCapacityFrame _ _
      (ScalarAllocationOutputFrame.lowerExpr_admitted_preservesOutputCapacityFrame field fieldAdmission)
    intro text
    exact Zkir.pure_preservesOutputCapacityFrame _
  · intro returned
    exact Zkir.pure_preservesOutputCapacityFrame (ForInStep.yield returned)

private theorem returnFieldsStep_eq (circuit : Circuit)
    (scalarAdmission : ScalarCircuitAdmission circuit) (output : Output)
    (member : output ∈ circuit.outputs) (accumulated : List String) :
    ∃ field, output.nativeReturnFields = .ok [field] ∧
      returnFieldsStep output accumulated = (do
        let text ← Zkir.lowerExpr field
        pure (ForInStep.yield (accumulated ++ [text]))) := by
  obtain ⟨field, projection, _⟩ := scalarAdmission.nativeReturnFields circuit output member
  refine ⟨field, projection, ?_⟩
  have preflight : Zkir.lowerReturnPreflight output = pure () := by
    obtain ⟨sourceType, _⟩ := scalarAdmission.outputs output member
    cases output with
    | mk name ty value span => cases sourceType <;> rfl
  change Zkir.lowerReturnFieldStep output accumulated = _
  simp only [Zkir.lowerReturnFieldStep, preflight, projection, pure_bind]
  rfl

private theorem returnFieldsLoopFrom_frame (circuit : Circuit)
    (scalarAdmission : ScalarCircuitAdmission circuit) (outputs : List Output)
    (subset : ∀ output ∈ outputs, output ∈ circuit.outputs) (initial : List String) :
    Zkir.PreservesOutputCapacityFrame (returnFieldsLoopFrom outputs initial) := by
  change Zkir.PreservesOutputCapacityFrame (Zkir.lowerReturnFieldsFrom outputs initial)
  unfold Zkir.lowerReturnFieldsFrom
  apply Zkir.forIn_preservesOutputCapacityFrame_of_mem
  intro output member accumulated
  exact returnFieldsStep_frame circuit scalarAdmission output (subset output member) accumulated

private theorem completes_returnFieldsFrom (ctx : EvalContext) (hash : Hash)
    (implementation : HashAgreement ctx hash) (circuit : Circuit) (values : EvalEnv)
    (inputs : NativeRelation.Assignment) (admitted : CanonicalInputs circuit values inputs)
    (identifiers : ∀ input ∈ circuit.inputs,
      validIdentifier ("%input_" ++ input.name) = true)
    (scalarAdmission : ScalarCircuitAdmission circuit)
    (complete : ∀ returned ∈ circuit.outputs, ∀ fields,
      returned.nativeReturnFields = .ok fields → ∀ field ∈ fields, ExprComplete field)
    (outputValidation : ∀ returned ∈ circuit.outputs,
      returned.value.validate Capabilities.crypto
        (circuit.inputs.map fun input => (input.name, input.ty)) = .ok ())
    (outputsEvaluated : ∃ result,
      circuit.outputs.mapM (evalOutput ctx values) = .ok result)
    (outputs : List Output) (subset : ∀ output ∈ outputs, output ∈ circuit.outputs)
    (initial : List String) (witness : NativeRelation.Assignment) (state : Zkir.LowerState)
    (meaning : LowerStateMeaning hash witness state) (inputFrame : InputFrame inputs witness)
    (aliases : state.aliases = [])
    (scopes : ∀ text ∈ initial, TextScope state.next text)
    (budget : ((returnFieldsLoopFrom outputs initial).run state).2.next ≤
      Native.maxInstructions * Native.maxVectorLength) :
    Nonempty (PrefixExtension hash witness state ((returnFieldsLoopFrom outputs initial).run state).2) ∧
    ∀ text ∈ ((returnFieldsLoopFrom outputs initial).run state).1,
      TextScope ((returnFieldsLoopFrom outputs initial).run state).2.next text := by
  induction outputs generalizing initial witness state with
  | nil =>
    exact ⟨⟨{witness, meaning, aliases := rfl, frame := by intro name _; rfl}⟩, scopes⟩
  | cons output outputs ih =>
    have outputMember : output ∈ circuit.outputs := subset output (by simp)
    obtain ⟨result, resultSuccess⟩ := outputsEvaluated
    obtain ⟨sourceValue, sourceEvaluation⟩ := output_eval_member ctx values
      circuit.outputs result resultSuccess output outputMember
    obtain ⟨field, projection, fieldAdmission⟩ :=
      scalarAdmission.nativeReturnFields circuit output outputMember
    obtain ⟨stepEqField, stepProjection, stepEq⟩ :=
      returnFieldsStep_eq circuit scalarAdmission output outputMember initial
    have fieldEq : stepEqField = field :=
      (List.cons.inj (Except.ok.inj (stepProjection.symm.trans projection))).1
    subst stepEqField
    have loopEq : returnFieldsLoopFrom (output :: outputs) initial = (do
        let text ← Zkir.lowerExpr field
        returnFieldsLoopFrom outputs (initial ++ [text])) := by
      change (forIn (output :: outputs) initial Zkir.lowerReturnFieldStep) = _
      rw [List.forIn_cons]
      change (returnFieldsStep output initial >>= fun outcome =>
        match outcome with
        | .done returned => pure returned
        | .yield returned => returnFieldsLoopFrom outputs returned) = _
      rw [stepEq]
      simp only [bind_assoc, pure_bind]
    rw [loopEq] at budget ⊢
    let evaluated := (Zkir.lowerExpr field).run state
    have tailFrame (text : String) : Zkir.PreservesOutputCapacityFrame
        (returnFieldsLoopFrom outputs (initial ++ [text])) :=
      returnFieldsLoopFrom_frame circuit scalarAdmission outputs
        (by
          intro returned member
          exact subset returned (List.mem_cons_of_mem _ member)) (initial ++ [text])
    have tailAfterExpressionBudget :
        (returnFieldsLoopFrom outputs (initial ++ [evaluated.1])).run evaluated.2 |>.2.next ≤
          Native.maxInstructions * Native.maxVectorLength := by
      have budgetAfterBind := budget
      rw [stateRunBind] at budgetAfterBind
      simpa [evaluated] using budgetAfterBind
    have expressionBudget : evaluated.2.next ≤ Native.maxInstructions * Native.maxVectorLength :=
      Nat.le_trans (tailFrame evaluated.1 evaluated.2).next tailAfterExpressionBudget
    obtain ⟨projectedValue, fieldEvaluation⟩ := scalarReturnField_evaluates ctx hash implementation
      circuit values inputs admitted scalarAdmission output outputMember sourceValue sourceEvaluation
      field projection
    have fieldValidation := scalarReturnField_validates circuit output outputMember scalarAdmission
      (circuit.inputs.map fun input => (input.name, input.ty))
      (outputValidation output outputMember) field projection
    have fieldComplete := complete output outputMember [field] (by simpa using projection)
      field (by simp)
    have aliasesAgreement := current_aliases hash inputs witness circuit values state admitted
      identifiers inputFrame aliases
    obtain ⟨step⟩ := fieldComplete ctx hash implementation inputs witness state
      (circuitAliases circuit) values
      (circuit.inputs.map fun input => (input.name, input.ty)) projectedValue fieldValidation
      fieldEvaluation (admitted.typedEnvironment circuit values inputs hash).aliases
      aliasesAgreement meaning expressionBudget
    have sameRun : (do
        let text ← Zkir.lowerExpr field
        returnFieldsLoopFrom outputs (initial ++ [text])).run state =
        (returnFieldsLoopFrom outputs (initial ++ [step.text])).run step.finalState := by
      rw [stateRunBind]
      rw [step.run]
    have tailBudget : (returnFieldsLoopFrom outputs (initial ++ [step.text])).run step.finalState |>.2.next ≤
        Native.maxInstructions * Native.maxVectorLength := by
      change ((do
        let text ← Zkir.lowerExpr field
        returnFieldsLoopFrom outputs (initial ++ [text])).run state).2.next ≤ _ at budget
      rw [stateRunBind] at budget
      rw [step.run] at budget
      exact budget
    have nextInput : InputFrame inputs step.finalWitness := fun name =>
      (step.frame _ (Or.inl ⟨name, rfl⟩)).trans (inputFrame name)
    have nextScopes : ∀ text ∈ initial ++ [step.text], TextScope step.finalState.next text := by
      intro text member
      rcases List.mem_append.mp member with old | new
      · have nextMono : state.next ≤ step.finalState.next := by
          have frame := (ScalarAllocationOutputFrame.lowerExpr_admitted_preservesOutputCapacityFrame
            field fieldAdmission state).next
          simpa [step.run] using frame
        exact (scopes text old).mono nextMono
      · exact List.mem_singleton.mp new ▸ step.textScope
    obtain ⟨⟨rest⟩, finalScopes⟩ := ih
      (by intro returned member; exact subset returned (List.mem_cons_of_mem _ member))
      (initial ++ [step.text]) step.finalWitness step.finalState step.stateMeaning nextInput
      (step.aliasesPreserved.trans aliases) nextScopes tailBudget
    refine ⟨⟨{witness := rest.witness, meaning := ?_, aliases := ?_, frame := ?_}⟩, ?_⟩
    · rw [sameRun]
      exact rest.meaning
    · rw [sameRun]
      exact rest.aliases.trans step.aliasesPreserved
    · intro name scope
      have nextMono : state.next ≤ step.finalState.next := by
        have frame := (ScalarAllocationOutputFrame.lowerExpr_admitted_preservesOutputCapacityFrame
          field fieldAdmission state).next
        simpa [step.run] using frame
      exact (rest.frame name (InScope.mono nextMono scope)).trans (step.frame name scope)
    · intro text member
      rw [sameRun] at member
      rw [sameRun]
      exact finalScopes text member

theorem completes_circuit_outputs (ctx : EvalContext) (hash : Hash)
    (implementation : HashAgreement ctx hash) (circuit : Circuit) (values : EvalEnv)
    (inputs : NativeRelation.Assignment) (admitted : CanonicalInputs circuit values inputs)
    (identifiers : ∀ input ∈ circuit.inputs,
      validIdentifier ("%input_" ++ input.name) = true)
    (scalarAdmission : ScalarCircuitAdmission circuit)
    (complete : ∀ returned ∈ circuit.outputs, ∀ fields,
      returned.nativeReturnFields = .ok fields → ∀ field ∈ fields, ExprComplete field)
    (outputValidation : ∀ returned ∈ circuit.outputs,
      returned.value.validate Capabilities.crypto
        (circuit.inputs.map fun input => (input.name, input.ty)) = .ok ())
    (outputsEvaluated : ∃ result,
      circuit.outputs.mapM (evalOutput ctx values) = .ok result) :
    Completes hash inputs (do
      let texts ← Zkir.lowerReturnFields circuit.outputs
      if !texts.isEmpty then Zkir.bindPublic texts
      Zkir.emit "output" [("vals", toJson texts)]) := by
  intro witness state meaning inputFrame aliases budget
  let footer (texts : List String) : StateM Zkir.LowerState Unit := do
    if !texts.isEmpty then Zkir.bindPublic texts
    Zkir.emit "output" [("vals", toJson texts)]
  have footerFrame : ∀ texts, Zkir.PreservesOutputCapacityFrame (footer texts) := by
    intro texts
    dsimp only [footer]
    split
    · apply Zkir.bind_preservesOutputCapacityFrame
      · exact Zkir.emit_preservesOutputCapacityFrame _ _
      · intro _
        exact Zkir.emit_preservesOutputCapacityFrame _ _
    · exact Zkir.emit_preservesOutputCapacityFrame _ _
  have fieldsBudget : (Zkir.lowerReturnFields circuit.outputs).run state |>.2.next ≤
      Native.maxInstructions * Native.maxVectorLength := by
    let texts := (Zkir.lowerReturnFields circuit.outputs).run state |>.1
    let fieldsState := (Zkir.lowerReturnFields circuit.outputs).run state |>.2
    have footerBudget : (footer texts).run fieldsState |>.2.next ≤
        Native.maxInstructions * Native.maxVectorLength := by
      change ((do
        let returned ← Zkir.lowerReturnFields circuit.outputs
        footer returned).run state).2.next ≤ _ at budget
      rw [stateRunBind] at budget
      simpa [texts, fieldsState] using budget
    exact Nat.le_trans (footerFrame texts fieldsState).next footerBudget
  have loopEq := returnFieldsLoop_eq circuit.outputs
  have fieldsLoopBudget : (returnFieldsLoopFrom circuit.outputs []).run state |>.2.next ≤
      Native.maxInstructions * Native.maxVectorLength := fieldsBudget
  obtain ⟨⟨result⟩, scopes⟩ := completes_returnFieldsFrom ctx hash implementation circuit values inputs
    admitted identifiers scalarAdmission complete outputValidation outputsEvaluated circuit.outputs
    (by intro output member; exact member) [] witness state meaning inputFrame aliases
    (by simp) fieldsLoopBudget
  have footerMeaning : LowerStateMeaning hash result.witness
      ((footer ((Zkir.lowerReturnFields circuit.outputs).run state).1).run
        ((Zkir.lowerReturnFields circuit.outputs).run state).2).2 := by
    dsimp only [footer]
    split
    · exact emit_output hash result.witness _
        (emit_impact hash result.witness _ result.meaning _ scopes) _ scopes
    · exact emit_output hash result.witness _ result.meaning _ scopes
  refine ⟨{witness := result.witness, meaning := footerMeaning, aliases := ?_, frame := result.frame}⟩
  change ((footer ((Zkir.lowerReturnFields circuit.outputs).run state).1).run
    ((Zkir.lowerReturnFields circuit.outputs).run state).2).2.aliases = state.aliases
  dsimp only [footer]
  split <;> exact result.aliases

end Noctium.Verification.ScalarWitnessConstruction
