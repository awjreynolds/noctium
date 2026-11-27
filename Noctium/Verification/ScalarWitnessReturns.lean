import Noctium.Verification.ScalarWitnessAssembly
import Noctium.Verification.ScalarAllocationOutputFrame
import Noctium.Verification.ScalarExpressionLowering
import Noctium.Verification.ScalarNormalizationSoundness

namespace Noctium.Verification.ScalarWitnessConstruction

open Lean Backend NativeRelation NativeRelationJson ScalarLowering ScalarNormalization

private theorem stateRunBind {α β} (first : StateM Zkir.LowerState α)
    (next : α → StateM Zkir.LowerState β) (state : Zkir.LowerState) :
    (do let value ← first; next value).run state =
      (next (first.run state).1).run (first.run state).2 := rfl

private theorem return_eval_member (ctx : EvalContext) (values : EvalEnv)
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

private theorem scalarReturnProjection (output : Output)
    (sourceType : ScalarType output.ty) (sourceAdmission : ScalarExpression output.value) :
    ∃ field : Expr .native,
      output.nativeReturnFields = .ok [field] ∧ ScalarExpression field := by
  cases output with
  | mk name ty value span =>
    cases sourceType with
    | native => exact ⟨value, rfl, sourceAdmission⟩
    | bool => exact ⟨.cast .native value, rfl,
        ScalarExpression.cast value .bool .native sourceAdmission⟩
    | uint maximum => exact ⟨.cast .native value, rfl,
        ScalarExpression.cast value (.uint maximum) .native sourceAdmission⟩

private theorem scalarReturnField_evaluates (ctx : EvalContext) (hash : Hash)
    (implementation : HashAgreement ctx hash) (normalAliases : Backend.Native.AliasEnvironment)
    (values : EvalEnv) (inputs : NativeRelation.Assignment)
    (aliasAgreement : AliasAgreement hash inputs normalAliases values)
    (output : Output) (sourceType : ScalarType output.ty)
    (sourceAdmission : ScalarExpression output.value) (sourceValue : output.ty.Denote)
    (sourceEvaluation : output.value.eval ctx values = .ok sourceValue)
    (field : Expr .native) (projection : output.nativeReturnFields = .ok [field]) :
    ∃ value, field.eval ctx values = .ok value ∧
      value = number sourceType sourceValue := by
  obtain ⟨normalized, _, represents⟩ := normalize_success ctx hash implementation inputs
    normalAliases values aliasAgreement output.value sourceAdmission sourceValue sourceEvaluation
  cases output with
  | mk name ty value span =>
    cases sourceType with
    | native =>
      have fieldEq : field = value := by
        change Except.ok [value] = Except.ok [field] at projection
        exact (List.cons.inj (Except.ok.inj projection)).1.symm
      subst field
      exact ⟨sourceValue, sourceEvaluation, rfl⟩
    | bool =>
      have fieldEq : field = .cast .native value := by
        change Except.ok [.cast .native value] = Except.ok [field] at projection
        exact (List.cons.inj (Except.ok.inj projection)).1.symm
      subst field
      have range : number ScalarType.bool sourceValue < ctx.modulus := by
        cases sourceValue <;> simp [number, implementation.modulus, Field.modulus]
      rw [eval_cast_scalar ctx values value ScalarType.bool ScalarType.native sourceValue sourceEvaluation]
      refine ⟨number ScalarType.bool sourceValue, ?_, rfl⟩
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
      refine ⟨number (.uint maximum) sourceValue, ?_, rfl⟩
      simp [scalarCast, range]

/-- The operand emitted for one scalar return is the value of its sole native
ABI field under the successful source evaluation. -/
def ScalarAbiReturnFieldOperandCorrespondence (ctx : EvalContext) (values : EvalEnv)
    (witness : NativeRelation.Assignment) (output : Output) (text : String) : Prop :=
  ∃ sourceType : ScalarType output.ty, ∃ sourceValue,
    output.value.eval ctx values = .ok sourceValue ∧
    ∃ field : Expr .native, output.nativeReturnFields = .ok [field] ∧
    ∃ fieldValue operand,
      field.eval ctx values = .ok fieldValue ∧
      fieldValue = number sourceType sourceValue ∧
      decodeOperand (toJson text) = .ok operand ∧
      operand.read witness = scalar fieldValue

inductive ScalarAbiReturnFieldOperandCorrespondences (ctx : EvalContext) (values : EvalEnv)
    (witness : NativeRelation.Assignment) : List Output → List String → Prop where
  | nil : ScalarAbiReturnFieldOperandCorrespondences ctx values witness [] []
  | cons {output : Output} {outputs : List Output} {text : String} {texts : List String}
      (head : ScalarAbiReturnFieldOperandCorrespondence ctx values witness output text)
      (tail : ScalarAbiReturnFieldOperandCorrespondences ctx values witness outputs texts) :
      ScalarAbiReturnFieldOperandCorrespondences ctx values witness (output :: outputs)
        (text :: texts)

private theorem scalarReturnField_validates (output : Output)
    (sourceType : ScalarType output.ty) (types : TypeEnv)
    (sourceValidation : output.value.validate Capabilities.crypto types = .ok ())
    (field : Expr .native) (projection : output.nativeReturnFields = .ok [field]) :
    field.validate Capabilities.crypto types = .ok () := by
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

private theorem returnFieldsStep_frame (output : Output) (sourceType : ScalarType output.ty)
    (sourceAdmission : ScalarExpression output.value) (accumulated : List String) :
    Zkir.PreservesOutputCapacityFrame (Zkir.lowerReturnFieldStep output accumulated) := by
  obtain ⟨field, projection, fieldAdmission⟩ := scalarReturnProjection output sourceType sourceAdmission
  unfold Zkir.lowerReturnFieldStep
  apply Zkir.bind_preservesOutputCapacityFrame _ _
    (ScalarAllocationOutputFrame.scalarReturnPreflight_preservesOutputCapacityFrame output sourceType)
  intro ignored
  rw [projection]
  apply Zkir.bind_preservesOutputCapacityFrame _ _
  · apply Zkir.forIn_preservesOutputCapacityFrame_of_mem
    intro returned member values
    have sameField : returned = field := by simpa only [List.mem_singleton] using member
    subst returned
    apply Zkir.bind_preservesOutputCapacityFrame _ _
      (ScalarAllocationOutputFrame.lowerExpr_admitted_preservesOutputCapacityFrame field fieldAdmission)
    intro text
    exact Zkir.pure_preservesOutputCapacityFrame _
  · intro returned
    exact Zkir.pure_preservesOutputCapacityFrame (ForInStep.yield returned)

private theorem returnFieldsStep_eq (output : Output) (sourceType : ScalarType output.ty)
    (sourceAdmission : ScalarExpression output.value) (accumulated : List String) :
    ∃ field, output.nativeReturnFields = .ok [field] ∧
      Zkir.lowerReturnFieldStep output accumulated = (do
        let text ← Zkir.lowerExpr field
        pure (ForInStep.yield (accumulated ++ [text]))) := by
  obtain ⟨field, projection, _⟩ := scalarReturnProjection output sourceType sourceAdmission
  refine ⟨field, projection, ?_⟩
  have preflight : Zkir.lowerReturnPreflight output = pure () := by
    cases output with
    | mk name ty value span => cases sourceType <;> rfl
  change Zkir.lowerReturnFieldStep output accumulated = _
  simp only [Zkir.lowerReturnFieldStep, preflight, projection, pure_bind]
  rfl

private theorem returnFieldsFrom_frame (returns : List Output)
    (admission : ∀ output ∈ returns,
      ∃ _sourceType : ScalarType output.ty, ScalarExpression output.value)
    (outputs : List Output) (subset : ∀ output ∈ outputs, output ∈ returns)
    (initial : List String) :
    Zkir.PreservesOutputCapacityFrame (Zkir.lowerReturnFieldsFrom outputs initial) := by
  unfold Zkir.lowerReturnFieldsFrom
  apply Zkir.forIn_preservesOutputCapacityFrame_of_mem
  intro output member accumulated
  obtain ⟨sourceType, sourceAdmission⟩ := admission output (subset output member)
  exact returnFieldsStep_frame output sourceType sourceAdmission accumulated

private theorem completes_returnFieldsFrom (ctx : EvalContext) (hash : Hash)
    (implementation : HashAgreement ctx hash) (returns : List Output) (values : EvalEnv)
    (inputs : NativeRelation.Assignment) (types : TypeEnv)
    (normalAliases : Backend.Native.AliasEnvironment)
    (admission : ∀ output ∈ returns,
      ∃ _sourceType : ScalarType output.ty, ScalarExpression output.value)
    (validation : ∀ output ∈ returns,
      output.value.validate Capabilities.crypto types = .ok ())
    (outputsEvaluated : ∃ result,
      returns.mapM (evalOutput ctx values) = .ok result)
    (outputs : List Output) (subset : ∀ output ∈ outputs, output ∈ returns)
    (initial : List String) (witness : NativeRelation.Assignment) (state : Zkir.LowerState)
    (meaning : LowerStateMeaning hash witness state)
    (aliasAgreement : AliasAgreement hash inputs normalAliases values)
    (lowerAliasAgreement : LowerAliasAgreement hash inputs witness normalAliases state.aliases values)
    (scopes : ∀ text ∈ initial, TextScope state.next text)
    (budget : (Zkir.lowerReturnFieldsFrom outputs initial).run state |>.2.next ≤
      Native.maxInstructions * Native.maxVectorLength) :
    ∃ extension : PrefixExtension hash witness state
        ((Zkir.lowerReturnFieldsFrom outputs initial).run state).2,
      (∀ text ∈ ((Zkir.lowerReturnFieldsFrom outputs initial).run state).1,
        TextScope ((Zkir.lowerReturnFieldsFrom outputs initial).run state).2.next text) ∧
      ∃ emitted, ((Zkir.lowerReturnFieldsFrom outputs initial).run state).1 =
          initial ++ emitted ∧
        ScalarAbiReturnFieldOperandCorrespondences ctx values extension.witness outputs emitted := by
  induction outputs generalizing initial witness state with
  | nil =>
    refine ⟨{witness, meaning, aliases := rfl, frame := by intro name _; rfl}, scopes, [], ?_, ?_⟩
    · simp only [Zkir.lowerReturnFieldsFrom, List.forIn_nil, List.append_nil]
      change (initial, state).1 = initial
      rfl
    · exact .nil
  | cons output outputs ih =>
    have outputMember : output ∈ returns := subset output (by simp)
    obtain ⟨result, resultSuccess⟩ := outputsEvaluated
    obtain ⟨sourceValue, sourceEvaluation⟩ := return_eval_member ctx values
      returns result resultSuccess output outputMember
    obtain ⟨sourceType, sourceAdmission⟩ := admission output outputMember
    obtain ⟨field, projection, fieldAdmission⟩ :=
      scalarReturnProjection output sourceType sourceAdmission
    obtain ⟨stepField, stepProjection, stepEq⟩ :=
      returnFieldsStep_eq output sourceType sourceAdmission initial
    have fieldEq : stepField = field :=
      (List.cons.inj (Except.ok.inj (stepProjection.symm.trans projection))).1
    subst stepField
    have loopEq : Zkir.lowerReturnFieldsFrom (output :: outputs) initial = (do
        let text ← Zkir.lowerExpr field
        Zkir.lowerReturnFieldsFrom outputs (initial ++ [text])) := by
      change (forIn (output :: outputs) initial Zkir.lowerReturnFieldStep) = _
      rw [List.forIn_cons]
      change (Zkir.lowerReturnFieldStep output initial >>= fun outcome =>
        match outcome with
        | .done returned => pure returned
        | .yield returned => Zkir.lowerReturnFieldsFrom outputs returned) = _
      rw [stepEq]
      simp only [bind_assoc, pure_bind]
    rw [loopEq] at budget ⊢
    let evaluated := (Zkir.lowerExpr field).run state
    have tailFrame (text : String) : Zkir.PreservesOutputCapacityFrame
        (Zkir.lowerReturnFieldsFrom outputs (initial ++ [text])) :=
      returnFieldsFrom_frame returns admission outputs
        (by
          intro returned member
          exact subset returned (List.mem_cons_of_mem _ member)) (initial ++ [text])
    have tailAfterExpressionBudget :
        (Zkir.lowerReturnFieldsFrom outputs (initial ++ [evaluated.1])).run evaluated.2 |>.2.next ≤
          Native.maxInstructions * Native.maxVectorLength := by
      have budgetAfterBind := budget
      rw [stateRunBind] at budgetAfterBind
      simpa [evaluated] using budgetAfterBind
    have expressionBudget : evaluated.2.next ≤ Native.maxInstructions * Native.maxVectorLength :=
      Nat.le_trans (tailFrame evaluated.1 evaluated.2).next tailAfterExpressionBudget
    obtain ⟨projectedValue, fieldEvaluation, projectedValueEq⟩ := scalarReturnField_evaluates ctx hash
      implementation normalAliases values inputs aliasAgreement output sourceType sourceAdmission
      sourceValue sourceEvaluation field projection
    have fieldValidation := scalarReturnField_validates output sourceType types
      (validation output outputMember) field projection
    have fieldComplete := ScalarExpressionLowering.lowerExpr_complete field fieldAdmission
    obtain ⟨step⟩ := fieldComplete ctx hash implementation inputs witness state normalAliases values
      types projectedValue fieldValidation fieldEvaluation aliasAgreement lowerAliasAgreement
      meaning expressionBudget
    have sameRun : (do
        let text ← Zkir.lowerExpr field
        Zkir.lowerReturnFieldsFrom outputs (initial ++ [text])).run state =
        (Zkir.lowerReturnFieldsFrom outputs (initial ++ [step.text])).run step.finalState := by
      rw [stateRunBind]
      rw [step.run]
    have tailBudget :
        (Zkir.lowerReturnFieldsFrom outputs (initial ++ [step.text])).run step.finalState |>.2.next ≤
          Native.maxInstructions * Native.maxVectorLength := by
      change ((do
        let text ← Zkir.lowerExpr field
        Zkir.lowerReturnFieldsFrom outputs (initial ++ [text])).run state).2.next ≤ _ at budget
      rw [stateRunBind] at budget
      rw [step.run] at budget
      exact budget
    have nextScopes : ∀ text ∈ initial ++ [step.text], TextScope step.finalState.next text := by
      intro text member
      rcases List.mem_append.mp member with old | new
      · have nextMono : state.next ≤ step.finalState.next := by
          have frame := (ScalarAllocationOutputFrame.lowerExpr_admitted_preservesOutputCapacityFrame
            field fieldAdmission state).next
          simpa [step.run] using frame
        exact (scopes text old).mono nextMono
      · exact List.mem_singleton.mp new ▸ step.textScope
    obtain ⟨rest, finalScopes, emittedTail, emittedTailRun, tailCorrespondence⟩ := ih
      (by intro returned member; exact subset returned (List.mem_cons_of_mem _ member))
      (initial ++ [step.text]) step.finalWitness step.finalState step.stateMeaning
      step.aliasAgreement nextScopes tailBudget
    have emittedRun :
        ((do
          let text ← Zkir.lowerExpr field
          Zkir.lowerReturnFieldsFrom outputs (initial ++ [text])).run state).1 =
          initial ++ (step.text :: emittedTail) := by
      rw [stateRunBind, step.run, emittedTailRun]
      simp [List.append_assoc]
    have represented :
        interpret hash inputs step.normalized.term = some (scalar projectedValue) := by
      rw [step.represents.2.2, sourceScalar_number ScalarType.native projectedValue]
      rfl
    obtain ⟨operand, parsed, operandMeaning⟩ := OperandMeaning.of_frame hash inputs
      step.finalWitness rest.witness step.finalState.next step.text step.normalized.term
      step.operandMeaning
      step.textScope rest.frame
    have operandValue : operand.read rest.witness = scalar projectedValue :=
      Option.some.inj (operandMeaning.symm.trans represented)
    have headCorrespondence : ScalarAbiReturnFieldOperandCorrespondence ctx values
        rest.witness output step.text := by
      refine ⟨sourceType, sourceValue, sourceEvaluation, field, projection,
        projectedValue, operand, fieldEvaluation, projectedValueEq, parsed, operandValue⟩
    refine ⟨{witness := rest.witness, meaning := ?_, aliases := ?_, frame := ?_}, ?_, ?_⟩
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
    · exact ⟨step.text :: emittedTail, emittedRun,
        ScalarAbiReturnFieldOperandCorrespondences.cons headCorrespondence tailCorrespondence⟩

/-- Lower the complete scalar return list while retaining the witness and
operand scopes needed by the caller's actual output instructions. -/
theorem completes_scalar_returnFields (ctx : EvalContext) (hash : Hash)
    (implementation : HashAgreement ctx hash) (returns : List Output) (values : EvalEnv)
    (inputs : NativeRelation.Assignment) (types : TypeEnv)
    (normalAliases : Backend.Native.AliasEnvironment)
    (admission : ∀ output ∈ returns,
      ∃ _sourceType : ScalarType output.ty, ScalarExpression output.value)
    (validation : ∀ output ∈ returns,
      output.value.validate Capabilities.crypto types = .ok ())
    (outputsEvaluated : ∃ result, returns.mapM (evalOutput ctx values) = .ok result)
    (witness : NativeRelation.Assignment) (state : Zkir.LowerState)
    (meaning : LowerStateMeaning hash witness state)
    (aliasAgreement : AliasAgreement hash inputs normalAliases values)
    (lowerAliasAgreement : LowerAliasAgreement hash inputs witness normalAliases state.aliases values)
    (budget : (Zkir.lowerReturnFields returns).run state |>.2.next ≤
      Native.maxInstructions * Native.maxVectorLength) :
    Nonempty (PrefixExtension hash witness state
      ((Zkir.lowerReturnFields returns).run state).2) ∧
    ∀ text ∈ ((Zkir.lowerReturnFields returns).run state).1,
      TextScope ((Zkir.lowerReturnFields returns).run state).2.next text := by
  unfold Zkir.lowerReturnFields
  obtain ⟨extension, scopes, _, _, _⟩ :=
    completes_returnFieldsFrom ctx hash implementation returns values inputs types
      normalAliases admission validation outputsEvaluated returns (fun _ member => member) []
      witness state meaning aliasAgreement lowerAliasAgreement (by simp) budget
  exact ⟨⟨extension⟩, scopes⟩

/-- Lower every scalar return field in source order and retain the operand
value correspondence needed to interpret the emitted output row. -/
theorem completes_scalar_returnFields_correspondence (ctx : EvalContext) (hash : Hash)
    (implementation : HashAgreement ctx hash) (returns : List Output) (values : EvalEnv)
    (inputs : NativeRelation.Assignment) (types : TypeEnv)
    (normalAliases : Backend.Native.AliasEnvironment)
    (admission : ∀ output ∈ returns,
      ∃ _sourceType : ScalarType output.ty, ScalarExpression output.value)
    (validation : ∀ output ∈ returns,
      output.value.validate Capabilities.crypto types = .ok ())
    (outputsEvaluated : ∃ result, returns.mapM (evalOutput ctx values) = .ok result)
    (witness : NativeRelation.Assignment) (state : Zkir.LowerState)
    (meaning : LowerStateMeaning hash witness state)
    (aliasAgreement : AliasAgreement hash inputs normalAliases values)
    (lowerAliasAgreement : LowerAliasAgreement hash inputs witness normalAliases state.aliases values)
    (budget : (Zkir.lowerReturnFields returns).run state |>.2.next ≤
      Native.maxInstructions * Native.maxVectorLength) :
    ∃ extension : PrefixExtension hash witness state
        ((Zkir.lowerReturnFields returns).run state).2,
      (∀ text ∈ ((Zkir.lowerReturnFields returns).run state).1,
        TextScope ((Zkir.lowerReturnFields returns).run state).2.next text) ∧
      ScalarAbiReturnFieldOperandCorrespondences ctx values extension.witness
        returns ((Zkir.lowerReturnFields returns).run state).1 := by
  unfold Zkir.lowerReturnFields
  obtain ⟨extension, scopes, emitted, emittedEq, correspondence⟩ :=
    completes_returnFieldsFrom ctx hash implementation returns values inputs types
      normalAliases admission validation outputsEvaluated returns (fun _ member => member) []
      witness state meaning aliasAgreement lowerAliasAgreement (by simp) budget
  refine ⟨extension, ?_, ?_⟩
  · simpa only [List.nil_append] using scopes
  · rw [emittedEq]
    simpa only [List.nil_append] using correspondence

/-- The final entrypoint output row decodes to the ordered operands for the
scalar ABI return fields. The field correspondence uses the same final witness
as the emitted output instruction. -/
theorem completes_entrypoint_returns_output_row (ctx : EvalContext) (hash : Hash)
    (implementation : HashAgreement ctx hash) (entry : Entrypoint) (values : EvalEnv)
    (inputs : NativeRelation.Assignment) (types : TypeEnv)
    (normalAliases : Backend.Native.AliasEnvironment)
    (admission : ∀ output ∈ entry.returns,
      ∃ _sourceType : ScalarType output.ty, ScalarExpression output.value)
    (validation : ∀ output ∈ entry.returns,
      output.value.validate Capabilities.crypto types = .ok ())
    (outputsEvaluated : ∃ result,
      entry.returns.mapM (evalOutput ctx values) = .ok result) :
    ∀ witness state, LowerStateMeaning hash witness state →
      AliasAgreement hash inputs normalAliases values →
      LowerAliasAgreement hash inputs witness normalAliases state.aliases values →
      ((do
        let returned ← Zkir.lowerReturnFields entry.returns
        Zkir.emit "output" [("vals", toJson returned)]).run state).2.next ≤
          Native.maxInstructions * Native.maxVectorLength →
      ∃ extension : PrefixExtension hash witness state
          ((do
            let returned ← Zkir.lowerReturnFields entry.returns
            Zkir.emit "output" [("vals", toJson returned)]).run state).2,
        ∃ operands,
          ((do
            let returned ← Zkir.lowerReturnFields entry.returns
            Zkir.emit "output" [("vals", toJson returned)]).run state).2.instructions =
            ((Zkir.lowerReturnFields entry.returns).run state).2.instructions.push
              (Zkir.instruction "output"
                [("vals", toJson ((Zkir.lowerReturnFields entry.returns).run state).1)]) ∧
          decodeOperands (toJson ((Zkir.lowerReturnFields entry.returns).run state).1) =
            .ok operands ∧
          decodeInstruction (Zkir.instruction "output"
              [("vals", toJson ((Zkir.lowerReturnFields entry.returns).run state).1)]) =
            .ok (.output operands) ∧
          ScalarAbiReturnFieldOperandCorrespondences ctx values extension.witness
            entry.returns ((Zkir.lowerReturnFields entry.returns).run state).1 := by
  intro witness state meaning aliasAgreement lowerAliasAgreement budget
  have outputFrame (returned : List String) :
      Zkir.PreservesOutputCapacityFrame
        (Zkir.emit "output" [("vals", toJson returned)]) :=
    Zkir.emit_preservesOutputCapacityFrame _ _
  have fieldsBudget : (Zkir.lowerReturnFields entry.returns).run state |>.2.next ≤
      Native.maxInstructions * Native.maxVectorLength := by
    let returned := (Zkir.lowerReturnFields entry.returns).run state |>.1
    let fieldsState := (Zkir.lowerReturnFields entry.returns).run state |>.2
    have outputBudget : (Zkir.emit "output" [("vals", toJson returned)]).run fieldsState |>.2.next ≤
        Native.maxInstructions * Native.maxVectorLength := by
      change ((do
        let returned ← Zkir.lowerReturnFields entry.returns
        Zkir.emit "output" [("vals", toJson returned)]).run state).2.next ≤ _ at budget
      rw [stateRunBind] at budget
      simpa [returned, fieldsState] using budget
    exact Nat.le_trans (outputFrame returned fieldsState).next outputBudget
  let returned := (Zkir.lowerReturnFields entry.returns).run state |>.1
  let fieldsState := (Zkir.lowerReturnFields entry.returns).run state |>.2
  obtain ⟨returnsPrefix, scopes, correspondence⟩ := completes_scalar_returnFields_correspondence
    ctx hash implementation entry.returns values inputs types normalAliases admission validation
    outputsEvaluated witness state meaning aliasAgreement lowerAliasAgreement fieldsBudget
  obtain ⟨operands, parsed, _operandScope⟩ :=
    scoped_operands fieldsState.next returned scopes
  have decodedOutput := ScalarInstructionEncoding.decode_output_instruction parsed
  have combinedRun :
      ((do
        let returned ← Zkir.lowerReturnFields entry.returns
        Zkir.emit "output" [("vals", toJson returned)]).run state) =
      (Zkir.emit "output" [("vals", toJson returned)]).run fieldsState := by
    rw [stateRunBind]
  have rowMeaning : LowerStateMeaning hash returnsPrefix.witness
      ((do
        let returned ← Zkir.lowerReturnFields entry.returns
        Zkir.emit "output" [("vals", toJson returned)]).run state).2 := by
    rw [combinedRun]
    exact emit_output hash returnsPrefix.witness fieldsState returnsPrefix.meaning
      returned scopes
  have rowAliases :
      ((do
        let returned ← Zkir.lowerReturnFields entry.returns
        Zkir.emit "output" [("vals", toJson returned)]).run state).2.aliases = state.aliases := by
    rw [combinedRun]
    change fieldsState.aliases = state.aliases
    exact returnsPrefix.aliases
  let extension : PrefixExtension hash witness state
      ((do
        let returned ← Zkir.lowerReturnFields entry.returns
        Zkir.emit "output" [("vals", toJson returned)]).run state).2 :=
    { witness := returnsPrefix.witness
      meaning := rowMeaning
      aliases := rowAliases
      frame := returnsPrefix.frame }
  have outputRowAppended :
      ((do
        let returned ← Zkir.lowerReturnFields entry.returns
        Zkir.emit "output" [("vals", toJson returned)]).run state).2.instructions =
        fieldsState.instructions.push (Zkir.instruction "output" [("vals", toJson returned)]) := by
    rw [combinedRun]
    rfl
  refine ⟨extension, operands, ?_⟩
  refine ⟨?_, parsed, decodedOutput, ?_⟩
  · simpa [returned, fieldsState] using outputRowAppended
  · simpa [returned] using correspondence

/-- The ledger return suffix preserves the current alias scope while lowering
each admitted scalar return through its native ABI field and emitting output. -/
theorem completes_entrypoint_returns (ctx : EvalContext) (hash : Hash)
    (implementation : HashAgreement ctx hash) (entry : Entrypoint) (values : EvalEnv)
    (inputs : NativeRelation.Assignment) (types : TypeEnv)
    (normalAliases : Backend.Native.AliasEnvironment)
    (admission : ∀ output ∈ entry.returns,
      ∃ _sourceType : ScalarType output.ty, ScalarExpression output.value)
    (validation : ∀ output ∈ entry.returns,
      output.value.validate Capabilities.crypto types = .ok ())
    (outputsEvaluated : ∃ result,
      entry.returns.mapM (evalOutput ctx values) = .ok result) :
    ∀ witness state, LowerStateMeaning hash witness state →
      AliasAgreement hash inputs normalAliases values →
      LowerAliasAgreement hash inputs witness normalAliases state.aliases values →
      ((do
        let returned ← Zkir.lowerReturnFields entry.returns
        Zkir.emit "output" [("vals", toJson returned)]).run state).2.next ≤
          Native.maxInstructions * Native.maxVectorLength →
      Nonempty (PrefixExtension hash witness state
        ((do
          let returned ← Zkir.lowerReturnFields entry.returns
          Zkir.emit "output" [("vals", toJson returned)]).run state).2) := by
  intro witness state meaning aliasAgreement lowerAliasAgreement budget
  obtain ⟨extension, operands, _, _, _, _⟩ :=
    completes_entrypoint_returns_output_row ctx hash implementation entry values inputs types
      normalAliases admission validation outputsEvaluated witness state meaning aliasAgreement
      lowerAliasAgreement budget
  exact ⟨extension⟩

end Noctium.Verification.ScalarWitnessConstruction
