import Noctium.Verification.ScalarWitnessAliases
import Noctium.Verification.ScalarExpressionLowering
import Noctium.Verification.ScalarAllocationOutputFrame
import Noctium.Verification.ScalarEntrypointSeedFrame
import Noctium.Verification.GenericStateCircuitParts

namespace Noctium.Verification.ScalarWitnessConstruction

open Backend Backend.Native NativeRelation NativeRelationJson ScalarLowering ScalarNormalization
open GenericStateCircuitParts ScalarEntrypointSeedFrame ScalarExpressionLowering
open ScalarAllocationOutputFrame

private theorem bind_ok {α β : Type} {first : Except ε α}
    {next : α → Except ε β} {result : β} :
    (first >>= next) = .ok result ↔
      ∃ value, first = .ok value ∧ next value = .ok result := by
  cases first <;> simp [Bind.bind, Except.bind]

private theorem normalizeOutput_ok (aliases : AliasEnvironment) (output : Output)
    (normalized : Normalized)
    (accepted : GenericStateCircuitParts.normalizeOutput aliases output = .ok normalized) :
    normalize aliases output.value = .ok normalized := by
  unfold GenericStateCircuitParts.normalizeOutput at accepted
  cases checked : normalize aliases output.value with
  | error message => simp [checked, Except.mapError] at accepted
  | ok found =>
    simp [checked, Except.mapError] at accepted
    subst normalized
    rfl

private theorem lowerAliasAgreement_cons_unused (hash : Hash)
    (inputs witness : NativeRelation.Assignment) (normalAliases : AliasEnvironment)
    (lowerAliases : List (String × String)) (values : EvalEnv)
    (name : String) (term : Term) (text : String)
    (agreement : LowerAliasAgreement hash inputs witness normalAliases lowerAliases values)
    (unused : values.lookup name = none) :
    LowerAliasAgreement hash inputs witness
      ((name, term) :: normalAliases) ((name, text) :: lowerAliases) values := by
  intro found ty raw value lookup typed
  have different : found ≠ name := by
    intro same
    subst found
    rw [unused] at lookup
    cases lookup
  have unequal : (found == name) = false := by simp [different]
  obtain ⟨oldTerm, oldNormal, oldMeaning⟩ := agreement found ty raw value lookup typed
  refine ⟨oldTerm, ?_, ?_⟩
  · simpa [List.lookup_cons, unequal] using oldNormal
  · simpa [List.lookup_cons, unequal] using oldMeaning

private def lowerScalarOutput (output : Output) : StateM Zkir.LowerState Unit := do
  let text ← Zkir.lowerExpr output.value
  modify fun state => {state with aliases := (output.name, text) :: state.aliases}

private def lowerScalarOutputs (outputs : List Output) : StateM Zkir.LowerState Unit := do
  for output in outputs do
    let text ← Zkir.lowerExpr output.value
    modify fun state => {state with aliases := (output.name, text) :: state.aliases}

private theorem lowerScalarOutputs_cons (output : Output) (outputs : List Output) :
    lowerScalarOutputs (output :: outputs) =
      lowerScalarOutput output >>= fun _ => lowerScalarOutputs outputs := by
  unfold lowerScalarOutputs
  rw [List.forIn_cons]
  simp only [bind_assoc, pure_bind]
  simp [lowerScalarOutput]

private theorem lowerScalarOutput_preservesOutputCapacityFrame (output : Output)
    (admission : ScalarExpression output.value) :
    Zkir.PreservesOutputCapacityFrame (lowerScalarOutput output) := by
  unfold lowerScalarOutput
  apply Zkir.bind_preservesOutputCapacityFrame _ _
    (lowerExpr_admitted_preservesOutputCapacityFrame output.value admission)
  intro text
  exact Zkir.modify_preservesOutputCapacityFrame _ (fun _ => rfl) (fun _ => rfl)

private theorem lowerScalarOutputs_preservesOutputCapacityFrame (outputs : List Output)
    (admitted : ∀ output ∈ outputs, ScalarExpression output.value) :
    Zkir.PreservesOutputCapacityFrame (lowerScalarOutputs outputs) := by
  unfold lowerScalarOutputs
  apply Zkir.forIn_preservesOutputCapacityFrame_of_mem
  intro output member _
  exact lowerScalarOutput_preservesOutputCapacityFrame output (admitted output member)

private theorem evalOutput_ok (ctx : EvalContext) (values : EvalEnv)
    (output : Output) (pair : String × Value)
    (accepted : evalOutput ctx values output = .ok pair) :
    ∃ value, output.value.eval ctx values = .ok value ∧
      pair = (output.name, Value.pack output.ty value) := by
  unfold evalOutput at accepted
  simp only [bind_ok] at accepted
  rcases accepted with ⟨value, evaluated, produced⟩
  cases produced
  exact ⟨value, evaluated, rfl⟩

theorem evalOutputs_names (ctx : EvalContext) (values : EvalEnv)
    (outputs : List Output) (results : List (String × Value))
    (accepted : outputs.mapM (evalOutput ctx values) = .ok results) :
    results.map Prod.fst = outputs.map Output.name := by
  induction outputs generalizing results with
  | nil =>
    simp only [List.mapM_nil, pure, Except.pure, Except.ok.injEq] at accepted
    subst results
    rfl
  | cons output outputs ih =>
    rw [List.mapM_cons] at accepted
    simp only [bind_ok] at accepted
    obtain ⟨pair, outputAccepted, tailResults, tailAccepted, resultShape⟩ := accepted
    cases resultShape
    obtain ⟨value, _, pairShape⟩ := evalOutput_ok ctx values output pair outputAccepted
    cases pairShape
    simp [ih tailResults tailAccepted]

private theorem lookup_reverse_of_nodup_keys {α : Type} (values : List (String × α))
    (keys : (values.map Prod.fst).Nodup) (name : String) :
    values.reverse.lookup name = values.lookup name := by
  induction values with
  | nil => rfl
  | cons pair rest ih =>
    rcases pair with ⟨key, value⟩
    obtain ⟨fresh, restNodup⟩ := List.nodup_cons.mp keys
    by_cases found : name == key
    · have reverseRestNone : rest.reverse.lookup name = none := by
        apply List.lookup_eq_none_iff.mpr
        intro item member
        simp only [List.mem_reverse] at member
        have keyDifferent : (key != item.1) = true := by
          have unequal : (key == item.1) = false := by
            cases checked : (key == item.1) with
            | false => rfl
            | true =>
              have same := beq_iff_eq.mp checked
              apply False.elim
              apply fresh
              apply List.mem_map.mpr
              exact ⟨item, member, same.symm⟩
          simp [bne_eq, unequal]
        have nameEq : name = key := beq_iff_eq.mp found
        rw [nameEq]
        exact keyDifferent
      simp only [List.reverse_cons]
      change (rest.reverse ++ [(key, value)]).lookup name = ((key, value) :: rest).lookup name
      rw [List.lookup_append, reverseRestNone]
      simp [List.lookup_cons, found]
    · simp only [List.reverse_cons]
      change (rest.reverse ++ [(key, value)]).lookup name = ((key, value) :: rest).lookup name
      rw [List.lookup_append, ih restNodup]
      simp [List.lookup_cons, found]

private theorem lookup_results_reverse_eq {α : Type} (results : List (String × α))
    (current : List (String × α))
    (keys : (results.map Prod.fst).Nodup) (name : String) :
    (results.reverse ++ current).lookup name = (results ++ current).lookup name := by
  rw [List.lookup_append, List.lookup_append,
    lookup_reverse_of_nodup_keys results keys name]

private theorem stateRunBind {α β} (first : StateM Zkir.LowerState α)
    (next : α → StateM Zkir.LowerState β) (state : Zkir.LowerState) :
    (do let value ← first; next value).run state =
      (next (first.run state).1).run (first.run state).2 := rfl

/-- Lowering the production output fold keeps both alias relations in step.
The normalizer and lowerer prepend each output, so the downstream value
environment uses `results.reverse ++ currentValues`. Source evaluation stays
on `originalValues` for every output. -/
private theorem lowerScalarOutputs_complete (ctx : EvalContext) (hash : Hash)
    (implementation : HashAgreement ctx hash) (inputs : NativeRelation.Assignment)
    (originalValues currentValues : EvalEnv) (outputs : List Output)
    (frame finalFrame : GenericStateCircuitParts.OutputFrame)
    (results : List (String × Value)) (witness : NativeRelation.Assignment)
    (state : Zkir.LowerState)
    (scalarAdmission : ∀ output ∈ outputs,
      ∃ _scalarType : ScalarType output.ty, ScalarExpression output.value)
    (types : TypeEnv)
    (outputValidation : ∀ output ∈ outputs,
      output.value.validate Capabilities.crypto types = .ok ())
    (source : outputs.mapM (evalOutput ctx originalValues) = .ok results)
    (normalized : GenericStateCircuitParts.outputFold frame outputs = .ok finalFrame)
    (namesNodup : (outputs.map Output.name).Nodup)
    (forbiddenNames : List String)
    (outputNamesForbidden : ∀ output ∈ outputs, output.name ∈ forbiddenNames)
    (originalUnused : ∀ output ∈ outputs, originalValues.lookup output.name = none)
    (currentUnused : ∀ output ∈ outputs, currentValues.lookup output.name = none)
    (sourceAgreement : AliasAgreement hash inputs frame.1 originalValues)
    (currentAgreement : AliasAgreement hash inputs frame.1 currentValues)
    (sourceLowerAgreement : LowerAliasAgreement hash inputs witness frame.1 state.aliases originalValues)
    (currentLowerAgreement : LowerAliasAgreement hash inputs witness frame.1 state.aliases currentValues)
    (meaning : LowerStateMeaning hash witness state)
    (budget : (lowerScalarOutputs outputs).run state |>.2.next ≤
      Native.maxInstructions * Native.maxVectorLength) :
    ∃ finalWitness,
      LowerStateMeaning hash finalWitness ((lowerScalarOutputs outputs).run state).2 ∧
      (∀ name, InScope state.next name → finalWitness name = witness name) ∧
      AliasAgreement hash inputs finalFrame.1 originalValues ∧
      LowerAliasAgreement hash inputs finalWitness finalFrame.1
        ((lowerScalarOutputs outputs).run state).2.aliases originalValues ∧
      AliasAgreement hash inputs finalFrame.1 (results.reverse ++ currentValues) ∧
      LowerAliasAgreement hash inputs finalWitness finalFrame.1
        ((lowerScalarOutputs outputs).run state).2.aliases
        (results.reverse ++ currentValues) ∧
      (∀ name, name ∉ forbiddenNames → state.aliases.lookup name = none →
        ((lowerScalarOutputs outputs).run state).2.aliases.lookup name = none) := by
  induction outputs generalizing frame finalFrame results currentValues witness state with
  | nil =>
    simp only [List.mapM_nil, pure, Except.pure, Except.ok.injEq] at source
    subst results
    simp only [GenericStateCircuitParts.outputFold_nil, Except.ok.injEq] at normalized
    subst finalFrame
    refine ⟨witness, meaning, ?_, sourceAgreement, sourceLowerAgreement,
      currentAgreement, currentLowerAgreement, ?_⟩
    · intro name _
      rfl
    · intro name _ originalAbsent
      have runNil : (lowerScalarOutputs ([] : List Output)).run state = ((), state) := by
        rfl
      rw [runNil]
      exact originalAbsent
  | cons output outputs ih =>
    have outputMember : output ∈ output :: outputs := by simp
    have outputForbidden := outputNamesForbidden output outputMember
    obtain ⟨scalarType, expressionAdmission⟩ := scalarAdmission output outputMember
    have outputValid := outputValidation output outputMember
    rw [List.mapM_cons] at source
    simp only [bind_ok] at source
    obtain ⟨pair, outputAccepted, tailResults, tailAccepted, resultShape⟩ := source
    cases resultShape
    obtain ⟨sourceValue, sourceEvaluation, pairShape⟩ :=
      evalOutput_ok ctx originalValues output pair outputAccepted
    subst pair
    rw [GenericStateCircuitParts.outputFold_cons] at normalized
    change (GenericStateCircuitParts.appendOutput output frame >>= fun next =>
      GenericStateCircuitParts.outputFold next outputs) = .ok finalFrame at normalized
    simp only [bind_ok] at normalized
    obtain ⟨middle, first, later⟩ := normalized
    unfold GenericStateCircuitParts.appendOutput at first
    simp only [bind_ok] at first
    obtain ⟨normal, normalAccepted, appended⟩ := first
    let nextFrame : GenericStateCircuitParts.OutputFrame :=
      ((output.name, normal.term) :: frame.1,
        frame.2.1 ++ normal.bounds, frame.2.2 ++ normal.assertions)
    have middleEq : nextFrame = middle := (Except.ok.inj appended)
    rw [← middleEq] at later
    have normalAccepted' := normalizeOutput_ok frame.1 output normal normalAccepted
    let expressionOperation := Zkir.lowerExpr output.value
    let expressionFrame :=
      lowerExpr_admitted_preservesOutputCapacityFrame output.value expressionAdmission
    let firstOperation := lowerScalarOutput output
    let afterFirst := (firstOperation.run state).2
    have firstRun : firstOperation.run state =
        ((), { (expressionOperation.run state).2 with
          aliases := (output.name, (expressionOperation.run state).1) ::
            (expressionOperation.run state).2.aliases }) := by
      unfold firstOperation lowerScalarOutput expressionOperation
      rw [stateRunBind]
      rfl
    have sameNext : (expressionOperation.run state).2.next = afterFirst.next := by
      have equal := congrArg (fun result : Unit × Zkir.LowerState => result.2.next) firstRun
      simpa [afterFirst] using equal.symm
    have tailAdmission : ∀ item ∈ outputs, ScalarExpression item.value := by
      intro item member
      obtain ⟨_, supported⟩ := scalarAdmission item (List.mem_cons_of_mem _ member)
      exact supported
    have tailFrame := lowerScalarOutputs_preservesOutputCapacityFrame outputs tailAdmission
    have fullBudget : ((lowerScalarOutputs outputs).run afterFirst).2.next ≤
        Native.maxInstructions * Native.maxVectorLength := by
      rw [lowerScalarOutputs_cons] at budget
      change ((lowerScalarOutputs outputs).run afterFirst).2.next ≤ _ at budget
      exact budget
    have expressionBudget : (expressionOperation.run state).2.next ≤
        Native.maxInstructions * Native.maxVectorLength := by
      rw [sameNext]
      exact Nat.le_trans (tailFrame afterFirst).next fullBudget
    obtain ⟨step⟩ := (lowerExpr_complete output.value expressionAdmission)
      ctx hash implementation inputs witness state frame.1 originalValues types sourceValue
      outputValid sourceEvaluation sourceAgreement sourceLowerAgreement meaning expressionBudget
    have headRun : firstOperation.run state =
        ((), {step.finalState with aliases := (output.name, step.text) :: state.aliases}) := by
      rw [firstRun, step.run]
      simp [step.aliasesPreserved]
    have operationRun : (lowerScalarOutputs (output :: outputs)).run state =
        (lowerScalarOutputs outputs).run
          {step.finalState with aliases := (output.name, step.text) :: state.aliases} := by
      rw [lowerScalarOutputs_cons, stateRunBind, headRun]
    have stepMeaning : LowerStateMeaning hash step.finalWitness
        {step.finalState with aliases := (output.name, step.text) :: state.aliases} := by
      apply LowerStateMeaning.withAliases hash step.finalWitness step.finalState
        step.stateMeaning _
      intro name text member
      simp only [List.mem_cons] at member
      rcases member with same | old
      · cases same
        exact step.textScope
      · have oldMember : (name, text) ∈ step.finalState.aliases := by
          simpa [step.aliasesPreserved] using old
        exact step.stateMeaning.aliases name text oldMember
    have represented : Represents hash inputs output.ty step.normalized sourceValue :=
      step.represents
    obtain ⟨stepCanonical, stepRequirements, normalizedMeaning⟩ := represented
    have sameNormalized : step.normalized = normal := by
      exact (Except.ok.inj (step.normalization.symm.trans normalAccepted'))
    subst normal
    have sourceAgreementNext : AliasAgreement hash inputs nextFrame.1 originalValues := by
      simpa [nextFrame] using GenericStateAliases.aliasAgreement_cons_unused hash inputs
        frame.1 originalValues output.name step.normalized.term sourceAgreement
        (originalUnused output (by simp))
    have currentAgreementNext : AliasAgreement hash inputs nextFrame.1
        ((output.name, Value.pack output.ty sourceValue) :: currentValues) := by
      simpa [nextFrame] using ScalarNormalization.aliasAgreement_cons hash inputs
        frame.1 currentValues output.name output.ty sourceValue step.normalized.term
        currentAgreement stepCanonical normalizedMeaning
    have sourceLowerAgreementNext : LowerAliasAgreement hash inputs step.finalWitness
        nextFrame.1 ({step.finalState with aliases := (output.name, step.text) :: state.aliases}).aliases
          originalValues := by
      have stepSourceLower : LowerAliasAgreement hash inputs step.finalWitness frame.1
          state.aliases originalValues := by
        simpa [step.aliasesPreserved] using step.aliasAgreement
      simpa [nextFrame, step.aliasesPreserved] using lowerAliasAgreement_cons_unused
        hash inputs step.finalWitness frame.1 state.aliases originalValues output.name
        step.normalized.term step.text stepSourceLower
        (originalUnused output (by simp))
    have currentLowerAfterExpression : LowerAliasAgreement hash inputs step.finalWitness
        frame.1 state.aliases currentValues := by
      exact LowerAliasAgreement.of_frame hash inputs witness step.finalWitness state.next
        frame.1 state.aliases currentValues currentLowerAgreement
        (by intro name text member; exact meaning.aliases name text member)
        step.frame
    have currentLowerAgreementNext : LowerAliasAgreement hash inputs step.finalWitness
        nextFrame.1 ({step.finalState with aliases := (output.name, step.text) :: state.aliases}).aliases
          ((output.name, Value.pack output.ty sourceValue) :: currentValues) := by
      simpa [nextFrame, step.aliasesPreserved] using LowerAliasAgreement.cons hash inputs
        step.finalWitness frame.1 state.aliases currentValues output.name output.ty sourceValue
        step.normalized.term step.text currentLowerAfterExpression step.operandMeaning
    have tailNamesNodup : (outputs.map Output.name).Nodup := (List.nodup_cons.mp namesNodup).2
    have tailOutputNamesForbidden : ∀ item ∈ outputs, item.name ∈ forbiddenNames := by
      intro item member
      exact outputNamesForbidden item (List.mem_cons_of_mem _ member)
    have outputFreshTail : output.name ∉ outputs.map Output.name :=
      (List.nodup_cons.mp namesNodup).1
    have currentUnusedTail : ∀ item ∈ outputs,
        ((output.name, Value.pack output.ty sourceValue) :: currentValues).lookup item.name = none := by
      intro item member
      have oldUnused := currentUnused item (List.mem_cons_of_mem _ member)
      have different : (item.name == output.name) = false := by
        apply Bool.eq_false_iff.mpr
        intro same
        exact outputFreshTail (List.mem_map.mpr ⟨item, member, beq_iff_eq.mp same⟩)
      simp [List.lookup_cons, different, oldUnused]
    have outputUnusedTail : ∀ item ∈ outputs, originalValues.lookup item.name = none := by
      intro item member
      exact originalUnused item (List.mem_cons_of_mem _ member)
    have tailBudget : (lowerScalarOutputs outputs).run
          {step.finalState with aliases := (output.name, step.text) :: state.aliases} |>.2.next ≤
        Native.maxInstructions * Native.maxVectorLength := by
      change (lowerScalarOutputs outputs).run
        {step.finalState with aliases := (output.name, step.text) :: state.aliases} |>.2.next ≤ _
      rw [← operationRun]
      exact budget
    obtain ⟨finalWitness, finalMeaning, finalFrame, finalSource, finalSourceLower,
      finalCurrent, finalCurrentLower, finalAbsent⟩ := ih
        (frame := nextFrame) (finalFrame := finalFrame) (results := tailResults)
        (currentValues := (output.name, Value.pack output.ty sourceValue) :: currentValues)
        (witness := step.finalWitness)
        (state := {step.finalState with aliases := (output.name, step.text) :: state.aliases})
        (scalarAdmission := fun item member => scalarAdmission item (List.mem_cons_of_mem _ member))
        (outputValidation := fun item member => outputValidation item (List.mem_cons_of_mem _ member))
        (source := tailAccepted) (normalized := later) (namesNodup := tailNamesNodup)
        (outputNamesForbidden := tailOutputNamesForbidden)
        (originalUnused := outputUnusedTail) (currentUnused := currentUnusedTail)
        (sourceAgreement := sourceAgreementNext) (currentAgreement := currentAgreementNext)
        (sourceLowerAgreement := sourceLowerAgreementNext)
        (currentLowerAgreement := currentLowerAgreementNext) (meaning := stepMeaning)
        (budget := tailBudget)
    refine ⟨finalWitness, ?_, ?_, finalSource, ?_, ?_, ?_, ?_⟩
    · rw [operationRun]
      exact finalMeaning
    · intro name scope
      have nextMono : state.next ≤ step.finalState.next := by
        simpa [step.run] using (expressionFrame state).next
      exact (finalFrame name (InScope.mono nextMono scope)).trans (step.frame name scope)
    · rw [operationRun]
      exact finalSourceLower
    · simpa [List.reverse_cons, List.append_assoc] using finalCurrent
    · rw [operationRun]
      simpa [List.reverse_cons, List.append_assoc] using finalCurrentLower
    · intro name notForbidden originalAbsent
      have outputDifferent : (name == output.name) = false := by
        have unequal : name ≠ output.name := by
          intro same
          subst name
          exact notForbidden outputForbidden
        simp [unequal]
      have afterHeadAbsent :
          ({step.finalState with aliases := (output.name, step.text) :: state.aliases}).aliases.lookup name = none := by
        simp [List.lookup_cons, outputDifferent, originalAbsent]
      rw [operationRun]
      exact finalAbsent name notForbidden afterHeadAbsent

private theorem lowerEntrypointAliases_eq_scalarOutputs (entry : Entrypoint)
    (admitted : ∀ output ∈ entry.circuit.outputs,
      ∃ _scalarType : ScalarType output.ty, ScalarExpression output.value) :
    Zkir.lowerEntrypointAliases entry = lowerScalarOutputs entry.circuit.outputs := by
  unfold Zkir.lowerEntrypointAliases lowerScalarOutputs
  change List.forIn' (m := StateM Zkir.LowerState) _ _ _ =
    List.forIn' (m := StateM Zkir.LowerState) _ _ _
  apply List.forIn'_congr rfl rfl
  intro output member accumulator
  obtain ⟨scalarType, _⟩ := admitted output member
  cases output with
  | mk name ty value span =>
    cases scalarType <;> rfl

/-- The admitted scalar entrypoint aliases have the exact production run,
including the accumulated output aliases consumed by later ledger lowering. -/
theorem lowerEntrypointAliases_complete (ctx : EvalContext) (hash : Hash)
    (implementation : HashAgreement ctx hash) (entry : Entrypoint)
    (plan : Backend.Impact.Plan) (values : EvalEnv) (results : List (String × Value))
    (inputs witness : NativeRelation.Assignment) (state : Zkir.LowerState)
    (outputFrame : GenericStateCircuitParts.OutputFrame)
    (admitted : CanonicalInputs entry.circuit values inputs)
    (scalarAdmission : ScalarCircuitAdmission entry.circuit)
    (types : TypeEnv)
    (outputValidation : ∀ output ∈ entry.circuit.outputs,
      output.value.validate Capabilities.crypto types = .ok ())
    (outputNamesNodup : (entry.circuit.outputs.map Output.name).Nodup)
    (outputNameFresh : ∀ output ∈ entry.circuit.outputs,
      values.lookup output.name = none)
    (source : entry.circuit.outputs.mapM (evalOutput ctx values) = .ok results)
    (normalized : GenericStateCircuitParts.normalizeOutputs
      (entrypointSeedAliases entry plan) entry.circuit.outputs = .ok outputFrame)
    (sourceLowerAgreement : LowerAliasAgreement hash inputs witness
      (entrypointSeedAliases entry plan) state.aliases values)
    (meaning : LowerStateMeaning hash witness state)
    (budget : (Zkir.lowerEntrypointAliases entry).run state |>.2.next ≤
      Native.maxInstructions * Native.maxVectorLength) :
    ∃ finalWitness,
      LowerStateMeaning hash finalWitness
        ((Zkir.lowerEntrypointAliases entry).run state).2 ∧
      (∀ name, InScope state.next name → finalWitness name = witness name) ∧
      AliasAgreement hash inputs outputFrame.1 values ∧
      LowerAliasAgreement hash inputs finalWitness outputFrame.1
        ((Zkir.lowerEntrypointAliases entry).run state).2.aliases values ∧
      AliasAgreement hash inputs outputFrame.1 (results ++ values) ∧
      LowerAliasAgreement hash inputs finalWitness outputFrame.1
        ((Zkir.lowerEntrypointAliases entry).run state).2.aliases
        (results ++ values) ∧
      (∀ name, name ∉ entry.circuit.outputs.map Output.name →
        state.aliases.lookup name = none →
        ((Zkir.lowerEntrypointAliases entry).run state).2.aliases.lookup name = none) := by
  let seed := entrypointSeedAliases entry plan
  let initialFrame : GenericStateCircuitParts.OutputFrame := (seed, [], [])
  have sourceAgreement : AliasAgreement hash inputs seed values :=
    (entrypointSeedAliases_typedEnvironment entry plan hash values inputs admitted).aliases
  have scalarOutputs : ∀ output ∈ entry.circuit.outputs,
      ∃ scalarType : ScalarType output.ty, ScalarExpression output.value := by
    intro output member
    exact scalarAdmission.outputs output member
  have runEq := lowerEntrypointAliases_eq_scalarOutputs entry scalarOutputs
  have normalizedFold : GenericStateCircuitParts.outputFold initialFrame
      entry.circuit.outputs = .ok outputFrame := by
    simpa [initialFrame, seed, GenericStateCircuitParts.normalizeOutputs] using normalized
  have helperBudget : (lowerScalarOutputs entry.circuit.outputs).run state |>.2.next ≤
      Native.maxInstructions * Native.maxVectorLength := by
    simpa [runEq] using budget
  have resultNames := evalOutputs_names ctx values entry.circuit.outputs results source
  have resultNamesNodup : (results.map Prod.fst).Nodup := by
    rw [resultNames]
    exact outputNamesNodup
  obtain ⟨finalWitness, finalMeaning, finalFrame, finalSource, finalSourceLower,
    finalCurrentReverse, finalCurrentLowerReverse, finalAbsent⟩ := lowerScalarOutputs_complete ctx hash implementation
      inputs values values entry.circuit.outputs initialFrame outputFrame results witness state
      scalarOutputs types outputValidation source normalizedFold outputNamesNodup
      (entry.circuit.outputs.map Output.name)
      (fun output member => List.mem_map.mpr ⟨output, member, rfl⟩)
      outputNameFresh
      outputNameFresh sourceAgreement sourceAgreement sourceLowerAgreement sourceLowerAgreement
      meaning helperBudget
  have lookupOrder (name : String) :=
    lookup_results_reverse_eq results values resultNamesNodup name
  have finalCurrent : AliasAgreement hash inputs outputFrame.1 (results ++ values) := by
    intro name ty raw value lookup typed
    have reverseLookup : (results.reverse ++ values).lookup name = some raw := by
      rw [lookupOrder name]
      exact lookup
    exact finalCurrentReverse name ty raw value reverseLookup typed
  have finalCurrentLower : LowerAliasAgreement hash inputs finalWitness outputFrame.1
      ((lowerScalarOutputs entry.circuit.outputs).run state).2.aliases (results ++ values) := by
    intro name ty raw value lookup typed
    have reverseLookup : (results.reverse ++ values).lookup name = some raw := by
      rw [lookupOrder name]
      exact lookup
    exact finalCurrentLowerReverse name ty raw value reverseLookup typed
  refine ⟨finalWitness, ?_, finalFrame, finalSource, ?_, finalCurrent, ?_, ?_⟩
  · simpa [runEq] using finalMeaning
  · simpa [runEq] using finalSourceLower
  · simpa [runEq] using finalCurrentLower
  · simpa [runEq] using finalAbsent

end Noctium.Verification.ScalarWitnessConstruction
