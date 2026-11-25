import Noctium.Verification.ScalarCellCallNativeRun
import Noctium.Verification.ScalarCellSoundnessRequirements
import Noctium.Verification.ScalarCellSoundnessScope
import Noctium.Verification.ScalarStateSoundness

namespace Noctium.Verification.ScalarCellNativeTranscript

open Lean Backend NativeRelation NativeRelationJson NativeState ScalarNormalization
open GenericStateEffectValidation GenericStateInputValues
open GenericStatePrefixEnvironment
open ScalarLowering ScalarWitnessConstruction ScalarLedgerWitnessPreflight
open ScalarCellSourceReads
open ScalarValidationOpcodeProfile (checkedScalarOpcodeProfile)

/-- From a successful admitted unguarded scalar-cell call, construct a
satisfying witness for the decoded default ZKIR and run the accepted Impact
plan in the VM model. Its ordered groups match the circuit, and its encoded
successor and decoded circuit returns match the original source call. -/
theorem lowerEntrypoint_checked_native_transcript
    (ctx : EvalContext) (hash : Hash) (implementation : HashAgreement ctx hash)
    (declarations : List StateDecl) (entry : Entrypoint) (plan : Impact.Plan)
    (values result : EvalEnv) (initial next : LedgerState)
    (inputs : NativeRelation.Assignment) (initialSlots : List Slot)
    {json : Json} {call : ScalarCall}
    (lowered : Zkir.lowerEntrypoint declarations entry = .ok json)
    (decoded : decodeScalarCall json = .ok call)
    (planAccepted : Impact.lower declarations (Passes.pruneEntrypoint entry) = .ok plan)
    (profile : checkedScalarOpcodeProfile
      (defaultEntrypointRows entry plan).toList.zipIdx call.body.instructions = true)
    (admittedInputs : CanonicalInputs entry.circuit values inputs)
    (circuitAdmission : ScalarCircuitAdmission entry.circuit)
    (returnScope : ∀ output ∈ entry.returns,
      ∃ _ : ScalarType output.ty, ScalarExpression output.value)
    (unguarded : entry.effectGuards = [])
    (cellScope : ScalarCellEffects declarations entry.effects)
    (cellOperands : ∀ effect ∈ entry.effects, ScalarCellOperand effect)
    (admittedState : GenericStateEncoding.AdmittedState declarations initial initialSlots)
    (success : entry.run ctx values initial = .ok (result, next)) :
    ∃ expected outputs finalEnv entries witness readValues native finalSlots
      stateFinalTypes returned,
      Native.expectedEntrypoint declarations (Passes.pruneEntrypoint entry) = .ok expected ∧
      entry.circuit.run ctx values = .ok outputs ∧
      sourceReadInputs ctx entry.effects (Impact.publicInputReadCount entry.circuit.inputs)
        (outputs ++ values,
          {initial with unshieldedInputs := [], unshieldedOutputs := [], unshieldedSpendClaims := []}) =
        .ok (entries, (finalEnv, next)) ∧
      (∀ input ∈ entry.circuit.inputs,
        witness ("%input_" ++ input.name) = inputs ("%input_" ++ input.name)) ∧
      CircuitSatisfies hash call.body
        ⟨ScalarValidatedProgram.inputValues expected .public
            (ScalarCellWitnessReadSeed.seedReadValues inputs entries),
          ScalarValidatedProgram.inputValues expected .private
            (ScalarCellWitnessReadSeed.seedReadValues inputs entries)⟩
        witness (call.body.groups witness) ∧
      call.arguments.map witness = expected.rawInputs.map
        (fun input => ScalarCellWitnessReadSeed.seedReadValues inputs entries input.identifier) ∧
      decodeReads (plan.reads.drop (Impact.publicInputReadCount entry.circuit.inputs))
        witness = .ok readValues ∧
      GenericStateOps.evalPlan ctx ((outputs ++ values) ++ readValues) plan = .ok native ∧
      NativeState.run native (GenericStateEncoding.initial initialSlots) =
        some ⟨[.vector finalSlots],
          ScalarCellNativePublicPrefix.sourcePublicCells entry.circuit.inputs inputs ++
            ScalarCellNativeTrace.tapeCells entries⟩ ∧
      ValidatedEffects declarations
        (initialEffectTypeEnv (Passes.pruneEntrypoint entry)) entry.effects stateFinalTypes ∧
      runEffectsWithGuardsAndEnv ctx entry.effects entry.effectGuards (outputs ++ values)
        {initial with unshieldedInputs := [], unshieldedOutputs := [], unshieldedSpendClaims := []} =
        .ok (finalEnv, next) ∧
      GenericStatePrefixEnvironment.AgreesOnTypes stateFinalTypes finalEnv
        ((outputs ++ values) ++ readValues) ∧
      GenericStateEncoding.encodeState declarations next = some finalSlots ∧
      call.body.groups witness = NativeState.groups native ∧
      Entrypoint.evalReturns ctx entry finalEnv = .ok returned ∧
      result = outputs ++ returned ∧
      call.body.returns witness = returned.map (fun binding => scalar (valueNumber binding.2)) := by
  have requirements (expected : Native.Expected)
      (accepted : Native.expectedEntrypoint declarations (Passes.pruneEntrypoint entry) =
        .ok expected) :=
    ScalarCellSoundnessRequirements.accepted_scalar_cell_soundness_requirements
      declarations entry plan expected values inputs planAccepted accepted admittedInputs
      unguarded cellScope
  obtain ⟨effectScope, effectOperands, plainReads⟩ :=
    ScalarCellSoundnessScope.lowerEntrypoint_premises declarations entry plan planAccepted
      unguarded cellScope cellOperands
  have compatible := ScalarCellPublicFields.canonical_inputs_scalar_compatible
    entry.circuit values inputs admittedInputs
  have admittedPlan := ScalarCellPlanAdmission.lower_admission declarations
    (Passes.pruneEntrypoint entry) plan planAccepted unguarded compatible cellScope
    cellOperands returnScope
  obtain ⟨jsonPlan, _, planFromJson, _, _, actualRows⟩ :=
    Zkir.lowerEntrypoint_validation_and_instructions declarations entry json lowered
  have samePlan := Except.ok.inj (planFromJson.symm.trans planAccepted)
  cases samePlan
  have rowsParsed : Native.arrayField json "instructions" =
      .ok (defaultEntrypointRows entry plan) := by
    simpa [defaultEntrypointRows] using actualRows
  let rows := defaultEntrypointRows entry plan
  obtain ⟨expected, outputs, finalEnv, entries, witness, readValues, native, finalSlots,
      expectedAccepted, circuitRun, sourceTape, bindings, satisfies, arguments,
      readDecoded, planEvaluated, stateEncoded, nativeRun⟩ :=
    ScalarCellNativeTrace.lowerEntrypoint_construct_scalar_cell_execution
      ctx hash implementation declarations entry plan values result initial next inputs initialSlots
      lowered decoded planAccepted profile admittedInputs circuitAdmission returnScope
      unguarded cellScope cellOperands admittedState success
  have witnessInputs : CanonicalInputs entry.circuit values witness := by
    refine ⟨admittedInputs.unique, admittedInputs.declared, admittedInputs.complete, ?_⟩
    intro input member value found canonical
    rw [bindings input member]
    exact admittedInputs.binding input member value found canonical
  have unguardedAll : entry.effectGuards.all Option.isNone = true := by
    simp [unguarded]
  have outputEvaluation : entry.circuit.outputs.mapM (evalOutput ctx values) = .ok outputs :=
    (circuit_run_steps ctx entry.circuit values outputs circuitRun).2
  have planEvaluatedRight :
      GenericStateOps.evalPlan ctx (outputs ++ (values ++ readValues)) plan = .ok native := by
    simpa [List.append_assoc] using planEvaluated
  have evaluated : (do
      let outputs ← entry.circuit.outputs.mapM (evalOutput ctx values)
      let reads ← decodeReads
        (plan.reads.drop (Impact.publicInputReadCount entry.circuit.inputs)) witness
      GenericStateOps.evalPlan ctx ((outputs ++ values) ++ reads) plan) = .ok native := by
    simp [outputEvaluation, readDecoded, planEvaluatedRight, Bind.bind, Except.bind]
  let final : NativeState.Machine := ⟨[.vector finalSlots],
    ScalarCellNativePublicPrefix.sourcePublicCells entry.circuit.inputs inputs ++
      ScalarCellNativeTrace.tapeCells entries⟩
  have checked : NativeState.run native (GenericStateEncoding.initial initialSlots) = some final :=
    nativeRun
  obtain ⟨stateOutputs, stateReads, stateFinalEnv, stateFinalTypes, stateNext,
      stateFinalSlots, stateFinalReads, stateCircuitRun, stateReadDecoded,
      effectsValidated, effectsEvaluated, _, _, agreement,
      groupAndReturnExact⟩ :=
    ScalarStateSoundness.lowerEntrypoint_checked_state
      declarations entry .disabled ctx hash implementation values witness
      ⟨ScalarValidatedProgram.inputValues expected .public
          (ScalarCellWitnessReadSeed.seedReadValues inputs entries),
        ScalarValidatedProgram.inputValues expected .private
          (ScalarCellWitnessReadSeed.seedReadValues inputs entries)⟩
      (call.body.groups witness) json call rows plan initial initialSlots native final
      lowered decoded rowsParsed profile satisfies planAccepted
      (fun expected accepted => (requirements expected accepted).1) witnessInputs
      circuitAdmission unguardedAll effectScope effectOperands plainReads admittedPlan.planGuards
      admittedState evaluated checked
  have sameOutputs : stateOutputs = outputs := Except.ok.inj (stateCircuitRun.symm.trans circuitRun)
  subst stateOutputs
  have sameReads : stateReads = readValues := Except.ok.inj (stateReadDecoded.symm.trans readDecoded)
  subst stateReads
  obtain ⟨groupExact, sourceRun, returnExact⟩ := groupAndReturnExact
  have exactGroups : call.body.groups witness = NativeState.groups native :=
    groupExact (fun expected accepted => (requirements expected accepted).2)
      (ScalarCellPlanAdmission.admitted_operation_fields admittedPlan)
  obtain ⟨returned, returnedRun, returnedExact⟩ := returnExact returnScope
  have resultStateEq : (outputs ++ returned, stateNext) = (result, next) :=
    Except.ok.inj (returnedRun.symm.trans success)
  have resultShape : result = outputs ++ returned := by
    exact (congrArg Prod.fst resultStateEq).symm
  have nextShape : stateNext = next := congrArg Prod.snd resultStateEq
  subst stateNext
  have sourceFold := ScalarCellSourceReads.sourceReadInputs_frame ctx entry.effects
    (Impact.publicInputReadCount entry.circuit.inputs)
    (outputs ++ values,
      {initial with unshieldedInputs := [], unshieldedOutputs := [], unshieldedSpendClaims := []})
    (finalEnv, next) entries sourceTape
  have sourceEffects : runEffectsWithGuardsAndEnv ctx entry.effects entry.effectGuards
      (outputs ++ values)
      {initial with unshieldedInputs := [], unshieldedOutputs := [], unshieldedSpendClaims := []} =
      .ok (finalEnv, next) := by
    simpa [unguarded, runEffectsWithGuardsAndEnv, SourceEffects.runEffectsWithEnv_eq_fold]
      using sourceFold
  have sameSourceFrame : (stateFinalEnv, next) = (finalEnv, next) :=
    Except.ok.inj (effectsEvaluated.symm.trans sourceEffects)
  have envEq : stateFinalEnv = finalEnv := congrArg Prod.fst sameSourceFrame
  subst stateFinalEnv
  have returnedEvaluation : Entrypoint.evalReturns ctx entry finalEnv = .ok returned := by
    rw [sourceRun] at returnedRun
    cases evalReturnsResult : Entrypoint.evalReturns ctx entry finalEnv with
    | error message => simp [evalReturnsResult, Bind.bind, Except.bind] at returnedRun
    | ok sourceValues =>
      have pairEq : (outputs ++ sourceValues, next) = (outputs ++ returned, next) := by
        simpa [evalReturnsResult, Bind.bind, Except.bind, Pure.pure, Except.pure]
          using returnedRun
      have returnsEq : sourceValues = returned := by
        apply List.append_cancel_left
        exact congrArg Prod.fst pairEq
      simp [returnsEq]
  exact ⟨expected, outputs, finalEnv, entries, witness, readValues, native, finalSlots,
    stateFinalTypes, returned, expectedAccepted, circuitRun, sourceTape, bindings,
    satisfies, arguments,
    readDecoded, planEvaluated, nativeRun, effectsValidated, effectsEvaluated,
    agreement, stateEncoded, exactGroups, returnedEvaluation,
    resultShape, returnedExact⟩

end Noctium.Verification.ScalarCellNativeTranscript
