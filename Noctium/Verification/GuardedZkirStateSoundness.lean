import Noctium.Verification.GuardedZkirPlanSoundness
import Noctium.Verification.GuardedStateEffectFold
import Noctium.Verification.GuardedStatementConsumption
import Noctium.Verification.GuardedSourceActivity
import Noctium.Verification.ImpactPlanStatementAgreement

namespace Noctium.Verification.GuardedZkirStateSoundness
open Lean Backend NativeRelation ScalarNormalization
open GenericStateEffectValidation GenericStatePrefixEnvironment
open GenericStateCircuitParts GenericStateInputValues GenericStateCheckedReadTrace
open GenericStateEffectStep
open GuardedImpactTranscript

/-- Checked guarded ZKIR consumes the public streams of the same modeled VM
run whose operation order and activity agree with the Impact bytes. Inactive
and active group widths follow from the validated source plan. The guarded
payload follows from the modeled VM transcript. For accepted native call
metadata, the Impact preview derives the header used for the ZKIR public
instance. Metadata and ordinary circuit satisfaction remain input evidence. -/
theorem lowerEntrypoint_checked_guarded_state
    (state : List StateDecl) (sourceEntry : Entrypoint) (rewrites : Zkir.Rewrites)
    (ctx : EvalContext) (hash : Hash) (implementation : HashAgreement ctx hash)
    (assignment : Assignment) (zkirBytes : ArtifactBytes.Bytes) (json : Json)
    (rows : List GuardedScalarRows.Row) (plan : Impact.Plan) (expected : Native.Expected)
    (frame : OutputFrame) (base decoded : EvalEnv)
    (initial : LedgerState) (slots : List NativeState.Slot)
    (native : List NativeState.Op) (final : NativeState.Machine)
    (lowered : Zkir.lowerEntrypoint state sourceEntry rewrites = .ok json)
    (artifactChecked : GuardedZkirArtifact.check zkirBytes json = .ok rows)
    (holds : ∀ row ∈ rows, ordinaryHolds hash assignment row)
    (planAccepted : Impact.lower state (Passes.pruneEntrypoint sourceEntry) = .ok plan)
    (expectedAccepted : Native.expectedEntrypoint state (Passes.pruneEntrypoint sourceEntry) = .ok expected)
    (inputSchema : ∀ requirement ∈ expected.rawInputs ++ expected.inputs,
      requirement.ty.isForeign = Bool.false)
    (frameAccepted : normalizeOutputs
      (entrypointSeedAliases (Passes.pruneEntrypoint sourceEntry) plan)
      (Passes.pruneEntrypoint sourceEntry).circuit.outputs = .ok frame)
    (baseEnvironment : TypedEnvironment hash assignment frame.1 base
      (GenericStateEffectValidation.initialEffectTypeEnv (Passes.pruneEntrypoint sourceEntry)))
    (scope : GuardedScalarReadEffects sourceEntry.effectGuards sourceEntry.effects.zipIdx)
    (readAdmitted : ∀ readSpec ∈ plan.reads.drop
      (Impact.publicInputReadCount sourceEntry.circuit.inputs),
      readSpec.components = [] ∧ (scalarType? readSpec.ty).isSome = Bool.true ∧
        readSpec.ty.validate {poseidon2 := Bool.true, stateCells := Bool.true, stateMaps := Bool.true} = .ok ())
    (readFresh : ∀ readSpec ∈ plan.reads.drop
      (Impact.publicInputReadCount sourceEntry.circuit.inputs),
      base.lookup readSpec.name = none ∧
        (GenericStateEffectValidation.initialEffectTypeEnv
          sourceEntry).lookup readSpec.name = none)
    (readDistinct : (plan.reads.drop
      (Impact.publicInputReadCount sourceEntry.circuit.inputs)).Pairwise
        (fun left right => left.name ≠ right.name))
    (readAliases : ∀ readSpec ∈ plan.reads.drop
      (Impact.publicInputReadCount sourceEntry.circuit.inputs),
      frame.1.lookup readSpec.name = some (.input ("%input_" ++ readSpec.name)))
    (readGuards : ∀ readSpec ∈ plan.reads.drop
      (Impact.publicInputReadCount sourceEntry.circuit.inputs),
      ∀ guard, readSpec.guard = some guard → ScalarExpression guard)
    (guardAdmission : plan.guards.all
      (fun guard => (ScalarExpressionAdmission.certify guard).isSome) = Bool.true)
    (decodedReads : decodeReads (plan.reads.drop
      (Impact.publicInputReadCount sourceEntry.circuit.inputs))
      assignment = .ok decoded)
    (effectsAdmitted : ScalarStateEffects sourceEntry.effects)
    (operands : ∀ effect ∈ sourceEntry.effects, ScalarOperands effect)
    (publicCompatible : ∀ input ∈ sourceEntry.circuit.inputs,
      Impact.publicInputScalarCompatible input)
    (encoded : GenericStateEncoding.encodeState state initial = some slots)
    (distinct : state.Pairwise (fun left right => left.name ≠ right.name))
    (stateBound : state.length < Field.modulus)
    (evaluated : GuardedPlanExecution.evalPlan ctx (base ++ decoded) plan = .ok native)
    (checked : NativeState.run native ⟨[.vector slots], []⟩ = some final)
    (observations : List GuardedImpactObservation.Observation)
    (consumed : GuardedStatementConsumption.consumeArtifact zkirBytes assignment
      ⟨native.flatMap ImpactStatementScalar.opFields, final.reads.map NativeState.Cell.value⟩ =
        some observations)
    (profile : TargetProfile) (contractName : Name) (ctor : Option Constructor)
    (standaloneFile : _root_.Bool) (impactBytes : ArtifactBytes.Bytes) (budget : Nat)
    (keyWidth : Nat → Option Nat)
    (statementAdmitted : ImpactPlanStatementAgreement.admitsScalarPlan keyWidth plan = Bool.true)
    (statementMatched : ImpactPlanStatementAgreement.matchesBytes budget impactBytes
      (Compiler.nativePlanJson profile contractName state ctor (Passes.pruneEntrypoint sourceEntry)
        plan standaloneFile) = Bool.true) :
    (GuardedZkirArtifact.decodeBytes zkirBytes).map GuardedZkirArtifact.View.rows = .ok rows ∧
    (emittedObservations assignment rows = some observations ∧
      native.flatMap ImpactStatementScalar.opFields =
        GuardedImpactObservation.activePayloads observations ∧
      final.reads.map NativeState.Cell.value = GuardedScalarInput.activeReadValues
        (GuardedInputTranscript.emittedPublicReads assignment rows) ∧
      (∀ observed ∈ GuardedInputTranscript.emittedPublicReads assignment rows,
        observed.guard = one ∨ (observed.guard = zero ∧ observed.value = zero))) ∧
    (∃ minimum, ∀ fuel, minimum ≤ fuel → ∃ raw,
      ArtifactBytes.parse impactBytes = .ok raw ∧
      ImpactPlanAgreement.evaluatePlan fuel ctx (base ++ decoded) raw = some native ∧
      ImpactTranscriptSchedule.evaluateSchedule fuel ctx (base ++ decoded) keyWidth raw =
        some (GuardedStatementConsumption.observationActivity observations) ∧
      ((plan.operations.zipIdx.mapM
        (ImpactTranscriptSchedule.sourceGroups ctx (base ++ decoded) plan)).map List.flatten) =
        some (GuardedStatementConsumption.observationActivity observations) ∧
      ∀ inputs fields,
        ImpactPlanStatement.fromBytes fuel ctx (base ++ decoded) keyWidth impactBytes inputs =
          some fields →
        ∃ header : ImpactCallStatement.Header,
          ImpactPlanStatement.headerFor inputs native
            (GuardedStatementConsumption.observationActivity observations) = some header ∧
          GuardedStatementConsumption.fromArtifact zkirBytes assignment header
            ⟨native.flatMap ImpactStatementScalar.opFields, final.reads.map NativeState.Cell.value⟩ =
            some ⟨fields, GuardedStatementConsumption.observationActivity observations⟩ ∧
          ImpactPlanStatementAgreement.fromEntrypoint ctx (base ++ decoded) state
            (Passes.pruneEntrypoint sourceEntry) inputs = some fields) ∧
    ∃ finalTypes finalEnv finalState finalSlots finalReads,
      runEffectsWithGuardsAndEnv ctx sourceEntry.effects sourceEntry.effectGuards base initial =
          .ok (finalEnv, finalState) ∧
      GenericStateEncoding.encodeState state finalState = some finalSlots ∧
      final = ⟨[.vector finalSlots], finalReads⟩ ∧
      AgreesOnTypes finalTypes finalEnv (base ++ decoded) ∧
      GuardValidatedEffects state (Passes.pruneEntrypoint sourceEntry)
        (GenericStateEffectValidation.initialEffectTypeEnv
          (Passes.pruneEntrypoint sourceEntry))
        (Passes.pruneEntrypoint sourceEntry).effects.zipIdx finalTypes ∧
      ∀ returnValue ∈ sourceEntry.returns,
        returnValue.value.validate stateEffectCaps finalTypes = .ok () := by
  let ep := Passes.pruneEntrypoint sourceEntry
  obtain ⟨exactRows, values, readDecoded, environment, readFacts, assertions, inactiveZero, _⟩ :=
    GuardedZkirPlanSoundness.lowerEntrypoint_guardedArtifactRequirements
      state sourceEntry rewrites ctx hash implementation assignment zkirBytes json rows plan expected
      frame base initial lowered artifactChecked holds planAccepted expectedAccepted inputSchema
      frameAccepted baseEnvironment scope readAdmitted readFresh readDistinct readAliases
      readGuards guardAdmission
  have sameDecoded : values = decoded :=
    Except.ok.inj (readDecoded.symm.trans decodedReads)
  subst values
  obtain ⟨view, decodedView, _, rowConsumption⟩ :=
    GuardedStatementConsumption.consumeArtifact_sound zkirBytes assignment _ observations consumed
  have viewRows : view.rows = rows := by
    rw [decodedView] at exactRows
    exact Except.ok.inj exactRows
  rw [viewRows] at rowConsumption
  obtain ⟨emitted, impactStream, readStream, readDefaults⟩ :=
    (GuardedStatementConsumption.consumeRows_iff assignment rows _ observations).mp rowConsumption
  obtain ⟨_, instructions, parsedInstructions, decodedInstructions⟩ :=
    GuardedZkirArtifact.check_sound artifactChecked
  have schema : ∀ specimen, Native.expectedEntrypoint state ep = .ok specimen →
      ∀ requirement ∈ specimen.rawInputs ++ specimen.inputs, requirement.ty.isForeign = Bool.false := by
    intro specimen accepted
    have same := Except.ok.inj (accepted.symm.trans expectedAccepted)
    subst specimen
    exact inputSchema
  obtain ⟨guardExpected, expectedGuardAccepted, requirements⟩ :=
    GuardedZkirRequirements.lowerEntrypoint_guardedRows_sourceRequirements rewrites lowered
      parsedInstructions decodedInstructions schema
  have sameExpected := Except.ok.inj (expectedGuardAccepted.symm.trans expectedAccepted)
  subst guardExpected
  obtain ⟨checkedAssertions, checkedBounds, _⟩ := requirements holds
  obtain ⟨_, observedExpected, _, _, observedExpectedAccepted, _, observed⟩ :=
    GuardedImpactTranscript.lowerEntrypoint_guardedImpactTranscript rewrites lowered
      parsedInstructions decodedInstructions schema
  have sameExpected := Except.ok.inj (observedExpectedAccepted.symm.trans expectedAccepted)
  subst observedExpected
  obtain ⟨expectedObservations, emittedExpected, observedSource, _⟩ := observed holds
  have sameObservations := Option.some.inj (emittedExpected.symm.trans emitted)
  subst expectedObservations
  obtain ⟨sourceActivity, activeWidths⟩ :
      ((plan.operations.zipIdx.mapM
        (ImpactTranscriptSchedule.sourceGroups ctx (base ++ decoded) plan)).map List.flatten) =
        some (GuardedStatementConsumption.observationActivity observations) ∧
      native.map (fun op => (ImpactStatementScalar.opFields op).length) =
        (observations.filter (·.active)).map (fun row => row.payload.length) := by
    apply GuardedSourceActivity.lower_observations_activity state ep ctx hash assignment
      (base ++ decoded) implementation plan expected frame observations native evaluated planAccepted
      expectedAccepted frameAccepted environment ?_ ?_
      (ImpactPlanStatementAgreement.admitsScalarPlan_single_groups statementAdmitted)
      checkedAssertions checkedBounds observedSource
    · change ∀ readSpec ∈ (plan.reads.drop
        (Impact.publicInputReadCount sourceEntry.circuit.inputs)).flatMap Impact.Read.scalarReads,
        scalarAliasReadType readSpec.ty
      rw [ScalarPlanGuardSoundness.plain_reads_scalarReads _
        (fun readSpec inside => (readAdmitted readSpec inside).1)]
      exact fun readSpec inside =>
        ScalarPlanGuardSoundness.scalarType_shape readSpec.ty (readAdmitted readSpec inside).2.1
    · intro guard inside
      have checkedGuards := (Bool.and_eq_true_iff.mp statementAdmitted).2
      have checked := List.all_eq_true.mp checkedGuards (some guard) inside
      change (ScalarExpressionAdmission.certify guard).isSome = Bool.true at checked
      cases certified : ScalarExpressionAdmission.certify guard with
      | none => simp [certified] at checked
      | some supported => exact supported.down
  have scheduledPayload :
      ImpactStatementPayload.scheduledPayload ImpactStatementScalar.opFields
        native (GuardedStatementConsumption.observationActivity observations) =
        some (GuardedStatementConsumption.observationFields observations) := by
    exact GuardedStatementConsumption.scheduledPayload_of_observations native observations
      impactStream activeWidths
      (GuardedStatementConsumption.emittedObservations_inactive_zero assignment rows emitted)
  have initialAgreement := GenericStatePrefixEnvironment.initial_from_typed hash assignment
    frame.1 (GenericStateEffectValidation.initialEffectTypeEnv ep) base decoded baseEnvironment
  obtain ⟨finalTypes, finalEnv, finalState, finalSlots, finalReads, sourceRun,
    finalEncoded, layout, agreement, validated, returns⟩ :=
    GuardedStateEffectFold.lower_checked_guarded_effects ctx state ep plan base decoded assignment
      initial slots native final planAccepted effectsAdmitted scope operands publicCompatible
      decodedReads readDistinct readFacts inactiveZero assertions initialAgreement encoded
      distinct stateBound implementation.modulus evaluated checked
  refine ⟨exactRows, ?_, ?_, finalTypes, finalEnv, finalState, finalSlots, finalReads, sourceRun,
    finalEncoded, layout, agreement, validated, returns⟩
  · exact ⟨emitted, impactStream, readStream, readDefaults⟩
  · obtain ⟨minimum, agrees⟩ := ImpactPlanStatementAgreement.evaluations_fromBytes_agree
      profile contractName state ctor ep plan standaloneFile ctx implementation.modulus
      (ImpactTypedEnvironment.of_normalization environment)
      keyWidth statementAdmitted budget impactBytes planAccepted statementMatched
    refine ⟨minimum, ?_⟩
    intro fuel enough
    obtain ⟨raw, parsed, operationEq, activityEq⟩ := agrees fuel enough
    have decodedOperations : ImpactPlanAgreement.evaluatePlan fuel ctx (base ++ decoded) raw =
        some native := operationEq.trans (by rw [evaluated]; rfl)
    have decodedActivity := activityEq.trans sourceActivity
    refine ⟨raw, parsed, decodedOperations, decodedActivity, sourceActivity, ?_⟩
    intro inputs fields accepted
    have publicInputs : ImpactPlanStatement.publicInputs inputs native
        (GuardedStatementConsumption.observationActivity observations) = some fields := by
      unfold ImpactPlanStatement.fromBytes at accepted
      rw [parsed] at accepted
      simpa only [Except.toOption, Bind.bind, Option.bind_some, decodedOperations,
        decodedActivity] using accepted
    obtain ⟨header, payload, layout, reconstructed, headerDerived⟩ :=
      ImpactPlanStatement.publicInputs_header_and_payload inputs native
        (GuardedStatementConsumption.observationActivity observations) publicInputs
    have samePayload := Option.some.inj (reconstructed.symm.trans scheduledPayload)
    refine ⟨header, headerDerived, ?_, ?_⟩
    · unfold GuardedStatementConsumption.fromArtifact
      rw [consumed, layout, samePayload]
      rfl
    · rw [ImpactPlanStatementAgreement.fromEntrypoint_eq_fromSource
        ctx (base ++ decoded) state ep plan inputs planAccepted]
      unfold ImpactPlanStatementAgreement.fromSource
      rw [evaluated, sourceActivity]
      simpa only [Except.toOption, Bind.bind, Option.bind_some] using publicInputs

end Noctium.Verification.GuardedZkirStateSoundness
