import Noctium.Verification.GuardedZkirPlanSoundness
import Noctium.Verification.GuardedStateEffectFold
import Noctium.Verification.GuardedStatementConsumption
import Noctium.Verification.ImpactNativeStatementFixture
import Noctium.Verification.ImpactPlanStatementAgreement

namespace Noctium.Verification.GuardedZkirStateSoundness
open Lean Backend NativeRelation ScalarNormalization
open GenericStateEffectValidation GenericStatePrefixEnvironment
open GenericStateCircuitParts GenericStateInputValues GenericStateCheckedReadTrace
open GenericStateEffectStep
open GuardedImpactTranscript

/-- Checked guarded ZKIR consumes the public streams of the same modeled VM
run whose operation order and activity are checked against the Impact bytes.
The instance fields, including inactive padding, are compared with a native
statement fixture. Native header authentication and the assignment's ordinary
circuit constraints remain explicit premises. -/
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
    (header : ImpactCallStatement.Header) (projection : GuardedStatementConsumption.Projection)
    (consumed : GuardedStatementConsumption.fromArtifact zkirBytes assignment header
      ⟨native.flatMap ImpactStatementScalar.opFields, final.reads.map NativeState.Cell.value⟩ =
        some projection)
    (profile : TargetProfile) (contractName : Name) (ctor : Option Constructor)
    (standaloneFile : _root_.Bool) (impactBytes : ArtifactBytes.Bytes) (budget : Nat)
    (keyWidth : Nat → Option Nat)
    (environmentChecked : ImpactTypedEnvironment.check
      (plan.typeEnvironment (Passes.pruneEntrypoint sourceEntry)) (base ++ decoded) = Bool.true)
    (statementAdmitted : ImpactPlanStatementAgreement.admitsScalarPlan keyWidth plan = Bool.true)
    (statementMatched : ImpactPlanStatementAgreement.matchesBytes budget impactBytes
      (Compiler.nativePlanJson profile contractName state ctor (Passes.pruneEntrypoint sourceEntry)
        plan standaloneFile) = Bool.true) :
    (GuardedZkirArtifact.decodeBytes zkirBytes).map GuardedZkirArtifact.View.rows = .ok rows ∧
    (∃ observations,
      emittedObservations assignment rows = some observations ∧
      native.flatMap ImpactStatementScalar.opFields = GuardedImpactObservation.activePayloads observations ∧
      final.reads.map NativeState.Cell.value = GuardedScalarInput.activeReadValues
        (GuardedInputTranscript.emittedPublicReads assignment rows) ∧
      (∀ observed ∈ GuardedInputTranscript.emittedPublicReads assignment rows,
        observed.guard = one ∨ (observed.guard = zero ∧ observed.value = zero)) ∧
      projection.fields = [header.bindingInput, header.communicationsCommitment] ++
        GuardedStatementConsumption.observationFields observations ∧
      projection.activity = GuardedStatementConsumption.observationActivity observations) ∧
    (∃ minimum, ∀ fuel, minimum ≤ fuel → ∃ raw,
      ArtifactBytes.parse impactBytes = .ok raw ∧
      ImpactPlanAgreement.evaluatePlan fuel ctx (base ++ decoded) raw = some native ∧
      ∀ fixture : ImpactNativeStatementFixture.NativeStatementFixture,
        ImpactNativeStatementFixture.checkBytes fixture fuel ctx (base ++ decoded) keyWidth
          impactBytes = .ok () →
        fixture.fields = projection.fields →
        ImpactTranscriptSchedule.evaluateSchedule fuel ctx (base ++ decoded) keyWidth raw =
          some projection.activity →
        ImpactPlanStatementAgreement.fromEntrypoint ctx (base ++ decoded) state
          (Passes.pruneEntrypoint sourceEntry) fixture.inputs = some projection.fields ∧
        ((plan.operations.zipIdx.mapM
          (ImpactTranscriptSchedule.sourceGroups ctx (base ++ decoded) plan)).map List.flatten) =
          some projection.activity) ∧
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
  · obtain ⟨view, decodedView, _, projected⟩ := GuardedStatementConsumption.fromArtifact_sound
      zkirBytes assignment header _ projection consumed
    have viewRows : view.rows = rows := by
      rw [decodedView] at exactRows
      exact Except.ok.inj exactRows
    rw [viewRows] at projected
    obtain ⟨observations, emitted, impactStream, readStream, readDefaults, fields, activity⟩ :=
      (GuardedStatementConsumption.fromRows_iff assignment rows header _ projection).mp projected
    exact ⟨observations, emitted, impactStream, readStream, readDefaults, fields, activity⟩
  · obtain ⟨minimum, agrees⟩ := ImpactPlanStatementAgreement.evaluations_fromBytes_agree
      profile contractName state ctor ep plan standaloneFile ctx implementation.modulus
      environmentChecked keyWidth statementAdmitted budget impactBytes planAccepted statementMatched
    refine ⟨minimum, ?_⟩
    intro fuel enough
    obtain ⟨raw, parsed, operationEq, activityEq⟩ := agrees fuel enough
    refine ⟨raw, parsed, operationEq.trans (by rw [evaluated]; rfl), ?_⟩
    intro fixture fixtureChecked fieldsMatch activityMatch
    have sourceEq := ImpactPlanStatementAgreement.fromEntrypoint_eq_fromSource
      ctx (base ++ decoded) state ep plan fixture.inputs planAccepted
    have byteEq : ImpactPlanStatement.fromBytes fuel ctx (base ++ decoded) keyWidth impactBytes
        fixture.inputs = ImpactPlanStatementAgreement.fromSource ctx (base ++ decoded) plan
          fixture.inputs := by
      unfold ImpactPlanStatement.fromBytes ImpactPlanStatementAgreement.fromSource
      rw [parsed]
      simp only [Except.toOption, Bind.bind, Option.bind_some]
      rw [operationEq, activityEq]
      rfl
    have fixtureFields := ImpactNativeStatementFixture.checkBytes_sound fixture fuel ctx
      (base ++ decoded) keyWidth impactBytes fixtureChecked
    exact ⟨sourceEq.trans (byteEq.symm.trans (fixtureFields.trans (congrArg some fieldsMatch))),
      activityEq.symm.trans activityMatch⟩

end Noctium.Verification.GuardedZkirStateSoundness
