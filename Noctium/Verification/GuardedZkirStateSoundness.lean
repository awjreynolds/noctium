import Noctium.Verification.GuardedZkirPlanSoundness
import Noctium.Verification.GuardedStateEffectFold

namespace Noctium.Verification.GuardedZkirStateSoundness
open Lean Backend NativeRelation ScalarNormalization
open GenericStateEffectValidation GenericStatePrefixEnvironment
open GenericStateCircuitParts GenericStateInputValues GenericStateCheckedReadTrace
open GenericStateEffectStep
open GuardedImpactTranscript

/-- Accepted emitted guarded rows establish the scalar plan requirements used
by the checked effect fold. A checked VM run then agrees with ordered source
execution from the same encoded initial state. -/
theorem lowerEntrypoint_checked_guarded_state
    (state : List StateDecl) (entry : Entrypoint) (rewrites : Zkir.Rewrites)
    (ctx : EvalContext) (hash : Hash) (implementation : HashAgreement ctx hash)
    (witness : Assignment) (json : Json) (instructions : Array Json)
    (rows : List GuardedScalarRows.Row) (plan : Impact.Plan) (expected : Native.Expected)
    (frame : OutputFrame) (base decoded : EvalEnv)
    (initial : LedgerState) (slots : List NativeState.Slot)
    (native : List NativeState.Op) (final : NativeState.Machine)
    (lowered : Zkir.lowerEntrypoint state entry rewrites = .ok json)
    (parsed : Native.arrayField json "instructions" = .ok instructions)
    (rowsDecoded : instructions.toList.mapM GuardedScalarRows.decodeRow = .ok rows)
    (holds : ∀ row ∈ rows, ordinaryHolds hash witness row)
    (planAccepted : Impact.lower state (Passes.pruneEntrypoint entry) = .ok plan)
    (expectedAccepted : Native.expectedEntrypoint state (Passes.pruneEntrypoint entry) = .ok expected)
    (inputSchema : ∀ requirement ∈ expected.rawInputs ++ expected.inputs,
      requirement.ty.isForeign = false)
    (frameAccepted : normalizeOutputs
      (entrypointSeedAliases (Passes.pruneEntrypoint entry) plan)
      (Passes.pruneEntrypoint entry).circuit.outputs = .ok frame)
    (baseEnvironment : TypedEnvironment hash witness frame.1 base
      (GenericStateEffectValidation.initialEffectTypeEnv (Passes.pruneEntrypoint entry)))
    (scope : GuardedScalarReadEffects entry.effectGuards entry.effects.zipIdx)
    (readAdmitted : ∀ read ∈ plan.reads.drop
      (Impact.publicInputReadCount entry.circuit.inputs),
      read.components = [] ∧ (scalarType? read.ty).isSome = true ∧
        read.ty.validate {poseidon2 := true, stateCells := true, stateMaps := true} = .ok ())
    (readFresh : ∀ read ∈ plan.reads.drop
      (Impact.publicInputReadCount entry.circuit.inputs),
      base.lookup read.name = none ∧
        (GenericStateEffectValidation.initialEffectTypeEnv
          entry).lookup read.name = none)
    (readDistinct : (plan.reads.drop
      (Impact.publicInputReadCount entry.circuit.inputs)).Pairwise
        (fun left right => left.name ≠ right.name))
    (readAliases : ∀ read ∈ plan.reads.drop
      (Impact.publicInputReadCount entry.circuit.inputs),
      frame.1.lookup read.name = some (.input ("%input_" ++ read.name)))
    (readGuards : ∀ read ∈ plan.reads.drop
      (Impact.publicInputReadCount entry.circuit.inputs),
      ∀ guard, read.guard = some guard → ScalarExpression guard)
    (admitted : ∀ guard ∈ plan.guards, ScalarExpression guard)
    (decodedReads : decodeReads (plan.reads.drop
      (Impact.publicInputReadCount entry.circuit.inputs))
      witness = .ok decoded)
    (effectsAdmitted : ScalarStateEffects entry.effects)
    (operands : ∀ effect ∈ entry.effects, ScalarOperands effect)
    (publicCompatible : ∀ input ∈ entry.circuit.inputs,
      Impact.publicInputScalarCompatible input)
    (encoded : GenericStateEncoding.encodeState state initial = some slots)
    (distinct : state.Pairwise (fun left right => left.name ≠ right.name))
    (stateBound : state.length < Field.modulus)
    (evaluated : GuardedPlanExecution.evalPlan ctx (base ++ decoded) plan = .ok native)
    (checked : NativeState.run native ⟨[.vector slots], []⟩ = some final) :
    ∃ finalTypes finalEnv finalState finalSlots finalReads,
      runEffectsWithGuardsAndEnv ctx entry.effects entry.effectGuards base initial =
          .ok (finalEnv, finalState) ∧
      GenericStateEncoding.encodeState state finalState = some finalSlots ∧
      final = ⟨[.vector finalSlots], finalReads⟩ ∧
      AgreesOnTypes finalTypes finalEnv (base ++ decoded) ∧
      GuardValidatedEffects state (Passes.pruneEntrypoint entry)
        (GenericStateEffectValidation.initialEffectTypeEnv
          (Passes.pruneEntrypoint entry))
        (Passes.pruneEntrypoint entry).effects.zipIdx finalTypes ∧
      ∀ output ∈ entry.returns,
        output.value.validate stateEffectCaps finalTypes = .ok () := by
  let ep := Passes.pruneEntrypoint entry
  obtain ⟨values, readDecoded, environment, readFacts, assertions, inactiveZero⟩ :=
    GuardedZkirPlanSoundness.lowerEntrypoint_guardedPlanRequirements
      state entry rewrites ctx hash implementation witness json instructions rows plan expected
      frame base lowered parsed rowsDecoded holds planAccepted expectedAccepted inputSchema
      frameAccepted baseEnvironment scope readAdmitted readFresh readDistinct readAliases
      readGuards admitted
  have sameDecoded : values = decoded :=
    Except.ok.inj (readDecoded.symm.trans decodedReads)
  subst values
  have initialAgreement := GenericStatePrefixEnvironment.initial_from_typed hash witness
    frame.1 (GenericStateEffectValidation.initialEffectTypeEnv ep) base decoded baseEnvironment
  obtain ⟨finalTypes, finalEnv, finalState, finalSlots, finalReads, sourceRun,
    finalEncoded, layout, agreement, validated, returns⟩ :=
    GuardedStateEffectFold.lower_checked_guarded_effects ctx state ep plan base decoded witness
      initial slots native final planAccepted effectsAdmitted scope operands publicCompatible
      decodedReads readDistinct readFacts inactiveZero assertions initialAgreement encoded
      distinct stateBound implementation.modulus evaluated checked
  exact ⟨finalTypes, finalEnv, finalState, finalSlots, finalReads, sourceRun,
    finalEncoded, layout, agreement, validated, returns⟩

end Noctium.Verification.GuardedZkirStateSoundness
