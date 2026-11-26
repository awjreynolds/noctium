import Noctium.Verification.GenericStateCandidateEnvironment
import Noctium.Verification.ScalarGuardedPlanAdmission

namespace Noctium.Verification.GenericStateNativeSchedule

open Backend NativeRelation ScalarNormalization Backend.Native
open GenericStateCircuitParts
open ScalarGuardedPlanAdmission (ScalarEffect)

/-- Strict decoding and an arbitrary satisfying witness determine the
compiler's full ordered native group schedule. The result is the complete
ordered schedule before applying activity guards or checking a VM state
transition. -/
theorem accepted_native_schedule (state : List StateDecl)
    (sourceEntry : Entrypoint) (json : Lean.Json) (relation : Program)
    (ctx : EvalContext) (hash : Hash)
    (implementation : HashAgreement ctx hash)
    (values : EvalEnv) (candidateWitness : Assignment)
    (streams : InputStreams) (publicGroups : List (List Scalar))
    (admittedInputs : CanonicalInputs sourceEntry.circuit values candidateWitness)
    (circuitAdmission : ScalarCircuitAdmission sourceEntry.circuit)
    (effects : ∀ effect ∈ sourceEntry.effects, ScalarEffect state effect)
    (guardsAdmitted : ∀ condition, some condition ∈ sourceEntry.effectGuards →
      ScalarExpression condition)
    (lowered : Zkir.lowerEntrypoint state sourceEntry = .ok json)
    (decoded : NativeRelationJson.decode json = .ok relation)
    (satisfies : CircuitSatisfies hash relation streams candidateWitness publicGroups) :
    ∃ (plan : Impact.Plan) (expected : Native.Expected) (frame : OutputFrame)
        (result candidates : EvalEnv) (ops : List NativeState.Op),
      let ep := Passes.pruneEntrypoint sourceEntry
      Impact.lower state ep = .ok plan ∧
      Native.expectedEntrypoint state ep = .ok expected ∧
      ScalarValidatedProgram.Sound hash candidateWitness candidateWitness expected relation streams publicGroups ∧
      normalizeOutputs (entrypointSeedAliases ep plan) ep.circuit.outputs = .ok frame ∧
      sourceEntry.circuit.run ctx values = .ok result ∧
      GenericStateInputValues.decodeReads
        (plan.reads.drop (Impact.publicInputReadCount sourceEntry.circuit.inputs)) candidateWitness = .ok candidates ∧
      TypedEnvironment hash candidateWitness frame.1 ((result ++ values) ++ candidates)
        (plan.typeEnvironment ep) ∧
      forIn ((plan.reads.drop (Impact.publicInputReadCount sourceEntry.circuit.inputs)).flatMap
        Impact.Read.scalarReads) frame.1 (readAliasStep ep) = .ok frame.1 ∧
      GenericStateOps.evalPlan ctx ((result ++ values) ++ candidates) plan = .ok ops ∧
      publicGroups = NativeState.groups ops := by
  let ep := Passes.pruneEntrypoint sourceEntry
  obtain ⟨plan, expected, frame, result, candidates, planAccepted, expectedAccepted,
    sound, normalized, sourceRun, candidatesDecoded, environment, readAliasFold⟩ :=
    GenericStateCandidateEnvironment.accepted_candidate_environment state sourceEntry json relation
      ctx hash implementation values candidateWitness streams publicGroups admittedInputs
      circuitAdmission effects lowered decoded satisfies
  have prunedEffects : ∀ effect ∈ ep.effects, ScalarEffect state effect := by
    intro effect effectPresent
    exact effects effect (by simpa [ep, Passes.pruneEntrypoint] using effectPresent)
  have prunedGuards : ∀ condition, some condition ∈ ep.effectGuards →
      ScalarExpression condition := by
    intro condition guardPresent
    exact guardsAdmitted condition (by simpa [ep, Passes.pruneEntrypoint] using guardPresent)
  have prunedInputs : CanonicalInputs ep.circuit values candidateWitness :=
    ⟨admittedInputs.unique, admittedInputs.declared, admittedInputs.complete,
      admittedInputs.binding⟩
  have inputScope : ∀ input ∈ ep.circuit.inputs, Nonempty (ScalarType input.ty) := by
    intro input present
    obtain ⟨_, _, canonical⟩ := prunedInputs.complete input present
    exact GenericStateWriteEvaluation.scalarType_of_canonical canonical
  have compatible : ∀ input ∈ ep.circuit.inputs, Impact.publicInputScalarCompatible input := by
    intro input present
    obtain ⟨supported⟩ := inputScope input present
    cases input with
    | mk name ty visibility span => cases supported <;>
        simp [Impact.publicInputScalarCompatible]
  let candidateValues := (result ++ values) ++ candidates
  obtain ⟨ops, evaluated, expectedGroups⟩ :=
    ScalarGuardedPlanAdmission.lower_expected_scalar_schedule state ep expected plan frame
      frame.1 ctx hash implementation candidateWitness candidateValues environment expectedAccepted
      planAccepted normalized readAliasFold compatible prunedEffects prunedGuards
      sound.bounds sound.assertions
  have groupsSome : publicGroups.map (List.map some) =
      (NativeState.groups ops).map (List.map some) :=
    sound.impact.trans expectedGroups
  have groupsExact : publicGroups = NativeState.groups ops := by
    apply (List.map_inj_right (f := List.map some) (by
      intro left right same
      exact (List.map_inj_right (f := some) (fun _ _ => Option.some.inj)).mp same)).mp
    exact groupsSome
  exact ⟨plan, expected, frame, result, candidates, ops, planAccepted,
    expectedAccepted, sound, normalized, sourceRun, candidatesDecoded, environment,
    readAliasFold, evaluated, groupsExact⟩

end Noctium.Verification.GenericStateNativeSchedule
