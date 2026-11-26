import Noctium.Verification.GuardedScalarCandidateSchedule
import Noctium.Verification.NativeRelationInstructionProjection
import Noctium.Verification.ScalarGuardedPlanAdmission
import Noctium.Verification.ScalarGuardedReadAdmission
import Noctium.Verification.ScalarValidation
import Noctium.Verification.ScalarValidationProjection

namespace Noctium.Verification.GenericStateCandidateEnvironment

open Backend NativeRelation ScalarNormalization Backend.Native
open GenericStateCircuitParts
open ScalarGuardedPlanAdmission (ScalarEffect)

/-- An arbitrary satisfying relation witness determines the actual candidate
frame for the exact plan emitted by the strict ledger lowerer. The caller
supplies the source circuit and guarded effect admissions used to construct
that frame. -/
theorem accepted_candidate_environment (state : List StateDecl)
    (sourceEntry : Entrypoint) (json : Lean.Json) (relation : Program)
    (ctx : EvalContext) (hash : Hash)
    (implementation : HashAgreement ctx hash)
    (values : EvalEnv) (candidateWitness : Assignment)
    (streams : InputStreams) (publicGroups : List (List Scalar))
    (admittedInputs : CanonicalInputs sourceEntry.circuit values candidateWitness)
    (circuitAdmission : ScalarCircuitAdmission sourceEntry.circuit)
    (effects : ∀ effect ∈ sourceEntry.effects, ScalarEffect state effect)
    (lowered : Zkir.lowerEntrypoint state sourceEntry = .ok json)
    (decoded : NativeRelationJson.decode json = .ok relation)
    (satisfies : CircuitSatisfies hash relation streams candidateWitness publicGroups) :
    ∃ (plan : Impact.Plan) (expected : Native.Expected) (frame : OutputFrame)
        (result candidates : EvalEnv),
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
        Impact.Read.scalarReads) frame.1 (readAliasStep ep) = .ok frame.1 := by
  let ep := Passes.pruneEntrypoint sourceEntry
  obtain ⟨plan, expected, planAccepted, expectedAccepted, validationAccepted,
    _emittedInstructions⟩ :=
    Zkir.lowerEntrypoint_validation_and_instructions state sourceEntry json lowered
  obtain ⟨_instructionRows, inputHeader, _parsedRows, _decodedRows⟩ :=
    NativeRelationInstructionProjection.decode_headerAndInstructions decoded
  obtain ⟨rawInputsEmpty, _driverInstructions, _driverFinal, _driverFacts⟩ :=
    ScalarValidationProjection.validate_driver_result_empty_header
      validationAccepted inputHeader
  have sound : ScalarValidatedProgram.Sound hash candidateWitness candidateWitness expected relation
      streams publicGroups := by
    exact @ScalarValidation.validate_sound hash candidateWitness candidateWitness expected
      json relation streams publicGroups (by
        intro requirement present
        rfl) validationAccepted decoded satisfies
  have prunedInputs : CanonicalInputs ep.circuit values candidateWitness :=
    ⟨admittedInputs.unique, admittedInputs.declared, admittedInputs.complete,
      admittedInputs.binding⟩
  have prunedCircuitAdmission : ScalarCircuitAdmission ep.circuit :=
    ScalarCircuitAdmission.pruneCircuit sourceEntry.circuit circuitAdmission
  have prunedEffects : ∀ effect ∈ ep.effects, ScalarEffect state effect := by
    intro effect present
    exact effects effect (by simpa [ep, Passes.pruneEntrypoint] using present)
  obtain ⟨plainReads, separateReads, distinctReads⟩ :=
    ScalarGuardedReadAdmission.lower_read_admission state ep plan planAccepted prunedEffects
  have inputBounds : ∀ requirement ∈ expected.rawInputs ++ expected.inputs,
      requirement.ty.isForeign = _root_.Bool.false →
      requirement.canonicalJubjubScalar = _root_.Bool.false →
      (candidateWitness requirement.identifier).val ≤ Native.sourceMaximum requirement.ty := by
    intro requirement present _nonforeign ordinary
    rw [rawInputsEmpty] at present
    exact sound.inputBounds requirement present ordinary
  obtain ⟨frame, result, candidates, normalized, executed, candidatesDecoded,
    environment, readAliasFold⟩ :=
    GuardedScalarCandidateSchedule.expected_candidate_frame state ep expected plan ctx hash
      implementation values candidateWitness planAccepted expectedAccepted prunedInputs
      prunedCircuitAdmission plainReads separateReads distinctReads sound.assertions
      sound.bounds inputBounds
  refine ⟨plan, expected, frame, result, candidates, planAccepted, expectedAccepted,
    sound, normalized, ?_, ?_, environment, ?_⟩
  · simpa only [ep, Passes.pruneEntrypoint, Passes.pruneCircuit_run] using executed
  · simpa only [ep, Passes.pruneEntrypoint, Passes.pruneCircuit] using candidatesDecoded
  · simpa only [ep, Passes.pruneEntrypoint, Passes.pruneCircuit] using readAliasFold

end Noctium.Verification.GenericStateCandidateEnvironment
