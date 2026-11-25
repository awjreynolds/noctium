import Noctium.Verification.ScalarWitnessEntrypointInputs
import Noctium.Verification.ScalarWitnessCircuitConstraints
import Noctium.Verification.ScalarExpressionLowering
import Noctium.Verification.ScalarEntrypointSeedFrame

namespace Noctium.Verification.ScalarWitnessConstruction

open Backend NativeRelation NativeRelationJson ScalarLowering ScalarNormalization
open ScalarAllocationOutputFrame
open GenericStateCircuitParts (entrypointSeedAliases)

/-- The input and constraint prefix follows the entrypoint's actual lowering.
Its aliases are still empty when the circuit constraints run. -/
theorem completes_entrypoint_prelude (ctx : EvalContext) (hash : Hash)
    (implementation : HashAgreement ctx hash) (entry : Entrypoint) (values result : EvalEnv)
    (inputs : NativeRelation.Assignment)
    (admitted : CanonicalInputs entry.circuit values inputs)
    (scalarAdmission : ScalarCircuitAdmission entry.circuit)
    (identifiers : ∀ input ∈ entry.circuit.inputs,
      validIdentifier ("%input_" ++ input.name) = true)
    (valid : entry.circuit.validate Capabilities.crypto = .ok ())
    (success : entry.circuit.run ctx values = .ok result) :
    Completes hash inputs (do
      Zkir.lowerEntrypointInputs entry
      Zkir.lowerConstraints entry.circuit.constraints) := by
  have constraintFrames :=
    Zkir.lowerConstraints_preservesOutputCapacityFrame entry.circuit.constraints
      (fun condition member => lowerExpr_admitted_preservesOutputCapacityFrame condition
        (scalarAdmission.constraints condition member))
  have conditions := completes_circuit_constraints ctx hash implementation entry.circuit
    values inputs admitted identifiers scalarAdmission
    (fun condition member => ScalarExpressionLowering.lowerExpr_complete condition
      (scalarAdmission.constraints condition member))
    (circuit_validation_parts entry.circuit valid).1
    (circuit_run_steps ctx entry.circuit values result success).1
  exact completes_bind hash inputs _ _
    (Zkir.lowerEntrypointInputs_preservesOutputCapacityFrame entry) (fun _ => constraintFrames)
    (completes_entrypoint_inputs hash inputs entry values admitted identifiers) (fun _ => conditions)

/-- The empty emitter aliases resolve both raw call arguments and transcript
inputs through the real entrypoint normalizer's seed. The post-public read
aliases are appended after this input environment. -/
theorem entrypoint_seed_lowerAliasAgreement (hash : Hash)
    (inputs witness : NativeRelation.Assignment) (entry : Entrypoint) (plan : Impact.Plan)
    (values : EvalEnv) (state : Zkir.LowerState)
    (admitted : CanonicalInputs entry.circuit values inputs)
    (identifiers : ∀ input ∈ entry.circuit.inputs,
      validIdentifier ("%input_" ++ input.name) = true)
    (frame : InputFrame inputs witness) (aliasesEmpty : state.aliases = []) :
    LowerAliasAgreement hash inputs witness (entrypointSeedAliases entry plan) state.aliases values := by
  intro name ty raw value lookup typed
  obtain ⟨term, found, meaning⟩ := current_aliases hash inputs witness entry.circuit values
    state admitted identifiers frame aliasesEmpty name ty raw value lookup typed
  refine ⟨term, ?_, meaning⟩
  rw [ScalarEntrypointSeedFrame.entrypointSeedAliases_eq entry plan values inputs admitted]
  simp [List.lookup_append, found]

end Noctium.Verification.ScalarWitnessConstruction
