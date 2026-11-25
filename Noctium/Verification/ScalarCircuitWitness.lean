import Noctium.Verification.ScalarTranslationSoundness
import Noctium.Verification.ScalarWitnessCircuitInputs
import Noctium.Verification.ScalarWitnessCircuitConstraints
import Noctium.Verification.ScalarWitnessCircuitOutputs
import Noctium.Verification.ScalarWitnessReturnProjection

namespace Noctium.Verification.ScalarWitnessConstruction

open Lean Backend NativeRelation NativeRelationJson ScalarNormalization ScalarLowering
open ScalarAllocationOutputFrame
open ScalarTranslationSoundness (defaultLoweredRows)
open ScalarValidationOpcodeProfile (checkedScalarOpcodeProfile)

private theorem returnSuffix_capacity (circuit : Circuit)
    (admitted : ScalarCircuitAdmission circuit) :
    Zkir.PreservesOutputCapacityFrame (do
      let texts ← Zkir.lowerReturnFields circuit.outputs
      if !texts.isEmpty then Zkir.bindPublic texts
      Zkir.emit "output" [("vals", toJson texts)]) := by
  apply Zkir.bind_preservesOutputCapacityFrame
  · apply Zkir.lowerReturnFields_preservesOutputCapacityFrame
    · intro output present
      obtain ⟨scalarType, _⟩ := admitted.outputs output present
      exact scalarReturnPreflight_preservesOutputCapacityFrame output scalarType
    · intro output present
      obtain ⟨scalarType, expressionAdmission⟩ := admitted.outputs output present
      exact scalarReturnFields_preservesOutputCapacityFrame output scalarType expressionAdmission
  · intro texts
    split
    · apply Zkir.bind_preservesOutputCapacityFrame
      · exact Zkir.emit_preservesOutputCapacityFrame _ _
      · intro _
        exact Zkir.emit_preservesOutputCapacityFrame _ _
    · exact Zkir.emit_preservesOutputCapacityFrame _ _

/-- Construct an extension satisfying every instruction of the exact default
standalone lowering. Expression completeness applies to the actual source
constraints and outputs. The circuit proof supplies the preflight, projection,
instruction ordering and final output binding. -/
theorem lowerCircuit_construct_witness (ctx : EvalContext) (hash : Hash)
    (implementation : HashAgreement ctx hash) (circuit : Circuit) (values result : EvalEnv)
    (inputs : NativeRelation.Assignment) (json : Json) (relation : Program)
    (admitted : CanonicalInputs circuit values inputs)
    (scalarAdmission : ScalarCircuitAdmission circuit)
    (conditionComplete : ∀ condition ∈ circuit.constraints, ExprComplete condition)
    (outputComplete : ∀ output ∈ circuit.outputs, ExprComplete output.value)
    (lowered : Zkir.lowerCircuit circuit = .ok json)
    (decoded : NativeRelationJson.decode json = .ok relation)
    (profile : checkedScalarOpcodeProfile
      (defaultLoweredRows circuit).toList.zipIdx relation.instructions = true)
    (success : circuit.run ctx values = .ok result) :
    ∃ witness, InputFrame inputs witness ∧
      ∀ instruction ∈ relation.instructions, instruction.Holds hash witness := by
  let pruned := Passes.pruneCircuit circuit
  have prunedAdmission := scalarAdmission.pruneCircuit circuit
  have prunedInputs : CanonicalInputs pruned values inputs :=
    ⟨admitted.unique, admitted.declared, admitted.complete, admitted.binding⟩
  have prunedConditions : ∀ condition ∈ pruned.constraints, ExprComplete condition := by
    intro condition present
    exact conditionComplete condition (pruneTrue_subset circuit.constraints condition present)
  have prunedOutputs : ∀ output ∈ pruned.outputs, ExprComplete output.value := outputComplete
  have prunedSuccess : pruned.run ctx values = .ok result := by
    rw [Passes.pruneCircuit_run]
    exact success
  have steps := circuit_run_steps ctx pruned values result prunedSuccess
  obtain ⟨expected, expectedAccepted, _⟩ := Zkir.lowerCircuit_validated circuit json lowered
  have acceptedSource := (expectedCircuit_parts pruned expected expectedAccepted).1
  have validation := circuit_validation_parts pruned acceptedSource
  obtain ⟨names, capacity, rows⟩ := ScalarTranslationSoundness.lowerCircuit_witness_preflight
    circuit admitted scalarAdmission lowered decoded profile
  have inputCompletion := completes_circuit_inputs hash inputs pruned values prunedInputs names
  have constraintCompletion := completes_circuit_constraints ctx hash implementation pruned values inputs
    prunedInputs names prunedAdmission prunedConditions validation.1 steps.1
  have outputCompletion := completes_circuit_outputs ctx hash implementation pruned values inputs
    prunedInputs names prunedAdmission (complete_scalar_return_fields pruned prunedAdmission prunedOutputs)
    validation.2 ⟨result, steps.2⟩
  have constraintCapacity := Zkir.lowerConstraints_preservesOutputCapacityFrame pruned.constraints
    (fun condition present => lowerExpr_admitted_preservesOutputCapacityFrame condition
      (prunedAdmission.constraints condition present))
  have returnCapacity := returnSuffix_capacity pruned prunedAdmission
  have bodyComplete : Completes hash inputs (Zkir.lowerBody pruned) := by
    unfold Zkir.lowerBody
    apply completes_bind hash inputs _ _
      (Zkir.lowerCircuitInputs_preservesOutputCapacityFrame pruned.inputs)
    · intro _
      exact Zkir.bind_preservesOutputCapacityFrame _ _ constraintCapacity (fun _ => returnCapacity)
    · exact inputCompletion
    · intro _
      exact completes_bind hash inputs _ _ constraintCapacity
        (fun _ => returnCapacity) constraintCompletion (fun _ => outputCompletion)
  obtain ⟨extension⟩ := bodyComplete inputs {} (empty_state hash inputs) (fun _ => rfl) rfl capacity
  refine ⟨extension.witness, ?_, extension.meaning.holds _ rows⟩
  intro name
  exact extension.frame _ (Or.inl ⟨name, rfl⟩)

/-- A successful admitted standalone source run has a witness for the
decoded default lowering, with its exact source input streams, Impact groups
and return values. Hash implementation agreement remains explicit. -/
theorem lowerCircuit_complete (ctx : EvalContext) (hash : Hash)
    (implementation : HashAgreement ctx hash) (circuit : Circuit) (values result : EvalEnv)
    (inputs : NativeRelation.Assignment) (json : Json) (relation : Program)
    (admitted : CanonicalInputs circuit values inputs)
    (scalarAdmission : ScalarCircuitAdmission circuit)
    (conditionComplete : ∀ condition ∈ circuit.constraints, ExprComplete condition)
    (outputComplete : ∀ output ∈ circuit.outputs, ExprComplete output.value)
    (lowered : Zkir.lowerCircuit circuit = .ok json)
    (decoded : NativeRelationJson.decode json = .ok relation)
    (profile : checkedScalarOpcodeProfile
      (defaultLoweredRows circuit).toList.zipIdx relation.instructions = true)
    (success : circuit.run ctx values = .ok result) :
    ∃ witness, InputFrame inputs witness ∧
      Satisfies hash relation
        {publicValues := (circuit.inputs.filter (·.visibility == .«public»)).map
          (fun input => inputs ("%input_" ++ input.name)),
         privateValues := (circuit.inputs.filter (·.visibility == .private)).map
          (fun input => inputs ("%input_" ++ input.name))}
        witness
        ((circuit.inputs.filter (·.visibility == .«public»)).map
          (fun input => [inputs ("%input_" ++ input.name)]) ++
          (if result.isEmpty then [] else [result.map (fun pair => scalar (valueNumber pair.2))]))
        (result.map (fun pair => scalar (valueNumber pair.2))) := by
  obtain ⟨witness, frame, holds⟩ := lowerCircuit_construct_witness ctx hash implementation
    circuit values result inputs json relation admitted scalarAdmission conditionComplete outputComplete
    lowered decoded profile success
  exact ⟨witness, frame, ScalarTranslationSoundness.lowerCircuit_complete_of_witness
    ctx hash implementation circuit values result json relation inputs witness admitted scalarAdmission
    lowered decoded profile success frame holds⟩

end Noctium.Verification.ScalarWitnessConstruction
