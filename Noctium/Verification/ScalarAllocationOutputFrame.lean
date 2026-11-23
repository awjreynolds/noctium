import Noctium.Backend.Zkir

namespace Noctium.Verification.ScalarAllocationOutputFrame

open Backend

private def hashCircuit : Circuit := {
  name := "allocationOutputFrame"
  outputs := [{
    name := "digest"
    ty := .bytes 32
    value := .persistentHash32 (.bytes32Literal (List.replicate 32 0))
  }]
}

private def hashState : Zkir.LowerState :=
  ((Zkir.lowerBody (Passes.pruneCircuit hashCircuit)).run {}).2

private def packedInputHashCircuit : Circuit := {
  name := "packedInputHashOutputFrame"
  inputs := [{name := "preimage", ty := .bytes 32, visibility := .«public»}]
  outputs := [{
    name := "digest"
    ty := .bytes 32
    value := .persistentHash32 (.ref "preimage")
  }]
}

private def packedInputHashState : Zkir.LowerState :=
  ((Zkir.lowerBody (Passes.pruneCircuit packedInputHashCircuit)).run {}).2

theorem packedInputHash_counts :
    packedInputHashState.next = 3 ∧ packedInputHashState.instructions.size = 9 ∧
      packedInputHashState.outputDefinitions = 5 := by
  decide +kernel

theorem packedInputHash_emits_hash_and_two_output_packing :
    Native.opcode packedInputHashState.instructions[5]! = "persistent_hash" ∧
      Native.opcode packedInputHashState.instructions[6]! = "bytes_into_natives" ∧
      Native.outputDefinitionsInInstruction packedInputHashState.instructions[6]! = 2 := by
  decide +kernel

theorem packedInputHash_has_actual_output_capacity_frame :
    Zkir.OutputCapacityFrame {} packedInputHashState := by
  constructor
  · change 0 ≤ packedInputHashState.next
    decide +kernel
  · change 0 + (packedInputHashState.next - 0) ≤ packedInputHashState.outputDefinitions
    decide +kernel

theorem packedInputHash_is_within_instruction_cap :
    packedInputHashState.instructions.size ≤ Native.maxInstructions := by
  decide +kernel

theorem coldTwoLimbHash_counts :
    hashState.next = 3 ∧ hashState.instructions.size = 4 ∧
      hashState.outputDefinitions = 3 := by
  decide +kernel

theorem coldTwoLimbHash_emits_two_output_packing_instruction :
    Native.outputDefinitionsInInstruction hashState.instructions[1]! = 2 := by
  decide +kernel

theorem coldTwoLimbHash_has_actual_output_capacity_frame :
    Zkir.OutputCapacityFrame {} hashState := by
  constructor
  · change 0 ≤ hashState.next
    decide +kernel
  · change 0 + (hashState.next - 0) ≤ hashState.outputDefinitions
    decide +kernel

private def accepted {ε α} : Except ε α → Bool
  | .ok _ => true
  | .error _ => false

#guard accepted (Zkir.lowerCircuit hashCircuit)

theorem coldTwoLimbHash_has_producerCapacity {program : Lean.Json}
    (produced : Zkir.lowerCircuit hashCircuit = .ok program) :
    hashState.outputDefinitions ≤ Native.maxInstructions * Native.maxVectorLength := by
  obtain ⟨expected, expectedAccepted, producerAccepted⟩ :=
    Zkir.lowerCircuit_validated hashCircuit program produced
  obtain ⟨instructions, parsed, capacity⟩ :=
    Native.validate_output_definitions_by_instruction_count producerAccepted
  have actualInstructions : Native.arrayField program "instructions" =
      .ok hashState.instructions := by
    simpa [hashState] using
      Zkir.lowerCircuit_instructions hashCircuit program produced
  have instructionsEqual : instructions = hashState.instructions := by
    apply Except.ok.inj
    calc
      .ok instructions = Native.arrayField program "instructions" := parsed.symm
      _ = .ok hashState.instructions := actualInstructions
  simpa [Zkir.LowerState.outputDefinitions, instructionsEqual] using capacity

theorem coldTwoLimbHash_names_fit_producerCapacity :
    ∀ {program : Lean.Json}, Zkir.lowerCircuit hashCircuit = .ok program →
      hashState.next ≤ Native.maxInstructions * Native.maxVectorLength := by
  intro program produced
  exact Zkir.OutputCapacityFrame.next_le_producerCapacity
    coldTwoLimbHash_has_actual_output_capacity_frame
    (coldTwoLimbHash_has_producerCapacity produced)

#guard accepted (Zkir.lowerCircuit packedInputHashCircuit)

theorem packedInputHash_has_producerCapacity {program : Lean.Json}
    (produced : Zkir.lowerCircuit packedInputHashCircuit = .ok program) :
    packedInputHashState.outputDefinitions ≤ Native.maxInstructions * Native.maxVectorLength := by
  obtain ⟨expected, expectedAccepted, producerAccepted⟩ :=
    Zkir.lowerCircuit_validated packedInputHashCircuit program produced
  obtain ⟨instructions, parsed, capacity⟩ :=
    Native.validate_output_definitions_by_instruction_count producerAccepted
  have actualInstructions : Native.arrayField program "instructions" =
      .ok packedInputHashState.instructions := by
    simpa [packedInputHashState] using
      Zkir.lowerCircuit_instructions packedInputHashCircuit program produced
  have instructionsEqual : instructions = packedInputHashState.instructions := by
    apply Except.ok.inj
    calc
      .ok instructions = Native.arrayField program "instructions" := parsed.symm
      _ = .ok packedInputHashState.instructions := actualInstructions
  simpa [Zkir.LowerState.outputDefinitions, instructionsEqual] using capacity

theorem packedInputHash_names_fit_producerCapacity :
    ∀ {program : Lean.Json}, Zkir.lowerCircuit packedInputHashCircuit = .ok program →
      packedInputHashState.next ≤ Native.maxInstructions * Native.maxVectorLength := by
  intro program produced
  exact Zkir.OutputCapacityFrame.next_le_producerCapacity
    packedInputHash_has_actual_output_capacity_frame
    (packedInputHash_has_producerCapacity produced)

end Noctium.Verification.ScalarAllocationOutputFrame
