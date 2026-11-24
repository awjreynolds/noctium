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

private def publicFixedBytesInputPrefixState (length : Nat) : Zkir.LowerState :=
  (Zkir.lowerPublicFixedBytesInputPrefix
    {name := "preimage", ty := .bytes length, visibility := .«public»}).run {} |>.2

theorem publicFixedBytesInputPrefix_has_actual_output_capacity_frame (length : Nat) :
    Zkir.OutputCapacityFrame {} (publicFixedBytesInputPrefixState length) := by
  simpa [publicFixedBytesInputPrefixState] using
    (Zkir.lowerPublicFixedBytesInputPrefix_preservesOutputCapacityFrame "preimage" length {}) {}

theorem publicFixedBytesInputPrefix_names_fit_actual_output_count (length : Nat) :
    (publicFixedBytesInputPrefixState length).next ≤
      (publicFixedBytesInputPrefixState length).outputDefinitions := by
  exact Zkir.OutputCapacityFrame.next_le_outputDefinitions
    (publicFixedBytesInputPrefix_has_actual_output_capacity_frame length)
    (by simp [Zkir.LowerState.outputDefinitions])

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

/-- A composed lowering frame connects a supported actual lowering run to the
producer's validated output-slot budget. Callers must supply the frame for the
specific lowering path they proved. -/
theorem lowerCircuit_output_budget_of_frame (circuit : Circuit) {program : Lean.Json}
    (produced : Zkir.lowerCircuit circuit = .ok program)
    (frame : Zkir.OutputCapacityFrame {} ((Zkir.lowerBody (Passes.pruneCircuit circuit)).run {}).2) :
    ((Zkir.lowerBody (Passes.pruneCircuit circuit)).run {}).2.next ≤
      Native.maxInstructions * Native.maxVectorLength := by
  obtain ⟨expected, _, producerAccepted⟩ :=
    Zkir.lowerCircuit_validated circuit program produced
  obtain ⟨instructions, parsed, capacity⟩ :=
    Native.validate_output_definitions_by_instruction_count producerAccepted
  have actualInstructions : Native.arrayField program "instructions" =
      .ok ((Zkir.lowerBody (Passes.pruneCircuit circuit)).run {}).2.instructions :=
    Zkir.lowerCircuit_instructions circuit program produced
  have instructionsEqual : instructions =
      ((Zkir.lowerBody (Passes.pruneCircuit circuit)).run {}).2.instructions := by
    apply Except.ok.inj
    calc
      .ok instructions = Native.arrayField program "instructions" := parsed.symm
      _ = .ok ((Zkir.lowerBody (Passes.pruneCircuit circuit)).run {}).2.instructions :=
        actualInstructions
  have outputCapacity :
      ((Zkir.lowerBody (Passes.pruneCircuit circuit)).run {}).2.outputDefinitions ≤
        Native.maxInstructions * Native.maxVectorLength := by
    simpa [Zkir.LowerState.outputDefinitions, instructionsEqual] using capacity
  exact Zkir.OutputCapacityFrame.next_le_producerCapacity frame outputCapacity

theorem coldTwoLimbHash_names_fit_producerCapacity :
    ∀ {program : Lean.Json}, Zkir.lowerCircuit hashCircuit = .ok program →
      hashState.next ≤ Native.maxInstructions * Native.maxVectorLength := by
  intro program produced
  exact lowerCircuit_output_budget_of_frame hashCircuit produced
    coldTwoLimbHash_has_actual_output_capacity_frame

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
  exact lowerCircuit_output_budget_of_frame packedInputHashCircuit produced
    packedInputHash_has_actual_output_capacity_frame

end Noctium.Verification.ScalarAllocationOutputFrame
