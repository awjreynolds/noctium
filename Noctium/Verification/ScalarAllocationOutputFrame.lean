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

theorem lowerCircuit_outputDefinitions_budget (circuit : Circuit) {program : Lean.Json}
    (produced : Zkir.lowerCircuit circuit = .ok program) :
    ((Zkir.lowerBody (Passes.pruneCircuit circuit)).run {}).2.outputDefinitions ≤
      Native.maxInstructions * Native.maxVectorLength := by
  obtain ⟨expected, _, producerAccepted⟩ :=
    Zkir.lowerCircuit_validated circuit program produced
  obtain ⟨instructions, parsed, capacity⟩ :=
    Native.validate_output_definitions_by_instruction_count producerAccepted
  have actualInstructions := Zkir.lowerCircuit_instructions circuit program produced
  have instructionsEqual := Except.ok.inj (parsed.symm.trans actualInstructions)
  simpa [Zkir.LowerState.outputDefinitions, instructionsEqual] using capacity

/-- A composed frame bounds allocated names by the producer's output budget. -/
theorem lowerCircuit_output_budget_of_frame (circuit : Circuit) {program : Lean.Json}
    (produced : Zkir.lowerCircuit circuit = .ok program)
    (frame : Zkir.OutputCapacityFrame {} ((Zkir.lowerBody (Passes.pruneCircuit circuit)).run {}).2) :
    ((Zkir.lowerBody (Passes.pruneCircuit circuit)).run {}).2.next ≤
      Native.maxInstructions * Native.maxVectorLength :=
  Zkir.OutputCapacityFrame.next_le_producerCapacity frame
    (lowerCircuit_outputDefinitions_budget circuit produced)

#guard accepted (Zkir.lowerCircuit hashCircuit)

theorem coldTwoLimbHash_has_producerCapacity {program : Lean.Json}
    (produced : Zkir.lowerCircuit hashCircuit = .ok program) :
    hashState.outputDefinitions ≤ Native.maxInstructions * Native.maxVectorLength :=
  lowerCircuit_outputDefinitions_budget hashCircuit produced

theorem coldTwoLimbHash_names_fit_producerCapacity :
    ∀ {program : Lean.Json}, Zkir.lowerCircuit hashCircuit = .ok program →
      hashState.next ≤ Native.maxInstructions * Native.maxVectorLength :=
  fun produced => lowerCircuit_output_budget_of_frame hashCircuit produced
    coldTwoLimbHash_has_actual_output_capacity_frame

#guard accepted (Zkir.lowerCircuit packedInputHashCircuit)

theorem packedInputHash_has_producerCapacity {program : Lean.Json}
    (produced : Zkir.lowerCircuit packedInputHashCircuit = .ok program) :
    packedInputHashState.outputDefinitions ≤ Native.maxInstructions * Native.maxVectorLength :=
  lowerCircuit_outputDefinitions_budget packedInputHashCircuit produced

theorem packedInputHash_names_fit_producerCapacity :
    ∀ {program : Lean.Json}, Zkir.lowerCircuit packedInputHashCircuit = .ok program →
      packedInputHashState.next ≤ Native.maxInstructions * Native.maxVectorLength :=
  fun produced => lowerCircuit_output_budget_of_frame packedInputHashCircuit produced
    packedInputHash_has_actual_output_capacity_frame

/-- The producer's output-slot bound applies to the exact ledger body.
The instruction cap stays a separate bound. This checks default lowering. -/
theorem lowerEntrypoint_outputDefinitions_budget (state : List StateDecl)
    (entry : Entrypoint) (program : Lean.Json)
    (accepted : Zkir.lowerEntrypoint state entry = .ok program) :
    ∃ plan, Impact.lower state (Passes.pruneEntrypoint entry) = .ok plan ∧
      ((Zkir.lowerEntrypointBody (Passes.pruneEntrypoint entry) plan).run {}).2.outputDefinitions ≤
        Native.maxInstructions * Native.maxVectorLength := by
  obtain ⟨plan, _, planAccepted, _, producerAccepted, actualInstructions⟩ :=
    Zkir.lowerEntrypoint_validation_and_instructions state entry program accepted
  obtain ⟨instructions, parsed, capacity⟩ :=
    Native.validate_output_definitions_by_instruction_count producerAccepted
  have instructionsEqual := Except.ok.inj (parsed.symm.trans actualInstructions)
  refine ⟨plan, planAccepted, ?_⟩
  simpa [Zkir.LowerState.outputDefinitions, instructionsEqual] using capacity

end Noctium.Verification.ScalarAllocationOutputFrame
