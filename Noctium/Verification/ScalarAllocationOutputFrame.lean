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

private def cachedHashCircuit : Circuit := {
  name := "cachedAllocationOutputFrame"
  outputs := [
    {name := "firstDigest", ty := .bytes 32,
      value := .persistentHash32 (.bytes32Literal (List.replicate 32 0))},
    {name := "secondDigest", ty := .bytes 32,
      value := .persistentHash32 (.bytes32Literal (List.replicate 32 0))}]
}

private def cachedHashState : Zkir.LowerState :=
  ((Zkir.lowerBody (Passes.pruneCircuit cachedHashCircuit)).run {}).2

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

private theorem bytes32ReturnPreflight_preservesOutputCapacityFrame
    (name : String) (value : Expr (.bytes 32)) :
    Zkir.PreservesOutputCapacityFrame
      (Zkir.lowerReturnPreflight {name, ty := .bytes 32, value}) := by
  simpa [Zkir.lowerReturnPreflight] using
    (Zkir.pure_preservesOutputCapacityFrame ())

private theorem bytes32ReturnFields_preservesOutputCapacityFrame
    (name : String) (value : Expr (.bytes 32))
    (fieldFrames : ∀ index,
      Zkir.PreservesOutputCapacityFrame (Zkir.lowerExpr (.bytesField value index))) :
    ∀ projections,
      ({name, ty := .bytes 32, value} : Output).nativeReturnFields = .ok projections →
      ∀ field ∈ projections, Zkir.PreservesOutputCapacityFrame (Zkir.lowerExpr field) := by
  intro projections fieldsAccepted field member
  have projectionsEq : [.bytesField value 0, .bytesField value 1] = projections := by
    have accepted :
        (Except.ok value.nativeCallFields : Except String (List (Expr .native))) =
          Except.ok projections := by
      change Except.ok value.nativeCallFields = Except.ok projections
      exact fieldsAccepted
    have projectionsEq := Except.ok.inj accepted
    simpa [Expr.nativeCallFields, List.range_succ] using projectionsEq
  subst projections
  rcases List.mem_cons.mp member with first | second
  · cases first
    exact fieldFrames 0
  · have fieldEq : field = .bytesField value 1 := by simpa using second
    subst field
    exact fieldFrames 1

private def bytes32Returns (names : List String) (value : Expr (.bytes 32)) : List Output :=
  names.map fun name => {name, ty := .bytes 32, value}

private theorem bytes32OutputCircuit_has_output_capacity_frame
    (circuit : Circuit) (names : List String) (value : Expr (.bytes 32))
    (constraintsEmpty : circuit.constraints = [])
    (outputsMatch : circuit.outputs = bytes32Returns names value)
    (fieldFrames : ∀ index,
      Zkir.PreservesOutputCapacityFrame (Zkir.lowerExpr (.bytesField value index))) :
    Zkir.OutputCapacityFrame {} ((Zkir.lowerBody circuit).run {}).2 := by
  have bodyFrame := Zkir.lowerBody_preservesOutputCapacityFrame circuit
    (by
      intro condition member
      rw [constraintsEmpty] at member
      simp at member)
    (by
      intro output member
      rw [outputsMatch] at member
      obtain ⟨name, _, rfl⟩ := List.mem_map.mp member
      exact bytes32ReturnPreflight_preservesOutputCapacityFrame name value)
    (by
      intro output member projections fieldsAccepted field fieldMember
      rw [outputsMatch] at member
      obtain ⟨name, _, rfl⟩ := List.mem_map.mp member
      exact bytes32ReturnFields_preservesOutputCapacityFrame name value fieldFrames
        projections fieldsAccepted field fieldMember)
  exact bodyFrame {}

private def publicSecpPointInput : Input := {
  name := "point"
  ty := .foreign (.point .secp256k1)
  visibility := .public
}

private def publicSecpPointReturnCircuit : Circuit := {
  name := "publicSecpPointReturn"
  inputs := [publicSecpPointInput]
  outputs := [{
    name := "pointResult"
    ty := .foreign (.point .secp256k1)
    value := .ref "point"
  }]
}

private def publicSecpPointReturnState : Zkir.LowerState :=
  ((Zkir.lowerBody (Passes.pruneCircuit publicSecpPointReturnCircuit)).run {}).2

private def publicSecpPointInputPrefixState : Zkir.LowerState :=
  (Zkir.lowerPublicForeignInputPrefix publicSecpPointInput (.point .secp256k1)).run {} |>.2

theorem publicSecpPointInputPrefix_has_output_capacity_frame :
    Zkir.OutputCapacityFrame {} publicSecpPointInputPrefixState := by
  simpa [publicSecpPointInputPrefixState, publicSecpPointInput] using
    (Zkir.lowerPublicForeignInputPrefix_preservesOutputCapacityFrame "point"
      (.point .secp256k1) {}) {}

set_option maxHeartbeats 0 in
theorem publicSecpPointReturn_counts_and_reuses_encoding :
    publicSecpPointReturnCircuit.outputs.map (·.nativeReturnFieldCount) = [5] ∧
      publicSecpPointReturnState.next = 5 ∧
      publicSecpPointReturnState.instructions.size = 9 ∧
      publicSecpPointReturnState.outputDefinitions = 6 ∧
      (publicSecpPointReturnState.instructions.toList.map Native.opcode).count "encode" = 1 ∧
      Native.outputDefinitionsInInstruction publicSecpPointReturnState.instructions[1]! = 5 := by
  decide +kernel

set_option maxHeartbeats 0 in
theorem publicSecpPointReturn_has_actual_output_capacity_frame :
    Zkir.OutputCapacityFrame {} publicSecpPointReturnState := by
  have counts := publicSecpPointReturn_counts_and_reuses_encoding
  rcases counts with ⟨_, next, _, definitions, _, _⟩
  constructor
  · change 0 ≤ publicSecpPointReturnState.next
    rw [next]
    omega
  · change 0 + (publicSecpPointReturnState.next - 0) ≤
      publicSecpPointReturnState.outputDefinitions
    rw [next, definitions]
    omega

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
  let value : Expr (.bytes 32) := .persistentHash32 (.ref "preimage")
  have hashFrame := Zkir.lowerBytes_persistentHash32_preservesOutputCapacityFrame
    (.ref "preimage") (Zkir.lowerBytes_ref_preservesOutputCapacityFrame "preimage")
  have fieldFrames : ∀ index,
      Zkir.PreservesOutputCapacityFrame (Zkir.lowerExpr (.bytesField value index)) :=
    fun index => Zkir.lowerExpr_bytesField_preservesOutputCapacityFrame value index hashFrame
  have frame := bytes32OutputCircuit_has_output_capacity_frame
    (Passes.pruneCircuit packedInputHashCircuit) ["digest"] value (by rfl) (by rfl)
    fieldFrames
  simpa [packedInputHashState] using frame

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
  let value : Expr (.bytes 32) :=
    .persistentHash32 (.bytes32Literal (List.replicate 32 0))
  have hashFrame := Zkir.lowerBytes_persistentHash32_preservesOutputCapacityFrame
    (.bytes32Literal (List.replicate 32 0))
    (Zkir.lowerBytes_literal32_preservesOutputCapacityFrame (List.replicate 32 0))
  have fieldFrames : ∀ index,
      Zkir.PreservesOutputCapacityFrame (Zkir.lowerExpr (.bytesField value index)) :=
    fun index => Zkir.lowerExpr_bytesField_preservesOutputCapacityFrame value index hashFrame
  have frame := bytes32OutputCircuit_has_output_capacity_frame
    (Passes.pruneCircuit hashCircuit) ["digest"]
    value (by rfl) (by rfl) fieldFrames
  simpa [hashState] using frame

/-- A repeated persistent hash emits both public results but reuses the one
hash and packing sequence. -/
theorem cachedTwoLimbHash_counts_and_cache_hit :
    cachedHashCircuit.outputs.length = 2 ∧ cachedHashState.next = 3 ∧
      cachedHashState.instructions.size = 4 ∧
      cachedHashState.outputDefinitions = 3 ∧
      (cachedHashState.instructions.toList.map Native.opcode).count "persistent_hash" = 1 ∧
      (cachedHashState.instructions.toList.map Native.opcode).count "bytes_into_natives" = 1 ∧
      Native.outputDefinitionsInInstruction cachedHashState.instructions[1]! = 2 ∧
      (cachedHashState.instructions.toList.map Native.opcode).count "output" = 1 := by
  decide +kernel

theorem cachedTwoLimbHash_has_actual_output_capacity_frame :
    Zkir.OutputCapacityFrame {} cachedHashState := by
  let value : Expr (.bytes 32) :=
    .persistentHash32 (.bytes32Literal (List.replicate 32 0))
  have hashFrame := Zkir.lowerBytes_persistentHash32_preservesOutputCapacityFrame
    (.bytes32Literal (List.replicate 32 0))
    (Zkir.lowerBytes_literal32_preservesOutputCapacityFrame (List.replicate 32 0))
  have fieldFrames : ∀ index,
      Zkir.PreservesOutputCapacityFrame (Zkir.lowerExpr (.bytesField value index)) :=
    fun index => Zkir.lowerExpr_bytesField_preservesOutputCapacityFrame value index hashFrame
  have frame := bytes32OutputCircuit_has_output_capacity_frame
    (Passes.pruneCircuit cachedHashCircuit) ["firstDigest", "secondDigest"]
    value (by rfl) (by rfl) fieldFrames
  simpa [cachedHashState] using frame

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

#guard accepted (Zkir.lowerCircuit cachedHashCircuit)

theorem coldTwoLimbHash_has_producerCapacity {program : Lean.Json}
    (produced : Zkir.lowerCircuit hashCircuit = .ok program) :
    hashState.outputDefinitions ≤ Native.maxInstructions * Native.maxVectorLength :=
  lowerCircuit_outputDefinitions_budget hashCircuit produced

theorem coldTwoLimbHash_names_fit_producerCapacity :
    ∀ {program : Lean.Json}, Zkir.lowerCircuit hashCircuit = .ok program →
      hashState.next ≤ Native.maxInstructions * Native.maxVectorLength :=
  fun produced => lowerCircuit_output_budget_of_frame hashCircuit produced
    coldTwoLimbHash_has_actual_output_capacity_frame

theorem cachedTwoLimbHash_has_producerCapacity {program : Lean.Json}
    (produced : Zkir.lowerCircuit cachedHashCircuit = .ok program) :
    cachedHashState.outputDefinitions ≤ Native.maxInstructions * Native.maxVectorLength :=
  lowerCircuit_outputDefinitions_budget cachedHashCircuit produced

theorem cachedTwoLimbHash_names_fit_producerCapacity :
    ∀ {program : Lean.Json}, Zkir.lowerCircuit cachedHashCircuit = .ok program →
      cachedHashState.next ≤ Native.maxInstructions * Native.maxVectorLength :=
  fun produced => lowerCircuit_output_budget_of_frame cachedHashCircuit produced
    cachedTwoLimbHash_has_actual_output_capacity_frame

#guard accepted (Zkir.lowerCircuit packedInputHashCircuit)

#guard accepted (Zkir.lowerCircuit publicSecpPointReturnCircuit)

theorem packedInputHash_has_producerCapacity {program : Lean.Json}
    (produced : Zkir.lowerCircuit packedInputHashCircuit = .ok program) :
    packedInputHashState.outputDefinitions ≤ Native.maxInstructions * Native.maxVectorLength :=
  lowerCircuit_outputDefinitions_budget packedInputHashCircuit produced

theorem packedInputHash_names_fit_producerCapacity :
    ∀ {program : Lean.Json}, Zkir.lowerCircuit packedInputHashCircuit = .ok program →
      packedInputHashState.next ≤ Native.maxInstructions * Native.maxVectorLength :=
  fun produced => lowerCircuit_output_budget_of_frame packedInputHashCircuit produced
    packedInputHash_has_actual_output_capacity_frame

theorem publicSecpPointReturn_has_producerCapacity {program : Lean.Json}
    (produced : Zkir.lowerCircuit publicSecpPointReturnCircuit = .ok program) :
    publicSecpPointReturnState.outputDefinitions ≤
      Native.maxInstructions * Native.maxVectorLength :=
  lowerCircuit_outputDefinitions_budget publicSecpPointReturnCircuit produced

theorem publicSecpPointReturn_names_fit_producerCapacity :
    ∀ {program : Lean.Json},
      Zkir.lowerCircuit publicSecpPointReturnCircuit = .ok program →
      publicSecpPointReturnState.next ≤ Native.maxInstructions * Native.maxVectorLength :=
  fun produced => lowerCircuit_output_budget_of_frame publicSecpPointReturnCircuit produced
    publicSecpPointReturn_has_actual_output_capacity_frame

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
