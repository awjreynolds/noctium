import Noctium.Backend.Zkir
import Noctium.Verification.ScalarNormalization
import Noctium.Verification.ScalarCircuit
import Noctium.Verification.NativeRelationJson

namespace Noctium.Verification.ScalarAllocationOutputFrame

open Backend

theorem lowerExpr_admitted_preservesOutputCapacityFrame (value : Expr ty)
    (admitted : ScalarNormalization.ScalarExpression value) :
    Zkir.PreservesOutputCapacityFrame (Zkir.lowerExpr value) := by
  induction admitted with
  | native number =>
    simp only [Zkir.lowerExpr]
    exact Zkir.pure_preservesOutputCapacityFrame _
  | bool boolean =>
    simp only [Zkir.lowerExpr]
    exact Zkir.pure_preservesOutputCapacityFrame _
  | uint maximum number =>
    simp only [Zkir.lowerExpr]
    exact Zkir.pure_preservesOutputCapacityFrame _
  | ref name scalarType =>
    cases scalarType
    all_goals
      simp only [Zkir.lowerExpr]
      have getFrame : Zkir.PreservesOutputCapacityFrame
          (get : StateM Zkir.LowerState Zkir.LowerState) := by
        intro state
        exact Zkir.OutputCapacityFrame.refl state
      apply Zkir.bind_preservesOutputCapacityFrame _ _ getFrame
      intro state
      exact Zkir.pure_preservesOutputCapacityFrame _
  | add left right leftSupported rightSupported leftFrame rightFrame =>
    simp only [Zkir.lowerExpr]
    apply Zkir.bind_preservesOutputCapacityFrame _ _ leftFrame
    intro leftValue
    apply Zkir.bind_preservesOutputCapacityFrame _ _ rightFrame
    intro rightValue
    exact Zkir.nativeAdd_preservesOutputCapacityFrame
      (Native.isLiteralNativeZero left) (Native.isLiteralNativeZero right)
      leftValue rightValue
  | mul left right leftSupported rightSupported leftFrame rightFrame =>
    simp only [Zkir.lowerExpr]
    apply Zkir.bind_preservesOutputCapacityFrame _ _ leftFrame
    intro leftValue
    apply Zkir.bind_preservesOutputCapacityFrame _ _ rightFrame
    intro rightValue
    exact Zkir.ordinaryBinary_preservesOutputCapacityFrame "mul" leftValue rightValue
      ⟨by decide, by decide, by decide⟩
  | sub left right leftSupported rightSupported leftFrame rightFrame =>
    simp only [Zkir.lowerExpr]
    apply Zkir.bind_preservesOutputCapacityFrame _ _ leftFrame
    intro leftValue
    apply Zkir.bind_preservesOutputCapacityFrame _ _ rightFrame
    intro rightValue
    apply Zkir.bind_preservesOutputCapacityFrame _ _
      (Zkir.ordinaryUnary_preservesOutputCapacityFrame "neg" rightValue
        ⟨by decide, by decide, by decide⟩)
    intro negated
    exact Zkir.ordinaryBinary_preservesOutputCapacityFrame "add" leftValue negated
      ⟨by decide, by decide, by decide⟩
  | uadd left right leftSupported rightSupported leftFrame rightFrame =>
    simp only [Zkir.lowerExpr]
    apply Zkir.bind_preservesOutputCapacityFrame _ _ leftFrame
    intro leftValue
    apply Zkir.bind_preservesOutputCapacityFrame _ _ rightFrame
    intro rightValue
    exact Zkir.nativeUIntAdd_preservesOutputCapacityFrame _
      (Native.isLiteralUIntZero left) (Native.isLiteralUIntZero right)
      leftValue rightValue
  | usub left right leftSupported rightSupported leftFrame rightFrame =>
    simp only [Zkir.lowerExpr]
    apply Zkir.bind_preservesOutputCapacityFrame _ _ leftFrame
    intro leftValue
    apply Zkir.bind_preservesOutputCapacityFrame _ _ rightFrame
    intro rightValue
    apply Zkir.bind_preservesOutputCapacityFrame _ _
      (Zkir.ordinaryUnary_preservesOutputCapacityFrame "neg" rightValue
        ⟨by decide, by decide, by decide⟩)
    intro negated
    apply Zkir.bind_preservesOutputCapacityFrame _ _
      (Zkir.ordinaryBinary_preservesOutputCapacityFrame "add" leftValue negated
        ⟨by decide, by decide, by decide⟩)
    intro output
    apply Zkir.bind_preservesOutputCapacityFrame _ _
      (Zkir.constrainUnsigned_preservesOutputCapacityFrame _ output)
    intro ignored
    exact Zkir.pure_preservesOutputCapacityFrame output
  | umul left right leftSupported rightSupported leftFrame rightFrame =>
    simp only [Zkir.lowerExpr]
    apply Zkir.bind_preservesOutputCapacityFrame _ _ leftFrame
    intro leftValue
    apply Zkir.bind_preservesOutputCapacityFrame _ _ rightFrame
    intro rightValue
    apply Zkir.bind_preservesOutputCapacityFrame _ _
      (Zkir.ordinaryBinary_preservesOutputCapacityFrame "mul" leftValue rightValue
        ⟨by decide, by decide, by decide⟩)
    intro output
    apply Zkir.bind_preservesOutputCapacityFrame _ _
      (Zkir.constrainUnsigned_preservesOutputCapacityFrame _ output)
    intro ignored
    exact Zkir.pure_preservesOutputCapacityFrame output
  | @cast source target value sourceType targetType valueSupported valueFrame =>
    cases targetType with
    | native =>
      simp only [Zkir.lowerExpr]
      apply Zkir.bind_preservesOutputCapacityFrame _ _ valueFrame
      intro output
      exact Zkir.pure_preservesOutputCapacityFrame output
    | bool =>
      simp only [Zkir.lowerExpr]
      apply Zkir.bind_preservesOutputCapacityFrame _ _ valueFrame
      intro output
      apply Zkir.bind_preservesOutputCapacityFrame _ _
        (Zkir.ordinaryBinary_preservesOutputCapacityFrame "test_eq" output "0x00"
          ⟨by decide, by decide, by decide⟩)
      intro zero
      exact Zkir.ordinaryUnary_preservesOutputCapacityFrame "not" zero
        ⟨by decide, by decide, by decide⟩
    | uint maximum =>
      simp only [Zkir.lowerExpr]
      apply Zkir.bind_preservesOutputCapacityFrame _ _ valueFrame
      intro output
      apply Zkir.bind_preservesOutputCapacityFrame _ _
        (Zkir.constrainUnsigned_preservesOutputCapacityFrame maximum output)
      intro ignored
      exact Zkir.pure_preservesOutputCapacityFrame output
  | @letE source target name value body sourceScalar valueSupported bodySupported valueFrame bodyFrame =>
    cases sourceScalar
    all_goals
      simp only [Zkir.lowerExpr]
      apply Zkir.bind_preservesOutputCapacityFrame _ _ valueFrame
      intro valueText
      have readStateFrame : Zkir.PreservesOutputCapacityFrame
          (get : StateM Zkir.LowerState Zkir.LowerState) := by
        intro state
        exact Zkir.OutputCapacityFrame.refl state
      apply Zkir.bind_preservesOutputCapacityFrame _ _ readStateFrame
      intro previousState
      apply Zkir.bind_preservesOutputCapacityFrame _ _
        (Zkir.modify_preservesOutputCapacityFrame
          (fun state => {state with aliases := (name, valueText) :: previousState.aliases})
          (by intro state; rfl) (by intro state; rfl))
      intro ignored
      apply Zkir.bind_preservesOutputCapacityFrame _ _ bodyFrame
      intro result
      apply Zkir.bind_preservesOutputCapacityFrame _ _
        (Zkir.modify_preservesOutputCapacityFrame
          (fun state => {state with aliases := previousState.aliases})
          (by intro state; rfl) (by intro state; rfl))
      intro ignored
      exact Zkir.pure_preservesOutputCapacityFrame result
  | assertE condition body conditionSupported bodySupported conditionFrame bodyFrame =>
    simp only [Zkir.lowerExpr]
    apply Zkir.bind_preservesOutputCapacityFrame _ _ conditionFrame
    intro value
    apply Zkir.bind_preservesOutputCapacityFrame _ _
      (Zkir.emit_preservesOutputCapacityFrame "assert" [("cond", Lean.toJson value)])
    intro ignored
    exact bodyFrame
  | copyValue value supported valueFrame =>
    simp only [Zkir.lowerExpr]
    apply Zkir.bind_preservesOutputCapacityFrame _ _ valueFrame
    intro operand
    exact Zkir.copyVal_preservesOutputCapacityFrame operand
  | disclose span value supported valueFrame =>
    simpa only [Zkir.lowerExpr] using valueFrame
  | eq left right scalarType leftSupported rightSupported leftFrame rightFrame =>
    cases scalarType
    all_goals
      simp only [Zkir.lowerExpr]
      apply Zkir.bind_preservesOutputCapacityFrame _ _ leftFrame
      intro leftValue
      apply Zkir.bind_preservesOutputCapacityFrame _ _ rightFrame
      intro rightValue
      exact Zkir.ordinaryBinary_preservesOutputCapacityFrame "test_eq" leftValue rightValue
        ⟨by decide, by decide, by decide⟩
  | select condition yes no scalarType conditionSupported yesSupported noSupported
      conditionFrame yesFrame noFrame =>
    exact Zkir.lowerExpr_select_preservesOutputCapacityFrame condition yes no
      conditionFrame yesFrame noFrame
  | poseidon2 domain left right leftSupported rightSupported leftFrame rightFrame =>
    exact Zkir.lowerExpr_poseidon2_preservesOutputCapacityFrame domain left right
      leftFrame rightFrame

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

private def sha512ThreeChunkValue : Expr (.bytes 64) :=
  .sha512 (length := 1) (.bytesLiteral 1 [0])

private def sha512ThreeChunkField : Expr .native :=
  .disclose {} (.bytesField sha512ThreeChunkValue 0)

private def sha512ThreeChunkOutput : Output := {
  name := "firstChunk"
  ty := .native
  value := sha512ThreeChunkField
}

private def sha512ThreeChunkCircuit : Circuit := {
  name := "sha512ThreeChunkOutputFrame"
  outputs := [sha512ThreeChunkOutput]
}

private def sha512ThreeChunkState : Zkir.LowerState :=
  ((Zkir.lowerBody (Passes.pruneCircuit sha512ThreeChunkCircuit)).run {}).2

theorem sha512ThreeChunk_actualEmission_counts :
    sha512ThreeChunkState.next = 4 ∧
      sha512ThreeChunkState.instructions.size = 4 ∧
      sha512ThreeChunkState.outputDefinitions = 4 ∧
      Native.opcode sha512ThreeChunkState.instructions[0]! = "sha512" ∧
      Native.opcode sha512ThreeChunkState.instructions[1]! = "bytes_into_natives" ∧
      Native.outputDefinitionsInInstruction sha512ThreeChunkState.instructions[1]! = 3 := by
  decide +kernel

/-- A concrete SHA-512 return exercises the three fresh SSA names emitted by
one dynamic bytes_into_natives instruction. The frame uses the actual ZKIR
lowering and its output slot count. -/
theorem sha512ThreeChunk_has_actual_output_capacity_frame :
    Zkir.OutputCapacityFrame {} sha512ThreeChunkState := by
  let pruned := Passes.pruneCircuit sha512ThreeChunkCircuit
  have digestFrame := Zkir.lowerBytes_sha512_preservesOutputCapacityFrame
      (.bytesLiteral 1 [0])
      (Zkir.lowerBytes_literal_preservesOutputCapacityFrame [0])
  have projectedFrame := Zkir.lowerExpr_bytesField_preservesOutputCapacityFrame
    sha512ThreeChunkValue 0 digestFrame
  have fieldFrame : Zkir.PreservesOutputCapacityFrame (Zkir.lowerExpr sha512ThreeChunkField) := by
    simpa [sha512ThreeChunkField, Zkir.lowerExpr] using projectedFrame
  have bodyFrame := Zkir.lowerBody_preservesOutputCapacityFrame pruned
    (by
      intro condition member
      simp [pruned, sha512ThreeChunkCircuit, Passes.pruneCircuit, pruneTrue] at member)
    (by
      intro output member
      have outputEq : output = sha512ThreeChunkOutput := by
        simpa [pruned, sha512ThreeChunkCircuit, Passes.pruneCircuit, pruneTrue] using member
      subst output
      simpa [Zkir.lowerReturnPreflight, sha512ThreeChunkOutput] using
        (Zkir.pure_preservesOutputCapacityFrame ()))
    (by
      intro output member projections fieldsAccepted field fieldMember
      have outputEq : output = sha512ThreeChunkOutput := by
        simpa [pruned, sha512ThreeChunkCircuit, Passes.pruneCircuit, pruneTrue] using member
      subst output
      have projectionsEq : [sha512ThreeChunkField] = projections := by
        have parsed : (Except.ok [sha512ThreeChunkField] : Except String (List (Expr .native))) =
            .ok projections := by
          change Except.ok [sha512ThreeChunkField] = Except.ok projections at fieldsAccepted
          exact fieldsAccepted
        exact Except.ok.inj parsed
      have fieldIn : field ∈ [sha512ThreeChunkField] := by
        simpa [projectionsEq] using fieldMember
      have fieldEq : field = sha512ThreeChunkField := by simpa using fieldIn
      subst field
      exact fieldFrame)
  simpa [sha512ThreeChunkState, pruned] using bodyFrame {}

#guard (Zkir.lowerCircuit sha512ThreeChunkCircuit).isOk

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

/-- Connect a frame for the exact accepted ledger plan to the native decoder's
identifier limit. The producer validates the emitted output-slot budget. -/
theorem lowerEntrypoint_name_budget_of_frame (state : List StateDecl)
    (entry : Entrypoint) (program : Lean.Json)
    (accepted : Zkir.lowerEntrypoint state entry = .ok program)
    (frame : ∀ plan, Impact.lower state (Passes.pruneEntrypoint entry) = .ok plan →
      Zkir.OutputCapacityFrame {} ((Zkir.lowerEntrypointBody (Passes.pruneEntrypoint entry) plan).run {}).2) :
    ∃ plan, Impact.lower state (Passes.pruneEntrypoint entry) = .ok plan ∧
      let next := ((Zkir.lowerEntrypointBody (Passes.pruneEntrypoint entry) plan).run {}).2.next
      next ≤ Native.maxInstructions * Native.maxVectorLength ∧
        ∀ index, index < next → NativeRelationJson.validIdentifier s!"%v{index}" = true := by
  obtain ⟨plan, planAccepted, capacity⟩ :=
    lowerEntrypoint_outputDefinitions_budget state entry program accepted
  have bounded := Zkir.OutputCapacityFrame.next_le_producerCapacity
    (frame plan planAccepted) capacity
  refine ⟨plan, planAccepted, bounded, ?_⟩
  intro index indexBound
  exact NativeRelationJson.generatedIdentifier_fits_output_capacity index
    (Nat.lt_of_lt_of_le indexBound bounded)

private theorem scalarReturnPreflight_preservesOutputCapacityFrame
    (circuit : Circuit)
    (admitted : ScalarNormalization.ScalarCircuitAdmission circuit)
    (output : Output) (member : output ∈ circuit.outputs) :
    Zkir.PreservesOutputCapacityFrame (Zkir.lowerReturnPreflight output) := by
  cases output with
  | mk name ty value span =>
    obtain ⟨scalarType, _⟩ := admitted.outputs ⟨name, ty, value, span⟩ member
    cases scalarType with
    | native =>
      simpa [Zkir.lowerReturnPreflight] using Zkir.pure_preservesOutputCapacityFrame ()
    | bool =>
      simpa [Zkir.lowerReturnPreflight] using Zkir.pure_preservesOutputCapacityFrame ()
    | uint maximum =>
      simpa [Zkir.lowerReturnPreflight] using Zkir.pure_preservesOutputCapacityFrame ()

private theorem scalarReturnFields_preservesOutputCapacityFrame
    (circuit : Circuit)
    (admitted : ScalarNormalization.ScalarCircuitAdmission circuit)
    (output : Output) (member : output ∈ circuit.outputs) :
    ∀ projections, output.nativeReturnFields = .ok projections → ∀ field ∈ projections,
      Zkir.PreservesOutputCapacityFrame (Zkir.lowerExpr field) := by
  obtain ⟨nativeField, fieldsAccepted, expressionAdmission⟩ :=
    ScalarNormalization.ScalarCircuitAdmission.nativeReturnFields
      circuit admitted output member
  intro projections acceptedProjections field fieldMember
  have projectionsEq : [nativeField] = projections :=
    Except.ok.inj (fieldsAccepted.symm.trans acceptedProjections)
  subst projections
  have fieldEq : field = nativeField := by simpa using fieldMember
  subst field
  exact lowerExpr_admitted_preservesOutputCapacityFrame nativeField expressionAdmission

/-- Scalar admission supplies every expression frame needed to prove the
default, pruned circuit body preserves its output allocation capacity. -/
theorem lowerBody_scalarAdmission_has_output_capacity_frame (circuit : Circuit)
    (admitted : ScalarNormalization.ScalarCircuitAdmission circuit) :
    Zkir.OutputCapacityFrame {} ((Zkir.lowerBody (Passes.pruneCircuit circuit)).run {}).2 := by
  let pruned := Passes.pruneCircuit circuit
  have prunedAdmission :=
    ScalarNormalization.ScalarCircuitAdmission.pruneCircuit circuit admitted
  have bodyFrame := Zkir.lowerBody_preservesOutputCapacityFrame pruned
    (fun condition member =>
      lowerExpr_admitted_preservesOutputCapacityFrame condition
        (prunedAdmission.constraints condition member))
    (fun output member =>
      scalarReturnPreflight_preservesOutputCapacityFrame pruned prunedAdmission output member)
    (fun output member =>
      scalarReturnFields_preservesOutputCapacityFrame pruned prunedAdmission output member)
  exact bodyFrame {}

/-- An accepted producer circuit assigns numeric names within the producer's
output budget whenever its source circuit has scalar admission. -/
theorem lowerCircuit_scalarAdmission_names_fit_producerCapacity (circuit : Circuit)
    (admitted : ScalarNormalization.ScalarCircuitAdmission circuit) {program : Lean.Json}
    (produced : Zkir.lowerCircuit circuit = .ok program) :
    ((Zkir.lowerBody (Passes.pruneCircuit circuit)).run {}).2.next ≤
      Native.maxInstructions * Native.maxVectorLength :=
  lowerCircuit_output_budget_of_frame circuit produced
    (lowerBody_scalarAdmission_has_output_capacity_frame circuit admitted)

/-- Every default-lowering name covered by the accepted producer result fits
the native relation JSON decoder's identifier limit. -/
theorem lowerCircuit_scalarAdmission_generatedIdentifier (circuit : Circuit)
    (admitted : ScalarNormalization.ScalarCircuitAdmission circuit) {program : Lean.Json}
    (produced : Zkir.lowerCircuit circuit = .ok program) :
    ∀ index, index < ((Zkir.lowerBody (Passes.pruneCircuit circuit)).run {}).2.next →
      NativeRelationJson.validIdentifier s!"%v{index}" = true := by
  intro index bounded
  apply NativeRelationJson.generatedIdentifier_fits_output_capacity
  exact Nat.lt_of_lt_of_le bounded
    (lowerCircuit_scalarAdmission_names_fit_producerCapacity circuit admitted produced)

end Noctium.Verification.ScalarAllocationOutputFrame
