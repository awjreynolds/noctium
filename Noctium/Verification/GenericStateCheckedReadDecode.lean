import Noctium.Verification.GenericStateCheckedReadTrace
import Noctium.Verification.GenericStateCandidateDecode
import Noctium.Verification.GenericStateCircuitParts
import Noctium.Verification.NativeRelationInstructionProjection
import Noctium.Verification.RangeDedupAcceptedArray
import Noctium.Verification.ScalarValidationNativeDefinitions
import Noctium.Verification.ScalarValidationProjection

namespace Noctium.Verification.GenericStateCheckedReadDecode
open Backend
open NativeRelation ScalarNormalization
open GenericStateCheckedReadTrace
open GenericStateInputValues

/-- An accepted Native validation bounds the input slot for an actual
post-public scalar read in the accepted Impact plan. The descriptor match
connects the plan's singleton binding to the expected constructor's input
slot. This bounds the accepted scalar input; it does not authenticate a
candidate read value against ledger state. -/
theorem accepted_scalarRead_inputBound
    (state : List StateDecl) (entry : Entrypoint)
    (expected : Backend.Native.Expected)
    (expectedAccepted : Backend.Native.expectedEntrypoint state entry = .ok expected)
    (plan : Backend.Impact.Plan)
    (planAccepted : Backend.Impact.lower state entry = .ok plan)
    (read : Backend.Impact.Read) (name : String) (ty : Ty)
    (postPublic : read ∈ plan.reads.drop
      (Backend.Impact.publicInputReadCount entry.circuit.inputs))
    (singleton : read.bindings = [(name, ty)])
    (supported : ty = .native ∨ ty = .bool ∨ ∃ width, ty = .uint width)
    {program : Lean.Json} {instructions rawInputs : Array Lean.Json}
    {seed final : Backend.Native.State} {hash : Hash} {inputs witness : Assignment}
    (driver : ScalarValidationProjection.NativeValidationDriverFacts
      expected program instructions rawInputs seed final)
    (meaning : ScalarValidationMeaning.StateMeaning hash inputs witness final) :
    (inputs ("%input_" ++ name)).val ≤ Backend.Native.sourceMaximum ty := by
  obtain ⟨requirement, requirementPresent, descriptor⟩ :=
    GenericStateCircuitParts.expectedEntrypoint_scalarReadDescriptor state entry expected
      expectedAccepted plan planAccepted read name ty postPublic singleton supported
  have identifier : requirement.identifier = "%input_" ++ name := by
    have projection := congrArg Prod.fst descriptor
    simpa [GenericStateCircuitParts.inputRequirementCore] using projection
  have requirementTy : requirement.ty = ty := by
    have projection := congrArg
      (fun core : String × Visibility × Ty × Bool => core.2.2.1) descriptor
    simpa [GenericStateCircuitParts.inputRequirementCore] using projection
  have ordinary : requirement.canonicalJubjubScalar = false := by
    have projection := congrArg
      (fun core : String × Visibility × Ty × Bool => core.2.2.2) descriptor
    simpa [GenericStateCircuitParts.inputRequirementCore] using projection
  have nonforeign : requirement.ty.isForeign = false := by
    rw [requirementTy]
    rcases supported with native | bool | ⟨width, uint⟩
    · rw [native]
      rfl
    · rw [bool]
      rfl
    · rw [uint]
      rfl
  have bound := driver.inputBound meaning
    (List.mem_append_right expected.rawInputs requirementPresent) nonforeign ordinary
  simpa [identifier, requirementTy] using bound

/-- The accepted default lowerer and checked scalar opcode profile provide the
final Native state meaning needed to bound every identity-preserving singleton
scalar read in the accepted post-public Impact suffix. -/
theorem accepted_scalarRead_inputBounds_of_checkedProfile
    (state : List StateDecl) (entry : Entrypoint)
    (json : Lean.Json) (relation : NativeRelation.Program)
    (hash : Hash) (witness : Assignment) (streams : InputStreams)
    (publicGroups : List (List Scalar))
    (lowered : Backend.Zkir.lowerEntrypoint state entry = .ok json)
    (decoded : NativeRelationJson.decode json = .ok relation)
    (satisfies : CircuitSatisfies hash relation streams witness publicGroups)
    (inputSchema : ∀ expected,
      Backend.Native.expectedEntrypoint state (Passes.pruneEntrypoint entry) = .ok expected →
      ∀ requirement ∈ expected.inputs, requirement.ty.isForeign = false)
    (profile : ∃ instructions : Array Lean.Json,
      Backend.Native.arrayField json "instructions" = .ok instructions ∧
      ScalarValidationOpcodeProfile.checkedScalarOpcodeProfile
        (instructions.toList.zipIdx) relation.instructions = true) :
    ∃ plan, Backend.Impact.lower state (Passes.pruneEntrypoint entry) = .ok plan ∧
      ∀ read ∈ plan.reads.drop
        (Backend.Impact.publicInputReadCount
          (Passes.pruneEntrypoint entry).circuit.inputs),
        read.bindings = [(read.name, read.ty)] →
        (scalarType? read.ty).isSome = true →
        (witness ("%input_" ++ read.name)).val ≤
          Backend.Native.sourceMaximum read.ty := by
  let ep := Passes.pruneEntrypoint entry
  obtain ⟨plan, expected, _, planAccepted, expectedAccepted, validated, _, _, _⟩ :=
    NativeRelationInstructionProjection.lowerEntrypoint_instructionProjection
      state entry json relation lowered decoded
  obtain ⟨decodedRows, inputHeader, decodedRowsParsed, decodedInstructions⟩ :=
    NativeRelationInstructionProjection.decode_headerAndInstructions decoded
  obtain ⟨instructions, instructionsParsed, profileAccepted⟩ := profile
  obtain ⟨_, driverInstructions, final, driver⟩ :=
    ScalarValidationProjection.validate_driver_result_empty_header validated inputHeader
  have decodedRowsEq : decodedRows = instructions :=
    Except.ok.inj (decodedRowsParsed.symm.trans instructionsParsed)
  subst decodedRows
  have driverInstructionsEq : driverInstructions = instructions :=
    Except.ok.inj (driver.instructionsParsed.symm.trans instructionsParsed)
  subst driverInstructions
  have indexedDecoded :
      ((instructions.toList.zipIdx).map Prod.fst).mapM
        NativeRelationJson.decodeInstruction = .ok relation.instructions := by
    rw [List.zipIdx_map_fst]
    exact decodedInstructions
  have acceptedSteps := RangeDedupAcceptedArray.checkedScalarOpcodeProfile_acceptedMeaningSteps
    indexedDecoded profileAccepted satisfies.instructions
  obtain ⟨meaning, _, _⟩ := RangeDedupAcceptedArray.accepted_loop_meaning_at_steps
    (ScalarValidationMeaning.empty_meaning hash witness witness)
    ScalarValidationNativeDefinitions.empty_nativeDefinitions
    (inputSchema expected expectedAccepted) (by intro _ _; rfl) acceptedSteps
    driver.instructionTrace
  refine ⟨plan, planAccepted, ?_⟩
  intro read postPublic singleton supported
  have supportedTy : read.ty = .native ∨ read.ty = .bool ∨
      ∃ width, read.ty = .uint width := by
    cases readTy : read.ty with
    | native => exact Or.inl rfl
    | bool => exact Or.inr (Or.inl rfl)
    | uint width => exact Or.inr (Or.inr ⟨width, rfl⟩)
    | bytes _ => rw [readTy] at supported; simp [scalarType?] at supported
    | opaqueBytes => rw [readTy] at supported; simp [scalarType?] at supported
    | opaqueString => rw [readTy] at supported; simp [scalarType?] at supported
    | jubjubScalar => rw [readTy] at supported; simp [scalarType?] at supported
    | jubjubPoint => rw [readTy] at supported; simp [scalarType?] at supported
    | foreign _ => rw [readTy] at supported; simp [scalarType?] at supported
  exact accepted_scalarRead_inputBound state ep expected expectedAccepted
    plan planAccepted read read.name read.ty postPublic singleton supportedTy driver meaning

private theorem supported_plain_read_bindings (read : Impact.Read)
    (plain : read.components = []) (supported : (scalarType? read.ty).isSome = true) :
    read.bindings = [(read.name, read.ty)] := by
  cases read with
  | mk name ty components schema guard rootCellRead =>
    change components = [] at plain
    subst components
    cases ty <;> first | rfl | cases supported

/-- The actual decoded scalar relation supplies all bounds needed to decode
the admitted post-public reads of its own Impact plan and type their aliases.
The caller supplies scalar descriptor and type admission. The checked ledger
execution must still authenticate these candidate bindings against state. -/
theorem accepted_scalarRead_environment
    (state : List StateDecl) (entry : Entrypoint) (plan : Impact.Plan)
    (json : Lean.Json) (relation : NativeRelation.Program)
    (hash : Hash) (witness : Assignment) (streams : InputStreams)
    (publicGroups : List (List Scalar))
    (lowered : Backend.Zkir.lowerEntrypoint state entry = .ok json)
    (decoded : NativeRelationJson.decode json = .ok relation)
    (satisfies : CircuitSatisfies hash relation streams witness publicGroups)
    (planAccepted : Impact.lower state (Passes.pruneEntrypoint entry) = .ok plan)
    (inputSchema : ∀ expected,
      Backend.Native.expectedEntrypoint state (Passes.pruneEntrypoint entry) = .ok expected →
      ∀ requirement ∈ expected.inputs, requirement.ty.isForeign = false)
    (profile : ∃ instructions : Array Lean.Json,
      Backend.Native.arrayField json "instructions" = .ok instructions ∧
      ScalarValidationOpcodeProfile.checkedScalarOpcodeProfile
        (instructions.toList.zipIdx) relation.instructions = true)
    (admitted : ∀ read ∈ plan.reads.drop (Impact.publicInputReadCount entry.circuit.inputs),
      read.components = [] ∧ (scalarType? read.ty).isSome = true ∧
      read.ty.validate {poseidon2 := true, stateCells := true, stateMaps := true} = .ok ()) :
    let reads := plan.reads.drop (Impact.publicInputReadCount entry.circuit.inputs)
    ∃ values, decodeReads reads witness = .ok values ∧
      TypedEnvironment hash witness (readAliases reads) values (readTypes reads) ∧
      ∀ read ∈ reads, (witness ("%input_" ++ read.name)).val ≤ Native.sourceMaximum read.ty := by
  let reads := plan.reads.drop (Impact.publicInputReadCount entry.circuit.inputs)
  obtain ⟨actualPlan, actualAccepted, bounds⟩ :=
    accepted_scalarRead_inputBounds_of_checkedProfile state entry json relation
      hash witness streams publicGroups lowered decoded satisfies inputSchema profile
  have exactPlan := Except.ok.inj (actualAccepted.symm.trans planAccepted)
  subst actualPlan
  have bounded : ∀ read ∈ reads,
      (witness ("%input_" ++ read.name)).val ≤ Native.sourceMaximum read.ty := by
    intro read member
    obtain ⟨plain, supported, _⟩ := admitted read member
    exact bounds read member (supported_plain_read_bindings read plain supported) supported
  obtain ⟨values, success⟩ := GenericStateCandidateDecode.decodeReads_supported_success
    reads witness (fun read member => (admitted read member).2.1)
  exact ⟨values, success, decodedReads_typedEnvironment reads hash witness values success
    (fun read member => (admitted read member).2.2) bounded, bounded⟩

private theorem read_suffix_metadata (state : List StateDecl) (entry : Entrypoint)
    (plan inputPlan : Impact.Plan) (boundaries : List Nat)
    (accepted : Impact.lowerWithEffectBoundaries state entry = .ok (plan, boundaries))
    (scope : GuardedScalarReadEffects entry.effectGuards entry.effects.zipIdx)
    (prefixAccepted : Impact.publicInputPlan entry.circuit.inputs {} = .ok inputPlan) :
    (plan.reads.drop inputPlan.reads.length).map readMetadata =
      (readChunks entry.effects inputPlan.reads.length).flatten := by
  obtain ⟨actualPrefix, prefixLowered, metadata⟩ :=
    lowerWithEffectBoundaries_guarded_read_metadata state entry plan boundaries accepted scope
  have prefixEq := Except.ok.inj (prefixLowered.symm.trans prefixAccepted)
  subst actualPrefix
  rw [List.map_drop]
  change (planReadMetadata plan).drop inputPlan.reads.length = _
  rw [metadata]
  simp [planReadMetadata]

/-- A successful checked decode keeps each production read's name and type in
its ordered candidate environment. The metadata suffix still comes from the
accepted production lowering trace. -/
theorem lowerWithEffectBoundaries_decodeReads (state : List StateDecl)
    (entry : Entrypoint) (plan : Impact.Plan) (boundaries : List Nat)
    (inputPlan : Impact.Plan) (witness : Assignment)
    (accepted : Impact.lowerWithEffectBoundaries state entry = .ok (plan, boundaries))
    (scope : GuardedScalarReadEffects entry.effectGuards entry.effects.zipIdx)
    (prefixAccepted : Impact.publicInputPlan entry.circuit.inputs {} = .ok inputPlan)
    (supported : ∀ read ∈ plan.reads.drop inputPlan.reads.length,
      (scalarType? read.ty).isSome = true)
    (distinct : (plan.reads.drop inputPlan.reads.length).Pairwise
      (fun left right => left.name ≠ right.name))
    (typed : ∀ read ∈ plan.reads.drop inputPlan.reads.length,
      read.ty.validate {poseidon2 := true, stateCells := true, stateMaps := true} = .ok ())
    (bounded : ∀ read ∈ plan.reads.drop inputPlan.reads.length,
      (witness ("%input_" ++ read.name)).val ≤ Native.sourceMaximum read.ty) :
    ∃ decodedValues,
      decodeReads (plan.reads.drop inputPlan.reads.length) witness = .ok decodedValues ∧
      (plan.reads.drop inputPlan.reads.length).map readMetadata =
        (readChunks entry.effects inputPlan.reads.length).flatten ∧
      ∀ read ∈ plan.reads.drop inputPlan.reads.length,
        (∃ decoder : ScalarType read.ty,
          decodedValues.lookup read.name = some (Value.pack read.ty
            (sourceValue decoder (witness ("%input_" ++ read.name))))) ∧
        (∃ decoder : ScalarType read.ty,
          Canonical read.ty (sourceValue decoder (witness ("%input_" ++ read.name))) ∧
          sourceScalar? read.ty (sourceValue decoder
            (witness ("%input_" ++ read.name))) =
              some (witness ("%input_" ++ read.name))) := by
  obtain ⟨decodedValues, decoded, meaning⟩ :=
    GenericStateCandidateDecode.decodeReads_candidate_meaning
      (plan.reads.drop inputPlan.reads.length) witness supported distinct typed bounded
  exact ⟨decodedValues, decoded,
    read_suffix_metadata state entry plan inputPlan boundaries accepted scope
      prefixAccepted, meaning⟩

/-- The same value looked up for a source read has the canonical encoding of
its candidate witness lane. The read must occur in the accepted production
suffix. A later native step still authenticates the candidate against state. -/
theorem lowerWithEffectBoundaries_read_candidate (state : List StateDecl)
    (entry : Entrypoint) (plan inputPlan : Impact.Plan) (boundaries : List Nat)
    (witness : Assignment) (base decodedValues : EvalEnv) (name : String) (ty : Ty)
    (accepted : Impact.lowerWithEffectBoundaries state entry = .ok (plan, boundaries))
    (scope : GuardedScalarReadEffects entry.effectGuards entry.effects.zipIdx)
    (prefixAccepted : Impact.publicInputPlan entry.circuit.inputs {} = .ok inputPlan)
    (sourceRead : (name, ty) ∈ (readChunks entry.effects inputPlan.reads.length).flatten)
    (decoded : decodeReads (plan.reads.drop inputPlan.reads.length) witness = .ok decodedValues)
    (distinct : (plan.reads.drop inputPlan.reads.length).Pairwise
      (fun left right => left.name ≠ right.name))
    (fresh : base.lookup name = none)
    (typed : ty.validate {poseidon2 := true, stateCells := true, stateMaps := true} = .ok ())
    (bounded : (witness ("%input_" ++ name)).val ≤ Native.sourceMaximum ty) :
    ∃ candidate : ty.Denote,
      (base ++ decodedValues).lookup name = some (Value.pack ty candidate) ∧
      Canonical ty candidate ∧ sourceScalar? ty candidate = some (witness ("%input_" ++ name)) := by
  rw [← read_suffix_metadata state entry plan inputPlan boundaries accepted scope
    prefixAccepted] at sourceRead
  obtain ⟨read, member, same⟩ := List.mem_map.mp sourceRead
  have nameEq : read.name = name := congrArg Prod.fst same
  have typeEq : read.ty = ty := congrArg Prod.snd same
  subst name
  subst ty
  exact GenericStateReadEnvironment.read_candidate_from_decoded_reads base
    (plan.reads.drop inputPlan.reads.length) witness decodedValues decoded distinct
    read member fresh typed bounded

/-- The checked candidate decoder rejects an unsupported first read instead
of supplying a default value. -/
theorem decodeReads_unsupported_head (read : Impact.Read)
    (rest : List Impact.Read) (witness : Assignment)
    (unsupported : scalarType? read.ty = none) :
    decodeReads (read :: rest) witness = .error "unsupported non-scalar read type" := by
  simp [decodeReads, List.mapM_cons, decodeRead, unsupported,
    bind, Except.bind]

/-- An unsupported first read in an exact accepted production suffix keeps the
same checked failure. This theorem makes no claim about ledger authentication. -/
theorem lowerWithEffectBoundaries_unsupported_head_fails (state : List StateDecl)
    (entry : Entrypoint) (plan : Impact.Plan) (boundaries : List Nat)
    (inputPlan : Impact.Plan) (witness : Assignment)
    (read : Impact.Read) (rest : List Impact.Read)
    (accepted : Impact.lowerWithEffectBoundaries state entry = .ok (plan, boundaries))
    (scope : GuardedScalarReadEffects entry.effectGuards entry.effects.zipIdx)
    (prefixAccepted : Impact.publicInputPlan entry.circuit.inputs {} = .ok inputPlan)
    (head : plan.reads.drop inputPlan.reads.length = read :: rest)
    (unsupported : scalarType? read.ty = none) :
    decodeReads (plan.reads.drop inputPlan.reads.length) witness =
      .error "unsupported non-scalar read type" := by
  have metadata := lowerWithEffectBoundaries_guarded_read_metadata state entry plan
    boundaries accepted scope
  obtain ⟨acceptedPrefix, prefixSame, _⟩ := metadata
  have samePrefix : acceptedPrefix = inputPlan :=
    Except.ok.inj (prefixSame.symm.trans prefixAccepted)
  subst acceptedPrefix
  rw [head]
  exact decodeReads_unsupported_head read rest witness unsupported

end Noctium.Verification.GenericStateCheckedReadDecode
