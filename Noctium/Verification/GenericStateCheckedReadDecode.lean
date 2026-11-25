import Noctium.Verification.GenericStateCheckedReadTrace
import Noctium.Verification.GenericStateCandidateDecode
import Noctium.Verification.GenericStateCircuitParts
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

private theorem read_suffix_metadata (state : List StateDecl) (entry : Entrypoint)
    (plan inputPlan : Impact.Plan) (boundaries : List Nat)
    (accepted : Impact.lowerWithEffectBoundaries state entry = .ok (plan, boundaries))
    (unguarded : entry.effectGuards = [])
    (scope : ScalarReadEffects entry.effects)
    (prefixAccepted : Impact.publicInputPlan entry.circuit.inputs {} = .ok inputPlan) :
    (plan.reads.drop inputPlan.reads.length).map readMetadata =
      (readChunks entry.effects inputPlan.reads.length).flatten := by
  obtain ⟨actualPrefix, prefixLowered, metadata⟩ :=
    lowerWithEffectBoundaries_read_metadata state entry plan boundaries accepted unguarded scope
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
    (unguarded : entry.effectGuards = [])
    (scope : ScalarReadEffects entry.effects)
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
    read_suffix_metadata state entry plan inputPlan boundaries accepted unguarded scope
      prefixAccepted, meaning⟩

/-- The same value looked up for a source read has the canonical encoding of
its candidate witness lane. The read must occur in the accepted production
suffix. A later native step still authenticates the candidate against state. -/
theorem lowerWithEffectBoundaries_read_candidate (state : List StateDecl)
    (entry : Entrypoint) (plan inputPlan : Impact.Plan) (boundaries : List Nat)
    (witness : Assignment) (base decodedValues : EvalEnv) (name : String) (ty : Ty)
    (accepted : Impact.lowerWithEffectBoundaries state entry = .ok (plan, boundaries))
    (unguarded : entry.effectGuards = [])
    (scope : ScalarReadEffects entry.effects)
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
  rw [← read_suffix_metadata state entry plan inputPlan boundaries accepted unguarded scope
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
    (unguarded : entry.effectGuards = [])
    (scope : ScalarReadEffects entry.effects)
    (prefixAccepted : Impact.publicInputPlan entry.circuit.inputs {} = .ok inputPlan)
    (head : plan.reads.drop inputPlan.reads.length = read :: rest)
    (unsupported : scalarType? read.ty = none) :
    decodeReads (plan.reads.drop inputPlan.reads.length) witness =
      .error "unsupported non-scalar read type" := by
  have metadata := lowerWithEffectBoundaries_read_metadata state entry plan
    boundaries accepted unguarded scope
  obtain ⟨acceptedPrefix, prefixSame, _⟩ := metadata
  have samePrefix : acceptedPrefix = inputPlan :=
    Except.ok.inj (prefixSame.symm.trans prefixAccepted)
  subst acceptedPrefix
  rw [head]
  exact decodeReads_unsupported_head read rest witness unsupported

end Noctium.Verification.GenericStateCheckedReadDecode
