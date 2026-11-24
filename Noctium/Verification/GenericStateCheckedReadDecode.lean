import Noctium.Verification.GenericStateCheckedReadTrace
import Noctium.Verification.GenericStateCandidateDecode

namespace Noctium.Verification.GenericStateCheckedReadDecode
open Backend
open NativeRelation ScalarNormalization
open GenericStateCheckedReadTrace
open GenericStateInputValues

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
  obtain ⟨acceptedPrefix, prefixSame, metadata⟩ :=
    lowerWithEffectBoundaries_read_metadata state entry plan boundaries accepted
      unguarded scope
  have samePrefix : acceptedPrefix = inputPlan :=
    Except.ok.inj (prefixSame.symm.trans prefixAccepted)
  subst acceptedPrefix
  have suffixMetadata :
      (plan.reads.drop inputPlan.reads.length).map readMetadata =
        (readChunks entry.effects inputPlan.reads.length).flatten := by
    have full : plan.reads.map readMetadata =
        inputPlan.reads.map readMetadata ++
          (readChunks entry.effects inputPlan.reads.length).flatten := by
      simpa [planReadMetadata] using metadata
    rw [List.map_drop, full]
    simp [List.length_map]
  obtain ⟨decodedValues, decoded, meaning⟩ :=
    GenericStateCandidateDecode.decodeReads_candidate_meaning
      (plan.reads.drop inputPlan.reads.length) witness supported distinct typed bounded
  exact ⟨decodedValues, decoded, suffixMetadata, meaning⟩

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
