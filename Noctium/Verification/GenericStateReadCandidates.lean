import Noctium.Verification.GenericStateCheckedReadDecode

namespace Noctium.Verification.GenericStateReadCandidates

open Backend NativeRelation ScalarNormalization
open GenericStateCheckedReadTrace GenericStateInputValues

private theorem readChunk_member (effects : List Effect) (ordinal : Nat)
    (effect : Effect) (metadata : ReadMetadata) (member : effect ∈ effects)
    (produces : ∀ position, metadata ∈ effectReadChunk effect position) :
    metadata ∈ (readChunks effects ordinal).flatten := by
  induction effects generalizing ordinal with
  | nil => cases member
  | cons head rest ih =>
    rcases List.mem_cons.mp member with first | later
    · subst head
      exact List.mem_append_left _ (produces ordinal)
    · exact List.mem_append_right _ (ih _ later)

/-- The source read's destination and type occur in the metadata tape at
its own source effect, even after earlier reads advance the ordinal. -/
theorem readCell_in_readChunks (effects : List Effect) (ordinal : Nat)
    (name destination : String) (ty : Ty)
    (member : Effect.readCell name destination ty ∈ effects) :
    (destination, ty) ∈ (readChunks effects ordinal).flatten := by
  exact readChunk_member effects ordinal _ _ member (by intro; simp [effectReadChunk])

theorem readMap_in_readChunks (effects : List Effect) (ordinal : Nat)
    (name destination : String) (keyTy valueTy : Ty) (key : Expr keyTy)
    (member : Effect.readMap name destination keyTy valueTy key ∈ effects) :
    (destination, valueTy) ∈ (readChunks effects ordinal).flatten := by
  exact readChunk_member effects ordinal _ _ member (by intro; simp [effectReadChunk])

/-- A source cell read selects its exact typed candidate from the accepted
plan's post-public reads. The candidate still needs the checked native state
read to authenticate its value. -/
theorem readCell_candidate (state : List StateDecl) (entry : Entrypoint)
    (plan : Impact.Plan) (base decodedValues : EvalEnv) (witness : Assignment)
    (name destination : String) (ty : Ty)
    (accepted : Impact.lower state entry = .ok plan)
    (scope : GuardedScalarReadEffects entry.effectGuards entry.effects.zipIdx)
    (member : Effect.readCell name destination ty ∈ entry.effects)
    (decoded : decodeReads (plan.reads.drop (Impact.publicInputReadCount entry.circuit.inputs))
      witness = .ok decodedValues)
    (distinct : (plan.reads.drop (Impact.publicInputReadCount entry.circuit.inputs)).Pairwise
      (fun left right => left.name ≠ right.name))
    (fresh : base.lookup destination = none)
    (typed : ty.validate {poseidon2 := true, stateCells := true, stateMaps := true} = .ok ())
    (bounded : (witness ("%input_" ++ destination)).val ≤ Native.sourceMaximum ty) :
    ∃ candidate : ty.Denote,
      (base ++ decodedValues).lookup destination = some (Value.pack ty candidate) ∧
      Canonical ty candidate ∧
      sourceScalar? ty candidate = some (witness ("%input_" ++ destination)) := by
  obtain ⟨boundaries, inputPlan, lowered, prefixAccepted, _⟩ :=
    GenericStateAdmissionPrefix.lower_input_prefix state entry plan accepted
  have prefixLength :=
    GenericStateAdmissionPrefix.publicInputPlan_readCount entry.circuit.inputs inputPlan prefixAccepted
  rw [← prefixLength] at decoded distinct
  exact GenericStateCheckedReadDecode.lowerWithEffectBoundaries_read_candidate
    state entry plan inputPlan boundaries witness base decodedValues destination ty
    lowered scope prefixAccepted
    (readCell_in_readChunks entry.effects inputPlan.reads.length name destination ty member)
    decoded distinct fresh typed bounded

/-- A source Map read selects its exact typed candidate from the accepted
plan's post-public reads. The candidate still needs the checked native state
read to authenticate its value. -/
theorem readMap_candidate (state : List StateDecl) (entry : Entrypoint)
    (plan : Impact.Plan) (base decodedValues : EvalEnv) (witness : Assignment)
    (name destination : String) (keyTy ty : Ty) (key : Expr keyTy)
    (accepted : Impact.lower state entry = .ok plan)
    (scope : GuardedScalarReadEffects entry.effectGuards entry.effects.zipIdx)
    (member : Effect.readMap name destination keyTy ty key ∈ entry.effects)
    (decoded : decodeReads (plan.reads.drop (Impact.publicInputReadCount entry.circuit.inputs))
      witness = .ok decodedValues)
    (distinct : (plan.reads.drop (Impact.publicInputReadCount entry.circuit.inputs)).Pairwise
      (fun left right => left.name ≠ right.name))
    (fresh : base.lookup destination = none)
    (typed : ty.validate {poseidon2 := true, stateCells := true, stateMaps := true} = .ok ())
    (bounded : (witness ("%input_" ++ destination)).val ≤ Native.sourceMaximum ty) :
    ∃ candidate : ty.Denote,
      (base ++ decodedValues).lookup destination = some (Value.pack ty candidate) ∧
      Canonical ty candidate ∧
      sourceScalar? ty candidate = some (witness ("%input_" ++ destination)) := by
  obtain ⟨boundaries, inputPlan, lowered, prefixAccepted, _⟩ :=
    GenericStateAdmissionPrefix.lower_input_prefix state entry plan accepted
  have prefixLength :=
    GenericStateAdmissionPrefix.publicInputPlan_readCount entry.circuit.inputs inputPlan prefixAccepted
  rw [← prefixLength] at decoded distinct
  exact GenericStateCheckedReadDecode.lowerWithEffectBoundaries_read_candidate
    state entry plan inputPlan boundaries witness base decodedValues destination ty
    lowered scope prefixAccepted
    (readMap_in_readChunks entry.effects inputPlan.reads.length name destination keyTy ty key member)
    decoded distinct fresh typed bounded

end Noctium.Verification.GenericStateReadCandidates
