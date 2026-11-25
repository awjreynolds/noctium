import Noctium.Verification.GenericStateCheckedReadDecode

namespace Noctium.Verification.GenericStateReadCandidates

open Backend NativeRelation ScalarNormalization
open GenericStateCheckedReadTrace GenericStateInputValues

/-- A source cell read appears at its own position in the metadata tape,
including when earlier reads change the generated read ordinal. -/
theorem readCell_in_readChunks (effects : List Effect) (ordinal : Nat)
    (name destination : String) (ty : Ty)
    (member : Effect.readCell name destination ty ∈ effects) :
    (destination, ty) ∈ (readChunks effects ordinal).flatten := by
  induction effects generalizing ordinal with
  | nil => cases member
  | cons effect rest ih =>
    rcases List.mem_cons.mp member with first | later
    · subst effect
      simp [readChunks, effectReadChunk]
    · simp only [readChunks, List.flatten_cons, List.mem_append]
      exact Or.inr (ih _ later)

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

end Noctium.Verification.GenericStateReadCandidates
