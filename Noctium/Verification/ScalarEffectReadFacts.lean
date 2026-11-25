import Noctium.Verification.GenericStateAdmissionPrefix
import Noctium.Verification.GenericStateCheckedReadTrace
import Noctium.Verification.GenericStateReadCandidates

namespace Noctium.Verification.ScalarEffectReadFacts

open Backend
open NativeRelation
open GenericStateCheckedReadTrace

/-- Exact names and types of the checked plan's post-public read tape. -/
theorem lower_postPublic_read_metadata (state : List StateDecl)
    (entry : Entrypoint) (plan : Impact.Plan)
    (lowered : Impact.lower state entry = .ok plan)
    (scope : GuardedScalarReadEffects entry.effectGuards (entry.effects.zipIdx)) :
    (plan.reads.drop (Impact.publicInputReadCount entry.circuit.inputs)).map readMetadata =
      (readChunks entry.effects (Impact.publicInputReadCount entry.circuit.inputs)).flatten := by
  obtain ⟨boundaries, inputPlan, boundedLowering, prefixAccepted, _⟩ :=
    GenericStateAdmissionPrefix.lower_guarded_effect_trace state entry plan lowered
  have metadata := lowerWithEffectBoundaries_guarded_read_metadata state entry plan boundaries
    boundedLowering scope
  obtain ⟨actualInputPlan, actualPrefix, readMetadataShape⟩ := metadata
  have prefixEqual : actualInputPlan = inputPlan :=
    Except.ok.inj (actualPrefix.symm.trans prefixAccepted)
  subst actualInputPlan
  have cutoff := GenericStateAdmissionPrefix.publicInputPlan_readCount
    entry.circuit.inputs inputPlan prefixAccepted
  have mappedDrop :
      (plan.reads.drop (Impact.publicInputReadCount entry.circuit.inputs)).map readMetadata =
        (planReadMetadata plan).drop (Impact.publicInputReadCount entry.circuit.inputs) := by
    simp [planReadMetadata, List.map_drop]
  rw [mappedDrop, readMetadataShape]
  change List.drop (Impact.publicInputReadCount entry.circuit.inputs)
      (inputPlan.reads.map readMetadata ++
        (readChunks entry.effects inputPlan.reads.length).flatten) = _
  have mappedCutoff : (inputPlan.reads.map readMetadata).length =
      Impact.publicInputReadCount entry.circuit.inputs := by
    rw [List.length_map, cutoff]
  rw [List.drop_left' mappedCutoff, cutoff]

/-- A source cell read contributes its exact destination/type pair to the
accepted plan's post-public read descriptors. -/
theorem readCell_descriptor (state : List StateDecl) (entry : Entrypoint)
    (plan : Impact.Plan) (name destination : String) (ty : Ty)
    (lowered : Impact.lower state entry = .ok plan)
    (scope : GuardedScalarReadEffects entry.effectGuards (entry.effects.zipIdx))
    (member : Effect.readCell name destination ty ∈ entry.effects) :
    ∃ read, read ∈ plan.reads.drop
      (Impact.publicInputReadCount entry.circuit.inputs) ∧
      read.name = destination ∧ read.ty = ty := by
  have pairMember : (destination, ty) ∈
      (readChunks entry.effects (Impact.publicInputReadCount entry.circuit.inputs)).flatten :=
    GenericStateReadCandidates.readCell_in_readChunks entry.effects
      (Impact.publicInputReadCount entry.circuit.inputs)
      name destination ty member
  rw [← lower_postPublic_read_metadata state entry plan lowered scope] at pairMember
  have mapped : (destination, ty) ∈
      (plan.reads.drop (Impact.publicInputReadCount entry.circuit.inputs)).map readMetadata :=
    pairMember
  obtain ⟨read, readMember, same⟩ := List.mem_map.mp mapped
  refine ⟨read, readMember, ?_, ?_⟩
  · have names := congrArg Prod.fst same
    simpa [readMetadata] using names
  · have types := congrArg Prod.snd same
    simpa [readMetadata] using types

/-- A source map read contributes its exact destination/value-type pair to the
accepted plan's post-public read descriptors. -/
theorem readMap_descriptor (state : List StateDecl) (entry : Entrypoint)
    (plan : Impact.Plan) (name destination : String) (keyTy valueTy : Ty)
    (key : Expr keyTy) (lowered : Impact.lower state entry = .ok plan)
    (scope : GuardedScalarReadEffects entry.effectGuards (entry.effects.zipIdx))
    (member : Effect.readMap name destination keyTy valueTy key ∈ entry.effects) :
    ∃ read, read ∈ plan.reads.drop
      (Impact.publicInputReadCount entry.circuit.inputs) ∧
      read.name = destination ∧ read.ty = valueTy := by
  have pairMember : (destination, valueTy) ∈
      (readChunks entry.effects (Impact.publicInputReadCount entry.circuit.inputs)).flatten :=
    GenericStateReadCandidates.readMap_in_readChunks entry.effects
      (Impact.publicInputReadCount entry.circuit.inputs)
      name destination keyTy valueTy key member
  rw [← lower_postPublic_read_metadata state entry plan lowered scope] at pairMember
  have mapped : (destination, valueTy) ∈
      (plan.reads.drop (Impact.publicInputReadCount entry.circuit.inputs)).map readMetadata :=
    pairMember
  obtain ⟨read, readMember, same⟩ := List.mem_map.mp mapped
  refine ⟨read, readMember, ?_, ?_⟩
  · have names := congrArg Prod.fst same
    simpa [readMetadata] using names
  · have types := congrArg Prod.snd same
    simpa [readMetadata] using types

/-- Facts consumed by checked effect lowering follow from the accepted plan's
actual post-public scalar read descriptors. The source effect's destination
and type are matched against the plan metadata before descriptor facts are
transported to the input witness. -/
theorem lower_read_facts (state : List StateDecl) (entry : Entrypoint)
    (plan : Impact.Plan) (base : EvalEnv) (witness : Assignment)
    (accepted : Impact.lower state entry = .ok plan)
    (scope : GuardedScalarReadEffects entry.effectGuards (entry.effects.zipIdx))
    (fresh : ∀ read ∈ plan.reads.drop
      (Impact.publicInputReadCount entry.circuit.inputs),
      base.lookup read.name = none)
    (typed : ∀ read ∈ plan.reads.drop
      (Impact.publicInputReadCount entry.circuit.inputs),
      read.ty.validate {poseidon2 := true, stateCells := true, stateMaps := true} = .ok ())
    (witnessBounds : ∀ read ∈ plan.reads.drop
      (Impact.publicInputReadCount entry.circuit.inputs),
      (witness ("%input_" ++ read.name)).val ≤ Native.sourceMaximum read.ty) :
    ∀ effect ∈ entry.effects, match effect with
      | .readCell _ destination ty | .readMap _ destination _ ty _ =>
        base.lookup destination = none ∧
        ty.validate {poseidon2 := true, stateCells := true, stateMaps := true} = .ok () ∧
        (witness ("%input_" ++ destination)).val ≤ Native.sourceMaximum ty
      | _ => True := by
  intro effect member
  cases effect with
  | readCell name destination ty =>
    obtain ⟨read, readMember, nameEqual, typeEqual⟩ :=
      readCell_descriptor state entry plan name destination ty accepted scope member
    have readFresh := fresh read readMember
    have readTyped := typed read readMember
    have readBound := witnessBounds read readMember
    refine ⟨?_, ?_, ?_⟩
    · simpa [nameEqual] using readFresh
    · rw [← typeEqual]
      exact readTyped
    · simpa [nameEqual, typeEqual] using readBound
  | readMap name destination keyTy valueTy key =>
    obtain ⟨read, readMember, nameEqual, typeEqual⟩ :=
      readMap_descriptor state entry plan name destination keyTy valueTy key
        accepted scope member
    have readFresh := fresh read readMember
    have readTyped := typed read readMember
    have readBound := witnessBounds read readMember
    refine ⟨?_, ?_, ?_⟩
    · simpa [nameEqual] using readFresh
    · rw [← typeEqual]
      exact readTyped
    · simpa [nameEqual, typeEqual] using readBound
  | _ => trivial

end Noctium.Verification.ScalarEffectReadFacts
