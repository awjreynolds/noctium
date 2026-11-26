import Noctium.Verification.GenericStateReadTypes
import Noctium.Verification.GenericStateReadBounds

namespace Noctium.Verification.GenericStateReadAdmission
open Backend NativeRelation ScalarNormalization
open GenericStateEffectValidation GenericStateCheckedReadTrace

/-- The accepted descriptor of a scalar ledger-read candidate validates at
the source type and bounds the corresponding witness lane. -/
theorem accepted_read_candidates (state : List StateDecl) (entry : Entrypoint)
    (json : Lean.Json) (relation : Program) (hash : Hash)
    (witness : Assignment) (streams : InputStreams)
    (publicGroups : List (List Scalar))
    (lowered : Zkir.lowerEntrypoint state entry = .ok json)
    (decoded : NativeRelationJson.decode json = .ok relation)
    (satisfies : CircuitSatisfies hash relation streams witness publicGroups)
    (typed : ScalarStateEffects (Passes.pruneEntrypoint entry).effects)
    (scope : GuardedScalarReadEffects (Passes.pruneEntrypoint entry).effectGuards
      (Passes.pruneEntrypoint entry).effects.zipIdx) :
    ∃ plan, Impact.lower state (Passes.pruneEntrypoint entry) = .ok plan ∧
      ∀ read ∈ plan.reads.drop
        (Impact.publicInputReadCount (Passes.pruneEntrypoint entry).circuit.inputs),
        read.bindings = [(read.name, read.ty)] → ScalarType read.ty →
          read.ty.validate {poseidon2 := true, stateCells := true, stateMaps := true} = .ok () ∧
          (witness ("%input_" ++ read.name)).val ≤ Native.sourceMaximum read.ty := by
  obtain ⟨plan, accepted, bounded⟩ :=
    GenericStateReadBounds.accepted_read_bounds state entry json relation hash
      witness streams publicGroups lowered decoded satisfies
  refine ⟨plan, accepted, ?_⟩
  intro read member singleton scalarType
  have checked := GenericStateReadTypes.lower_read_types state
    (Passes.pruneEntrypoint entry) plan accepted typed scope read member
  refine ⟨?_, bounded read member singleton scalarType⟩
  have sameCaps : read.ty.validate
      {poseidon2 := true, stateCells := true, stateMaps := true} =
        read.ty.validate stateEffectCaps := by
    cases ty : read.ty with
    | native | bool | uint => rfl
    | _ => rw [ty] at scalarType; cases scalarType
  rwa [sameCaps]

end Noctium.Verification.GenericStateReadAdmission
