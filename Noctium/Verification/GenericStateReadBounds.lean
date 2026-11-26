import Noctium.Verification.GenericStateLowering
import Noctium.Verification.GenericStateCheckedReadDecode

namespace Noctium.Verification.GenericStateReadBounds
open Backend NativeRelation ScalarNormalization

/-- The satisfying relation's producer bounds apply to each singleton scalar
read binding in the actual post-public suffix of the accepted Impact plan. -/
theorem accepted_read_bounds (state : List StateDecl) (entry : Entrypoint)
    (json : Lean.Json) (relation : Program) (hash : Hash)
    (witness : Assignment) (streams : InputStreams)
    (publicGroups : List (List Scalar))
    (lowered : Zkir.lowerEntrypoint state entry = .ok json)
    (decoded : NativeRelationJson.decode json = .ok relation)
    (satisfies : CircuitSatisfies hash relation streams witness publicGroups) :
    ∃ plan, Impact.lower state (Passes.pruneEntrypoint entry) = .ok plan ∧
      ∀ read ∈ plan.reads.drop
        (Impact.publicInputReadCount (Passes.pruneEntrypoint entry).circuit.inputs),
        read.bindings = [(read.name, read.ty)] → ScalarType read.ty →
          (witness ("%input_" ++ read.name)).val ≤ Native.sourceMaximum read.ty := by
  let ep := Passes.pruneEntrypoint entry
  obtain ⟨plan, expected, planAccepted, expectedAccepted, validated, _⟩ :=
    GenericStateLowering.lowerEntrypoint_validated state entry json lowered
  obtain ⟨bounded, boundedAccepted, inputBounds⟩ :=
    GenericStateLowering.accepted_relation_input_bounds_self state entry json
      relation hash witness streams publicGroups lowered decoded satisfies
  have same := Except.ok.inj (boundedAccepted.symm.trans expectedAccepted)
  subst bounded
  obtain ⟨_, headerEmpty, _, _⟩ :=
    NativeRelationInstructionProjection.decode_headerAndInstructions decoded
  have rawEmpty := (ScalarValidationProjection.validate_driver_result_empty_header
    validated headerEmpty).1
  refine ⟨plan, planAccepted, ?_⟩
  intro read member singleton scalarType
  have supported : read.ty = .native ∨ read.ty = .bool ∨ ∃ width, read.ty = .uint width := by
    cases ty : read.ty with
    | native => exact Or.inl rfl
    | bool => exact Or.inr (Or.inl rfl)
    | uint width => exact Or.inr (Or.inr ⟨width, rfl⟩)
    | _ => rw [ty] at scalarType; cases scalarType
  exact GenericStateCheckedReadDecode.accepted_scalarRead_inputBound_of_requirements
    state ep expected expectedAccepted plan planAccepted read read.name read.ty
    member singleton supported (by
      intro requirement present _ ordinary
      rw [rawEmpty, List.nil_append] at present
      exact inputBounds requirement present ordinary)

end Noctium.Verification.GenericStateReadBounds
