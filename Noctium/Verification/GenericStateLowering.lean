import Noctium.Backend.Zkir
import Noctium.Verification.ScalarValidation

namespace Noctium.Verification.GenericStateLowering
open Backend

/-- Project the real default ledger producer acceptance theorem onto the
independent expected statement, producer validation, and exact emitted
instruction array. -/
theorem lowerEntrypoint_validated (state : List StateDecl) (entry : Entrypoint)
    (json : Lean.Json) (lowered : Zkir.lowerEntrypoint state entry = .ok json) :
    ∃ plan expected,
      Impact.lower state (Passes.pruneEntrypoint entry) = .ok plan ∧
      Native.expectedEntrypoint state (Passes.pruneEntrypoint entry) = .ok expected ∧
      Native.validate expected json = .ok () ∧
      Native.arrayField json "instructions" =
        .ok ((Zkir.lowerEntrypointBody (Passes.pruneEntrypoint entry) plan).run {}).2.instructions := by
  obtain ⟨plan, expected, planAccepted, expectedAccepted, validated, instructions⟩ :=
    Zkir.lowerEntrypoint_validation_and_instructions state entry json lowered
  exact ⟨plan, expected, planAccepted, expectedAccepted, validated, instructions⟩

/-- The exact strict decoded accepted relation fixes its groups, source bounds,
and assertions for every satisfying assignment. Input names required by the
producer agree between the source assignment and that assignment. -/
theorem accepted_relation_groups (state : List StateDecl) (entry : Entrypoint)
    (json : Lean.Json) (relation : NativeRelation.Program)
    (hash : NativeRelation.Hash) (inputs witness : NativeRelation.Assignment)
    (streams : NativeRelation.InputStreams)
    (publicGroups : List (List NativeRelation.Scalar))
    (lowered : Zkir.lowerEntrypoint state entry = .ok json)
    (decoded : NativeRelationJson.decode json = .ok relation)
    (satisfies : NativeRelation.CircuitSatisfies hash relation streams witness publicGroups)
    (binding : ∀ expected,
      Native.expectedEntrypoint state (Passes.pruneEntrypoint entry) = .ok expected →
      ScalarValidation.InputAgreement expected inputs witness) :
    ∃ plan expected,
      Impact.lower state (Passes.pruneEntrypoint entry) = .ok plan ∧
      Native.expectedEntrypoint state (Passes.pruneEntrypoint entry) = .ok expected ∧
      publicGroups.map (List.map some) =
        expected.groups.map (List.map (ScalarNormalization.interpret hash inputs)) ∧
      (∀ requirement ∈ expected.bounds,
        ∃ value, ScalarNormalization.interpret hash inputs requirement.1 = some value ∧
          value.val ≤ requirement.2) ∧
      (∀ assertion ∈ expected.assertions,
        ScalarNormalization.interpret hash inputs assertion = some NativeRelation.one) := by
  obtain ⟨plan, expected, planAccepted, expectedAccepted, validated, _instructions⟩ :=
    lowerEntrypoint_validated state entry json lowered
  have facts := ScalarValidation.validate_sound (binding expected expectedAccepted)
    validated decoded satisfies
  exact ⟨plan, expected, planAccepted, expectedAccepted,
    facts.impact, facts.bounds, facts.assertions⟩

/-- Specialize the general accepted relation theorem to the satisfying
assignment itself. -/
theorem accepted_relation_groups_self (state : List StateDecl) (entry : Entrypoint)
    (json : Lean.Json) (relation : NativeRelation.Program)
    (hash : NativeRelation.Hash) (witness : NativeRelation.Assignment)
    (streams : NativeRelation.InputStreams)
    (publicGroups : List (List NativeRelation.Scalar))
    (lowered : Zkir.lowerEntrypoint state entry = .ok json)
    (decoded : NativeRelationJson.decode json = .ok relation)
    (satisfies : NativeRelation.CircuitSatisfies hash relation streams witness publicGroups) :
    ∃ plan expected,
      Impact.lower state (Passes.pruneEntrypoint entry) = .ok plan ∧
      Native.expectedEntrypoint state (Passes.pruneEntrypoint entry) = .ok expected ∧
      publicGroups.map (List.map some) =
        expected.groups.map (List.map (ScalarNormalization.interpret hash witness)) ∧
      (∀ requirement ∈ expected.bounds,
        ∃ value, ScalarNormalization.interpret hash witness requirement.1 = some value ∧
          value.val ≤ requirement.2) ∧
      (∀ assertion ∈ expected.assertions,
        ScalarNormalization.interpret hash witness assertion = some NativeRelation.one) := by
  exact accepted_relation_groups state entry json relation hash witness witness streams
    publicGroups lowered decoded satisfies (by
      intro expected _
      intro requirement _
      rfl)

/-- Ordinary producer inputs satisfy their source type bounds in every
satisfying assignment. The exact strict decoder has an empty raw header, so
these are the expected statement's complete input requirements. -/
theorem accepted_relation_input_bounds (state : List StateDecl)
    (entry : Entrypoint) (json : Lean.Json) (relation : NativeRelation.Program)
    (hash : NativeRelation.Hash) (inputs witness : NativeRelation.Assignment)
    (streams : NativeRelation.InputStreams)
    (publicGroups : List (List NativeRelation.Scalar))
    (lowered : Zkir.lowerEntrypoint state entry = .ok json)
    (decoded : NativeRelationJson.decode json = .ok relation)
    (satisfies : NativeRelation.CircuitSatisfies hash relation streams witness publicGroups)
    (binding : ∀ expected,
      Native.expectedEntrypoint state (Passes.pruneEntrypoint entry) = .ok expected →
      ScalarValidation.InputAgreement expected inputs witness) :
    ∃ expected,
      Native.expectedEntrypoint state (Passes.pruneEntrypoint entry) = .ok expected ∧
      ∀ requirement ∈ expected.inputs,
        requirement.canonicalJubjubScalar = false →
        (witness requirement.identifier).val ≤ Native.sourceMaximum requirement.ty := by
  obtain ⟨_, expected, _, expectedAccepted, validated, _instructions⟩ :=
    lowerEntrypoint_validated state entry json lowered
  have facts := ScalarValidation.validate_sound (binding expected expectedAccepted)
    validated decoded satisfies
  refine ⟨expected, expectedAccepted, ?_⟩
  intro requirement member ordinary
  calc
    (witness requirement.identifier).val = (inputs requirement.identifier).val :=
      congrArg (fun value : NativeRelation.Scalar => value.val)
        (binding expected expectedAccepted requirement member)
    _ ≤ Native.sourceMaximum requirement.ty := facts.inputBounds requirement member ordinary

/-- Self-specialized ordinary input bounds, again for an arbitrary satisfying
assignment (here the source assignment is that same assignment). -/
theorem accepted_relation_input_bounds_self (state : List StateDecl)
    (entry : Entrypoint) (json : Lean.Json) (relation : NativeRelation.Program)
    (hash : NativeRelation.Hash) (witness : NativeRelation.Assignment)
    (streams : NativeRelation.InputStreams)
    (publicGroups : List (List NativeRelation.Scalar))
    (lowered : Zkir.lowerEntrypoint state entry = .ok json)
    (decoded : NativeRelationJson.decode json = .ok relation)
    (satisfies : NativeRelation.CircuitSatisfies hash relation streams witness publicGroups) :
    ∃ expected,
      Native.expectedEntrypoint state (Passes.pruneEntrypoint entry) = .ok expected ∧
      ∀ requirement ∈ expected.inputs,
        requirement.canonicalJubjubScalar = false →
        (witness requirement.identifier).val ≤ Native.sourceMaximum requirement.ty := by
  exact accepted_relation_input_bounds state entry json relation hash witness witness streams
    publicGroups lowered decoded satisfies (by
      intro expected _
      intro requirement _
      rfl)

end Noctium.Verification.GenericStateLowering
