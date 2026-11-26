import Noctium.Verification.ScalarValidation
import Noctium.Verification.ScalarLowering
import Noctium.Verification.NativeState

namespace Noctium.Verification.GenericStateConverseLedgerSatisfies
open Backend NativeRelation ScalarLowering ScalarNormalization

private theorem map_of_mapM_some {α β : Type} (f : α → Option β)
    {items : List α} {values : List β}
    (mapped : items.mapM f = some values) :
    items.map f = values.map some := by
  induction items generalizing values with
  | nil =>
      simp only [List.mapM_nil] at mapped
      cases mapped
      rfl
  | cons item rest ih =>
      simp only [List.mapM_cons, Bind.bind, Option.bind_eq_some_iff, Pure.pure,
        Option.some.injEq] at mapped
      obtain ⟨value, first, tailValues, tail, resultShape⟩ := mapped
      cases resultShape
      simpa only [List.map_cons, first] using
        congrArg (List.cons (some value)) (ih tail)

private theorem mapM_groups_to_map_some {α β : Type} (f : α → Option β)
    {groups : List (List α)} {values : List (List β)}
    (mapped : groups.mapM (fun group => group.mapM f) = some values) :
    groups.map (fun group => group.map f) = values.map (List.map some) := by
  induction groups generalizing values with
  | nil =>
      simp only [List.mapM_nil] at mapped
      cases mapped
      rfl
  | cons group rest ih =>
      simp only [List.mapM_cons, Bind.bind, Option.bind_eq_some_iff, Pure.pure,
        Option.some.injEq] at mapped
      obtain ⟨values, first, tailValues, tail, resultShape⟩ := mapped
      cases resultShape
      simp only [List.map_cons, List.cons.injEq]
      exact ⟨map_of_mapM_some f first, ih tail⟩

/-- The meaning of the exact production ledger body transfers to every
instruction in its strictly decoded relation. -/
theorem lowered_body_instructions_hold (state : List StateDecl)
    (entry : Entrypoint) (json : Lean.Json) (relation : Program)
    (plan : Impact.Plan) (hash : Hash) (witness : NativeRelation.Assignment)
    (lowered : Zkir.lowerEntrypoint state entry = .ok json)
    (accepted : Impact.lower state (Passes.pruneEntrypoint entry) = .ok plan)
    (decoded : NativeRelationJson.decode json = .ok relation)
    (meaning : LowerStateMeaning hash witness
      ((Zkir.lowerEntrypointBody (Passes.pruneEntrypoint entry) plan).run {}).2) :
    ∀ instruction ∈ relation.instructions,
      instruction.Holds hash witness := by
  obtain ⟨samePlan, sameAccepted, instructions⟩ :=
    Zkir.lowerEntrypoint_instructions state entry json lowered
  have same : samePlan = plan := by
    rw [accepted] at sameAccepted
    exact (Except.ok.inj sameAccepted).symm
  subst samePlan
  obtain ⟨raw, parsed, trace⟩ := ScalarValidation.decode_result decoded
  rw [instructions] at parsed
  cases parsed
  exact meaning.holds relation.instructions trace

/-- Input streams and Impact groups are observations of the constructed
assignment. The nontrivial obligation is every decoded instruction. -/
theorem lowered_body_circuit_satisfies (state : List StateDecl)
    (entry : Entrypoint) (json : Lean.Json) (relation : Program)
    (plan : Impact.Plan) (hash : Hash) (witness : NativeRelation.Assignment)
    (lowered : Zkir.lowerEntrypoint state entry = .ok json)
    (accepted : Impact.lower state (Passes.pruneEntrypoint entry) = .ok plan)
    (decoded : NativeRelationJson.decode json = .ok relation)
    (meaning : LowerStateMeaning hash witness
      ((Zkir.lowerEntrypointBody (Passes.pruneEntrypoint entry) plan).run {}).2) :
    CircuitSatisfies hash relation
      ⟨relation.inputValues .«public» witness,
        relation.inputValues .«private» witness⟩
      witness (relation.groups witness) := by
  refine ⟨lowered_body_instructions_hold state entry json relation plan hash
    witness lowered accepted decoded meaning, rfl, rfl, rfl⟩

/-- For the exact emitted ledger relation, strict producer validation binds
Impact observations to the independently derived expected statement when
the partial source meanings match the supplied native-operation groups. -/
theorem lowered_body_authenticated_groups (state : List StateDecl)
    (entry : Entrypoint) (json : Lean.Json) (relation : Program)
    (plan : Impact.Plan) (expected : Backend.Native.Expected)
    (hash : Hash) (inputs witness : NativeRelation.Assignment)
    (native : List NativeState.Op)
    (lowered : Zkir.lowerEntrypoint state entry = .ok json)
    (accepted : Impact.lower state (Passes.pruneEntrypoint entry) = .ok plan)
    (expectedAccepted : Backend.Native.expectedEntrypoint state
      (Passes.pruneEntrypoint entry) = .ok expected)
    (decoded : NativeRelationJson.decode json = .ok relation)
    (inputAgreement : ScalarValidation.InputAgreement expected inputs witness)
    (meaning : LowerStateMeaning hash witness
      ((Zkir.lowerEntrypointBody (Passes.pruneEntrypoint entry) plan).run {}).2)
    (sourceGroups : expected.groups.mapM
      (fun group => group.mapM (interpret hash inputs)) =
        some (NativeState.groups native)) :
    relation.groups witness = NativeState.groups native := by
  obtain ⟨compiledPlan, compiledExpected, compiledPlanAccepted,
    compiledExpectedAccepted, validated, _instructions⟩ :=
    Zkir.lowerEntrypoint_validation_and_instructions state entry json lowered
  have samePlan : compiledPlan = plan :=
    Except.ok.inj (compiledPlanAccepted.symm.trans accepted)
  have sameExpected : compiledExpected = expected :=
    Except.ok.inj (compiledExpectedAccepted.symm.trans expectedAccepted)
  subst compiledPlan compiledExpected
  have holds := lowered_body_instructions_hold state entry json relation plan hash
    witness lowered accepted decoded meaning
  have observed :=
    (ScalarValidation.validate_observations inputAgreement validated decoded holds).1
  have sourceMap := mapM_groups_to_map_some (interpret hash inputs) sourceGroups
  apply (List.map_inj_right (f := List.map some) (by
    intro left right same
    exact (List.map_inj_right (f := some) (fun _ _ => Option.some.inj)).mp same)).mp
  exact observed.trans sourceMap

end Noctium.Verification.GenericStateConverseLedgerSatisfies
