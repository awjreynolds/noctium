import Noctium.Verification.GenericStateOps
import Noctium.Verification.ScalarNormalization

namespace Noctium.Verification.ScalarCellPublicAdmission

open Backend ScalarNormalization

private theorem field_aligned_fields_admitted (expression : Expr .native)
    (admitted : ScalarExpression expression) :
    ∀ field ∈ (Impact.Aligned.field expression).fields,
      ScalarExpression field := by
  intro field member
  change field ∈ [.native 1, .native (Field.modulus - 2), expression] at member
  simp only [List.mem_cons] at member
  rcases member with first | second | last
  · subst field
    exact ScalarExpression.native 1
  · subst field
    exact ScalarExpression.native (Field.modulus - 2)
  · have expressionEq : field = expression := by simpa using last
    subst field
    exact admitted

private theorem push_fields_admitted (expression : Expr .native)
    (admitted : ScalarExpression expression) :
    ∀ field ∈ (Impact.Op.push (.field expression)).fields,
      ScalarExpression field := by
  intro field member
  change field ∈ [.native 0x10, .native 1] ++
    (Impact.Aligned.field expression).fields at member
  rw [List.mem_append] at member
  rcases member with header | payload
  · simp only [List.mem_cons] at header
    rcases header with opcode | count
    · subst field
      exact ScalarExpression.native 0x10
    · have countEq : field = .native 1 := by simpa using count
      subst field
      exact ScalarExpression.native 1
  · exact field_aligned_fields_admitted expression admitted field payload

private theorem popeq_fields_admitted (expression : Expr .native)
    (admitted : ScalarExpression expression) :
    ∀ field ∈ (Impact.Op.popeq (.field expression)).fields,
      ScalarExpression field := by
  intro field member
  change field ∈ [.native 0x0c] ++
    (Impact.Aligned.field expression).fields at member
  rw [List.mem_append] at member
  rcases member with header | payload
  · have headerEq : field = .native 0x0c := by simpa using header
    subst field
    exact ScalarExpression.native 0x0c
  · exact field_aligned_fields_admitted expression admitted field payload

private theorem publicInputScalarOperation_fields_admitted (input : Input)
    (operation : Impact.Op)
    (member : operation ∈ Impact.publicInputScalarOperations input) :
    ∀ group ∈ operation.fieldGroups, ∀ field ∈ group, ScalarExpression field := by
  cases input with
  | mk name ty visibility span =>
    cases visibility with
    | «private» =>
      simp [Impact.publicInputScalarOperations] at member
    | «public» =>
      cases ty with
      | native =>
        simp [Impact.publicInputScalarOperations] at member
        rcases member with push | popeq
        · cases push
          intro group groupMember field fieldMember
          have groupEq : group =
              (Impact.Op.push (.field (.ref name)) false).fields := by
            simpa [Impact.Op.fieldGroups] using groupMember
          subst group
          exact push_fields_admitted (.ref name) (ScalarExpression.ref name .native)
            field fieldMember
        · cases popeq
          intro group groupMember field fieldMember
          have groupEq : group =
              (Impact.Op.popeq (.field (.ref name))).fields := by
            simpa [Impact.Op.fieldGroups] using groupMember
          subst group
          exact popeq_fields_admitted (.ref name) (ScalarExpression.ref name .native)
            field fieldMember
      | bool =>
        simp [Impact.publicInputScalarOperations] at member
        rcases member with push | popeq
        · cases push
          intro group groupMember field fieldMember
          have groupEq : group =
              (Impact.Op.push (.field (.cast .native
                (.ref (ty := .bool) name))) false).fields := by
            simpa [Impact.Op.fieldGroups] using groupMember
          subst group
          exact push_fields_admitted (.cast .native (.ref (ty := .bool) name))
            (ScalarExpression.cast (.ref (ty := .bool) name) .bool .native
              (ScalarExpression.ref name .bool)) field fieldMember
        · cases popeq
          intro group groupMember field fieldMember
          have groupEq : group =
              (Impact.Op.popeq (.field (.cast .native
                (.ref (ty := .bool) name)))).fields := by
            simpa [Impact.Op.fieldGroups] using groupMember
          subst group
          exact popeq_fields_admitted (.cast .native (.ref (ty := .bool) name))
            (ScalarExpression.cast (.ref (ty := .bool) name) .bool .native
              (ScalarExpression.ref name .bool)) field fieldMember
      | uint maximum =>
        simp [Impact.publicInputScalarOperations] at member
        rcases member with push | popeq
        · cases push
          intro group groupMember field fieldMember
          have groupEq : group =
              (Impact.Op.push (.field (.cast .native
                (.ref (ty := .uint maximum) name))) false).fields := by
            simpa [Impact.Op.fieldGroups] using groupMember
          subst group
          exact push_fields_admitted (.cast .native (.ref (ty := .uint maximum) name))
            (ScalarExpression.cast (.ref (ty := .uint maximum) name) (.uint maximum) .native
              (ScalarExpression.ref name (.uint maximum))) field fieldMember
        · cases popeq
          intro group groupMember field fieldMember
          have groupEq : group =
              (Impact.Op.popeq (.field (.cast .native
                (.ref (ty := .uint maximum) name)))).fields := by
            simpa [Impact.Op.fieldGroups] using groupMember
          subst group
          exact popeq_fields_admitted (.cast .native (.ref (ty := .uint maximum) name))
            (ScalarExpression.cast (.ref (ty := .uint maximum) name) (.uint maximum) .native
              (ScalarExpression.ref name (.uint maximum))) field fieldMember
      | bytes _ | opaqueBytes | opaqueString | jubjubScalar | jubjubPoint | foreign _ =>
        simp [Impact.publicInputScalarOperations] at member

/-- Each real accepted scalar public-input operation carries only scalar
expressions in its transcript groups. The theorem follows the production
input fold and projects Native, Bool, and UInt source references explicitly. -/
theorem publicInputPlan_fields_admitted (inputs : List Input) (plan : Impact.Plan)
    (compatible : ∀ input ∈ inputs, Impact.publicInputScalarCompatible input)
    (accepted : Impact.publicInputPlan inputs {} = .ok plan) :
    ∀ operation ∈ plan.operations, ∀ group ∈ operation.fieldGroups,
      ∀ field ∈ group, ScalarExpression field := by
  have operations := Impact.publicInputPlan_scalar_operations inputs {} plan
    accepted compatible
  intro operation member
  rw [operations] at member
  simp only [List.nil_append] at member
  obtain ⟨input, inputMember, operationMember⟩ := List.mem_flatMap.mp member
  exact publicInputScalarOperation_fields_admitted input operation operationMember

end Noctium.Verification.ScalarCellPublicAdmission
