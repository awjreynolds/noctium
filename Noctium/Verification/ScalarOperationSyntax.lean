import Noctium.Verification.ScalarCellOperationAdmission
import Noctium.Verification.ScalarLedgerPlanValidation

namespace Noctium.Verification.ScalarOperationSyntax

open Backend ScalarNormalization

/-- Each opcode and every field consumed by its scalar interpreter have
explicit support. The emitted operation order stays in the list. -/
def AdmittedOps (operations : List Impact.Op) : Prop :=
  ∀ operation ∈ operations, GenericStateOps.ScalarOperation operation ∧
    ∀ field ∈ operation.fields, ScalarExpression field

theorem append {before suffix : List Impact.Op}
    (previous : AdmittedOps before) (added : AdmittedOps suffix) :
    AdmittedOps (before ++ suffix) := by
  intro operation member
  rcases List.mem_append.mp member with old | new
  · exact previous operation old
  · exact added operation new

theorem field_of_group {operation : Impact.Op} {field : Impact.Scalar}
    (admitted : ∀ group ∈ operation.fieldGroups, ∀ item ∈ group, ScalarExpression item)
    (member : field ∈ operation.fields) : ScalarExpression field := by
  rw [← ScalarWitnessConstruction.Op.fieldGroups_flatten_eq_fields operation] at member
  obtain ⟨group, groupMember, fieldMember⟩ := List.mem_flatten.mp member
  exact admitted group groupMember field fieldMember

end Noctium.Verification.ScalarOperationSyntax
