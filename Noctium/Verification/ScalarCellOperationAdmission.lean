import Noctium.Verification.GenericStateCellAdmission
import Noctium.Verification.GenericStateOps
import Noctium.Verification.ScalarCellSourceReads
import Noctium.Verification.ScalarNormalization

namespace Noctium.Verification.ScalarCellOperationAdmission

open Backend GenericStateCellAdmission GenericStateOps ScalarNormalization

private theorem scalarCellReadExpression_admitted {ty : Ty}
    (scalar : ScalarCellType ty) (destination : String) :
    ScalarExpression (scalarCellReadExpression scalar destination) := by
  cases scalar with
  | native => exact ScalarExpression.ref destination .native
  | bool =>
    exact ScalarExpression.cast (.ref (ty := .bool) destination) .bool .native
      (ScalarExpression.ref destination .bool)
  | uint maximum _ =>
    exact ScalarExpression.cast (.ref (ty := .uint maximum) destination) (.uint maximum) .native
      (ScalarExpression.ref destination (.uint maximum))

private theorem scalarCellWriteExpression_admitted {ty : Ty}
    (scalar : ScalarCellType ty) (expression : Expr ty)
    (admitted : ScalarExpression expression) :
    ScalarExpression (scalarCellWriteExpression scalar expression) := by
  cases scalar with
  | native => exact admitted
  | bool =>
    exact ScalarExpression.select expression (.native 1) (.native 0) .native admitted
      (ScalarExpression.native 1) (ScalarExpression.native 0)
  | uint maximum _ =>
    exact ScalarExpression.cast expression (.uint maximum) .native admitted

private theorem native_list_admitted (values : List Nat) :
    ∀ field ∈ values.map (fun value => (Expr.native value : Impact.Scalar)),
      ScalarExpression field := by
  intro field member
  obtain ⟨value, _, rfl⟩ := List.mem_map.mp member
  exact ScalarExpression.native value

private theorem native_prefix_expression_admitted (values : List Nat)
    (expression : Expr .native) (expressionAdmitted : ScalarExpression expression) :
    ∀ field ∈ values.map (fun value => (Expr.native value : Impact.Scalar)) ++ [expression],
      ScalarExpression field := by
  intro field member
  rcases List.mem_append.mp member with prefixMember | finalMember
  · exact native_list_admitted values field prefixMember
  · simp only [List.mem_singleton] at finalMember
    subst field
    exact expressionAdmitted

private theorem index_fields_admitted (slot : Nat) (pushPath : Bool) :
    ∀ field ∈ (Impact.Op.index slot pushPath).fields, ScalarExpression field := by
  simpa [Impact.Op.fields, Impact.Aligned.fields] using
    (native_list_admitted
      [if pushPath then 0x70 else 0x50, 1, Field.modulus - 2, slot])

private theorem dup_fields_admitted :
    ∀ field ∈ Impact.Op.dup.fields, ScalarExpression field := by
  intro field member
  simp only [Impact.Op.fields, List.mem_singleton] at member
  subst field
  exact ScalarExpression.native 0x30

private theorem popeq_field_fields_admitted (expression : Expr .native)
    (expressionAdmitted : ScalarExpression expression) :
    ∀ field ∈ (Impact.Op.popeq (.field expression)).fields,
      ScalarExpression field := by
  simpa [Impact.Op.fields, Impact.Aligned.fields] using
    (native_prefix_expression_admitted [0x0c, 1, Field.modulus - 2]
      expression expressionAdmitted)

private theorem push_field_fields_admitted (expression : Expr .native) (storage : Bool)
    (expressionAdmitted : ScalarExpression expression) :
    ∀ field ∈ (Impact.Op.push (.field expression) storage).fields,
      ScalarExpression field := by
  simpa [Impact.Op.fields, Impact.Aligned.fields] using
    (native_prefix_expression_admitted
      [if storage then 0x11 else 0x10, 1, 1, Field.modulus - 2]
      expression expressionAdmitted)

private theorem insert_fields_admitted (levels : Nat) :
    ∀ field ∈ (Impact.Op.insert levels).fields, ScalarExpression field := by
  intro field member
  simp only [Impact.Op.fields, List.mem_singleton] at member
  subst field
  exact ScalarExpression.native (0x90 + levels)

private theorem scalarOperation_groups_singleton {operation : Impact.Op}
    (supported : ScalarOperation operation) :
    operation.fieldGroups = [operation.fields] := by
  cases operation <;> simp_all [ScalarOperation, Impact.Op.fieldGroups]

private theorem operation_groups_admitted (operation : Impact.Op)
    (supported : ScalarOperation operation)
    (fieldsAdmitted : ∀ field ∈ operation.fields, ScalarExpression field) :
    ∀ group ∈ operation.fieldGroups, ∀ field ∈ group, ScalarExpression field := by
  intro group groupMember field fieldMember
  rw [scalarOperation_groups_singleton supported] at groupMember
  simp only [List.mem_singleton] at groupMember
  subst group
  exact fieldsAdmitted field fieldMember

private theorem append_three_fields_admitted (before : List Impact.Op)
    (first second third : Impact.Op)
    (beforeAdmitted : ∀ operation ∈ before, ∀ group ∈ operation.fieldGroups,
      ∀ field ∈ group, ScalarExpression field)
    (firstSupported : ScalarOperation first)
    (secondSupported : ScalarOperation second)
    (thirdSupported : ScalarOperation third)
    (firstAdmitted : ∀ field ∈ first.fields, ScalarExpression field)
    (secondAdmitted : ∀ field ∈ second.fields, ScalarExpression field)
    (thirdAdmitted : ∀ field ∈ third.fields, ScalarExpression field) :
    ∀ operation ∈ before ++ [first, second, third],
      ∀ group ∈ operation.fieldGroups, ∀ field ∈ group, ScalarExpression field := by
  intro operation member
  rcases List.mem_append.mp member with old | added
  · exact beforeAdmitted operation old
  · simp only [List.mem_cons, List.not_mem_nil, or_false] at added
    rcases added with firstEq | secondEq | thirdEq
    · subst operation
      exact operation_groups_admitted first firstSupported firstAdmitted
    · subst operation
      exact operation_groups_admitted second secondSupported secondAdmitted
    · subst operation
      exact operation_groups_admitted third thirdSupported thirdAdmitted

/-- Accepted scalar cell lowering preserves field admission across an existing
scalar-operation prefix and admits each newly emitted group from its exact
cell projection. -/
theorem append_scalar_cell_fields_admitted
    (state : List StateDecl) (effect : Effect)
    (source : ScalarCellEffect state effect)
    (operand : ScalarCellSourceReads.ScalarCellOperand effect)
    (before next : Impact.Plan)
    (accepted : Impact.appendEffect state effect before = .ok next)
    (previousSupported : ∀ operation ∈ before.operations, ScalarOperation operation)
    (previousAdmitted : ∀ operation ∈ before.operations, ∀ group ∈ operation.fieldGroups,
      ∀ field ∈ group, ScalarExpression field) :
    ∀ operation ∈ next.operations, ∀ group ∈ operation.fieldGroups,
      ∀ field ∈ group, ScalarExpression field := by
  cases source with
  | readCell name destination ty scalar declaration =>
    obtain ⟨slot, shape, _⟩ :=
      GenericStateCellAdmission.append_read_cell_scalar_supported state before next
        name destination ty scalar declaration accepted previousSupported
    have readAdmitted := scalarCellReadExpression_admitted scalar destination
    let first : Impact.Op := .dup
    let second : Impact.Op := .index slot
    let third : Impact.Op := .popeq (.field (scalarCellReadExpression scalar destination))
    have exactShape : next.operations = before.operations ++ [first, second, third] := by
      simpa [first, second, third] using shape
    intro operation member
    rw [exactShape] at member
    exact append_three_fields_admitted before.operations first second third previousAdmitted
      (by simp [first, ScalarOperation]) (by simp [second, ScalarOperation])
      (by simp [third, ScalarOperation, ScalarAligned])
      (by simpa [first] using dup_fields_admitted)
      (by
        simpa [second] using index_fields_admitted slot false)
      (by
        simpa [third] using popeq_field_fields_admitted
          (scalarCellReadExpression scalar destination) readAdmitted)
      operation member
  | writeCell name ty expression scalar declaration =>
    have expressionAdmitted : ScalarExpression expression := by
      simpa [ScalarCellSourceReads.ScalarCellOperand] using operand
    obtain ⟨slot, shape, _⟩ :=
      GenericStateCellAdmission.append_write_cell_scalar_supported state before next
        name ty expression scalar declaration accepted previousSupported
    have writeAdmitted := scalarCellWriteExpression_admitted scalar expression expressionAdmitted
    let first : Impact.Op := .push (.field (.native slot))
    let second : Impact.Op := .push (.field (scalarCellWriteExpression scalar expression)) true
    let third : Impact.Op := .insert 1
    have exactShape : next.operations = before.operations ++ [first, second, third] := by
      simpa [first, second, third] using shape
    intro operation member
    rw [exactShape] at member
    exact append_three_fields_admitted before.operations first second third previousAdmitted
      (by simp [first, ScalarOperation, ScalarAligned])
      (by simp [second, ScalarOperation, ScalarAligned])
      (by simp [third, ScalarOperation])
      (by
        simpa [first] using push_field_fields_admitted (.native slot) false
          (ScalarExpression.native slot))
      (by
        simpa [second] using push_field_fields_admitted
          (scalarCellWriteExpression scalar expression) true writeAdmitted)
      (by simpa [third] using insert_fields_admitted 1)
      operation member

end Noctium.Verification.ScalarCellOperationAdmission
