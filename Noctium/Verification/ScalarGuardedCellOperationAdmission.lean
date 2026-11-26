import Noctium.Verification.GuardedEffectPrefix
import Noctium.Verification.GuardedScalarExpressionAdmission
import Noctium.Verification.ScalarCellOperationAdmission
import Noctium.Verification.ScalarOperationSyntax

namespace Noctium.Verification.ScalarGuardedCellOperationAdmission

open Backend GenericStateCellAdmission GenericStateOps ScalarNormalization
open ScalarOperationSyntax (AdmittedOps)

private theorem bind_ok {α β : Type} {first : Except ε α}
    {next : α → Except ε β} {result : β} :
    (first >>= next) = .ok result ↔
      ∃ value, first = .ok value ∧ next value = .ok result := by
  cases first <;> simp [Bind.bind, Except.bind]

/-- A guarded Cell read keeps the operations of its accepted raw append. -/
theorem appendEffectWithActivity_readCell_raw
    (state : List StateDecl) (name destination : String) (ty : Ty)
    (condition : Expr .bool) (before after : Impact.Plan)
    (accepted : Impact.appendEffectWithActivity state
      (.readCell name destination ty) (some condition) before = .ok after) :
    ∃ raw, Impact.appendEffect state (.readCell name destination ty) before = .ok raw ∧
      after.operations = raw.operations := by
  unfold Impact.appendEffectWithActivity at accepted
  simp only [bind_ok] at accepted
  rcases accepted with ⟨lowered, loweredAccepted, raw, appended, wrapped⟩
  have loweredShape : lowered = .readCell name destination ty := by
    change Except.ok (Effect.readCell name destination ty) = Except.ok lowered at loweredAccepted
    exact (Except.ok.inj loweredAccepted).symm
  subst lowered
  cases readFound : raw.reads[before.reads.length]? with
  | none => simp [readFound] at wrapped
  | some read =>
    simp only [readFound, Pure.pure, Except.pure] at wrapped
    have planShape := Except.ok.inj wrapped
    have sameOperations : after.operations = raw.operations := by
      simpa using (congrArg Impact.Plan.operations planShape).symm
    exact ⟨raw, appended, sameOperations⟩

private theorem previous_scalar_supported {operations : List Impact.Op}
    (previous : AdmittedOps operations) :
    ∀ operation ∈ operations, ScalarOperation operation := by
  intro operation member
  exact (previous operation member).1

private theorem previous_scalar_groups_admitted {operations : List Impact.Op}
    (previous : AdmittedOps operations) :
    ∀ operation ∈ operations, ∀ group ∈ operation.fieldGroups,
      ∀ field ∈ group, ScalarExpression field := by
  intro operation member
  exact ScalarCellOperationAdmission.operation_groups_admitted operation
    (previous operation member).1 (previous operation member).2

private theorem fields_of_groups_transport
    {left right : List Impact.Op} (same : left = right)
    (admitted : ∀ operation ∈ right, ∀ group ∈ operation.fieldGroups,
      ∀ field ∈ group, ScalarExpression field) :
    ∀ operation ∈ left, ∀ group ∈ operation.fieldGroups,
      ∀ field ∈ group, ScalarExpression field := by
  intro operation member group groupMember field fieldMember
  rw [same] at member
  exact admitted operation member group groupMember field fieldMember

private theorem admittedOps_of_groups
    {operations : List Impact.Op}
    (supported : ∀ operation ∈ operations, ScalarOperation operation)
    (groups : ∀ operation ∈ operations, ∀ group ∈ operation.fieldGroups,
      ∀ field ∈ group, ScalarExpression field) :
    AdmittedOps operations := by
  intro operation member
  refine ⟨supported operation member, ?_⟩
  intro field fieldMember
  exact ScalarOperationSyntax.field_of_group (groups operation member) fieldMember

/-- Accepted guarded or unguarded scalar Cell lowering preserves opcode and
field admission. Guarded writes admit the exact totalized operand selected by
the accepted append, and guarded reads retain the raw read operation fields. -/
theorem append_cell_fields_admitted
    (state : List StateDecl) (before after : Impact.Plan) (effect : Effect)
    (guard : Option (Expr .bool))
    (source : ScalarCellEffect state effect)
    (operand : ScalarCellSourceReads.ScalarCellOperand effect)
    (guardAdmitted : ∀ condition, guard = some condition → ScalarExpression condition)
    (accepted : Impact.appendEffectWithActivity state effect guard before = .ok after)
    (previous : AdmittedOps before.operations) :
    AdmittedOps after.operations := by
  have previousSupported := previous_scalar_supported previous
  have previousGroups := previous_scalar_groups_admitted previous
  have afterSupported :=
    GenericStateCellAdmission.append_cell_effect_with_activity_scalar_supported
      state before after effect guard source accepted previousSupported
  cases guard with
  | none =>
    obtain ⟨raw, rawAccepted, sameOperations, _⟩ :=
      GuardedEffectPrefix.appendEffectWithActivity_none_result
        state effect before after accepted
    have rawGroups := ScalarCellOperationAdmission.append_scalar_cell_fields_admitted
      state effect source operand before raw rawAccepted previousSupported previousGroups
    have afterGroups := fields_of_groups_transport sameOperations rawGroups
    exact admittedOps_of_groups afterSupported afterGroups
  | some condition =>
    cases source with
    | readCell name destination ty scalar declaration =>
      obtain ⟨raw, rawAccepted, sameOperations⟩ :=
        appendEffectWithActivity_readCell_raw
          state name destination ty condition before after accepted
      have readSource : ScalarCellEffect state (.readCell name destination ty) :=
        .readCell name destination ty scalar declaration
      have rawGroups := ScalarCellOperationAdmission.append_scalar_cell_fields_admitted
        state (.readCell name destination ty) readSource operand before raw rawAccepted
        previousSupported previousGroups
      have afterGroups := fields_of_groups_transport sameOperations rawGroups
      exact admittedOps_of_groups afterSupported afterGroups
    | writeCell name ty expression scalar declaration =>
      obtain ⟨binder, _fresh, raw, rawAccepted, sameOperations⟩ :=
        Impact.appendEffectWithActivity_writeCell_value
          state name ty expression condition before after accepted
      have expressionAdmitted : ScalarExpression expression := by
        simpa [ScalarCellSourceReads.ScalarCellOperand] using operand
      have conditionAdmitted : ScalarExpression condition :=
        guardAdmitted condition rfl
      have totalizedAdmitted :
          ScalarExpression (Noctium.GuardedExpression.totalize (.ref binder) expression) :=
        GuardedScalarExpressionAdmission.totalize_scalarExpression (.ref binder)
          (ScalarExpression.ref binder .bool) expression expressionAdmitted
      let stored : Expr ty := .letE binder condition
        (Noctium.GuardedExpression.totalize (.ref binder) expression)
      have storedAdmitted : ScalarExpression stored := by
        exact ScalarExpression.letE binder condition
          (Noctium.GuardedExpression.totalize (.ref binder) expression)
          .bool conditionAdmitted totalizedAdmitted
      have storedSource : ScalarCellEffect state (.writeCell name ty stored) :=
        .writeCell name ty stored scalar declaration
      have rawGroups := ScalarCellOperationAdmission.append_scalar_cell_fields_admitted
        state (.writeCell name ty stored) storedSource storedAdmitted before raw rawAccepted
        previousSupported previousGroups
      have afterGroups := fields_of_groups_transport sameOperations rawGroups
      exact admittedOps_of_groups afterSupported afterGroups

end Noctium.Verification.ScalarGuardedCellOperationAdmission
