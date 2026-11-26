import Noctium.Verification.GuardedRequireSemantics
import Noctium.Verification.GuardedEffectPrefix
import Noctium.Verification.ScalarOperationSyntax

namespace Noctium.Verification.ScalarRequireOperationAdmission

open Backend GenericStateCellAdmission GenericStateOps ScalarNormalization
open ScalarCellOperationAdmission ScalarOperationSyntax

private theorem bind_ok {α β : Type} {first : Except ε α}
    {next : α → Except ε β} {result : β} :
    (first >>= next) = .ok result ↔
      ∃ value, first = .ok value ∧ next value = .ok result := by
  cases first <;> simp [Bind.bind, Except.bind]

private theorem singleton_admitted (operation : Impact.Op)
    (supported : ScalarOperation operation)
    (fields : ∀ field ∈ operation.fields, ScalarExpression field) :
    AdmittedOps [operation] := by
  intro found member
  have same : found = operation := List.mem_singleton.mp (by simpa using member)
  subst found
  exact ⟨supported, fields⟩

/-- A source require leaves the operation transcript untouched for either
activity mode, so its admitted operation prefix remains admitted. -/
theorem append_require_fields_admitted (state : List StateDecl)
    (before after : Impact.Plan) (condition : Expr .bool)
    (guard : Option (Expr .bool))
    (accepted : Impact.appendEffectWithActivity state (.require condition)
      guard before = .ok after)
    (previous : AdmittedOps before.operations) :
    AdmittedOps after.operations := by
  cases guard with
  | none =>
    obtain ⟨raw, appended, sameOperations, _⟩ :=
      GuardedEffectPrefix.appendEffectWithActivity_none_result state
        (.require condition) before after accepted
    have rawOperations : raw.operations = before.operations := by
      simp only [Impact.appendEffect] at appended
      cases appended
      rfl
    rw [sameOperations, rawOperations]
    exact previous
  | some gate =>
    have shape := GuardedRequireSemantics.appendEffectWithActivity_require_shape
      state gate condition before after accepted
    rw [shape]
    intro operation member
    exact previous operation (by simpa using member)

private theorem append_requireAbsent_raw_suffix (state : List StateDecl)
    (name : String) (keyTy : Ty) (key : Expr keyTy)
    (keyScalar : ScalarCellType keyTy) (before after : Impact.Plan)
    (accepted : Impact.appendEffect state (.requireAbsent name keyTy key)
      before = .ok after) :
    ∃ slot, after.operations = before.operations ++
      [.dup, .index slot,
        .push (.field (GenericStateCellAdmission.scalarCellWriteExpression keyScalar key)) false,
        .member, .popeq (.bit false)] := by
  simp only [Impact.appendEffect, bind_ok] at accepted
  obtain ⟨slot, slotAccepted, aligned, alignedAccepted, resultAccepted⟩ := accepted
  have alignedShape : aligned =
      .field (GenericStateCellAdmission.scalarCellWriteExpression keyScalar key) := by
    cases keyScalar with
    | native =>
      change (Except.ok (.field key) : Except String Impact.Aligned) = .ok aligned
        at alignedAccepted
      exact (Except.ok.inj alignedAccepted).symm
    | bool =>
      change (Except.ok (.field (.select key (.native 1) (.native 0))) :
        Except String Impact.Aligned) = .ok aligned at alignedAccepted
      exact (Except.ok.inj alignedAccepted).symm
    | uint maximum _ =>
      change (Except.ok (.field (.cast .native key)) : Except String Impact.Aligned) =
        .ok aligned at alignedAccepted
      exact (Except.ok.inj alignedAccepted).symm
  rw [alignedShape] at resultAccepted
  simp only [Pure.pure, Except.pure] at resultAccepted
  have planShape := Except.ok.inj resultAccepted
  refine ⟨slot, ?_⟩
  rw [← planShape]
  rfl

/-- The unguarded activity wrapper preserves the exact ordered suffix emitted
by the raw requireAbsent lowering. -/
theorem append_require_absent_operation_suffix (state : List StateDecl)
    (before after : Impact.Plan) (name : String) (keyTy : Ty) (key : Expr keyTy)
    (keyScalar : ScalarCellType keyTy)
    (accepted : Impact.appendEffectWithActivity state
      (.requireAbsent name keyTy key) none before = .ok after) :
    ∃ slot, after.operations = before.operations ++
      [.dup, .index slot,
        .push (.field (GenericStateCellAdmission.scalarCellWriteExpression keyScalar key)) false,
        .member, .popeq (.bit false)] := by
  obtain ⟨raw, appended, sameOperations, _⟩ :=
    GuardedEffectPrefix.appendEffectWithActivity_none_result state
      (.requireAbsent name keyTy key) before after accepted
  obtain ⟨slot, rawShape⟩ := append_requireAbsent_raw_suffix state name keyTy key
    keyScalar before raw appended
  exact ⟨slot, sameOperations.trans rawShape⟩

/-- Guarded absence checks remain rejected by the production activity
wrapper. -/
theorem append_requireAbsent_guarded_rejected (state : List StateDecl)
    (name : String) (keyTy : Ty) (key : Expr keyTy) (gate : Expr .bool)
    (before after : Impact.Plan)
    (accepted : Impact.appendEffectWithActivity state
      (.requireAbsent name keyTy key) (some gate) before = .ok after) : False := by
  have rejected : Impact.appendEffectWithActivity state
      (.requireAbsent name keyTy key) (some gate) before =
        .error "native guards are supported only on ledger reads, writes, and require effects" := by
    rfl
  rw [rejected] at accepted
  cases accepted

private theorem requireAbsent_suffix_admitted (slot : Nat) (keyTy : Ty)
    (key : Expr keyTy) (keyScalar : ScalarCellType keyTy)
    (keyAdmitted : ScalarExpression key) :
    AdmittedOps
      [.dup, .index slot,
        .push (.field (GenericStateCellAdmission.scalarCellWriteExpression keyScalar key)) false,
        .member, .popeq (.bit false)] := by
  have normalizedKey := ScalarCellOperationAdmission.scalarCellWriteExpression_admitted
    keyScalar key keyAdmitted
  have dup : AdmittedOps [.dup] := singleton_admitted .dup
    (by simp [GenericStateOps.ScalarOperation])
    ScalarCellOperationAdmission.dup_fields_admitted
  have index : AdmittedOps [.index slot] := singleton_admitted (.index slot)
    (by simp [GenericStateOps.ScalarOperation])
    (by simpa using ScalarCellOperationAdmission.index_fields_admitted slot false)
  have pushed : AdmittedOps
      [.push (.field (GenericStateCellAdmission.scalarCellWriteExpression keyScalar key)) false] :=
    singleton_admitted
      (.push (.field (GenericStateCellAdmission.scalarCellWriteExpression keyScalar key)) false)
      (by simp [GenericStateOps.ScalarOperation, GenericStateOps.ScalarAligned])
      (by
        exact ScalarCellOperationAdmission.push_field_fields_admitted
          (GenericStateCellAdmission.scalarCellWriteExpression keyScalar key) false normalizedKey)
  have member : AdmittedOps [.member] := singleton_admitted .member
    (by simp [GenericStateOps.ScalarOperation])
    (by
      intro field fieldMember
      simp only [Impact.Op.fields, List.mem_singleton] at fieldMember
      subst field
      exact ScalarExpression.native 0x18)
  have popeq : AdmittedOps [.popeq (.bit false)] := singleton_admitted
    (.popeq (.bit false))
    (by simp [GenericStateOps.ScalarOperation, GenericStateOps.ScalarAligned])
    (by
      simpa [Impact.Op.fields, Impact.Aligned.fields] using
        ScalarCellOperationAdmission.native_prefix_expression_admitted
          [0x0c, 1, 1] (.native 0) (ScalarExpression.native 0))
  have nil : AdmittedOps [] := by
    intro operation member
    cases member
  exact append nil (append dup (append index (append pushed (append member popeq))))

/-- Accepted unguarded requireAbsent effects append the production key check
suffix. Every opcode and field in that suffix belongs to the scalar fragment. -/
theorem append_require_absent_fields_admitted (state : List StateDecl)
    (before after : Impact.Plan) (name : String) (keyTy : Ty) (key : Expr keyTy)
    (keyScalar : ScalarCellType keyTy) (keyAdmitted : ScalarExpression key)
    (guard : Option (Expr .bool))
    (accepted : Impact.appendEffectWithActivity state
      (.requireAbsent name keyTy key) guard before = .ok after)
    (previous : AdmittedOps before.operations) :
    AdmittedOps after.operations := by
  cases guard with
  | some gate =>
    exact False.elim
      (append_requireAbsent_guarded_rejected state name keyTy key gate before after accepted)
  | none =>
    obtain ⟨slot, exactShape⟩ := append_require_absent_operation_suffix state
      before after name keyTy key keyScalar accepted
    rw [exactShape]
    exact append previous (requireAbsent_suffix_admitted slot keyTy key keyScalar keyAdmitted)

end Noctium.Verification.ScalarRequireOperationAdmission
