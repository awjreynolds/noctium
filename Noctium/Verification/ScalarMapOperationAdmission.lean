import Noctium.GuardedExpression
import Noctium.Verification.GenericStateMapOperations
import Noctium.Verification.GuardedEffectPrefix
import Noctium.Verification.GuardedScalarExpressionAdmission
import Noctium.Verification.ScalarCellOperationAdmission
import Noctium.Verification.ScalarOperationSyntax

namespace Noctium.Verification.ScalarMapOperationAdmission

open Backend GenericStateCellAdmission GenericStateOps ScalarNormalization

private theorem singleton_admitted (operation : Impact.Op)
    (supported : ScalarOperation operation)
    (fieldsAdmitted : ∀ field ∈ operation.fields, ScalarExpression field) :
    ScalarOperationSyntax.AdmittedOps [operation] := by
  intro found member
  simp only [List.mem_singleton] at member
  subst found
  exact ⟨supported, fieldsAdmitted⟩

private theorem mapIndex_field_fields_admitted (slot : Nat) (key : Expr .native)
    (keyAdmitted : ScalarExpression key) :
    ∀ field ∈ (Impact.Op.mapIndex slot (.field key)).fields,
      ScalarExpression field := by
  simpa [Impact.Op.fields, Impact.Aligned.fields] using
    (ScalarCellOperationAdmission.native_prefix_expression_admitted
      [0x51, 1, Field.modulus - 2, slot, 1, Field.modulus - 2] key keyAdmitted)

private theorem read_map_suffix_admitted (slot : Nat)
    (key value : Expr .native)
    (keyAdmitted : ScalarExpression key)
    (valueAdmitted : ScalarExpression value) :
    ScalarOperationSyntax.AdmittedOps
      [.dup, .mapIndex slot (.field key), .popeq (.field value)] := by
  have duplicate := singleton_admitted .dup
    (by simp [ScalarOperation])
    ScalarCellOperationAdmission.dup_fields_admitted
  have lookup := singleton_admitted (.mapIndex slot (.field key))
    (by simp [ScalarOperation])
    (mapIndex_field_fields_admitted slot key keyAdmitted)
  have projection := singleton_admitted (.popeq (.field value))
    (by simp [ScalarOperation, ScalarAligned])
    (ScalarCellOperationAdmission.popeq_field_fields_admitted value valueAdmitted)
  simpa using
    ScalarOperationSyntax.append
      (ScalarOperationSyntax.append duplicate lookup) projection

private theorem write_map_suffix_admitted (slot : Nat)
    (key value : Expr .native)
    (keyAdmitted : ScalarExpression key)
    (valueAdmitted : ScalarExpression value) :
    ScalarOperationSyntax.AdmittedOps
      [.index slot true,
        .push (.field key) false,
        .push (.field value) true,
        .insert 2] := by
  have index := singleton_admitted (.index slot true)
    (by simp [ScalarOperation])
    (ScalarCellOperationAdmission.index_fields_admitted slot true)
  have keyPush := singleton_admitted (.push (.field key) false)
    (by simp [ScalarOperation, ScalarAligned])
    (ScalarCellOperationAdmission.push_field_fields_admitted key false keyAdmitted)
  have valuePush := singleton_admitted (.push (.field value) true)
    (by simp [ScalarOperation, ScalarAligned])
    (ScalarCellOperationAdmission.push_field_fields_admitted value true valueAdmitted)
  have insertion := singleton_admitted (.insert 2)
    (by simp [ScalarOperation])
    (ScalarCellOperationAdmission.insert_fields_admitted 2)
  simpa using
    ScalarOperationSyntax.append
      (ScalarOperationSyntax.append
        (ScalarOperationSyntax.append index keyPush) valuePush) insertion

private theorem append_read_map_fields_admitted_raw (state : List StateDecl)
    (before after : Impact.Plan) (name destination : String)
    (keyTy valueTy : Ty) (key : Expr keyTy)
    (keyScalar : ScalarCellType keyTy) (valueScalar : ScalarCellType valueTy)
    (keyAdmitted : ScalarExpression key)
    (accepted : Impact.appendEffect state
      (.readMap name destination keyTy valueTy key) before = .ok after)
    (previous : ScalarOperationSyntax.AdmittedOps before.operations) :
    ScalarOperationSyntax.AdmittedOps after.operations := by
  obtain ⟨slot, operationsShape, _⟩ :=
    GenericStateMapOperations.append_read_map_scalar_supported state before after
      name destination keyTy valueTy key keyScalar valueScalar accepted
      (fun operation member => (previous operation member).1)
  have keyWriteAdmitted :=
    ScalarCellOperationAdmission.scalarCellWriteExpression_admitted
      keyScalar key keyAdmitted
  have valueReadAdmitted :=
    ScalarCellOperationAdmission.scalarCellReadExpression_admitted
      valueScalar destination
  have suffixAdmitted := read_map_suffix_admitted slot
    (scalarCellWriteExpression keyScalar key)
    (scalarCellReadExpression valueScalar destination)
    keyWriteAdmitted valueReadAdmitted
  rw [operationsShape]
  exact ScalarOperationSyntax.append previous suffixAdmitted

private theorem append_write_map_fields_admitted_raw (state : List StateDecl)
    (before after : Impact.Plan) (name : String)
    (keyTy valueTy : Ty) (key : Expr keyTy) (value : Expr valueTy)
    (keyScalar : ScalarCellType keyTy) (valueScalar : ScalarCellType valueTy)
    (keyAdmitted : ScalarExpression key) (valueAdmitted : ScalarExpression value)
    (accepted : Impact.appendEffect state
      (.writeMap name keyTy valueTy key value) before = .ok after)
    (previous : ScalarOperationSyntax.AdmittedOps before.operations) :
    ScalarOperationSyntax.AdmittedOps after.operations := by
  obtain ⟨slot, operationsShape, _⟩ :=
    GenericStateMapOperations.append_write_map_scalar_supported state before after
      name keyTy valueTy key value keyScalar valueScalar accepted
      (fun operation member => (previous operation member).1)
  have keyWriteAdmitted :=
    ScalarCellOperationAdmission.scalarCellWriteExpression_admitted
      keyScalar key keyAdmitted
  have valueWriteAdmitted :=
    ScalarCellOperationAdmission.scalarCellWriteExpression_admitted
      valueScalar value valueAdmitted
  have suffixAdmitted := write_map_suffix_admitted slot
    (scalarCellWriteExpression keyScalar key)
    (scalarCellWriteExpression valueScalar value)
    keyWriteAdmitted valueWriteAdmitted
  rw [operationsShape]
  exact ScalarOperationSyntax.append previous suffixAdmitted

/-- Accepted guarded or unguarded plain Map reads admit each emitted opcode
and every field, including Impact's totalized key expression. -/
theorem append_read_map_fields_admitted (state : List StateDecl)
    (before after : Impact.Plan) (name destination : String)
    (keyTy valueTy : Ty) (key : Expr keyTy) (guard : Option (Expr .bool))
    (keyScalar : ScalarCellType keyTy) (valueScalar : ScalarCellType valueTy)
    (keyAdmitted : ScalarExpression key)
    (guardAdmitted : ∀ condition, guard = some condition → ScalarExpression condition)
    (accepted : Impact.appendEffectWithActivity state
      (.readMap name destination keyTy valueTy key) guard before = .ok after)
    (previous : ScalarOperationSyntax.AdmittedOps before.operations) :
    ScalarOperationSyntax.AdmittedOps after.operations := by
  cases guard with
  | none =>
    obtain ⟨raw, appended, sameOperations, _⟩ :=
      GuardedEffectPrefix.appendEffectWithActivity_none_result state
        (.readMap name destination keyTy valueTy key) before after accepted
    have rawAdmitted := append_read_map_fields_admitted_raw state before raw
      name destination keyTy valueTy key keyScalar valueScalar keyAdmitted appended previous
    rw [sameOperations]
    exact rawAdmitted
  | some condition =>
    have keyNonForeign : ∀ kind, keyTy ≠ .foreign kind := by
      cases keyScalar <;> simp
    obtain ⟨binder, _, raw, appended, sameOperations⟩ :=
      Impact.appendEffectWithActivity_readMap_key state name destination keyTy valueTy
        key condition before after keyNonForeign accepted
    let emittedKey : Expr keyTy :=
      .letE binder condition
        (Noctium.GuardedExpression.totalize (.ref binder) key)
    have conditionAdmitted := guardAdmitted condition (by rfl)
    have binderAdmitted : ScalarExpression (.ref (ty := .bool) binder) :=
      ScalarExpression.ref binder .bool
    have totalizedKeyAdmitted :=
      GuardedScalarExpressionAdmission.totalize_scalarExpression
        (.ref binder) binderAdmitted key keyAdmitted
    have emittedKeyAdmitted : ScalarExpression emittedKey := by
      change ScalarExpression (.letE binder condition
        (Noctium.GuardedExpression.totalize (.ref binder) key))
      exact ScalarExpression.letE binder condition
        (Noctium.GuardedExpression.totalize (.ref binder) key) .bool
        conditionAdmitted totalizedKeyAdmitted
    have rawAdmitted := append_read_map_fields_admitted_raw state before raw
      name destination keyTy valueTy emittedKey keyScalar valueScalar
      emittedKeyAdmitted appended previous
    rw [sameOperations]
    exact rawAdmitted

/-- Accepted guarded or unguarded plain Map writes admit each emitted opcode
and every field, including Impact's totalized key and value expressions. -/
theorem append_write_map_fields_admitted (state : List StateDecl)
    (before after : Impact.Plan) (name : String)
    (keyTy valueTy : Ty) (key : Expr keyTy) (value : Expr valueTy)
    (guard : Option (Expr .bool))
    (keyScalar : ScalarCellType keyTy) (valueScalar : ScalarCellType valueTy)
    (keyAdmitted : ScalarExpression key) (valueAdmitted : ScalarExpression value)
    (guardAdmitted : ∀ condition, guard = some condition → ScalarExpression condition)
    (accepted : Impact.appendEffectWithActivity state
      (.writeMap name keyTy valueTy key value) guard before = .ok after)
    (previous : ScalarOperationSyntax.AdmittedOps before.operations) :
    ScalarOperationSyntax.AdmittedOps after.operations := by
  cases guard with
  | none =>
    obtain ⟨raw, appended, sameOperations, _⟩ :=
      GuardedEffectPrefix.appendEffectWithActivity_none_result state
        (.writeMap name keyTy valueTy key value) before after accepted
    have rawAdmitted := append_write_map_fields_admitted_raw state before raw
      name keyTy valueTy key value keyScalar valueScalar keyAdmitted valueAdmitted
      appended previous
    rw [sameOperations]
    exact rawAdmitted
  | some condition =>
    have keyNonForeign : ∀ kind, keyTy ≠ .foreign kind := by
      cases keyScalar <;> simp
    obtain ⟨keyBinder, _, valueBinder, _, raw, appended, sameOperations⟩ :=
      Impact.appendEffectWithActivity_writeMap_key_value state name keyTy valueTy
        key value condition before after keyNonForeign accepted
    let emittedKey : Expr keyTy :=
      .letE keyBinder condition
        (Noctium.GuardedExpression.totalize (.ref keyBinder) key)
    let emittedValue : Expr valueTy :=
      .letE valueBinder condition
        (Noctium.GuardedExpression.totalize (.ref valueBinder) value)
    have conditionAdmitted := guardAdmitted condition (by rfl)
    have keyBinderAdmitted : ScalarExpression (.ref (ty := .bool) keyBinder) :=
      ScalarExpression.ref keyBinder .bool
    have valueBinderAdmitted : ScalarExpression (.ref (ty := .bool) valueBinder) :=
      ScalarExpression.ref valueBinder .bool
    have totalizedKeyAdmitted :=
      GuardedScalarExpressionAdmission.totalize_scalarExpression
        (.ref keyBinder) keyBinderAdmitted key keyAdmitted
    have totalizedValueAdmitted :=
      GuardedScalarExpressionAdmission.totalize_scalarExpression
        (.ref valueBinder) valueBinderAdmitted value valueAdmitted
    have emittedKeyAdmitted : ScalarExpression emittedKey := by
      change ScalarExpression (.letE keyBinder condition
        (Noctium.GuardedExpression.totalize (.ref keyBinder) key))
      exact ScalarExpression.letE keyBinder condition
        (Noctium.GuardedExpression.totalize (.ref keyBinder) key) .bool
        conditionAdmitted totalizedKeyAdmitted
    have emittedValueAdmitted : ScalarExpression emittedValue := by
      change ScalarExpression (.letE valueBinder condition
        (Noctium.GuardedExpression.totalize (.ref valueBinder) value))
      exact ScalarExpression.letE valueBinder condition
        (Noctium.GuardedExpression.totalize (.ref valueBinder) value) .bool
        conditionAdmitted totalizedValueAdmitted
    have rawAdmitted := append_write_map_fields_admitted_raw state before raw
      name keyTy valueTy emittedKey emittedValue keyScalar valueScalar
      emittedKeyAdmitted emittedValueAdmitted appended previous
    rw [sameOperations]
    exact rawAdmitted

end Noctium.Verification.ScalarMapOperationAdmission
