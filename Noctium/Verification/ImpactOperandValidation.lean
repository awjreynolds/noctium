import Noctium.Verification.ImpactOperationAgreement
import Noctium.Verification.ScalarExpressionAdmission

namespace Noctium.Verification.ImpactOperandValidation

open Lean Backend ImpactOperationAgreement ScalarNormalization
open ImpactExpressionSchedule ScalarExpressionAdmission

private theorem firstBindSuccess {α β : Type} (first : Except String α)
    (rest : α → Except String β) {result : β}
    (accepted : first.bind rest = .ok result) :
    ∃ value, first = .ok value := by
  cases first with
  | error message => simp [Except.bind] at accepted
  | ok value => exact ⟨value, rfl⟩

private theorem select_condition_valid {types : TypeEnv} {condition : Expr .bool}
    {yes no : Expr .native}
    (valid : (Expr.select condition yes no).validate Capabilities.crypto types = .ok ()) :
    condition.validate Capabilities.crypto types = .ok () := by
  have valid' :
      (condition.validate Capabilities.crypto types).bind (fun _ =>
        (yes.validate Capabilities.crypto types).bind (fun _ =>
          no.validate Capabilities.crypto types)) = .ok () := by
    simpa [Expr.validate, Capabilities.crypto, Ty.isJubjub, Ty.isBytes,
      Ty.isForeign, Bind.bind, Except.bind] using valid
  obtain ⟨value, conditionValid⟩ :=
    firstBindSuccess (condition.validate Capabilities.crypto types) (fun _ =>
      (yes.validate Capabilities.crypto types).bind (fun _ =>
        no.validate Capabilities.crypto types)) valid'
  cases value
  exact conditionValid

/-- Every scalar source operand is valid when all encoded fields validate.
For boolean expressions, the condition appears inside the encoded Native
selector, so validation of that field supplies the operand's validation. -/
theorem sourceOperandsValid_of_fields (types : TypeEnv) (operation : Impact.Op)
    (valid : ∀ field ∈ operation.fields,
      field.validate Capabilities.crypto types = .ok ()) :
    ImpactOperationAgreement.SourceOperandsValid types operation := by
  cases operation with
  | mapIndex slot key =>
    cases key with
    | field expression =>
      change expression.validate Capabilities.scalarFragment types = .ok ()
      exact valid expression (by simp [Impact.Op.fields, Impact.Aligned.fields])
    | _ => trivial
  | push value storage =>
    cases value with
    | field expression =>
      change expression.validate Capabilities.scalarFragment types = .ok ()
      exact valid expression (by simp [Impact.Op.fields, Impact.Aligned.fields])
    | bitExpr expression =>
      change expression.validate Capabilities.scalarFragment types = .ok ()
      have selectorValid :
          (Expr.select expression (.native 1) (.native 0)).validate
            Capabilities.crypto types = .ok () :=
        valid (.select expression (.native 1) (.native 0))
          (by simp [Impact.Op.fields, Impact.Aligned.fields])
      simpa [Capabilities.scalarFragment] using
        select_condition_valid selectorValid
    | _ => trivial
  | popeq value =>
    cases value with
    | field expression =>
      change expression.validate Capabilities.scalarFragment types = .ok ()
      exact valid expression (by simp [Impact.Op.fields, Impact.Aligned.fields])
    | bitExpr expression =>
      change expression.validate Capabilities.scalarFragment types = .ok ()
      have selectorValid :
          (Expr.select expression (.native 1) (.native 0)).validate
            Capabilities.crypto types = .ok () :=
        valid (.select expression (.native 1) (.native 0))
          (by simp [Impact.Op.fields, Impact.Aligned.fields])
      simpa [Capabilities.scalarFragment] using
        select_condition_valid selectorValid
    | _ => trivial
  | _ => trivial

/-- Check only the source expression admissions used by the scalar Impact
fragment. Opcode and plan-shape acceptance remain separate checks. -/
def operandsSupported : Impact.Op → _root_.Bool
  | .mapIndex _ (.field expression) => (certify expression).isSome
  | .push (.field expression) _ => (certify expression).isSome
  | .push (.bitExpr expression) _ => (certify expression).isSome
  | .popeq (.field expression) => (certify expression).isSome
  | .popeq (.bitExpr expression) => (certify expression).isSome
  | _ => _root_.Bool.true

private theorem scalarExpression_of_certified {ty : Ty} {expression : Expr ty}
    (checked : (certify expression).isSome = _root_.Bool.true) :
    ScalarExpression expression := by
  cases certificate : certify expression with
  | none => simp [certificate] at checked
  | some certified => exact certified.down

/-- A successful checker result provides exactly the operand admissions used
by source-to-wire projection. -/
theorem sourceOperandsAdmitted_of_check (operation : Impact.Op)
    (checked : operandsSupported operation = _root_.Bool.true) :
    ScalarOperandAdmission operation := by
  cases operation with
  | mapIndex slot key =>
    cases key with
    | field expression =>
      change (certify expression).isSome = _root_.Bool.true at checked
      exact scalarExpression_of_certified checked
    | _ => trivial
  | push value storage =>
    cases value with
    | field expression | bitExpr expression =>
      change (certify expression).isSome = _root_.Bool.true at checked
      exact scalarExpression_of_certified checked
    | _ => trivial
  | popeq value =>
    cases value with
    | field expression | bitExpr expression =>
      change (certify expression).isSome = _root_.Bool.true at checked
      exact scalarExpression_of_certified checked
    | _ => trivial
  | _ => trivial

end Noctium.Verification.ImpactOperandValidation
