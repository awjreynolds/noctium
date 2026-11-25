import Noctium.Verification.ImpactScalarType
import Noctium.Verification.ScalarNormalization

namespace Noctium.Verification.ImpactEvaluationValidation

open Noctium
open ScalarNormalization

/-- Invert a successful `Except.bind`. -/
private theorem validate_bind_ok {ε α β : Type} (first : Except ε α)
    (next : α → Except ε β) (result : β) :
    Except.bind first next = .ok result ↔
      ∃ intermediate, first = .ok intermediate ∧ next intermediate = .ok result := by
  cases first <;> simp [Except.bind]

/-- Invert a successful sequence of two unit validations. -/
theorem validate_unit_bind {ε : Type} (first next : Except ε Unit) :
    Except.bind first (fun _ => next) = .ok () ↔
      first = .ok () ∧ next = .ok () := by
  cases first <;> simp [Except.bind]

/-- A validated `let` validates its value and its body in the extended type
environment. -/
theorem let_valid (caps : Capabilities) (env : TypeEnv)
    {source target : Ty} (name : String) (value : Expr source) (body : Expr target)
    (valid : (Expr.letE name value body).validate caps env = .ok ()) :
    value.validate caps env = .ok () ∧
      body.validate caps ((name, source) :: env) = .ok () := by
  simp only [Expr.validate] at valid
  change Except.bind (value.validate caps env)
      (fun _ => body.validate caps ((name, source) :: env)) = .ok () at valid
  exact (validate_unit_bind _ _).mp valid

private theorem scalar_type_beq_sound {ty : Ty} (scalarType : ScalarType ty)
    (left : Ty) (equal : (left == ty) = true) : left = ty := by
  cases scalarType <;> cases left <;> simp_all [BEq.beq, instBEqTy.beq]

private theorem uint_type_valid_bound (caps : Capabilities) (maximum : Nat)
    (valid : (Ty.uint maximum).validate caps = .ok ()) :
    maximum ≤ ScalarPolicy.maxUint := by
  by_cases bound : maximum ≤ ScalarPolicy.maxUint
  · exact bound
  · simp [Ty.validate, Ty.scalarKind, ScalarPolicy.validate, bound,
      bind, Except.bind] at valid

/-- Successful validation of a scalar reference requires its visible type
environment entry to have the exact same name and type. -/
theorem ref_lookup (caps : Capabilities) (env : TypeEnv) {ty : Ty}
    (name : String) (scalarType : ScalarType ty)
    (valid : (Expr.ref (ty := ty) name).validate caps env = .ok ()) :
    env.lookup name = some ty := by
  simp only [Expr.validate, bind, validate_bind_ok] at valid
  rcases valid with ⟨_, typeValid, lookupValid⟩
  cases lookup : env.lookup name with
  | none => simp [lookup] at lookupValid
  | some found =>
      simp only [lookup] at lookupValid
      split at lookupValid
      · rename_i equal
        have sameType := scalar_type_beq_sound scalarType found equal
        rw [sameType]
      · simp at lookupValid

/-- A validated scalar cast validates its child and its target wire type name
decodes back to the same target type. -/
theorem cast_valid_children (caps : Capabilities) (env : TypeEnv)
    {source target : Ty} (sourceType : ScalarType source) (targetType : ScalarType target)
    (value : Expr source)
    (valid : (Expr.cast target value).validate caps env = .ok ()) :
    value.validate caps env = .ok () ∧
      ImpactScalarType.parseScalarTypeName (NativeExpression.typeName target) = some target := by
  cases targetType with
  | native =>
      cases sourceType <;>
        simp only [Expr.validate, Ty.isBytes, Ty.isOpaqueBytes, Ty.isOpaqueString,
          Ty.isJubjub, Ty.isForeign] at valid <;>
        change Except.bind (Ty.validate caps .native)
          (fun _ => value.validate caps env) = .ok () at valid
      all_goals
        rcases (validate_bind_ok _ _ _).mp valid with ⟨_, _, valueValid⟩
        exact ⟨valueValid, ImpactScalarType.parseScalarTypeName_native⟩
  | bool =>
      cases sourceType <;>
        simp only [Expr.validate, Ty.isBytes, Ty.isOpaqueBytes, Ty.isOpaqueString,
          Ty.isJubjub, Ty.isForeign] at valid <;>
        change Except.bind (Ty.validate caps .bool)
          (fun _ => value.validate caps env) = .ok () at valid
      all_goals
        rcases (validate_bind_ok _ _ _).mp valid with ⟨_, _, valueValid⟩
        exact ⟨valueValid, ImpactScalarType.parseScalarTypeName_bool⟩
  | uint maximum =>
      cases sourceType <;>
        simp only [Expr.validate, Ty.isBytes, Ty.isOpaqueBytes, Ty.isOpaqueString,
          Ty.isJubjub, Ty.isForeign] at valid <;>
        change Except.bind (Ty.validate caps (.uint maximum))
          (fun _ => value.validate caps env) = .ok () at valid
      all_goals
        rcases (validate_bind_ok _ _ _).mp valid with ⟨_, typeValid, valueValid⟩
        have maximumBound := uint_type_valid_bound caps maximum typeValid
        exact ⟨valueValid,
          ImpactScalarType.parseScalarTypeName_uint maximum maximumBound⟩

end Noctium.Verification.ImpactEvaluationValidation
