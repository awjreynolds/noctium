import Noctium.Verification.ImpactExpressionEvaluation
import Noctium.Verification.ScalarNormalization

namespace Noctium.Verification.ImpactReferenceEvaluation

open ImpactExpressionEvaluation ScalarNormalization

/-- Every declared name has the canonical dynamic value of its visible
source type. Lookup uses the first binding, including shadowed names. -/
def TypedScalarEnv (types : TypeEnv) (values : EvalEnv) : Prop :=
  ∀ name ty, types.lookup name = some ty →
    ∃ value : ty.Denote, values.lookup name = some (Value.pack ty value) ∧ Canonical ty value

theorem TypedScalarEnv.extend {types : TypeEnv} {values : EvalEnv}
    (typed : TypedScalarEnv types values) (name : String) {ty : Ty} (value : ty.Denote)
    (canonical : Canonical ty value) :
    TypedScalarEnv ((name, ty) :: types) ((name, Value.pack ty value) :: values) := by
  intro requested expected found
  by_cases same : requested = name
  · subst requested
    simp at found
    subst expected
    exact ⟨value, by simp, canonical⟩
  · have different : (requested == name) = false := beq_eq_false_iff_ne.mpr same
    simp [List.lookup_cons, different] at found ⊢
    exact typed requested expected found

/-- Rust's dynamic lookup and Lean's typed reference return the same packed
value when the environment supplies the canonical value of the declared type. -/
theorem evaluateReference_agrees (ctx : EvalContext) (modulus : ctx.modulus = Field.modulus)
    (types : TypeEnv) (values : EvalEnv) (typed : TypedScalarEnv types values)
    (name : String) {ty : Ty} (scalarType : ScalarType ty) (declared : types.lookup name = some ty) :
    evaluateReference ctx.modulus values name =
      ((Expr.ref (ty := ty) name).eval ctx values).toOption.map (Value.pack ty) := by
  obtain ⟨value, found, canonical⟩ := typed name ty declared
  have accepted := (ImpactScalarPrimitives.canonical_pack_iff ctx modulus scalarType value).2
    canonical
  have loaded : evaluateReference ctx.modulus values name = some (Value.pack ty value) := by
    simp [evaluateReference, found, accepted]
  rw [loaded]
  cases scalarType with
  | native =>
    have fits : value < ctx.modulus := modulus.symm ▸ canonical.1
    simp [Expr.eval, canonical_eq, Value.pack, Value.as, found, fits] <;> rfl
  | bool =>
    simp [Expr.eval, canonical_eq, Value.pack, Value.as, found] <;> rfl
  | uint maximum =>
    have fits : value < ctx.modulus := modulus.symm ▸ canonical.1
    simp [Expr.eval, canonical_eq, Value.pack, Value.as, found, fits,
      canonical.2.1, canonical.2.2] <;> rfl

end Noctium.Verification.ImpactReferenceEvaluation
