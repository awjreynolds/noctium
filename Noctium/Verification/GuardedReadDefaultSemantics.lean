import Noctium.Verification.GenericStateEvaluationCanonical
import Noctium.Verification.GenericStateReadCellEvaluation
import Noctium.Backend.Impact

namespace Noctium.Verification.GuardedReadDefaultSemantics

open Backend ScalarNormalization NativeRelation

def scalarDefaultValue {ty : Ty} (scalarType : ScalarType ty) : ty.Denote :=
  match scalarType with
  | .native => 0
  | .bool => false
  | .uint _ => 0

def scalarDefaultExpr {ty : Ty} (scalarType : ScalarType ty) : Expr ty :=
  match scalarType with
  | .native => .native 0
  | .bool => .bool false
  | .uint maximum => .uint maximum 0

def scalarDefaultTest {ty : Ty} (scalarType : ScalarType ty)
    (candidate : ty.Denote) : Bool :=
  match scalarType with
  | .native => candidate == 0
  | .bool => candidate == false
  | .uint _ => candidate == 0

def inactiveReadDefaultConstraint (name : String) (guard : Expr .bool)
    {ty : Ty} (scalarType : ScalarType ty) : Expr .bool :=
  .eq (.ref name) (.select guard (.ref name) (scalarDefaultExpr scalarType))

theorem inactiveDefaultConstraints_plain_scalar (read : Impact.Read)
    (guard : Expr .bool) (scalarType : ScalarType read.ty)
    (components : read.components = []) (guarded : read.guard = some guard) :
    read.inactiveDefaultConstraints =
      [inactiveReadDefaultConstraint read.name guard scalarType] := by
  cases read with
  | mk name ty readComponents schema readGuard rootCellRead =>
    cases scalarType with
    | native =>
      change readComponents = [] at components
      change readGuard = some guard at guarded
      subst readComponents
      subst readGuard
      rfl
    | bool =>
      change readComponents = [] at components
      change readGuard = some guard at guarded
      subst readComponents
      subst readGuard
      rfl
    | uint maximum =>
      change readComponents = [] at components
      change readGuard = some guard at guarded
      subst readComponents
      subst readGuard
      rfl

theorem inactiveReadDefaultConstraint_scalarExpression {ty : Ty}
    (name : String) (guard : Expr .bool) (scalarType : ScalarType ty)
    (guardAdmission : ScalarExpression guard) :
    ScalarExpression (inactiveReadDefaultConstraint name guard scalarType) := by
  cases scalarType with
  | native =>
    exact .eq (.ref name) (.select guard (.ref name) (.native 0)) .native
      (.ref name .native) (.select guard (.ref name) (.native 0) .native
        guardAdmission (.ref name .native) (.native 0))
  | bool =>
    exact .eq (.ref name) (.select guard (.ref name) (.bool false)) .bool
      (.ref name .bool) (.select guard (.ref name) (.bool false) .bool
        guardAdmission (.ref name .bool) (.bool false))
  | uint maximum =>
    exact .eq (.ref name) (.select guard (.ref name) (.uint maximum 0))
      (.uint maximum) (.ref name (.uint maximum))
      (.select guard (.ref name) (.uint maximum 0) (.uint maximum)
        guardAdmission (.ref name (.uint maximum)) (.uint maximum 0))

theorem inactiveReadDefaultConstraint_eval (ctx : EvalContext) (complete : EvalEnv)
    (name : String) {ty : Ty} (guard : Expr .bool) (scalarType : ScalarType ty)
    (candidate : ty.Denote)
    (lookup : complete.lookup name = some (Value.pack ty candidate))
    (canonical : Canonical ty candidate) (modulus : ctx.modulus = Field.modulus)
    (guardInactive : guard.eval ctx complete = .ok false) :
    ∃ result : Bool,
      (inactiveReadDefaultConstraint name guard scalarType).eval ctx complete = .ok result ∧
      (result = true ↔ candidate = scalarDefaultValue scalarType) := by
  have candidateEval := GenericStateReadCellEvaluation.canonical_ref_eval
    ctx complete name ty candidate lookup modulus canonical
  have modulusPos : 0 < Field.modulus := by decide
  have defaultEval : (scalarDefaultExpr scalarType).eval ctx complete =
      .ok (scalarDefaultValue scalarType) := by
    cases scalarType with
    | native => simp [scalarDefaultExpr, scalarDefaultValue, Expr.eval, modulus,
        modulusPos, Pure.pure, Except.pure]
    | bool => simp [scalarDefaultExpr, scalarDefaultValue, Expr.eval]
    | uint maximum =>
      have maximumBound : maximum ≤ ScalarPolicy.maxUint := canonical.2.1
      simp [scalarDefaultExpr, scalarDefaultValue, Expr.eval, canonical_eq,
        maximumBound, modulus, modulusPos, Pure.pure, Except.pure]
  have evalCondition :
      (inactiveReadDefaultConstraint name guard scalarType).eval ctx complete =
        .ok (scalarDefaultTest scalarType candidate) := by
    cases scalarType <;>
      simp [inactiveReadDefaultConstraint, Expr.eval, guardInactive,
        candidateEval, defaultEval, scalarDefaultTest, scalarDefaultValue,
        Bind.bind, Except.bind, Pure.pure, Except.pure]
    all_goals rfl
  refine ⟨scalarDefaultTest scalarType candidate, evalCondition, ?_⟩
  cases scalarType <;> cases candidate <;>
    simp [scalarDefaultTest, scalarDefaultValue]

theorem scalarDefaultValue_source_zero {ty : Ty} (scalarType : ScalarType ty)
    (candidate : ty.Denote) (canonical : Canonical ty candidate) :
    candidate = scalarDefaultValue scalarType ↔
      sourceScalar? ty candidate = some zero := by
  have numberBound := ScalarNormalization.scalar_number_canonical
    scalarType candidate canonical
  have scalarNumberZero (n : Nat) (bound : n < Field.modulus) :
      scalar n = zero ↔ n = 0 := by
    constructor
    · intro equal
      have values := congrArg Fin.val equal
      simpa [scalar, NativeRelation.scalar, NativeRelation.zero,
        Nat.mod_eq_of_lt bound] using values
    · intro equal
      subst n
      exact scalar_zero
  have sourceZero : sourceScalar? ty candidate = some zero ↔
      number scalarType candidate = 0 := by
    rw [ScalarNormalization.sourceScalar_number]
    simp only [Option.some.injEq]
    exact scalarNumberZero _ numberBound
  have candidateNumberZero : candidate = scalarDefaultValue scalarType ↔
      number scalarType candidate = 0 := by
    cases scalarType with
    | native => rfl
    | bool => cases candidate <;> simp [scalarDefaultValue, number]
    | uint maximum => rfl
  exact candidateNumberZero.trans sourceZero.symm

end Noctium.Verification.GuardedReadDefaultSemantics
