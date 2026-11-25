import Noctium.Verification.GenericStateAbsenceAuthentication
import Noctium.Verification.GenericStateWriteInversion

namespace Noctium.Verification.GenericStateAbsenceInversion
open Backend ScalarNormalization

/-- A successful evaluation of the exact scalar absence chunk forces the
original typed key expression to evaluate. -/
theorem requireAbsent_source_evaluates (state : List StateDecl) (name : String)
    (keyTy : Ty) (keyExpr : Expr keyTy) (base : Impact.Plan)
    (support : ScalarType keyTy) (ctx : EvalContext) (env : EvalEnv) (native : List NativeState.Op)
    (accepted : Impact.appendEffect state
      (.requireAbsent name keyTy keyExpr) {} = .ok base)
    (modulus : ctx.modulus = Field.modulus)
    (evaluated : base.operations.mapM (GenericStateOps.evalOp ctx env) = .ok native) :
    ∃ key, keyExpr.eval ctx env = .ok key := by
  obtain ⟨_, _, operations⟩ :=
    GenericStateAbsenceAuthentication.requireAbsent_scalar_chunk
      state name keyTy keyExpr base support accepted
  cases projected : (GenericStateWriteEvaluation.scalarProjection support keyExpr).eval ctx env with
  | error message =>
    simp [operations, List.mapM_cons, GenericStateOps.evalOp, GenericStateOps.evalAligned,
      projected, bind, Except.bind, pure, Except.pure] at evaluated
  | ok number =>
    obtain ⟨key, sourceEval, _⟩ :=
      GenericStateWriteInversion.scalarProjection_invert ctx env support keyExpr
        number modulus projected
    exact ⟨key, sourceEval⟩

end Noctium.Verification.GenericStateAbsenceInversion
