import Noctium.Verification
import Noctium.Verification.ScalarCircuitWitness

namespace ScalarExpressionLoweringTests

open Noctium Noctium.Verification ScalarLowering ScalarNormalization
open ScalarExpressionLowering

example : ExprComplete
    (.letE "x" (.poseidon2 11 (.native 3) (.native 4))
      (.assertE (.bool true) (.select (.bool true) (.ref "x") (.native 0)))) :=
  lowerExpr_complete _ (.letE _ _ _ .native
    (.poseidon2 _ _ _ (.native 3) (.native 4))
    (.assertE _ _ (.bool true)
      (.select _ _ _ .native (.bool true) (.ref "x" .native) (.native 0))))

private def ctx : EvalContext :=
  {modulus := Field.modulus, poseidon2 := fun _ _ _ => .ok 0}

example : (Expr.select (.bool true) (.native 9)
    (.assertE (.bool false) (.native 0))).eval ctx [] =
    .error "helper assertion failed" := by cbv

open Lean Elab Command in
run_cmd do
  let environment ← getEnv
  for proof in [
      `Noctium.Verification.ScalarExpressionLowering.lowerExpr_complete,
      `Noctium.Verification.ScalarTranslationSoundness.lowerCircuit_sound,
      `Noctium.Verification.ScalarWitnessConstruction.lowerCircuit_complete] do
    match Noctium.Verification.Audit.axiomsIn environment proof with
    | .ok _ => pure ()
    | .error error => throwError "{proof}: {error}"

end ScalarExpressionLoweringTests
