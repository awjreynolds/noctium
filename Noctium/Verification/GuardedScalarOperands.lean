import Noctium.Verification.GenericStateEffectStep
import Noctium.Verification.ScalarGuardedPlanAdmission

namespace Noctium.Verification.GuardedScalarOperands

open Backend

/-- Admitted guarded scalar effects provide the operand scope required by
the generic source-effect step. -/
theorem of_admitted {state : List StateDecl} {effect : Effect}
    (admitted : ScalarGuardedPlanAdmission.ScalarEffect state effect) :
    GenericStateEffectStep.ScalarOperands effect := by
  cases admitted with
  | cell effect _ operand =>
    cases effect <;>
      simp_all [ScalarCellSourceReads.ScalarCellOperand,
        GenericStateEffectStep.ScalarOperands]
  | readMap name destination keyTy valueTy key _ _ keyAdmitted =>
    simpa [GenericStateEffectStep.ScalarOperands] using keyAdmitted
  | writeMap name keyTy valueTy key value _ _ keyAdmitted valueAdmitted =>
    exact ⟨keyAdmitted, valueAdmitted⟩
  | require condition conditionAdmitted =>
    simpa [GenericStateEffectStep.ScalarOperands] using conditionAdmitted
  | requireAbsent name keyTy key _ keyAdmitted =>
    simpa [GenericStateEffectStep.ScalarOperands] using keyAdmitted

end Noctium.Verification.GuardedScalarOperands
