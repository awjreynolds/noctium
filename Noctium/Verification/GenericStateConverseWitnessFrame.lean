import Noctium.Verification.GenericStateCheckedSchedule
import Noctium.Verification.ScalarLedgerSourceIdentifiers
import Noctium.Verification.ScalarValidation

namespace Noctium.Verification.GenericStateConverseWitnessFrame
open Backend NativeRelation ScalarNormalization

theorem canonicalInputs_input_frame (sourceEntry : Entrypoint)
    (values : EvalEnv) (before after : Assignment)
    (admitted : CanonicalInputs sourceEntry.circuit values before)
    (frame : ∀ name, after ("%input_" ++ name) = before ("%input_" ++ name)) :
    CanonicalInputs sourceEntry.circuit values after := by
  refine ⟨admitted.unique, admitted.declared, admitted.complete, ?_⟩
  intro input present value found canonical
  rw [frame input.name]
  exact admitted.binding input present value found canonical

/-- Witness extension preserves the exact checked plan when it preserves the
source input bindings. Candidate decoding and the VM check both stay in place. -/
theorem checkedPlan_input_frame (ctx : EvalContext)
    (sourceEntry : Entrypoint) (plan : Impact.Plan) (values : EvalEnv)
    (before after : Assignment) (slots : List NativeState.Slot)
    (final : NativeState.Machine)
    (frame : ∀ name, after ("%input_" ++ name) = before ("%input_" ++ name))
    (checked : GenericStateCheckedSchedule.CheckedPlan ctx sourceEntry plan values
      before slots final) :
    GenericStateCheckedSchedule.CheckedPlan ctx sourceEntry plan values
      after slots final := by
  unfold GenericStateCheckedSchedule.CheckedPlan GuardedScalarCandidateState.runCheckedCandidates
    at checked ⊢
  rwa [GenericStateInputValues.decodeReads_input_frame _ before after frame]

/-- Actual accepted requirements retain their input names after witness
extension, including reads that carry activity metadata. -/
theorem expected_input_agreement (state : List StateDecl)
    (sourceEntry : Entrypoint) (plan : Impact.Plan) (expected : Backend.Native.Expected)
    (before after : Assignment)
    (planAccepted : Impact.lower state sourceEntry = .ok plan)
    (accepted : Backend.Native.expectedEntrypoint state sourceEntry = .ok expected)
    (scalarInputs : ∀ input ∈ sourceEntry.circuit.inputs, Nonempty (ScalarType input.ty))
    (frame : ∀ name, after ("%input_" ++ name) = before ("%input_" ++ name)) :
    ScalarValidation.InputAgreement expected before after := by
  intro requirement present
  exact ScalarLedgerSourceIdentifiers.accepted_scalar_requirements_input_frame
    state sourceEntry plan expected planAccepted accepted scalarInputs before after frame
    requirement (List.mem_append_right _ present)

end Noctium.Verification.GenericStateConverseWitnessFrame
