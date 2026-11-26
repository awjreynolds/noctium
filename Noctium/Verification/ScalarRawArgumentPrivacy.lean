import Noctium.Verification.GenericStateEffectValidation
import Noctium.Verification.GenericStateKeys

namespace Noctium.Verification.ScalarRawArgumentPrivacy
open Backend

/-- Every accepted native call input names a private source circuit input. -/
theorem lower_callInputs_private (state : List StateDecl) (entry : Entrypoint)
    (plan : Impact.Plan) (accepted : Impact.lower state entry = .ok plan) :
    ∀ input ∈ entry.circuit.inputs, input.name ∈ entry.callInputs →
      input.visibility = .private := by
  have sourceAccepted := GenericStateEffectValidation.lower_source_validated
    state entry plan accepted
  have circuitAccepted := GenericStateEffectValidation.lower_circuit_validated_source
    state entry plan accepted
  have inputNamesUnique : uniqueNames (entry.circuit.inputs.map (·.name)) = true := by
    cases unique : uniqueNames (entry.circuit.inputs.map (·.name)) with
    | true => rfl
    | false => simp [Circuit.validate, unique, Bind.bind, Except.bind] at circuitAccepted
  have inputNamesNodup : (entry.circuit.inputs.map (·.name)).Nodup := by
    apply GenericStateKeys.nodup_of_eraseDups_length_eq
    apply beq_iff_eq.mp
    simpa [uniqueNames] using inputNamesUnique
  exact Entrypoint.validate_callInputs_private
    GenericStateEffectValidation.stateEffectCaps
    state entry inputNamesNodup sourceAccepted

end Noctium.Verification.ScalarRawArgumentPrivacy
