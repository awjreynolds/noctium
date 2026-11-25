import Noctium.Verification.ScalarWitnessReturns
import Noctium.Verification.ScalarWitnessAliases

namespace Noctium.Verification.ScalarWitnessConstruction

open Lean Backend NativeRelation NativeRelationJson ScalarLowering ScalarNormalization

private theorem stateRunBind {α β} (first : StateM Zkir.LowerState α)
    (next : α → StateM Zkir.LowerState β) (state : Zkir.LowerState) :
    (do let value ← first; next value).run state =
      (next (first.run state).1).run (first.run state).2 := rfl

theorem completes_circuit_outputs (ctx : EvalContext) (hash : Hash)
    (implementation : HashAgreement ctx hash) (circuit : Circuit) (values : EvalEnv)
    (inputs : NativeRelation.Assignment) (admitted : CanonicalInputs circuit values inputs)
    (identifiers : ∀ input ∈ circuit.inputs,
      validIdentifier ("%input_" ++ input.name) = true)
    (scalarAdmission : ScalarCircuitAdmission circuit)
    (outputValidation : ∀ returned ∈ circuit.outputs,
      returned.value.validate Capabilities.crypto
        (circuit.inputs.map fun input => (input.name, input.ty)) = .ok ())
    (outputsEvaluated : ∃ result,
      circuit.outputs.mapM (evalOutput ctx values) = .ok result) :
    Completes hash inputs (do
      let texts ← Zkir.lowerReturnFields circuit.outputs
      if !texts.isEmpty then Zkir.bindPublic texts
      Zkir.emit "output" [("vals", toJson texts)]) := by
  intro witness state meaning inputFrame aliases budget
  let footer (texts : List String) : StateM Zkir.LowerState Unit := do
    if !texts.isEmpty then Zkir.bindPublic texts
    Zkir.emit "output" [("vals", toJson texts)]
  have footerFrame : ∀ texts, Zkir.PreservesOutputCapacityFrame (footer texts) := by
    intro texts
    dsimp only [footer]
    split
    · apply Zkir.bind_preservesOutputCapacityFrame
      · exact Zkir.emit_preservesOutputCapacityFrame _ _
      · intro _
        exact Zkir.emit_preservesOutputCapacityFrame _ _
    · exact Zkir.emit_preservesOutputCapacityFrame _ _
  have fieldsBudget : (Zkir.lowerReturnFields circuit.outputs).run state |>.2.next ≤
      Native.maxInstructions * Native.maxVectorLength := by
    let texts := (Zkir.lowerReturnFields circuit.outputs).run state |>.1
    let fieldsState := (Zkir.lowerReturnFields circuit.outputs).run state |>.2
    have footerBudget : (footer texts).run fieldsState |>.2.next ≤
        Native.maxInstructions * Native.maxVectorLength := by
      change ((do
        let returned ← Zkir.lowerReturnFields circuit.outputs
        footer returned).run state).2.next ≤ _ at budget
      rw [stateRunBind] at budget
      simpa [texts, fieldsState] using budget
    exact Nat.le_trans (footerFrame texts fieldsState).next footerBudget
  obtain ⟨⟨result⟩, scopes⟩ := completes_scalar_returnFields ctx hash implementation
    circuit.outputs values inputs (circuit.inputs.map fun input => (input.name, input.ty))
    (circuitAliases circuit) scalarAdmission.outputs outputValidation outputsEvaluated
    witness state meaning (admitted.typedEnvironment circuit values inputs hash).aliases
    (current_aliases hash inputs witness circuit values state admitted identifiers inputFrame aliases)
    fieldsBudget
  have footerMeaning : LowerStateMeaning hash result.witness
      ((footer ((Zkir.lowerReturnFields circuit.outputs).run state).1).run
        ((Zkir.lowerReturnFields circuit.outputs).run state).2).2 := by
    dsimp only [footer]
    split
    · exact emit_output hash result.witness _
        (emit_impact hash result.witness _ result.meaning _ scopes) _ scopes
    · exact emit_output hash result.witness _ result.meaning _ scopes
  refine ⟨{witness := result.witness, meaning := footerMeaning, aliases := ?_, frame := result.frame}⟩
  change ((footer ((Zkir.lowerReturnFields circuit.outputs).run state).1).run
    ((Zkir.lowerReturnFields circuit.outputs).run state).2).2.aliases = state.aliases
  dsimp only [footer]
  split <;> exact result.aliases

end Noctium.Verification.ScalarWitnessConstruction
