import Noctium.Verification.ScalarCircuitWitness

namespace ScalarTranslationTests
open Lean Noctium Noctium.Backend Noctium.Verification
open NativeRelation ScalarNormalization
open ScalarTranslationSoundness (defaultLoweredRows lowerCircuit_sound)
open ScalarValidationOpcodeProfile (checkedScalarOpcodeProfile)
open ScalarWitnessConstruction (lowerCircuit_complete)

private def ctx : EvalContext := {modulus := Field.modulus, poseidon2 := fun _ _ _ => .ok 0}
private def hash : Hash := fun _ => zero
private theorem implementation : HashAgreement ctx hash := by
  constructor
  · rfl
  · intro domain left right
    rfl

private def discardedUnderflow : Circuit := {
  name := "discardedUnderflow"
  outputs := [{name := "result", ty := .native, value := .letE "ignored" (.usub (.uint 7 1) (.uint 7 2)) (.native 9)}]
}

private def shadowed : Circuit := {
  name := "shadowed"
  outputs := [{name := "result", ty := .native, value := .letE "x" (.native 2) (.letE "x" (.add (.ref "x") (.native 3))
      (.mul (.ref "x") (.ref "x")))}]
}

private def checkedLowering (circuit : Circuit) : Bool :=
  match Zkir.lowerCircuit circuit with
  | .error _ => false
  | .ok json =>
    match NativeRelationJson.decode json with
    | .error _ => false
    | .ok program => checkedScalarOpcodeProfile (defaultLoweredRows circuit).toList.zipIdx program.instructions

#guard checkedLowering discardedUnderflow
#guard checkedLowering shadowed

private theorem discardedUnderflowRun :
    discardedUnderflow.run ctx [] = .error "unsigned subtraction underflow" := by cbv
private theorem shadowedRun :
    shadowed.run ctx [] = .ok [("result", .native 25)] := by cbv

private theorem emptyInputs (circuit : Circuit) (empty : circuit.inputs = []) (witness : Assignment) :
    CanonicalInputs circuit [] witness := by
  constructor
  · rfl
  · simp
  · simp [empty]
  · simp [empty]

private theorem discardedUnderflowAdmission : ScalarCircuitAdmission discardedUnderflow := by
  constructor
  · simp [discardedUnderflow]
  · intro returned member
    simp only [discardedUnderflow, List.mem_singleton] at member
    subst returned
    exact ⟨.native, .letE _ _ _ (.uint 7) (.usub _ _ (.uint 7 1) (.uint 7 2)) (.native 9)⟩

private theorem shadowedAdmission : ScalarCircuitAdmission shadowed := by
  constructor
  · simp [shadowed]
  · intro returned member
    simp only [shadowed, List.mem_singleton] at member
    subst returned
    exact ⟨.native, .letE _ _ _ .native (.native 2)
      (.letE _ _ _ .native (.add _ _ (.ref "x" .native) (.native 3))
        (.mul _ _ (.ref "x" .native) (.ref "x" .native)))⟩

/-- Every satisfying assignment would force successful source execution. An
unused partial expression therefore has no satisfying native assignment. -/
example (json : Json) (program : Program) (streams : InputStreams) (witness : Assignment)
    (groups : List (List Scalar))
    (lowered : Zkir.lowerCircuit discardedUnderflow = .ok json)
    (decoded : NativeRelationJson.decode json = .ok program)
    (profile : checkedScalarOpcodeProfile (defaultLoweredRows discardedUnderflow).toList.zipIdx
      program.instructions = true)
    (satisfies : CircuitSatisfies hash program streams witness groups) : False := by
  obtain ⟨result, successful, _⟩ := lowerCircuit_sound ctx hash implementation discardedUnderflow []
    json program streams witness groups (emptyInputs discardedUnderflow rfl witness)
    discardedUnderflowAdmission lowered decoded profile satisfies
  rw [discardedUnderflowRun] at successful
  cases successful

/-- Completeness supplies a witness for the actual emitted CSE/shadowing program,
with an authenticated final Impact vector and exact host returns. -/
example (json : Json) (program : Program)
    (lowered : Zkir.lowerCircuit shadowed = .ok json)
    (decoded : NativeRelationJson.decode json = .ok program)
    (profile : checkedScalarOpcodeProfile (defaultLoweredRows shadowed).toList.zipIdx
      program.instructions = true) :
    ∃ witness, Satisfies hash program {publicValues := [], privateValues := []}
      witness [[scalar 25]] [scalar 25] := by
  obtain ⟨witness, frame, satisfies⟩ := lowerCircuit_complete ctx hash implementation shadowed []
    [("result", .native 25)] (fun _ => zero) json program
    (emptyInputs shadowed rfl _) shadowedAdmission lowered decoded profile shadowedRun
  exact ⟨witness, by simpa [shadowed, valueNumber] using satisfies⟩

end ScalarTranslationTests
