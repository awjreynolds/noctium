import Noctium.Verification.ScalarCircuitWitness

namespace Noctium.Verification.ScalarTranslation

open Lean Backend NativeRelation ScalarNormalization
open ScalarWitnessConstruction (InputFrame)

export ScalarTranslationSoundness (lowerCircuit_sound)
export ScalarWitnessConstruction (lowerCircuit_complete)

/-- An admitted scalar circuit runs successfully exactly when its accepted,
strictly decoded lowering has a satisfying witness preserving the source inputs. -/
theorem lowerCircuit_satisfiable_iff (ctx : EvalContext) (hash : Hash)
    (implementation : HashAgreement ctx hash) (circuit : Circuit) (values : EvalEnv)
    (inputs : Assignment) (json : Json) (program : Program)
    (admitted : CanonicalInputs circuit values inputs)
    (scalarAdmission : ScalarCircuitAdmission circuit)
    (lowered : Zkir.lowerCircuit circuit = .ok json)
    (decoded : NativeRelationJson.decode json = .ok program) :
    (∃ result, circuit.run ctx values = .ok result) ↔
      (∃ witness, InputFrame inputs witness ∧
        ∀ instruction ∈ program.instructions, instruction.Holds hash witness) := by
  constructor
  · rintro ⟨result, success⟩
    exact ScalarWitnessConstruction.lowerCircuit_construct_witness ctx hash implementation
      circuit values result inputs json program admitted scalarAdmission lowered decoded success
  · rintro ⟨witness, frame, holds⟩
    have witnessInputs : CanonicalInputs circuit values witness :=
      ⟨admitted.unique, admitted.declared, admitted.complete,
        fun input member value lookup canonical =>
          (frame input.name).trans (admitted.binding input member value lookup canonical)⟩
    let streams : InputStreams :=
      ⟨program.inputValues .public witness, program.inputValues .private witness⟩
    have satisfies : CircuitSatisfies hash program streams witness (program.groups witness) :=
      ⟨holds, rfl, rfl, rfl⟩
    obtain ⟨result, success, _⟩ := lowerCircuit_sound ctx hash implementation circuit values
      json program streams witness (program.groups witness) witnessInputs scalarAdmission
      lowered decoded satisfies
    exact ⟨result, success⟩

end Noctium.Verification.ScalarTranslation
