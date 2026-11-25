import Noctium.Verification.ScalarWitnessAssembly
import Noctium.Verification.ScalarCircuit
import Noctium.Verification.ScalarValidationMeaning

namespace Noctium.Verification.ScalarWitnessConstruction

open Backend NativeRelation NativeRelationJson ScalarLowering ScalarNormalization

/-- Input admission establishes that every source input resolves through the
normalizer's typed aliases to the same native witness field. -/
theorem initial_aliases (circuit : Circuit) (values : EvalEnv)
    (inputs : NativeRelation.Assignment) (hash : Hash)
    (admitted : CanonicalInputs circuit values inputs)
    (identifiers : ∀ input ∈ circuit.inputs,
      validIdentifier ("%input_" ++ input.name) = true) :
    LowerAliasAgreement hash inputs inputs (circuitAliases circuit) [] values := by
  intro name ty raw value lookup typed
  obtain ⟨canonical, term, termLookup, meaning⟩ :=
    (CanonicalInputs.typedEnvironment circuit values inputs admitted hash).aliases
      name ty raw value lookup typed
  obtain ⟨input, member, inputName⟩ :=
    admitted.declared name raw (ScalarValidationMeaning.lookup_member lookup)
  have known : (circuitAliases circuit).lookup name =
      some (.input ("%input_" ++ name)) :=
    aliases_lookup circuit.inputs name ⟨input, member, inputName⟩
  have termIs : term = .input ("%input_" ++ name) :=
    Option.some.inj (termLookup.symm.trans known)
  have nativeValid : validIdentifier ("%input_" ++ name) = true := by
    simpa only [inputName] using identifiers input member
  refine ⟨term, termLookup, ?_⟩
  refine ⟨.reference ("%input_" ++ name), ?_, ?_⟩
  · exact (ScalarInstructionEncoding.OperandEncoding.reference _ nativeValid).decode
  · simp only [termIs, interpret_input, Operand.read]

/-- With no emitted aliases, the witness frame preserves every scoped source
input, so the initial normalizer aliases remain valid at the current witness. -/
theorem current_aliases (hash : Hash) (inputs witness : NativeRelation.Assignment)
    (circuit : Circuit) (values : EvalEnv) (state : Zkir.LowerState)
    (admitted : CanonicalInputs circuit values inputs)
    (identifiers : ∀ input ∈ circuit.inputs,
      validIdentifier ("%input_" ++ input.name) = true)
    (inputFrame : InputFrame inputs witness) (aliases : state.aliases = []) :
    LowerAliasAgreement hash inputs witness (circuitAliases circuit) state.aliases values := by
  rw [aliases]
  apply LowerAliasAgreement.of_frame hash inputs inputs witness 0
    (circuitAliases circuit) [] values
    (initial_aliases circuit values inputs hash admitted identifiers)
  · simp
  · intro name scope
    rcases scope with ⟨source, rfl⟩ | ⟨index, impossible, _⟩
    · exact inputFrame source
    · omega

end Noctium.Verification.ScalarWitnessConstruction
