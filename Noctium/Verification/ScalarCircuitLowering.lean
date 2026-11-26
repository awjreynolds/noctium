import Noctium.Verification.ScalarWitnessAssembly
import Noctium.Verification.ScalarWitnessAliases
import Noctium.Verification.ScalarWitnessCircuitInputs
import Noctium.Verification.ScalarWitnessCircuitConstraints
import Noctium.Verification.ScalarExpressionUIntAdd

namespace Noctium.Verification.ScalarCircuitLowering

open Lean Backend NativeRelation NativeRelationJson ScalarNormalization ScalarLowering

export ScalarWitnessConstruction (PrefixExtension InputFrame Completes emit_input scoped_operands
  emit_impact emit_output emit_assert completes_pure completes_emit_input completes_bind
  completes_forIn initial_aliases current_aliases constraints_members)

theorem constrain_type_complete (hash : Hash) (inputs witness : NativeRelation.Assignment)
    (state : Zkir.LowerState) (ty : Ty) (value : ty.Denote) (text : String)
    (term : Native.Term) (canonical : Canonical ty value)
    (termValue : interpret hash inputs term = sourceScalar? ty value)
    (meaning : LowerStateMeaning hash witness state)
    (operand : OperandMeaning hash inputs witness text term)
    (scope : TextScope state.next text)
    (budget : ((Zkir.constrainType ty text).run state).2.next ≤
      Native.maxInstructions * Native.maxVectorLength) :
    Nonempty (PrefixExtension hash witness state ((Zkir.constrainType ty text).run state).2) := by
  cases ty with
  | native =>
    exact ⟨ScalarWitnessConstruction.PrefixExtension.mk witness meaning rfl
      (by intro name _; rfl)⟩
  | bool =>
    obtain ⟨native, parsed, read⟩ := operand
    have termScalar : interpret hash inputs term =
        some (scalar (if value then 1 else 0)) := by
      simpa [sourceScalar?, sourceNumber?] using termValue
    have readValue : native.read witness = scalar (if value then 1 else 0) :=
      Option.some.inj (read.symm.trans termScalar)
    have boolean : native.read witness = zero ∨ native.read witness = one := by
      cases value with
      | false => exact Or.inl (by simpa [scalar_zero] using readValue)
      | true => exact Or.inr (by simpa [scalar_one] using readValue)
    obtain ⟨found, foundParsed, identifiers⟩ := scope
    rw [parsed] at foundParsed
    cases foundParsed
    refine ⟨ScalarWitnessConstruction.PrefixExtension.mk witness ?_ rfl
      (by intro name _; rfl)⟩
    change LowerStateMeaning hash witness {state with instructions := state.instructions.push _}
    exact LowerStateMeaning.append hash witness state meaning _ _
      (ScalarInstructionEncoding.decode_boolean_instruction parsed) boolean identifiers
  | uint maximum =>
    have range : ∃ value, interpret hash inputs term = some value ∧ value.val ≤ maximum := by
      refine ⟨scalar value, ?_, ?_⟩
      · simpa [sourceScalar?, sourceNumber?] using termValue
      · change value % Field.modulus ≤ maximum
        rw [Nat.mod_eq_of_lt canonical.1]
        exact canonical.2.2
    have operationRun :
        (do Zkir.constrainUnsigned maximum text; pure text).run state =
          (text, (Zkir.constrainUnsigned maximum text).run state |>.2) := by
      rfl
    have operationBudget :
        ((do Zkir.constrainUnsigned maximum text; pure text).run state).2.next ≤
          Native.maxInstructions * Native.maxVectorLength := by
      rw [operationRun]
      change ((Zkir.constrainUnsigned maximum text).run state).2.next ≤ _ at budget
      exact budget
    obtain ⟨step⟩ := ScalarWitnessConstruction.constrainUnsigned_step hash inputs witness
      state maximum text term meaning operand scope range canonical.2.1 operationBudget
    have stateEqual :
        ((Zkir.constrainType (.uint maximum) text).run state).2 = step.finalState := by
      change ((do Zkir.constrainUnsigned maximum text; pure text).run state).2 = step.finalState
      exact congrArg Prod.snd step.run
    exact ⟨ScalarWitnessConstruction.PrefixExtension.mk step.finalWitness
      (by rw [stateEqual]; exact step.stateMeaning)
      (by rw [stateEqual]; exact step.aliasesPreserved) step.frame⟩
  | bytes length => simp [Canonical, sourceNumber?] at canonical
  | opaqueBytes => simp [Canonical, sourceNumber?] at canonical
  | opaqueString => simp [Canonical, sourceNumber?] at canonical
  | jubjubScalar => simp [Canonical, sourceNumber?] at canonical
  | jubjubPoint => simp [Canonical, sourceNumber?] at canonical
  | foreign kind => simp [Canonical, sourceNumber?] at canonical

theorem completes_input_type (hash : Hash) (inputs : NativeRelation.Assignment)
    (input : Input) (value : input.ty.Denote) (canonical : Canonical input.ty value)
    (binding : inputs ("%input_" ++ input.name) =
      scalar (number (ScalarWitnessConstruction.scalarTypeOfCanonicalInput canonical) value))
    (valid : validIdentifier ("%input_" ++ input.name) = true)
    {aliasRequirement : List (String × String) → Prop} :
    Completes hash inputs (Zkir.constrainType input.ty ("%input_" ++ input.name))
      aliasRequirement := by
  exact ScalarWitnessConstruction.completes_scalar_constraint hash inputs input.name value
    (ScalarWitnessConstruction.scalarTypeOfCanonicalInput canonical) canonical binding valid

theorem completes_condition (ctx : EvalContext) (hash : Hash)
    (implementation : HashAgreement ctx hash)
    (complete : ∀ ty (expression : Expr ty), ExprComplete expression)
    (circuit : Circuit) (values : EvalEnv) (inputs : NativeRelation.Assignment)
    (admitted : CanonicalInputs circuit values inputs)
    (identifiers : ∀ input ∈ circuit.inputs,
      validIdentifier ("%input_" ++ input.name) = true)
    (condition : Expr .bool)
    (valid : condition.validate Capabilities.crypto
      (circuit.inputs.map (fun input => (input.name, input.ty))) = .ok ())
    (success : condition.eval ctx values = .ok true) :
    Completes hash inputs (do
      let text ← Zkir.lowerExpr condition
      Zkir.emit "assert" [("cond", toJson text)]) := by
  exact ScalarWitnessConstruction.completes_condition ctx hash implementation circuit values
    inputs admitted identifiers condition (complete _ condition) valid success

end Noctium.Verification.ScalarCircuitLowering
