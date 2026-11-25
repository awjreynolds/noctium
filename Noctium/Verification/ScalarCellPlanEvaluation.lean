import Noctium.Verification.ScalarCellEffectEvaluation
import Noctium.Verification.ScalarCellPlanScope
import Noctium.Verification.ScalarCellPublicFields
import Noctium.Verification.ScalarCellReturnValidation
import Noctium.Verification.ScalarLedgerSourceReturns

namespace Noctium.Verification.ScalarWitnessConstruction

open Backend NativeRelation ScalarNormalization
open GenericStateEffectValidation ScalarCellSourceReads

/-- Evaluation of exact lowered ledger expressions under the values from
the source circuit and source read tape. -/
structure ScalarLedgerPlanEvaluation (ctx : EvalContext) (entry : Entrypoint)
    (plan : Impact.Plan) (values returned : EvalEnv) : Prop where
  guards : ∀ guard ∈ plan.guards, guard.eval ctx values = .ok true
  operationFields : ∀ operation ∈ plan.operations, ∀ fields ∈ operation.fieldGroups,
    ∀ field ∈ fields, ∃ value, field.eval ctx values = .ok value
  returnsValid : ∀ output ∈ entry.returns,
    output.value.validate Capabilities.crypto (plan.typeEnvironment entry) = .ok ()
  returns : entry.returns.mapM (evalOutput ctx values) = .ok returned

/-- Successful source execution supplies evaluation of the actual compiled
plan. Operation chunks use the admitted source scope at their own step.
Returns use the same decoded read bindings as the emitted circuit body. -/
theorem lower_cell_plan_evaluation (ctx : EvalContext) (state : List StateDecl)
    (entry : Entrypoint) (plan : Impact.Plan) (values outputs returned readValues : EvalEnv)
    (inputs : Assignment) (before after : Frame) (entries : List (Impact.Read × Scalar))
    (baseShape : before.1 = outputs ++ values)
    (accepted : Impact.lower state (Passes.pruneEntrypoint entry) = .ok plan)
    (unguarded : entry.effectGuards = [])
    (admission : ScalarCellEffects state entry.effects)
    (operands : ∀ effect ∈ entry.effects, ScalarCellOperand effect)
    (inputAdmission : CanonicalInputs entry.circuit values inputs)
    (circuit : entry.circuit.run ctx values = .ok outputs)
    (returns : entry.evalReturns ctx after.1 = .ok returned)
    (modulus : ctx.modulus = Field.modulus)
    (source : sourceReadInputs ctx entry.effects
      (Impact.publicInputReadCount entry.circuit.inputs) before = .ok (entries, after))
    (metadata : (plan.reads.drop (Impact.publicInputReadCount entry.circuit.inputs)).map
        GenericStateCheckedReadTrace.readMetadata =
      (entries.map Prod.fst).map GenericStateCheckedReadTrace.readMetadata)
    (canonical : ∀ record ∈ entries, CanonicalReadRecord record)
    (decoded : GenericStateInputValues.decodeReads
      (plan.reads.drop (Impact.publicInputReadCount entry.circuit.inputs))
      (ScalarCellWitnessReadSeed.seedReadValues inputs entries) = .ok readValues) :
    ScalarLedgerPlanEvaluation ctx (Passes.pruneEntrypoint entry) plan
      ((outputs ++ values) ++ readValues) returned := by
  let ep := Passes.pruneEntrypoint entry
  let complete := (outputs ++ values) ++ readValues
  have compatible : ∀ input ∈ entry.circuit.inputs, Impact.publicInputScalarCompatible input := by
    intro input member
    obtain ⟨_, _, canonical⟩ := inputAdmission.complete input member
    have support := scalarTypeOfCanonicalInput canonical
    cases input with
    | mk name ty visibility span =>
      cases support with
      | native => exact Or.inr (Or.inl rfl)
      | bool => exact Or.inr (Or.inr (Or.inl rfl))
      | uint maximum => exact Or.inr (Or.inr (Or.inr ⟨maximum, rfl⟩))
  have noGuards := ScalarCellPlanScope.lower_guards_empty state ep plan
    accepted unguarded compatible admission
  obtain ⟨fieldEvaluation, finalTypes, validated, finalAgrees⟩ :=
    ScalarCellEffectEvaluation.lower_cell_fields_fold ctx state entry plan values outputs readValues
      inputs before after entries baseShape accepted unguarded admission operands inputAdmission
      circuit modulus source metadata canonical decoded
      (fun inputPlan prefixAccepted lookup =>
        ScalarCellPublicFields.publicInputPlan_group_fields_eval entry inputPlan ctx values complete
          inputs inputAdmission compatible prefixAccepted lookup modulus)
  have typesEq := ScalarCellReturnValidation.lower_cell_final_types state ep plan
    accepted unguarded admission finalTypes validated
  have validReturns := ScalarCellReturnValidation.lower_cell_returns_valid state ep plan
    accepted unguarded admission finalTypes validated
  have returnEvaluation := ScalarLedgerSourceReturns.evalReturns_transport ctx ep after.1 complete
    (plan.typeEnvironment ep) returned (by simpa only [typesEq] using finalAgrees)
    validReturns (by exact returns)
  exact ⟨by simp [noGuards], fieldEvaluation, validReturns, returnEvaluation⟩

end Noctium.Verification.ScalarWitnessConstruction
