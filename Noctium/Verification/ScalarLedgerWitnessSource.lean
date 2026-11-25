import Noctium.Verification.ScalarCellSourceReads
import Noctium.Verification.GenericStateAdmissionPrefix
import Noctium.Passes

namespace Noctium.Verification.ScalarLedgerWitnessSource

open Backend NativeRelation ScalarNormalization

private theorem bind_ok {first : Except ε α} {next : α → Except ε β} {result : β} :
    (first >>= next) = .ok result ↔ ∃ value, first = .ok value ∧ next value = .ok result := by
  cases first <;> simp [Bind.bind, Except.bind]

/-- A successful source call exposes the real circuit output, ledger
transition and return stages in order, using the production reset frame. -/
theorem entrypoint_run_steps (ctx : EvalContext) (entry : Entrypoint)
    (values result : EvalEnv) (initial next : LedgerState)
    (success : entry.run ctx values initial = .ok (result, next)) :
    ∃ outputs finalEnv returned,
      entry.circuit.run ctx values = .ok outputs ∧
      runEffectsWithGuardsAndEnv ctx entry.effects entry.effectGuards (outputs ++ values)
        {initial with unshieldedInputs := [], unshieldedOutputs := [], unshieldedSpendClaims := []} =
        .ok (finalEnv, next) ∧
      entry.evalReturns ctx finalEnv = .ok returned ∧ result = outputs ++ returned := by
  unfold Entrypoint.run at success
  cases checked : Disclosure.entrypoint entry with
  | error diagnostic => simp [checked, Bind.bind, Except.bind, throw] at success
  | ok accepted =>
    cases accepted
    rw [checked] at success
    change (entry.circuit.run ctx values >>= _) = _ at success
    obtain ⟨outputs, circuit, afterCircuit⟩ := bind_ok.mp success
    obtain ⟨⟨finalEnv, actualNext⟩, effects, afterEffects⟩ := bind_ok.mp afterCircuit
    obtain ⟨returned, returns, resultEq⟩ := bind_ok.mp afterEffects
    change Except.ok (outputs ++ returned, actualNext) = Except.ok (result, next) at resultEq
    cases resultEq
    exact ⟨outputs, finalEnv, returned, circuit, effects, returns, rfl⟩

/-- Record the real read values of a successful admitted scalar-cell call.
The post-public cutoff comes from the production public input fold, and
the lowered metadata matches the source record order. -/
theorem lowerEntrypoint_source_cell_read_tape (ctx : EvalContext)
    (state : List StateDecl) (entry : Entrypoint) (plan : Impact.Plan)
    (values result : EvalEnv) (initial next : LedgerState)
    (modulus : ctx.modulus = Field.modulus)
    (lowered : Impact.lower state (Passes.pruneEntrypoint entry) = .ok plan)
    (unguarded : entry.effectGuards = [])
    (cellScope : ScalarCellSourceReads.ScalarCellEffects state entry.effects)
    (operandScope : ∀ effect ∈ entry.effects, ScalarCellSourceReads.ScalarCellOperand effect)
    (success : entry.run ctx values initial = .ok (result, next)) :
    ∃ outputs finalEnv returned entries,
      entry.circuit.run ctx values = .ok outputs ∧
      entry.evalReturns ctx finalEnv = .ok returned ∧ result = outputs ++ returned ∧
      ScalarCellSourceReads.sourceReadInputs ctx entry.effects
        (Impact.publicInputReadCount entry.circuit.inputs)
        (outputs ++ values, {initial with unshieldedInputs := [], unshieldedOutputs := [], unshieldedSpendClaims := []}) =
        .ok (entries, (finalEnv, next)) ∧
      (plan.reads.drop (Impact.publicInputReadCount entry.circuit.inputs)).map
          GenericStateCheckedReadTrace.readMetadata =
        (entries.map Prod.fst).map GenericStateCheckedReadTrace.readMetadata ∧
      ∀ record ∈ entries, ScalarCellSourceReads.CanonicalReadRecord record := by
  let pruned := Passes.pruneEntrypoint entry
  obtain ⟨outputs, finalEnv, returned, circuit, effects, returns, resultEq⟩ :=
    entrypoint_run_steps ctx entry values result initial next success
  let reset := {initial with
    unshieldedInputs := []
    unshieldedOutputs := []
    unshieldedSpendClaims := []}
  obtain ⟨bounds, actual⟩ : ∃ bounds,
      Impact.lowerWithEffectBoundaries state pruned = .ok (plan, bounds) := by
    unfold Impact.lower at lowered
    change Prod.fst <$> Impact.lowerWithEffectBoundaries state pruned = .ok plan at lowered
    cases tracked : Impact.lowerWithEffectBoundaries state pruned with
    | error diagnostic => simp [tracked, Functor.map, Except.map] at lowered
    | ok pair =>
      obtain ⟨found, bounds⟩ := pair
      have eq : found = plan := by simpa [tracked, Functor.map, Except.map] using lowered
      subst found
      exact ⟨bounds, rfl⟩
  obtain ⟨inputPlan, entries, inputAccepted, tape, metadata, canonical⟩ :=
    ScalarCellSourceReads.lowerWithEffectBoundaries_source_cell_read_metadata
      ctx state pruned plan bounds (outputs ++ values, reset) (finalEnv, next)
      cellScope operandScope modulus actual unguarded effects
  have cutoff := GenericStateAdmissionPrefix.publicInputPlan_readCount
    pruned.circuit.inputs inputPlan inputAccepted
  change inputPlan.reads.length = Impact.publicInputReadCount entry.circuit.inputs at cutoff
  rw [cutoff] at tape metadata
  exact ⟨outputs, finalEnv, returned, entries, circuit, returns, resultEq, tape,
    by simpa only [GenericStateCheckedReadTrace.planReadMetadata, List.map_drop] using metadata,
    canonical⟩

end Noctium.Verification.ScalarLedgerWitnessSource
