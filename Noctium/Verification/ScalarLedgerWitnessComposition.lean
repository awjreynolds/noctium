import Noctium.Verification.ScalarWitnessLedgerReads
import Noctium.Verification.ScalarWitnessLedgerOperations
import Noctium.Verification.ScalarWitnessPlanGuards
import Noctium.Verification.ScalarWitnessReturns

namespace Noctium.Verification.ScalarWitnessConstruction

open Lean Backend NativeRelation NativeRelationJson ScalarLowering ScalarNormalization
open ScalarAllocationOutputFrame

/-- Follow the exact production state transitions after the circuit aliases
are installed. The source-seeded read values feed both the emitted reads
and the symbolic guard, operation and return expressions. -/
theorem completes_scalar_ledger_suffix (ctx : EvalContext) (hash : Hash)
    (implementation : HashAgreement ctx hash) (inputs : Assignment)
    (entry : Entrypoint) (plan : Impact.Plan)
    (normalAliases : Native.AliasEnvironment) (baseValues readValues : EvalEnv)
    (witness : Assignment) (state : Zkir.LowerState)
    (meaning : LowerStateMeaning hash witness state) (inputFrame : InputFrame inputs witness)
    (baseAliases : LowerAliasAgreement hash inputs witness normalAliases state.aliases baseValues)
    (sourceAliases : AliasAgreement hash inputs normalAliases (baseValues ++ readValues))
    (admission : ScalarEntrypointPlanAdmission entry plan)
    (frames : ScalarEntrypointStageFrames entry plan)
    (readAliases : ∀ pair ∈ readValues,
      normalAliases.lookup pair.1 = some (.input ("%input_" ++ pair.1)) ∧
      state.aliases.lookup pair.1 = none ∧ validIdentifier ("%input_" ++ pair.1) = true)
    (readsPlain : ∀ read ∈ plan.reads.drop (Impact.publicInputReadCount entry.circuit.inputs),
      PlainScalarLedgerRead read)
    (readsSeeded : ∀ read ∈ plan.reads.drop (Impact.publicInputReadCount entry.circuit.inputs),
      ∃ (value : read.ty.Denote) (scalarType : ScalarType read.ty),
        Canonical read.ty value ∧
        inputs ("%input_" ++ read.name) = scalar (number scalarType value))
    (readIdentifiers : ∀ read ∈ plan.reads.drop (Impact.publicInputReadCount entry.circuit.inputs),
      validIdentifier ("%input_" ++ read.name) = true)
    (guardsValid : ∀ guard ∈ plan.guards,
      guard.validate Capabilities.crypto (plan.typeEnvironment entry) = .ok ())
    (guardsTrue : ∀ guard ∈ plan.guards, guard.eval ctx (baseValues ++ readValues) = .ok true)
    (activity : plan.activityGuards.all Option.isNone = true)
    (fieldsValid : ∀ operation ∈ plan.operations, ∀ fields ∈ operation.fieldGroups,
      ∀ field ∈ fields, field.validate Capabilities.crypto (plan.typeEnvironment entry) = .ok ())
    (fieldsEvaluated : ∀ operation ∈ plan.operations, ∀ fields ∈ operation.fieldGroups,
      ∀ field ∈ fields, ∃ value, field.eval ctx (baseValues ++ readValues) = .ok value)
    (returnsValid : ∀ output ∈ entry.returns,
      output.value.validate Capabilities.crypto (plan.typeEnvironment entry) = .ok ())
    (returnsEvaluated : ∃ result,
      entry.returns.mapM (evalOutput ctx (baseValues ++ readValues)) = .ok result) :
    let suffix : StateM Zkir.LowerState Unit := do
      Zkir.lowerLedgerReads entry plan
      Zkir.lowerConstraints plan.guards
      Zkir.lowerLedgerOperations plan
      let returned ← Zkir.lowerReturnFields entry.returns
      Zkir.emit "output" [("vals", toJson returned)]
    (suffix.run state).2.next ≤ Native.maxInstructions * Native.maxVectorLength →
      Nonempty (PrefixExtension hash witness state (suffix.run state).2) := by
  intro suffix finalBudget
  let afterReads := ((Zkir.lowerLedgerReads entry plan).run state).2
  let afterGuards := ((Zkir.lowerConstraints plan.guards).run afterReads).2
  let afterOperations := ((Zkir.lowerLedgerOperations plan).run afterGuards).2
  let returnStage : StateM Zkir.LowerState Unit := do
    let returned ← Zkir.lowerReturnFields entry.returns
    Zkir.emit "output" [("vals", toJson returned)]
  have returnBudget : (returnStage.run afterOperations).2.next ≤
      Native.maxInstructions * Native.maxVectorLength := finalBudget
  have opsBudget := Nat.le_trans (frames.returns afterOperations).next returnBudget
  have guardsBudget := Nat.le_trans (frames.operations afterGuards).next opsBudget
  have readsBudget := Nat.le_trans (frames.guards afterReads).next guardsBudget
  obtain ⟨reads⟩ := completes_lowerLedgerReads_plain hash inputs entry plan
    readsPlain readsSeeded readIdentifiers witness state meaning inputFrame trivial readsBudget
  have inputFrameAfterReads : InputFrame inputs reads.witness := fun name =>
    (reads.frame _ (Or.inl ⟨name, rfl⟩)).trans (inputFrame name)
  have oldAliases := LowerAliasAgreement.of_frame hash inputs witness reads.witness state.next
    normalAliases state.aliases baseValues baseAliases meaning.aliases reads.frame
  have readAgreement : LowerAliasAgreement hash inputs reads.witness normalAliases afterReads.aliases
      (baseValues ++ readValues) := by
    rw [reads.aliases]
    exact LowerAliasAgreement.appendReadValues hash inputs reads.witness normalAliases state.aliases
      baseValues readValues oldAliases readAliases inputFrameAfterReads
  obtain ⟨guards, guardAgreement⟩ := completes_plan_guards ctx hash implementation inputs
    reads.witness afterReads normalAliases (baseValues ++ readValues) (plan.typeEnvironment entry)
    plan sourceAliases readAgreement reads.meaning admission.planGuards guardsValid guardsTrue guardsBudget
  have fieldsAdmitted : ∀ operation ∈ plan.operations, ∀ fields ∈ operation.fieldGroups,
      ∀ field ∈ fields, ScalarExpression field := by
    intro operation member fields group field fieldMember
    have found : operation ∈ plan.operations.zipIdx.map Prod.fst := by
      simpa only [List.zipIdx_map_fst] using member
    obtain ⟨indexed, indexedMember, eq⟩ := List.mem_map.mp found
    subst operation
    exact admission.operationFields indexed indexedMember fields group field fieldMember
  obtain ⟨ops, opAgreement⟩ := lowerLedgerOperations_complete_unGuarded ctx hash implementation inputs
    normalAliases (baseValues ++ readValues) entry plan sourceAliases guards.witness afterGuards
    guards.meaning guardAgreement activity fieldsAdmitted fieldsValid fieldsEvaluated opsBudget
  obtain ⟨returns⟩ := completes_entrypoint_returns ctx hash implementation entry (baseValues ++ readValues)
    inputs (plan.typeEnvironment entry) normalAliases admission.returns returnsValid returnsEvaluated
    ops.witness afterOperations ops.meaning sourceAliases opAgreement returnBudget
  refine ⟨{
    witness := returns.witness
    meaning := returns.meaning
    aliases := returns.aliases.trans (ops.aliases.trans (guards.aliases.trans reads.aliases))
    frame := ?_
  }⟩
  intro name present
  have atReads := InScope.mono (frames.reads state).next present
  have atGuards := InScope.mono (frames.guards afterReads).next atReads
  have atOps := InScope.mono (frames.operations afterGuards).next atGuards
  exact (returns.frame name atOps).trans
    ((ops.frame name atGuards).trans ((guards.frame name atReads).trans (reads.frame name present)))

end Noctium.Verification.ScalarWitnessConstruction
