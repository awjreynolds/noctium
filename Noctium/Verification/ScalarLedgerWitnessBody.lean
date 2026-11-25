import Noctium.Verification.ScalarLedgerWitnessComposition
import Noctium.Verification.ScalarLedgerPlanValidation
import Noctium.Verification.ScalarLedgerWitnessReadValues
import Noctium.Verification.ScalarWitnessEntrypointPrelude
import Noctium.Verification.ScalarWitnessEntrypointAliases
import Noctium.Verification.GenericStateCaps
import Noctium.Verification.GenericStateEffectValidation

namespace Noctium.Verification.ScalarWitnessConstruction

open Lean Backend NativeRelation NativeRelationJson ScalarLowering ScalarNormalization
open ScalarAllocationOutputFrame

/-- Construct a witness for the complete production scalar entrypoint body
from its circuit run and evaluated ledger plan. The seed supplies raw
arguments and transcript values and stays fixed through every stage. -/
theorem completes_scalar_ledger_body (ctx : EvalContext) (hash : Hash)
    (implementation : HashAgreement ctx hash)
    (declarations : List StateDecl) (entry : Entrypoint) (plan : Impact.Plan)
    (values outputs readValues : EvalEnv) (inputs : NativeRelation.Assignment)
    (outputFrame : GenericStateCircuitParts.OutputFrame)
    (planAccepted : Impact.lower declarations entry = .ok plan)
    (admittedInputs : CanonicalInputs entry.circuit values inputs)
    (circuitAdmission : ScalarCircuitAdmission entry.circuit)
    (planAdmission : ScalarEntrypointPlanAdmission entry plan)
    (success : entry.circuit.run ctx values = .ok outputs)
    (normalized : GenericStateCircuitParts.normalizeOutputs
      (GenericStateCircuitParts.entrypointSeedAliases entry plan)
      entry.circuit.outputs = .ok outputFrame)
    (inputIdentifiers : ∀ input ∈ entry.circuit.inputs,
      validIdentifier ("%input_" ++ input.name) = true)
    (readAliases : ∀ pair ∈ readValues,
      outputFrame.1.lookup pair.1 = some (.input ("%input_" ++ pair.1)) ∧
      pair.1 ∉ entry.circuit.outputs.map Output.name ∧
      validIdentifier ("%input_" ++ pair.1) = true ∧
      ∃ (ty : Ty) (value : ty.Denote), pair.2 = Value.pack ty value ∧
        Canonical ty value ∧ sourceScalar? ty value = some (inputs ("%input_" ++ pair.1)))
    (readsPlain : ∀ read ∈ plan.reads.drop (Impact.publicInputReadCount entry.circuit.inputs),
      PlainScalarLedgerRead read)
    (readsSeeded : ∀ read ∈ plan.reads.drop (Impact.publicInputReadCount entry.circuit.inputs),
      ∃ (value : read.ty.Denote) (scalarType : ScalarType read.ty),
        Canonical read.ty value ∧
        inputs ("%input_" ++ read.name) = scalar (number scalarType value))
    (readIdentifiers : ∀ read ∈ plan.reads.drop (Impact.publicInputReadCount entry.circuit.inputs),
      validIdentifier ("%input_" ++ read.name) = true)
    (guardsTrue : ∀ guard ∈ plan.guards,
      guard.eval ctx ((outputs ++ values) ++ readValues) = .ok true)
    (activity : plan.activityGuards.all Option.isNone = true)
    (fieldsEvaluated : ∀ operation ∈ plan.operations, ∀ fields ∈ operation.fieldGroups,
      ∀ field ∈ fields, ∃ value, field.eval ctx ((outputs ++ values) ++ readValues) = .ok value)
    (returnsValid : ∀ output ∈ entry.returns,
      output.value.validate Capabilities.crypto (plan.typeEnvironment entry) = .ok ())
    (returnsEvaluated : ∃ result,
      entry.returns.mapM (evalOutput ctx ((outputs ++ values) ++ readValues)) = .ok result)
    (capacity : ((Zkir.lowerEntrypointBody entry plan).run {}).2.next ≤
      Native.maxInstructions * Native.maxVectorLength) :
    ∃ witness, InputFrame inputs witness ∧
      LowerStateMeaning hash witness ((Zkir.lowerEntrypointBody entry plan).run {}).2 := by
  let initial : Zkir.LowerState := {}
  let prelude : StateM Zkir.LowerState Unit := do
    Zkir.lowerEntrypointInputs entry
    Zkir.lowerConstraints entry.circuit.constraints
  let afterPrelude := (prelude.run initial).2
  let afterAliases := ((Zkir.lowerEntrypointAliases entry).run afterPrelude).2
  let suffix : StateM Zkir.LowerState Unit := do
    Zkir.lowerLedgerReads entry plan
    Zkir.lowerConstraints plan.guards
    Zkir.lowerLedgerOperations plan
    let returned ← Zkir.lowerReturnFields entry.returns
    Zkir.emit "output" [("vals", toJson returned)]
  have finalBudget : (suffix.run afterAliases).2.next ≤
      Native.maxInstructions * Native.maxVectorLength := capacity
  have frames := scalarEntrypointStageFrames entry plan circuitAdmission planAdmission
  have suffixFrame : Zkir.PreservesOutputCapacityFrame suffix := by
    apply Zkir.bind_preservesOutputCapacityFrame _ _ frames.reads
    intro _
    apply Zkir.bind_preservesOutputCapacityFrame _ _ frames.guards
    intro _
    exact Zkir.bind_preservesOutputCapacityFrame _ _ frames.operations (fun _ => frames.returns)
  have aliasBudget := Nat.le_trans (suffixFrame afterAliases).next finalBudget
  have preludeBudget := Nat.le_trans (frames.aliases afterPrelude).next aliasBudget
  have checkedSource := GenericStateEffectValidation.lower_circuit_validated_source
    declarations entry plan planAccepted
  have checkedCircuit : entry.circuit.validate Capabilities.crypto = .ok () := by
    rwa [GenericStateCaps.circuit_validate_source_crypto] at checkedSource
  obtain ⟨uniqueOutputs, unshadowed⟩ :=
    GenericStateAliases.validated_output_scope Capabilities.crypto entry.circuit checkedCircuit
  have unused := GenericStateAliases.canonicalInputs_output_unused_of_scope entry.circuit
    values inputs admittedInputs unshadowed
  obtain ⟨prefixExtension⟩ := completes_entrypoint_prelude ctx hash implementation entry values outputs
    inputs admittedInputs circuitAdmission inputIdentifiers checkedCircuit success inputs initial
    (empty_state hash inputs) (fun _ => rfl) rfl preludeBudget
  have prefixInputs : InputFrame inputs prefixExtension.witness := fun name =>
    prefixExtension.frame _ (Or.inl ⟨name, rfl⟩)
  have installedNone : afterPrelude.aliases = [] := prefixExtension.aliases
  have prefixAliases := entrypoint_seed_lowerAliasAgreement hash inputs prefixExtension.witness
    entry plan values afterPrelude admittedInputs inputIdentifiers prefixInputs installedNone
  obtain ⟨aliasWitness, aliasMeaning, aliasFrame, _, _, sourceAgreement, aliasAgreement, absent⟩ :=
    lowerEntrypointAliases_complete ctx hash implementation entry plan values outputs inputs
      prefixExtension.witness afterPrelude outputFrame admittedInputs circuitAdmission
      _ (circuit_validation_parts entry.circuit checkedCircuit).2 uniqueOutputs unused
      (circuit_run_steps ctx entry.circuit values outputs success).2 normalized
      prefixAliases prefixExtension.meaning aliasBudget
  have aliasInputs : InputFrame inputs aliasWitness := fun name =>
    (aliasFrame _ (Or.inl ⟨name, rfl⟩)).trans (prefixInputs name)
  have suffixReadAliases : ∀ pair ∈ readValues,
      outputFrame.1.lookup pair.1 = some (.input ("%input_" ++ pair.1)) ∧
      afterAliases.aliases.lookup pair.1 = none ∧ validIdentifier ("%input_" ++ pair.1) = true := by
    intro pair member
    obtain ⟨normal, fresh, identifier, _⟩ := readAliases pair member
    refine ⟨normal, ?_, identifier⟩
    exact absent pair.1 fresh (by simp [installedNone])
  have sourceWithReads := AliasAgreement.appendCanonicalReadValues hash inputs outputFrame.1
    (outputs ++ values) readValues sourceAgreement (by
      intro pair member
      obtain ⟨term, _, _, ty, value, packed, canonical, field⟩ := readAliases pair member
      exact ⟨ty, value, packed, canonical, term, field⟩)
  obtain ⟨completed⟩ := completes_scalar_ledger_suffix ctx hash implementation inputs entry plan
    outputFrame.1 (outputs ++ values) readValues aliasWitness afterAliases aliasMeaning aliasInputs
    aliasAgreement sourceWithReads planAdmission frames suffixReadAliases readsPlain readsSeeded readIdentifiers
    (lower_plan_guard_members_validated declarations entry plan planAccepted) guardsTrue activity
    (lower_operation_group_members_validated declarations entry plan planAccepted) fieldsEvaluated
    returnsValid returnsEvaluated finalBudget
  exact ⟨completed.witness,
    fun name => (completed.frame _ (Or.inl ⟨name, rfl⟩)).trans (aliasInputs name), completed.meaning⟩

end Noctium.Verification.ScalarWitnessConstruction
