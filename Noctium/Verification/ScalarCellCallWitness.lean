import Noctium.Verification.ScalarCellWitnessReadSeed
import Noctium.Verification.ScalarCellPlanEvaluation
import Noctium.Verification.ScalarLedgerWitnessBody
import Noctium.Verification.ScalarLedgerWitnessProjection
import Noctium.Verification.ScalarLedgerWitnessSource
import Noctium.Verification.ScalarLedgerSourceIdentifiers
import Noctium.Verification.ScalarLedgerScalarSchema

namespace Noctium.Verification.ScalarWitnessConstruction

open Lean Backend NativeRelation NativeRelationJson ScalarLowering ScalarNormalization
open ScalarAllocationOutputFrame ScalarLedgerWitnessPreflight
open ScalarValidationOpcodeProfile (checkedScalarOpcodeProfile)

/-- Seed the accepted program from a successful scalar-cell source call,
construct its witness, and bind the strict decoded body to the ordered public,
private and raw inputs. The compiled plan evaluates on the same source values. -/
theorem lowerEntrypoint_construct_scalar_cell_witness
    (ctx : EvalContext) (hash : Hash) (implementation : HashAgreement ctx hash)
    (declarations : List StateDecl) (entry : Entrypoint) (plan : Impact.Plan)
    (values result : EvalEnv) (initial next : LedgerState) (inputs : NativeRelation.Assignment)
    {json : Json} {call : ScalarCall}
    (lowered : Zkir.lowerEntrypoint declarations entry = .ok json)
    (decoded : decodeScalarCall json = .ok call)
    (planAccepted : Impact.lower declarations (Passes.pruneEntrypoint entry) = .ok plan)
    (profile : checkedScalarOpcodeProfile
      (defaultEntrypointRows entry plan).toList.zipIdx call.body.instructions = true)
    (admittedInputs : CanonicalInputs entry.circuit values inputs)
    (circuitAdmission : ScalarCircuitAdmission entry.circuit)
    (planAdmission : ScalarEntrypointPlanAdmission (Passes.pruneEntrypoint entry) plan)
    (unguarded : entry.effectGuards = [])
    (cellScope : ScalarCellSourceReads.ScalarCellEffects declarations entry.effects)
    (operandScope : ∀ effect ∈ entry.effects, ScalarCellSourceReads.ScalarCellOperand effect)
    (success : entry.run ctx values initial = .ok (result, next)) :
    ∃ expected outputs finalEnv entries witness,
      Native.expectedEntrypoint declarations (Passes.pruneEntrypoint entry) = .ok expected ∧
      entry.circuit.run ctx values = .ok outputs ∧
      ScalarCellSourceReads.sourceReadInputs ctx entry.effects
        (Impact.publicInputReadCount entry.circuit.inputs)
        (outputs ++ values, {initial with unshieldedInputs := [], unshieldedOutputs := [], unshieldedSpendClaims := []}) =
        .ok (entries, (finalEnv, next)) ∧
      let seed := ScalarCellWitnessReadSeed.seedReadValues inputs entries
      InputFrame seed witness ∧
      (∀ input ∈ entry.circuit.inputs, witness ("%input_" ++ input.name) = inputs ("%input_" ++ input.name)) ∧
      CircuitSatisfies hash call.body
        ⟨ScalarValidatedProgram.inputValues expected .public seed,
          ScalarValidatedProgram.inputValues expected .private seed⟩
        witness (call.body.groups witness) ∧
      call.arguments.map witness = expected.rawInputs.map (fun input => seed input.identifier) := by
  let ep := Passes.pruneEntrypoint entry
  obtain ⟨outputs, finalEnv, returned, entries, circuitSuccess, returnSuccess, _, tape, metadata, canonical⟩ :=
    ScalarLedgerWitnessSource.lowerEntrypoint_source_cell_read_tape ctx declarations entry plan
      values result initial next implementation.modulus planAccepted unguarded cellScope operandScope success
  let seed := ScalarCellWitnessReadSeed.seedReadValues inputs entries
  obtain ⟨preserved, facts⟩ := ScalarCellWitnessReadSeed.seed_source_cell_read_assignment_from_tape
    declarations ctx inputs entry plan entries _ _ cellScope planAccepted metadata canonical tape
  obtain ⟨_, fresh⟩ := ScalarCellWitnessReadSeed.lower_source_cell_read_names declarations entry plan
    entries _ _ ctx cellScope planAccepted metadata tape
  let reads := plan.reads.drop (Impact.publicInputReadCount ep.circuit.inputs)
  obtain ⟨activity, readScope⟩ :=
    ScalarCellPlanScope.lower_scope declarations ep plan planAccepted unguarded cellScope
  have readsPlain : ∀ read ∈ reads, PlainScalarLedgerRead read :=
    fun read member => (readScope read member).1
  have scalarInputs : ∀ input ∈ ep.circuit.inputs, Nonempty (ScalarType input.ty) := by
    intro input member
    obtain ⟨_, _, canonical⟩ := admittedInputs.complete input member
    exact ⟨scalarTypeOfCanonicalInput canonical⟩
  have scalarReadBindings : ∀ read ∈ reads, ∀ name ty,
      (name, ty) ∈ read.bindings → Nonempty (ScalarType ty) := by
    intro read member name ty binding
    obtain ⟨_, support, _, _⟩ := facts read member
    rw [PlainScalarLedgerRead.bindings read (readsPlain read member) support] at binding
    obtain ⟨_, equalType⟩ := Prod.mk.inj (List.mem_singleton.mp binding)
    subst ty
    exact ⟨support⟩
  obtain ⟨expected, expectedAccepted, _, _, rows, header, descriptors, identifiers, capacity,
    _instructionBudget⟩ :=
    lowerEntrypoint_witness_preflight declarations entry plan lowered decoded planAccepted profile
      (fun expected accepted => ScalarLedgerScalarSchema.accepted_nonforeign_input_schema
        declarations ep plan expected planAccepted accepted scalarInputs scalarReadBindings)
      circuitAdmission planAdmission
  obtain ⟨readValues, readSuccess, readValuesFacts⟩ := decode_seeded_scalar_reads reads seed facts
  have planEvaluation := lower_cell_plan_evaluation ctx declarations entry plan
    values outputs returned readValues inputs _ _ entries rfl planAccepted unguarded
    cellScope operandScope admittedInputs circuitSuccess returnSuccess implementation.modulus
    tape metadata canonical readSuccess
  have epInputs : CanonicalInputs ep.circuit values seed := by
    refine ⟨admittedInputs.unique, admittedInputs.declared, admittedInputs.complete, ?_⟩
    intro input member value found canonical
    exact (preserved input member).trans (admittedInputs.binding input member value found canonical)
  obtain ⟨inputIdentifiers, readIdentifiers⟩ :=
    ScalarLedgerSourceIdentifiers.accepted_source_identifiers declarations ep plan expected
      planAccepted expectedAccepted identifiers
  have validInputs : ∀ input ∈ ep.circuit.inputs,
      validIdentifier ("%input_" ++ input.name) = true := by
    intro input member
    obtain ⟨_, _, canonical⟩ := epInputs.complete input member
    exact inputIdentifiers input member (scalarTypeOfCanonicalInput canonical)
  have validReads : ∀ read ∈ reads, validIdentifier ("%input_" ++ read.name) = true := by
    intro read member
    obtain ⟨_, scalarType, _, _⟩ := facts read member
    exact readIdentifiers read member (readsPlain read member).1 (readsPlain read member).2 scalarType
  obtain ⟨expectedPlan, outputFrame, _, _, _, _, _, _, _, _, _, samePlan, normalized, _⟩ :=
    GenericStateCircuitParts.expectedEntrypoint_parts declarations ep expected expectedAccepted
  have exactPlan := Except.ok.inj (samePlan.symm.trans planAccepted)
  subst expectedPlan
  have readAliases := ScalarEntrypointSeedFrame.normalized_read_lookup ep plan outputFrame values seed epInputs
    normalized (fun read member => by
      obtain ⟨_, type, _, _⟩ := facts read member
      exact PlainScalarLedgerRead.bindings read (readsPlain read member) type)
    (fun read member => by
      simpa only [GenericStateEffectValidation.initialEffectTypeEnv, List.map_append, List.map_map,
        Function.comp_def] using fresh read member)
  have readFacts : ∀ pair ∈ readValues,
      outputFrame.1.lookup pair.1 = some (.input ("%input_" ++ pair.1)) ∧
      pair.1 ∉ ep.circuit.outputs.map Output.name ∧ validIdentifier ("%input_" ++ pair.1) = true ∧
      ∃ (ty : Ty) (value : ty.Denote), pair.2 = Value.pack ty value ∧
        Canonical ty value ∧ sourceScalar? ty value = some (seed ("%input_" ++ pair.1)) := by
    intro pair member
    obtain ⟨read, present, value, rfl, canonical, field⟩ := readValuesFacts pair member
    refine ⟨readAliases read present, ?_, validReads read present, read.ty, value, rfl, canonical, field⟩
    intro outputMember
    apply fresh read present
    simp only [GenericStateEffectValidation.initialEffectTypeEnv, List.map_append, List.map_map,
      Function.comp_def]
    exact List.mem_append_right _ outputMember
  have prunedSuccess : ep.circuit.run ctx values = .ok outputs := by
    simpa only [ep, Passes.pruneEntrypoint, Passes.pruneCircuit_run] using circuitSuccess
  obtain ⟨witness, frame, meaning⟩ := completes_scalar_ledger_body ctx hash implementation declarations ep
    plan values outputs readValues seed outputFrame planAccepted epInputs
    (circuitAdmission.pruneCircuit entry.circuit) planAdmission prunedSuccess normalized validInputs
    readFacts readsPlain facts validReads planEvaluation.guards activity planEvaluation.operationFields
    planEvaluation.returnsValid ⟨returned, planEvaluation.returns⟩ capacity
  have inputAgreement (requirement : Native.InputRequirement)
      (member : requirement ∈ expected.rawInputs ++ expected.inputs) :
      witness requirement.identifier = seed requirement.identifier := by
    obtain ⟨name, equal⟩ :=
      ScalarLedgerSourceIdentifiers.accepted_scalar_requirement_source_names
        declarations ep plan expected planAccepted expectedAccepted
        scalarInputs requirement member
    rw [equal]
    exact frame name
  obtain ⟨satisfies, arguments⟩ := ScalarLedgerWitnessProjection.call_satisfies_seeded_inputs
    entry plan hash seed witness expected call rows header descriptors inputAgreement meaning
  exact ⟨expected, outputs, finalEnv, entries, witness, expectedAccepted, circuitSuccess, tape, frame,
    fun input member => (frame input.name).trans (preserved input member), satisfies, arguments⟩

end Noctium.Verification.ScalarWitnessConstruction
