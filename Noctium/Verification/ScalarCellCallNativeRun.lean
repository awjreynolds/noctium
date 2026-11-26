import Noctium.Verification.ScalarCellNativeTrace
import Noctium.Verification.ScalarCellNativePublicPrefix
import Noctium.Verification.ScalarCellCallWitness
import Noctium.Verification.ScalarCellPlanAdmission

namespace Noctium.Verification.ScalarCellNativeTrace

open Lean Backend NativeRelation NativeRelationJson ScalarNormalization NativeState
open ScalarLowering ScalarWitnessConstruction ScalarLedgerWitnessPreflight
open ScalarAllocationOutputFrame
open GenericStateCellAdmission GenericStateEffectValidation GenericStatePrefixEnvironment
open ScalarCellEffectEvaluation ScalarCellSourceReads

/-- A successful admitted source call constructs an execution of the exact
lowered plan in the scalar VM model, with the encoded successor and ordered
public input and read cells from the same call. -/
theorem lowerEntrypoint_run_scalar_cell_native (ctx : EvalContext)
    (declarations : List StateDecl) (entry : Entrypoint) (plan : Impact.Plan)
    (values result : EvalEnv) (initial next : LedgerState) (inputs : NativeRelation.Assignment)
    (initialSlots : List Slot)
    (accepted : Impact.lower declarations (Passes.pruneEntrypoint entry) = .ok plan)
    (inputAdmission : CanonicalInputs entry.circuit values inputs)
    (unguarded : entry.effectGuards = [])
    (cellScope : ScalarCellEffects declarations entry.effects)
    (operandScope : ∀ effect ∈ entry.effects, ScalarCellOperand effect)
    (modulus : ctx.modulus = Field.modulus)
    (admittedState : GenericStateEncoding.AdmittedState declarations initial initialSlots)
    (success : entry.run ctx values initial = .ok (result, next)) :
    ∃ outputs finalEnv returned entries readValues native finalSlots,
      entry.circuit.run ctx values = .ok outputs ∧
      entry.evalReturns ctx finalEnv = .ok returned ∧ result = outputs ++ returned ∧
      sourceReadInputs ctx entry.effects
        (Impact.publicInputReadCount entry.circuit.inputs)
        (outputs ++ values, {initial with unshieldedInputs := [], unshieldedOutputs := [], unshieldedSpendClaims := []}) =
        .ok (entries, (finalEnv, next)) ∧
      GenericStateInputValues.decodeReads
        (plan.reads.drop (Impact.publicInputReadCount entry.circuit.inputs))
        (ScalarCellWitnessReadSeed.seedReadValues inputs entries) = .ok readValues ∧
      GenericStateOps.evalPlan ctx ((outputs ++ values) ++ readValues) plan = .ok native ∧
      GenericStateEncoding.encodeState declarations next = some finalSlots ∧
      NativeState.run native (GenericStateEncoding.initial initialSlots) =
        some ⟨[.vector finalSlots], ScalarCellNativePublicPrefix.sourcePublicCells entry.circuit.inputs inputs ++ tapeCells entries⟩ := by
  let ep := Passes.pruneEntrypoint entry
  obtain ⟨outputs, finalEnv, returned, entries, sourceCircuit, sourceReturn, outputShape,
    tape, metadata, canonical⟩ :=
    ScalarLedgerWitnessSource.lowerEntrypoint_source_cell_read_tape ctx declarations entry plan
      values result initial next modulus accepted unguarded cellScope operandScope success
  let reset : LedgerState := {initial with
    unshieldedInputs := []
    unshieldedOutputs := []
    unshieldedSpendClaims := []}
  let before : Frame := (outputs ++ values, reset)
  let after : Frame := (finalEnv, next)
  obtain ⟨distinct, _⟩ := ScalarCellWitnessReadSeed.lower_source_cell_read_names declarations entry
    plan entries before after ctx cellScope accepted metadata tape
  obtain ⟨readValues, decodedReads, _, _⟩ := ScalarCellReadDecoding.decode_seeded_source_cell_reads
    (plan.reads.drop (Impact.publicInputReadCount entry.circuit.inputs)) inputs entries metadata canonical distinct
  let complete := (outputs ++ values) ++ readValues
  let publicCells := ScalarCellNativePublicPrefix.sourcePublicCells entry.circuit.inputs inputs
  obtain ⟨offsets, inputPlan, finalTypes, inputAccepted, trace, validated,
    baseAgreement, inputLookups, candidates⟩ :=
    lower_cell_evaluation_scope ctx declarations entry plan values outputs readValues
      inputs before after entries rfl accepted unguarded cellScope inputAdmission sourceCircuit
      tape metadata canonical decodedReads
  have compatible := ScalarCellPublicFields.canonical_inputs_scalar_compatible
    entry.circuit values inputs inputAdmission
  obtain ⟨nativePrefix, _, _, prefixEvaluated, _, _, _, prefixRun⟩ :=
    ScalarCellNativePublicPrefix.run_public_prefix_from_candidate entry inputPlan ctx
      values complete inputs [.vector initialSlots] [] inputAdmission compatible
      inputAccepted inputLookups modulus
  have resetEncoded : GenericStateEncoding.encodeState declarations before.2 = some initialSlots := by
    change GenericStateEncoding.encodeState declarations reset = some initialSlots
    rw [show GenericStateEncoding.encodeState declarations reset =
      GenericStateEncoding.encodeState declarations initial by
        unfold GenericStateEncoding.encodeState
        congr 1]
    exact admittedState.encoded
  obtain ⟨native, finalSlots, evaluated, encoded, nativeRun, _⟩ :=
    cell_trace_run ctx declarations entry.effects 0 (Impact.publicInputReadCount entry.circuit.inputs)
      inputPlan plan offsets (initialEffectTypeEnv ep) finalTypes before after entries complete
      (GenericStateEncoding.initial initialSlots) initialSlots publicCells [] nativePrefix
      cellScope operandScope trace validated tape candidates baseAgreement resetEncoded
      admittedState.distinctDeclarations admittedState.slotBound modulus
      prefixEvaluated (by simpa [GenericStateEncoding.initial] using prefixRun)
  exact ⟨outputs, finalEnv, returned, entries, readValues, native, finalSlots,
    sourceCircuit, sourceReturn, outputShape, tape, decodedReads, evaluated, encoded,
    by simpa [publicCells] using nativeRun⟩

/-- The same successful source call supplies both the decoded ZKIR witness
and the exact evaluated Impact plan. The typed ledger-read candidates are
decoded from that witness, whose input frame preserves the source tape. -/
theorem lowerEntrypoint_construct_scalar_cell_execution
    (ctx : EvalContext) (hash : Hash) (implementation : HashAgreement ctx hash)
    (declarations : List StateDecl) (entry : Entrypoint) (plan : Impact.Plan)
    (values result : EvalEnv) (initial next : LedgerState) (inputs : NativeRelation.Assignment)
    (initialSlots : List Slot)
    {json : Json} {call : ScalarCall}
    (lowered : Zkir.lowerEntrypoint declarations entry = .ok json)
    (decoded : decodeScalarCall json = .ok call)
    (planAccepted : Impact.lower declarations (Passes.pruneEntrypoint entry) = .ok plan)
    (profile : ScalarValidationOpcodeProfile.checkedScalarOpcodeProfile
      (defaultEntrypointRows entry plan).toList.zipIdx call.body.instructions = true)
    (admittedInputs : CanonicalInputs entry.circuit values inputs)
    (circuitAdmission : ScalarCircuitAdmission entry.circuit)
    (returnScope : ∀ output ∈ entry.returns,
      ∃ _ : ScalarType output.ty, ScalarExpression output.value)
    (unguarded : entry.effectGuards = [])
    (cellScope : ScalarCellEffects declarations entry.effects)
    (operandScope : ∀ effect ∈ entry.effects, ScalarCellOperand effect)
    (admittedState : GenericStateEncoding.AdmittedState declarations initial initialSlots)
    (success : entry.run ctx values initial = .ok (result, next)) :
    ∃ expected outputs finalEnv entries witness readValues native finalSlots,
      Native.expectedEntrypoint declarations (Passes.pruneEntrypoint entry) = .ok expected ∧
      entry.circuit.run ctx values = .ok outputs ∧
      sourceReadInputs ctx entry.effects
        (Impact.publicInputReadCount entry.circuit.inputs)
        (outputs ++ values, {initial with unshieldedInputs := [], unshieldedOutputs := [], unshieldedSpendClaims := []}) =
        .ok (entries, (finalEnv, next)) ∧
      (∀ input ∈ entry.circuit.inputs,
        witness ("%input_" ++ input.name) = inputs ("%input_" ++ input.name)) ∧
      CircuitSatisfies hash call.body
        ⟨ScalarValidatedProgram.inputValues expected .public
            (ScalarCellWitnessReadSeed.seedReadValues inputs entries),
          ScalarValidatedProgram.inputValues expected .private
            (ScalarCellWitnessReadSeed.seedReadValues inputs entries)⟩
        witness (call.body.groups witness) ∧
      call.arguments.map witness = expected.rawInputs.map
        (fun input => ScalarCellWitnessReadSeed.seedReadValues inputs entries input.identifier) ∧
      GenericStateInputValues.decodeReads
        (plan.reads.drop (Impact.publicInputReadCount entry.circuit.inputs)) witness = .ok readValues ∧
      GenericStateOps.evalPlan ctx ((outputs ++ values) ++ readValues) plan = .ok native ∧
      GenericStateEncoding.encodeState declarations next = some finalSlots ∧
      NativeState.run native (GenericStateEncoding.initial initialSlots) =
        some ⟨[.vector finalSlots],
          ScalarCellNativePublicPrefix.sourcePublicCells entry.circuit.inputs inputs ++ tapeCells entries⟩ := by
  have compatible := ScalarCellPublicFields.canonical_inputs_scalar_compatible
    entry.circuit values inputs admittedInputs
  have planAdmission := ScalarCellPlanAdmission.lower_admission declarations
    (Passes.pruneEntrypoint entry) plan planAccepted unguarded compatible cellScope operandScope returnScope
  obtain ⟨expected, outputs, finalEnv, entries, witness, expectedAccepted, circuitRun,
      sourceTape, frame, bindings, satisfies, arguments⟩ :=
    lowerEntrypoint_construct_scalar_cell_witness ctx hash implementation declarations entry plan
      values result initial next inputs lowered decoded planAccepted profile admittedInputs
      circuitAdmission planAdmission unguarded cellScope operandScope success
  obtain ⟨nativeOutputs, nativeEnv, _, nativeEntries, readValues, native, finalSlots, nativeCircuit,
      _, _, nativeTape, readDecoded, evaluated, encoded, nativeRun⟩ :=
    lowerEntrypoint_run_scalar_cell_native ctx declarations entry plan values result initial next
      inputs initialSlots planAccepted admittedInputs unguarded cellScope operandScope
      implementation.modulus admittedState success
  have sameOutputs := Except.ok.inj (circuitRun.symm.trans nativeCircuit)
  subst nativeOutputs
  have sameEntries : nativeEntries = entries :=
    congrArg Prod.fst (Except.ok.inj (nativeTape.symm.trans sourceTape))
  subst nativeEntries
  have witnessReads :=
    (GenericStateInputValues.decodeReads_input_frame _ _ witness frame).trans readDecoded
  exact ⟨expected, outputs, finalEnv, entries, witness, readValues, native, finalSlots,
    expectedAccepted, circuitRun, sourceTape, bindings, satisfies, arguments,
    witnessReads, evaluated, encoded, nativeRun⟩

end Noctium.Verification.ScalarCellNativeTrace
