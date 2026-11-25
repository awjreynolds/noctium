import Noctium.Verification
import Noctium.Verification.ScalarCellNativeTranscript
import Noctium.Verification.ScalarLedgerReturnObservation
import Noctium.Verification.ScalarLedgerSourceReturns

open Noctium Noctium.Backend Noctium.Verification
open NativeRelation NativeRelationJson ScalarValidationOpcodeProfile

private def declarations : List StateDecl := [{name := "counter", kind := .cell .native}]

private def entry : Entrypoint := {
  name := "increase"
  circuit := {
    name := "increaseCircuit"
    inputs := [
      {name := "delta", ty := .native, visibility := .private},
      {name := "enabled", ty := .bool, visibility := .public},
      {name := "limit", ty := .uint 63, visibility := .private}]
    constraints := [.ref "enabled"]
    outputs := [{
      name := "increment"
      ty := .native
      value := .disclose {} (.add (.ref "delta") (.native 1))}]
  }
  callInputs := ["delta"]
  effects := [
    .readCell "counter" "before" .native,
    .writeCell "counter" .native (.add (.ref "before") (.ref "increment")),
    .readCell "counter" "after" .native]
  returns := [{name := "result", ty := .native, value := .ref "after"}]
}

#guard match Zkir.lowerEntrypoint declarations entry with
  | .error _ => false
  | .ok json =>
    match decodeScalarCall json, Native.arrayField json "instructions" with
    | .ok call, .ok rows =>
      call.arguments == ["%input_delta"] &&
        call.body.instructions.flatMap NativeInputOrdinalTrace.strictInstructionInputDescriptors ==
          [(.public, "%input_enabled"), (.private, "%input_limit"),
           (.public, "%input_before"), (.public, "%input_after")] &&
        checkedScalarOpcodeProfile rows.toList.zipIdx call.body.instructions
    | _, _ => false

private def context : EvalContext :=
  {modulus := Field.modulus, poseidon2 := fun _ _ _ => .error "no hash in this fixture"}

private def values : EvalEnv := [("delta", .native 24), ("enabled", .bool true), ("limit", .uint 63 50)]

private def initial : LedgerState := {cells := [("counter", .native 17)]}

private def fixtureWitness (program : Program) (seed : Assignment) : Option Assignment :=
  program.instructions.foldlM (fun witness instruction => match instruction with
    | .add left right dest =>
      some (ScalarWitness.assign witness dest (scalar ((left.read witness).val + (right.read witness).val)))
    | .input .. | .boolean .. | .bits .. | .assert .. | .impact .. | .output .. => some witness
    | _ => none) seed

private def nativeCallMatches (plan : Impact.Plan) (complete : EvalEnv) (next : LedgerState)
    (call : ScalarCall) (seed : Assignment) : Bool :=
  match GenericStateEncoding.encodeInitialState declarations initial,
      GenericStateEncoding.encodeState declarations next,
      GenericStateOps.evalPlan context complete plan, fixtureWitness call.body seed with
  | some initialSlots, some finalSlots, .ok operations, some witness =>
    let cell := fun value => NativeState.field (scalar value)
    let expected : NativeState.Machine := ⟨[.vector finalSlots], [cell 1, cell 17, cell 42]⟩
    decide (NativeState.run operations (GenericStateEncoding.initial initialSlots) = some expected) &&
      decide (call.body.groups witness = NativeState.groups operations) &&
      decide (call.body.returns witness = [scalar 42])
  | _, _, _, _ => false

#guard match entry.run context values initial with
  | .ok (returned, next) =>
    returned == [("increment", .native 25), ("result", .native 42)] &&
      next.cells == [("counter", .native 42)]
  | .error _ => false

#guard match Impact.lower declarations entry,
    ((Zkir.lowerEntrypoint declarations entry).mapError (·.message)).bind decodeScalarCall with
  | .ok plan, .ok call =>
    let cutoff := Impact.publicInputReadCount entry.circuit.inputs
    match entry.circuit.run context values with
    | .error _ => false
    | .ok outputs =>
      match ScalarCellSourceReads.sourceReadInputs context entry.effects cutoff (outputs ++ values, initial) with
      | .error _ => false
      | .ok (entries, (_, next)) =>
        let seed := ScalarCellWitnessReadSeed.seedReadValues
          (fun
            | "%input_delta" => scalar 24
            | "%input_enabled" => one
            | "%input_limit" => scalar 50
            | _ => zero)
          entries
        let reads := plan.reads.drop cutoff
        (entries.map fun (read, value) => (read.name, value.val)) == [("before", 17), ("after", 42)] &&
          reads.map (·.name) == entries.map (·.1.name) &&
          (seed "%input_delta").val == 24 &&
          match GenericStateInputValues.decodeReads reads seed with
          | .ok readValues =>
            let complete := (outputs ++ values) ++ readValues
            readValues == [("before", .native 17), ("after", .native 42)] &&
              plan.operations.all (fun operation => operation.fieldGroups.all
                (fun fields => fields.all (fun field => (field.eval context complete).isOk))) &&
              nativeCallMatches plan complete next call seed &&
              match entry.evalReturns context complete with
              | .ok returned => returned == [("result", .native 42)]
              | .error _ => false
          | .error _ => false
  | _, _ => false

open Lean Elab Command in
run_cmd do
  let environment ← getEnv
  for proof in [
      `Noctium.Verification.ScalarLedgerWitnessPreflight.lowerEntrypoint_witness_preflight,
      `Noctium.Verification.ScalarLedgerWitnessSource.lowerEntrypoint_source_cell_read_tape,
      `Noctium.Verification.ScalarWitnessConstruction.completes_entrypoint_prelude,
      `Noctium.Verification.ScalarWitnessConstruction.completes_lowerLedgerReads_plain,
      `Noctium.Verification.ScalarWitnessConstruction.completes_plan_guards,
      `Noctium.Verification.ScalarWitnessConstruction.lowerLedgerOperations_complete_unGuarded,
      `Noctium.Verification.ScalarWitnessConstruction.completes_scalar_ledger_suffix,
      `Noctium.Verification.ScalarWitnessConstruction.lower_cell_plan_evaluation,
      `Noctium.Verification.ScalarWitnessConstruction.lowerEntrypoint_construct_scalar_cell_witness,
      `Noctium.Verification.ScalarCellNativeTrace.lowerEntrypoint_run_scalar_cell_native,
      `Noctium.Verification.ScalarCellNativeTrace.lowerEntrypoint_construct_scalar_cell_execution,
      `Noctium.Verification.ScalarCellNativeTranscript.lowerEntrypoint_checked_native_transcript,
      `Noctium.Verification.ScalarLedgerSourceReturns.evalReturns_transport,
      `Noctium.Verification.ScalarLedgerReturnObservation.expected_returns_observe_source,
      `Noctium.Verification.ScalarWitnessConstruction.completes_entrypoint_returns] do
    match Noctium.Verification.Audit.axiomsIn environment proof with
    | .ok _ => pure ()
    | .error error => throwError "{proof}: {error}"
