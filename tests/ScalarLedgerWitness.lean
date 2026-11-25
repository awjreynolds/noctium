import Noctium.Verification
import Noctium.Verification.ScalarLedgerWitnessComposition
import Noctium.Verification.ScalarLedgerWitnessPreflight
import Noctium.Verification.ScalarLedgerWitnessSource
import Noctium.Verification.ScalarWitnessEntrypointPrelude

open Noctium Noctium.Backend Noctium.Verification
open NativeRelationJson ScalarValidationOpcodeProfile

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
  }
  callInputs := ["delta"]
  effects := [
    .readCell "counter" "before" .native,
    .writeCell "counter" .native (.disclose {} (.add (.ref "before") (.ref "delta"))),
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

private def values : EvalEnv := [("delta", .native 25), ("enabled", .bool true), ("limit", .uint 63 50)]

private def initial : LedgerState := {cells := [("counter", .native 17)]}

#guard match entry.run context values initial with
  | .ok (returned, next) =>
    returned == [("result", .native 42)] && next.cells == [("counter", .native 42)]
  | .error _ => false

#guard match Impact.lower declarations entry with
  | .error _ => false
  | .ok plan =>
    let cutoff := Impact.publicInputReadCount entry.circuit.inputs
    match ScalarCellSourceReads.sourceReadInputs context entry.effects cutoff (values, initial) with
    | .error _ => false
    | .ok (entries, _) =>
      (entries.map fun (read, value) => (read.name, value.val)) == [("before", 17), ("after", 42)] &&
        (plan.reads.drop cutoff).map (·.name) == entries.map (·.1.name)

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
      `Noctium.Verification.ScalarWitnessConstruction.completes_entrypoint_returns] do
    match Noctium.Verification.Audit.axiomsIn environment proof with
    | .ok _ => pure ()
    | .error error => throwError "{proof}: {error}"
