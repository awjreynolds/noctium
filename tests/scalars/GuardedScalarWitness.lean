import Noctium.Verification
import Noctium.Verification.GuardedScalarWitness
import Noctium.Verification.GenericStateConverseSource
import Noctium.Verification.GenericStateConverseNativeTrace
import Noctium.Verification.ScalarWitnessReturns

open Noctium Noctium.Backend Noctium.Verification
open NativeRelation

private def declarations : List StateDecl := [
  {name := "balances", kind := .map .native .native},
  {name := "marker", kind := .cell .native}]

private def update : Entrypoint := {
  name := "update"
  circuit := {name := "updateInputs", inputs := [
    {name := "account", ty := .native, visibility := .«public»},
    {name := "enabled", ty := .bool, visibility := .«public»}]}
  effects := [
    .writeMap "balances" .native .native (.ref "account")
      (.copyValue (.add (.ref "account") (.native 5))),
    .readMap "balances" "saved" .native .native (.ref "account"),
    .requireAbsent "balances" .native (.native 99),
    .readCell "marker" "markerValue" .native]
  effectGuards := [none, some (.ref "enabled"), none, none]
}

private def ctx : EvalContext :=
  {modulus := Field.modulus, poseidon2 := fun _ _ _ => .ok zero}

private def initial : LedgerState :=
  {maps := [("balances", [])], cells := [("marker", .native 23)]}

private def fixture (enabled wrongTranscript : _root_.Bool) :
    Except String (Scalar × _root_.Bool) := do
  let values : EvalEnv := [("account", .native 17), ("enabled", .bool enabled)]
  let json ← (Zkir.lowerEntrypoint declarations update).mapError Diagnostic.message
  let bytes := json.compress.toUTF8.data.toList
  let call ← GuardedScalarWitness.buildSourceCall ctx (fun _ => zero) declarations
    update values initial bytes
  if wrongTranscript then
    discard <| GuardedScalarWitness.build (fun _ => zero) call.seed bytes call.expected
      {call.transcript with transcriptOutputs := call.transcript.transcriptOutputs.drop 1}
  return (call.checked.assignment "%input_saved", call.checked.observations.any fun observation =>
    !observation.active)

-- The same emitted bytes serve both branches. The seeded witness uses the
-- value written by the call when active and the source runner's zero otherwise.
#guard (fixture _root_.Bool.true _root_.Bool.false).toOption == some (scalar 22, _root_.Bool.false)
#guard (fixture _root_.Bool.false _root_.Bool.false).toOption == some (zero, _root_.Bool.true)
#guard match fixture _root_.Bool.false _root_.Bool.true with
  | .error reason => reason == "guarded witness does not consume the supplied transcript"
  | .ok _ => _root_.Bool.false

-- The decoded equality alone cannot distinguish an SSA definition from a
-- constraint. Witness construction checks the producer tag as well.
private def rejectsChangedCopy : Except String _root_.Bool := do
  let json ← (Zkir.lowerEntrypoint declarations update).mapError Diagnostic.message
  let rows ← Native.arrayField json "instructions"
  let replaced ← rows.mapM fun row => do
    let op ← Native.stringField row "op"
    if op == "copy" then
      let input ← row.getObjVal? "val"
      let destination ← row.getObjVal? "output"
      pure (Lean.Json.mkObj [("op", Lean.toJson "constrain_eq"),
        ("a", input), ("b", destination)])
    else pure row
  let fields ← json.getObj?
  let bytes := (Lean.Json.obj (fields.insert "instructions" (.arr replaced))).compress.toUTF8.data.toList
  discard <| GuardedZkirArtifact.check bytes json
  let values : EvalEnv := [("account", .native 17), ("enabled", .bool _root_.Bool.false)]
  match GuardedScalarWitness.buildSourceCall ctx (fun _ => zero) declarations update values initial bytes with
  | .error reason => pure (reason == "guarded artifact JSON differs from the emitted program")
  | .ok _ => pure _root_.Bool.false

#guard rejectsChangedCopy.toOption == some _root_.Bool.true

open Lean Elab Command in
run_cmd do
  for root in [`Noctium.Verification.GuardedScalarWitness.buildSourceCall,
      `Noctium.Verification.GuardedScalarWitness.Checked.source_read_values,
      `Noctium.Verification.GenericStateConverseSource.source_assignment_of_entry_run,
      `Noctium.Verification.GenericStateConverseCheckedPlan.checked_of_constructed_trace,
      `Noctium.Verification.GenericStateConverseNativeTrace.source_call_native_trace,
      `Noctium.Verification.GenericStateConverseNativeTrace.source_call_build_reduces_to_artifact,
      `Noctium.Verification.GuardedScalarWitness.build_of_scope,
      `Noctium.Verification.GuardedScalarWitness.build_of_lowered_scalar_artifact,
      `Noctium.Verification.GuardedScalarWitnessAssembly.ProducerScope.of_validation_loop,
      `Noctium.Verification.GuardedScalarWitnessAssembly.ProducerScope.assemble_scope,
      `Noctium.Verification.GuardedScalarWitnessAssembly.ProducerScope.cons_validated_copy,
      `Noctium.Verification.GuardedScalarWitnessAssembly.ProducerScope.cons_validated_constrain_eq,
      `Noctium.Verification.GuardedScalarWitnessAssembly.ProducerScope.cons_validated_publicInput,
      `Noctium.Verification.GuardedScalarWitnessAssembly.ProducerScope.cons_validated_impact,
      `Noctium.Verification.ScalarWitnessConstruction.completes_entrypoint_returns_output_row] do
    match Noctium.Verification.Audit.axiomsIn (← getEnv) root with
    | .ok _ => pure ()
    | .error error => throwError error
