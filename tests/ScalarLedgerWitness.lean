import Noctium.Verification
import Noctium.Verification.GenericStateLedgerAllocation
import Noctium.Verification.GenericStateLowering
import Noctium.Verification.GenericStateConverseLedgerSatisfies
import Noctium.Verification.GenericStateExpressionEnvironment
import Noctium.Verification.ScalarCellArtifactExecution
import Noctium.Verification.ScalarLedgerReturnObservation
import Noctium.Verification.ScalarLedgerSourceReturns

open Noctium Noctium.Backend Noctium.Verification
open NativeRelation NativeRelationJson ScalarValidationOpcodeProfile

private def declarations : List StateDecl := [{name := "counter", kind := .cell .native}]

private def fixtureEntry : Entrypoint := {
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

private def artifactBytes (json : Lean.Json) : ArtifactBytes.Bytes :=
  (json.pretty ++ "\n").toUTF8.data.toList

#guard match Zkir.lowerEntrypoint declarations fixtureEntry with
  | .error _ => _root_.Bool.false
  | .ok json =>
    let bytes := artifactBytes json
    match ScalarCellZkirByteBinding.decodeScalarCallBytes bytes, Native.arrayField json "instructions" with
    | .ok call, .ok rows =>
      (ArtifactBytes.parse bytes).toOption == some json &&
        !(NativeRelationJson.decode json).isOk &&
        call.arguments == ["%input_delta"] &&
        call.body.instructions.flatMap NativeInputOrdinalTrace.strictInstructionInputDescriptors ==
          [(.public, "%input_enabled"), (.private, "%input_limit"),
           (.public, "%input_before"), (.public, "%input_after")] &&
        checkedScalarOpcodeProfile rows.toList.zipIdx call.body.instructions
    | _, _ => _root_.Bool.false

private def context : EvalContext :=
  {modulus := Field.modulus, poseidon2 := fun _ _ _ => .error "no hash in this fixture"}

private def values : EvalEnv := [("delta", .native 24), ("enabled", .bool _root_.Bool.true), ("limit", .uint 63 50)]

#guard
  let bound : Expr .native := .add (.ref "delta") (.letE "delta" (.native 7) (.ref "delta"))
  let eager : Expr .native :=
    .letE "delta" (.native 7) (.select (.bool _root_.Bool.true) (.ref "delta") (.ref "absent"))
  let shadowed := values ++ [("delta", .native 99)]
  match bound.eval context shadowed, eager.eval context shadowed with
  | .ok value, .error message => value == 31 && message == "missing value 'absent'"
  | _, _ => _root_.Bool.false

private def initial : LedgerState := {cells := [("counter", .native 17)]}

private def fixtureWitness (program : Program) (seed : Assignment) : Option Assignment :=
  program.instructions.foldlM (fun assignment instruction => match instruction with
    | .add left right dest =>
      some (ScalarWitness.assign assignment dest (scalar ((left.read assignment).val + (right.read assignment).val)))
    | .input .. | .boolean .. | .bits .. | .assert .. | .impact .. | .output .. => some assignment
    | _ => none) seed

private def strictEntry : Entrypoint := {fixtureEntry with callInputs := []}

private def strictScheduleMatches (plan : Impact.Plan) (relation : Program)
    (assignment : Assignment) : _root_.Bool :=
  let reads := plan.reads.drop (Impact.publicInputReadCount strictEntry.circuit.inputs)
  match strictEntry.circuit.run context values, GenericStateInputValues.decodeReads reads assignment with
  | .ok outputs, .ok candidates =>
    candidates == [("before", .native 17), ("after", .native 42)] &&
      match GenericStateOps.evalPlan context ((outputs ++ values) ++ candidates) plan with
      | .ok operations => relation.groups assignment == NativeState.groups operations
      | .error _ => _root_.Bool.false
  | _, _ => _root_.Bool.false

-- The same source calculation also accepts strict scalar decoding when every
-- input is emitted as a transcript row instead of supplied in the raw header.
#guard
  let seed : Assignment := fun
    | "%input_delta" => scalar 24
    | "%input_enabled" => one
    | "%input_limit" => scalar 50
    | "%input_before" => scalar 17
    | "%input_after" => scalar 42
    | _ => zero
  match Zkir.lowerEntrypoint declarations strictEntry,
      Native.expectedEntrypoint declarations (Passes.pruneEntrypoint strictEntry),
      Impact.lower declarations (Passes.pruneEntrypoint strictEntry) with
  | .ok json, .ok expected, .ok plan =>
    match NativeRelationJson.decode json, Native.arrayField json "inputs" with
    | .ok relation, .ok rawInputs =>
      match fixtureWitness relation seed with
      | some assignment =>
        let body := ((Zkir.lowerEntrypointBody (Passes.pruneEntrypoint strictEntry) plan).run {}).2
        rawInputs.isEmpty && expected.rawInputs.isEmpty &&
          relation.instructions.flatMap NativeInputOrdinalTrace.strictInstructionInputDescriptors ==
            expected.inputs.map NativeInputOrdinalTrace.expectedInputDescriptor &&
          expected.inputs.map (·.identifier) ==
            ["%input_delta", "%input_enabled", "%input_limit", "%input_before", "%input_after"] &&
          expected.inputs.all (fun requirement => validIdentifier requirement.identifier) &&
          body.instructions.size == relation.instructions.length &&
          decide (body.next ≤ body.outputDefinitions) &&
          relation.inputValues .private assignment == [scalar 24, scalar 50] &&
          (relation.groups assignment).map (List.map some) ==
            expected.groups.map (List.map (ScalarNormalization.interpret (fun _ => zero) seed)) &&
          strictScheduleMatches plan relation assignment &&
          relation.returns assignment == [scalar 42]
      | none => _root_.Bool.false
    | _, _ => _root_.Bool.false
  | _, _, _ => _root_.Bool.false

private def nativeCallMatches (plan : Impact.Plan) (complete : EvalEnv) (next : LedgerState)
    (call : ScalarCall) (seed : Assignment) : _root_.Bool :=
  match GenericStateEncoding.encodeInitialState declarations initial,
      GenericStateEncoding.encodeState declarations next,
      GenericStateOps.evalPlan context complete plan, fixtureWitness call.body seed with
  | some initialSlots, some finalSlots, .ok operations, some assignment =>
    let fieldCell := fun value => NativeState.field (scalar value)
    let expected : NativeState.Machine := ⟨[.vector finalSlots], [fieldCell 1, fieldCell 17, fieldCell 42]⟩
    let planJson := Compiler.nativePlanJson TargetProfile.selected321 `ScalarLedgerFixture
      declarations none (Passes.pruneEntrypoint fixtureEntry) plan _root_.Bool.false
    let bytes := artifactBytes planJson
    (ArtifactBytes.parse bytes).toOption == some planJson &&
      ImpactPlanStatementAgreement.matchesBytes 64 bytes planJson &&
      decide (ImpactPlanAgreement.evaluatePlan 64 context complete planJson = some operations) &&
      decide (ImpactPlanAgreement.runPlanBytes 64 context complete bytes
        (GenericStateEncoding.initial initialSlots) = some expected) &&
      decide (call.body.groups assignment = NativeState.groups operations) &&
      decide (call.body.returns assignment = [scalar 42])
  | _, _, _, _ => _root_.Bool.false

#guard match fixtureEntry.run context values initial with
  | .ok (returned, next) =>
    returned == [("increment", .native 25), ("result", .native 42)] &&
      next.cells == [("counter", .native 42)]
  | .error _ => _root_.Bool.false

#guard match Impact.lower declarations fixtureEntry,
    ((Zkir.lowerEntrypoint declarations fixtureEntry).mapError (·.message)).bind
      (ScalarCellZkirByteBinding.decodeScalarCallBytes ∘ artifactBytes) with
  | .ok plan, .ok call =>
    let cutoff := Impact.publicInputReadCount fixtureEntry.circuit.inputs
    match fixtureEntry.circuit.run context values with
    | .error _ => _root_.Bool.false
    | .ok outputs =>
      match ScalarCellSourceReads.sourceReadInputs context fixtureEntry.effects cutoff (outputs ++ values, initial) with
      | .error _ => _root_.Bool.false
      | .ok (entries, (_, next)) =>
        let seed := ScalarCellWitnessReadSeed.seedReadValues
          (fun
            | "%input_delta" => scalar 24
            | "%input_enabled" => one
            | "%input_limit" => scalar 50
            | _ => zero)
          entries
        let reads := plan.reads.drop cutoff
        (entries.map fun (descriptor, value) => (descriptor.name, value.val)) == [("before", 17), ("after", 42)] &&
          reads.map (·.name) == entries.map (·.1.name) &&
          (seed "%input_delta").val == 24 &&
          match GenericStateInputValues.decodeReads reads seed with
          | .ok readValues =>
            let complete := (outputs ++ values) ++ readValues
            readValues == [("before", .native 17), ("after", .native 42)] &&
              plan.operations.all (fun operation => operation.fieldGroups.all
                (fun fields => fields.all (fun field => (field.eval context complete).isOk))) &&
              nativeCallMatches plan complete next call seed &&
              match fixtureEntry.evalReturns context complete with
              | .ok returned => returned == [("result", .native 42)]
              | .error _ => _root_.Bool.false
          | .error _ => _root_.Bool.false
  | _, _ => _root_.Bool.false

open Lean Elab Command in
run_cmd do
  let environment ← getEnv
  for proof in [
      `Noctium.Verification.GenericStateLedgerAllocation.lowerEntrypoint_allocation_bounds,
      `Noctium.Verification.GenericStateLowering.accepted_relation_groups,
      `Noctium.Verification.GenericStateConverseLedgerSatisfies.lowered_body_authenticated_groups,
      `Noctium.Verification.GenericStateExpressionEnvironment.eval_lookup_ext,
      `Noctium.Verification.ScalarLedgerWitnessPreflight.lowerEntrypoint_witness_preflight,
      `Noctium.Verification.ScalarLedgerWitnessPreflight.lowerEntrypoint_strict_witness_preflight,
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
      `Noctium.Verification.ScalarCellArtifactExecution.lowerEntrypoint_checked_artifact_execution,
      `Noctium.Verification.ScalarLedgerSourceReturns.evalReturns_transport,
      `Noctium.Verification.ScalarLedgerReturnObservation.expected_returns_observe_source,
      `Noctium.Verification.ScalarWitnessConstruction.completes_entrypoint_returns] do
    match Noctium.Verification.Audit.axiomsIn environment proof with
    | .ok _ => pure ()
    | .error error => throwError "{proof}: {error}"

private def repeatedHashEntry : Entrypoint :=
  let digest : Expr (.bytes 32) :=
    .persistentHash32 (.bytes32Literal (List.replicate 32 0))
  { name := "repeatedBytes32Hash"
    circuit := {name := "repeatedBytes32HashCircuit"}
    returns := [
      {name := "firstDigest", ty := .bytes 32, value := digest},
      {name := "secondDigest", ty := .bytes 32, value := digest}] }

private def repeatedHashBody (plan : Impact.Plan) : Zkir.LowerState :=
  ((Zkir.lowerEntrypointBody (Passes.pruneEntrypoint repeatedHashEntry) plan).run {}).2

-- Exercise the accepted ledger path and check the exact rows from its Impact plan.
#guard match Impact.lower [] (Passes.pruneEntrypoint repeatedHashEntry),
    Zkir.lowerEntrypoint [] repeatedHashEntry with
  | .ok plan, .ok program =>
    let body := repeatedHashBody plan
    match Native.arrayField program "instructions" with
    | .ok rows =>
      rows == body.instructions &&
        rows.toList.map Native.opcode == ["persistent_hash", "bytes_into_natives", "output"] &&
        Native.outputDefinitionsInInstruction rows[1]! == 2 &&
        body.next == 3 && body.outputDefinitions == 3
    | .error _ => _root_.Bool.false
  | _, _ => _root_.Bool.false

example : Zkir.OutputCapacityFrame {} (repeatedHashBody {}) := by
  constructor <;> decide +kernel

private def coldHashField : Expr .native :=
  .bytesField (.persistentHash32 (.bytes32Literal (List.replicate 32 0))) 0

-- A single cold hash field allocates more names than it emits rows.
example :
    let after := ((Zkir.lowerExpr coldHashField).run {}).2
    after.instructions.size = 2 ∧ after.next = 3 ∧ after.outputDefinitions = 3 ∧
      Zkir.OutputCapacityFrame {} after := by
  exact ⟨by decide +kernel, by decide +kernel, by decide +kernel,
    Zkir.lowerExpr_preservesOutputCapacityFrame coldHashField {}⟩
