import Noctium.Verification
import Noctium.Verification.GuardedScalarCandidateState
import Noctium.Verification.ScalarSourceReadWitness

open Noctium Noctium.Backend Noctium.Verification
open NativeRelation ScalarCellWitnessReadSeed

private def declarations : List StateDecl := [
  {name := "balances", kind := .map .native .native},
  {name := "marker", kind := .cell .native}]

private def update (enabled : _root_.Bool) : Entrypoint := {
  name := "update"
  circuit := {name := "updateInputs", inputs := [
    {name := "account", ty := .native, visibility := .«public»}]}
  effects := [
    .writeMap "balances" .native .native (.ref "account") (.native 7),
    .readMap "balances" "updated" .native .native (.ref "account"),
    .requireAbsent "balances" .native (.native 99),
    .readCell "marker" "markerValue" .native,
    .readMap "balances" "missing" .native .native (.native 99)]
  effectGuards := [none, none, none, none, some (.bool enabled)]
}

private def ctx : EvalContext := {
  modulus := Field.modulus
  poseidon2 := fun _ _ _ => .error "unused by this fixture"
}

private def initial : SourceEffects.Frame :=
  ([("account", .native 17)], {maps := [("balances", [])], cells := [("marker", .native 23)]})

private def recordUpdate (ep : Entrypoint) :=
  ScalarSourceReadTape.sourceReadInputs ctx ep.effectGuards ep.effects.zipIdx
    (Impact.publicInputReadCount ep.circuit.inputs) initial

private def vmMatchesSource (ep : Entrypoint) (plan : Impact.Plan)
    (seed : Assignment) (final : SourceEffects.Frame) : _root_.Bool :=
  match GenericStateEncoding.encodeInitialState declarations initial.2,
      GenericStateEncoding.encodeState declarations final.2 with
  | some before, some after =>
    GuardedScalarCandidateState.runCheckedCandidates ctx ep plan initial.1 seed before ==
      some ⟨[.vector after], [NativeState.field (scalar 17), NativeState.field (scalar 7),
        NativeState.boolean _root_.Bool.false, NativeState.field (scalar 23)]⟩
  | _, _ => _root_.Bool.false

-- The map value is read after the write. The following absence name reflects
-- the map-read position. The inactive missing lookup contributes a zero binding.
#guard
  let ep := update _root_.Bool.false
  match Impact.lower declarations ep, recordUpdate ep with
  | .ok plan, .ok (records, final) =>
    let reads := plan.reads.drop (Impact.publicInputReadCount ep.circuit.inputs)
    let inputs : Assignment := fun _ => scalar 17
    let seed := seedReadValues inputs records
    (records.map fun record => (record.1.name, record.2.val)) ==
        [("updated", 7), ("_noctium_absence_2", 0), ("markerValue", 23), ("missing", 0)] &&
      seed "%input_account" == scalar 17 &&
      (GenericStateInputValues.decodeReads reads seed).toOption == some
        [("updated", .native 7), ("_noctium_absence_2", .bool _root_.Bool.false),
          ("markerValue", .native 23), ("missing", .native 0)] &&
      vmMatchesSource ep plan seed final &&
      final.2.maps.lookup "balances" == some [(.native 17, .native 7)]
  | _, _ => _root_.Bool.false

#guard (recordUpdate (update _root_.Bool.true)).isOk == _root_.Bool.false

open Lean Elab Command in
run_cmd do
  match Noctium.Verification.Audit.axiomsIn (← getEnv) `Noctium.Verification.ScalarSourceReadWitness.lower_source_read_witness with
  | .ok _ => pure ()
  | .error error => throwError error
