import Noctium.Backend.Impact
import Noctium.Backend.Zkir
import Noctium.Frontend
import Noctium.Verification.ImpactPlanStatementAgreement

open scoped Noctium
open Noctium

noctium_circuit issue43GuardedPartialWrites where
  private enabled : Bool
  private checkEnabled : Bool
  private left : UInt 8
  private right : UInt 8
  private wide : Native
  private approved : Bool
end

noctium_contract Issue43GuardedPartialWrites where
  cell underflowed : UInt 8
  cell narrowed : UInt 3
  cell asserted : UInt 3
  cell shadowed : UInt 8
  cell valid : Native
  entry update uses issue43GuardedPartialWrites where
    when disclose(enabled) write underflowed := disclose(sub(left, right))
    when disclose(enabled) write narrowed := disclose(cast(UInt 3, wide))
    when disclose(enabled) write asserted := disclose(assertThen(approved, uint(7)))
    when disclose(enabled) write shadowed := disclose(let enabled := true in sub(left, right))
    when disclose(enabled) write valid := disclose(add(1, 2))
    when disclose(checkEnabled) require assertThen(approved, true)
  end
end

private def issue43PartialEntry : Entrypoint :=
  match Issue43GuardedPartialWrites.entrypoints with
  | ep :: _ => ep
  | _ => {name := "missing", circuit := {name := "missing"}}

private def issue43PartialContext : EvalContext := {
  modulus := Field.modulus
  poseidon2 := fun _ _ _ => .error "unused by this fixture"
}

private def issue43PartialInputs (enabled checkEnabled : _root_.Bool)
    (left right wide : Nat) (approved : _root_.Bool) : EvalEnv := [
  ("enabled", .bool enabled),
  ("checkEnabled", .bool checkEnabled),
  ("left", .uint 255 left),
  ("right", .uint 255 right),
  ("wide", .native wide),
  ("approved", .bool approved)]

private def issue43PartialInitial : LedgerState := {
  cells := [
    ("underflowed", .uint 255 0),
    ("narrowed", .uint 7 0),
    ("asserted", .uint 7 0),
    ("shadowed", .uint 255 0),
    ("valid", .native 0)]
}

#guard match issue43PartialEntry.run issue43PartialContext
    (issue43PartialInputs _root_.Bool.false _root_.Bool.false 1 2 8 _root_.Bool.false)
    issue43PartialInitial with
  | .ok (outputs, after) => outputs.isEmpty && after == issue43PartialInitial
  | .error _ => Bool.false

#guard match issue43PartialEntry.run issue43PartialContext
    (issue43PartialInputs _root_.Bool.true _root_.Bool.true 3 2 3 _root_.Bool.true)
    issue43PartialInitial with
  | .ok (outputs, after) => outputs.isEmpty &&
      after.cells.lookup "underflowed" == some (.uint 255 1) &&
      after.cells.lookup "narrowed" == some (.uint 7 3) &&
      after.cells.lookup "asserted" == some (.uint 7 7) &&
      after.cells.lookup "shadowed" == some (.uint 255 1) &&
      after.cells.lookup "valid" == some (.native 3)
  | .error _ => Bool.false

private def issue43WritesOnly : Entrypoint := {issue43PartialEntry with
  effects := issue43PartialEntry.effects.dropLast
  effectGuards := issue43PartialEntry.effectGuards.dropLast
  effectSpans := issue43PartialEntry.effectSpans.dropLast}

-- The final guarded require adds an assertion while preserving the write count.
#guard match Backend.Impact.lower Issue43GuardedPartialWrites.state issue43PartialEntry,
    Backend.Impact.lower Issue43GuardedPartialWrites.state issue43WritesOnly with
  | .ok plan, .ok writes => plan.guards.length == 1 && writes.guards.isEmpty &&
      plan.operations.length == writes.operations.length &&
      plan.activityGuards.length == plan.operations.length &&
      plan.activityGuards.any Option.isSome
  | _, _ => Bool.false

private def issue43PartialRequirementResult (checkEnabled approved : _root_.Bool)
    (expected : _root_.Bool) : _root_.Bool :=
  match Backend.Impact.lower Issue43GuardedPartialWrites.state issue43PartialEntry with
  | .ok plan =>
      match plan.guards with
      | [assertion] =>
          match assertion.eval issue43PartialContext
              (issue43PartialInputs _root_.Bool.false checkEnabled 1 2 3 approved) with
            | .ok value => value == expected
            | .error _ => expected == _root_.Bool.false
      | _ => _root_.Bool.false
  | .error _ => _root_.Bool.false

#guard issue43PartialRequirementResult _root_.Bool.false _root_.Bool.false _root_.Bool.true
#guard issue43PartialRequirementResult _root_.Bool.true _root_.Bool.true _root_.Bool.true
#guard issue43PartialRequirementResult _root_.Bool.true _root_.Bool.false _root_.Bool.false

def main (args : List String) : IO Unit := do
  let [artifact] := args | throw (IO.userError "expected the guarded partial-write Impact file")
  let contract := Issue43GuardedPartialWrites
  let selected := Passes.pruneEntrypoint issue43PartialEntry
  let plan ← IO.ofExcept ((Backend.Impact.lower contract.state selected).mapError (·.message))
  let expected := Compiler.nativePlanJson TargetProfile.selected321 `Issue43GuardedPartialWrites
    contract.state contract.constructor selected plan Bool.false
  let checkSchedule := fun bytes =>
    Verification.ImpactPlanStatementAgreement.matchesBytes 64 bytes expected
  let bytes := (← IO.FS.readBinFile artifact).data.toList
  unless checkSchedule bytes do
    throw (IO.userError "emitted Impact schedule disagrees with the lowered entrypoint")
  let operations ← IO.ofExcept (expected.getObjVal? "operations" >>= Lean.Json.getArr?)
  unless operations.size ≥ 2 do
    throw (IO.userError "the fixture must contain more than one operation")
  let reordered := operations.swapIfInBounds 0 1
  let first := operations[0]!
  let changedGuard := first.setObjVal! "guard"
    (NativeExpression.toJson (.bool _root_.Bool.false))
  let changedOperand := first.setObjVal! "operation" <|
    (first.getObjValD "operation").setObjVal! "expression" (NativeExpression.toJson (.native 713))
  for altered in [reordered, operations.set! 0 changedGuard, operations.set! 0 changedOperand] do
    let planWithChanges := expected.setObjVal! "operations" (.arr altered)
    let changedBytes := planWithChanges.compress.toUTF8.data.toList
    discard <| IO.ofExcept (Verification.ArtifactBytes.parse changedBytes >>=
      Verification.ImpactWireDecoder.decodePlanOperations)
    if checkSchedule changedBytes then
      throw (IO.userError "the schedule check accepted a changed operation, guard, or operand")
