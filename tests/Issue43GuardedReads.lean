import Noctium.Backend.Impact
import Noctium.Backend.NativeExpected
import Noctium.Backend.Zkir
import Noctium.Frontend
import Noctium.Verification.GuardedScalarInput

open scoped Noctium
open Lean Noctium

noctium_circuit issue43GuardedReads where
  public account : Native
  public enabled : Bool
end

noctium_contract Issue43GuardedReads where
  cell marker : Native
  map balances : Native => Native
  entry update uses issue43GuardedReads where
    member balances[account] as existed
    when existed read marker as skippedCell
    when existed read balances[account] as missingValue
    when eq(existed, false) insert balances[account] := 99
    when eq(existed, false) member balances[account] as initialized
    when initialized read balances[account] as currentValue
    when enabled read marker as markerValue
  end
end

private def issue43GuardedEntry : Entrypoint :=
  match Issue43GuardedReads.entrypoints with
  | ep :: _ => ep
  | _ => {name := "missing", circuit := {name := "missing"}}

private def issue43GuardedInputs : EvalEnv := [
  ("account", .native 7), ("enabled", .bool Bool.true)]

private def issue43GuardedState : LedgerState := {
  cells := [("marker", .native 23)]
  maps := [("balances", [])]
}

private def issue43GuardedContext : EvalContext := {
  modulus := Field.modulus
  poseidon2 := fun _ _ _ => .error "unused by this fixture"
}

#guard match issue43GuardedEntry.run issue43GuardedContext issue43GuardedInputs issue43GuardedState with
  | .ok (outputs, after) => outputs.isEmpty &&
      after.cells.lookup "marker" == some (.native 23) &&
      after.maps.lookup "balances" == some [(.native 7, .native 99)]
  | .error _ => Bool.false

private def replaceJsonField (value : Json) (name : String) (replacement : Json) : Json :=
  match value.getObj? with
  | .error _ => value
  | .ok object => Json.mkObj ((object.toList.filter (·.1 != name)) ++ [(name, replacement)])

private def guardedReadMutationRejected (change : List Json → List Json) : _root_.Bool :=
  match Backend.Native.expectedEntrypoint Issue43GuardedReads.state issue43GuardedEntry,
      Backend.Zkir.lowerEntrypoint Issue43GuardedReads.state issue43GuardedEntry with
  | .ok expected, .ok program =>
    let instructions := (program.getObjValD "instructions").getArr?.toOption.getD #[]
    let changed := replaceJsonField program "instructions" (toJson (change instructions.toList))
    !(Backend.Native.validate expected changed).isOk
  | _, _ => Bool.false

private def removeFirstAssert : List Json → List Json
  | [] => []
  | instruction :: rest =>
    if (instruction.getObjValD "op").getStr?.toOption == some "assert" then rest
    else instruction :: removeFirstAssert rest

#guard guardedReadMutationRejected (fun instructions => instructions.map fun instruction =>
  if (instruction.getObjValD "op").getStr?.toOption == some "public_input" &&
      (instruction.getObjValD "output").getStr?.toOption == some "%input_skippedCell" then
    replaceJsonField instruction "guard" Json.null
  else instruction)

#guard guardedReadMutationRejected removeFirstAssert

private def emittedMarkerGuardMatches : Except String _root_.Bool := do
  let pruned := Passes.pruneEntrypoint issue43GuardedEntry
  let expected ← (Backend.Native.expectedEntrypoint Issue43GuardedReads.state pruned).mapError (·.message)
  let artifact ← (Backend.Zkir.lowerEntrypoint Issue43GuardedReads.state
    issue43GuardedEntry).mapError (·.message)
  let rawInputs ← Backend.Native.arrayField artifact "inputs"
  unless rawInputs.isEmpty do
    throw "fixture has raw inputs before the instruction trace"
  let instructions ← Backend.Native.arrayField artifact "instructions"
  let (prelude, rest) := instructions.toList.span fun row =>
    Backend.Native.opcode row != "public_input" ||
      (Backend.Native.stringField row "output").toOption != some "%input_markerValue"
  let raw :: _ := rest | throw "missing guarded marker read"
  let before ← Backend.Native.validateInstructionLoop expected prelude.zipIdx {}
  let _ ← Backend.Native.validateInstruction expected before raw
  let operand ← Verification.NativeRelationJson.decodeOperandField raw "guard"
  let some requirement := expected.inputs[before.inputCount]? | throw "missing source input row"
  let inactive : Verification.NativeRelation.Assignment := fun _ => Verification.NativeRelation.zero
  let active : Verification.NativeRelation.Assignment := fun _ => Verification.NativeRelation.one
  let observed := [Verification.NativeRelation.scalar 23]
  return requirement.identifier == "%input_markerValue" &&
    requirement.activityGuard == some (.input "%input_enabled") &&
    decide (operand = .reference "%input_enabled" ∧
      Verification.GuardedScalarInput.consume (operand.read inactive) observed =
        some (Verification.NativeRelation.zero, observed) ∧
      Verification.GuardedScalarInput.consume (operand.read active) observed =
        some (Verification.NativeRelation.scalar 23, []) ∧
      Verification.GuardedScalarInput.consume (operand.read active) [] = none)

#guard emittedMarkerGuardMatches.toOption == some Bool.true
