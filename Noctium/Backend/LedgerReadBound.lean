import Noctium.Backend.Impact
import Noctium.Backend.NativeExpected
import Noctium.Passes

namespace Noctium.Backend.LedgerReadBound

open Noctium

/-- Source and Impact evidence for one unconditional UInt128 root-cell read.
This identifies the external ledger premise. It is not a standalone circuit proof. -/
structure Certificate where
  contractName : String
  entrypointName : String
  cellName : String
  cellSlot : Nat
  readInput : String
  popeqOperation : Nat
  popeqGroup : Nat
  popeqFields : List Backend.Impact.Scalar
  deriving Repr

private def uint128Maximum : Nat := 2 ^ 128 - 1

private def sourceCellSlot (contract : Contract) (cellName : String) : Except String Nat := do
  let some slot := contract.state.findIdx? (·.name == cellName)
    | throw s!"unknown state cell '{cellName}'"
  let some cell := contract.state[slot]?
    | throw s!"unknown state cell '{cellName}'"
  unless cell.kind == .cell (.uint uint128Maximum) && cell.cellAlignment? == some .u128 do
    throw s!"state cell '{cellName}' is not an aligned UInt 128 root cell"
  pure slot

/-- Check that the named source read lowers to the exact unconditional
`Popeq(Bytes(16), value)` transcript operation for its declared root cell. -/
def check (contract : Contract) (entrypointName cellName destination : String) :
    Except String Certificate := do
  match Contract.validate Capabilities.source contract with
  | .error diagnostic => throw diagnostic.message
  | .ok _ => pure ()
  let cellSlot ← sourceCellSlot contract cellName
  let some entry := contract.entrypoints.find? (·.name == entrypointName)
    | throw s!"unknown entrypoint '{entrypointName}'"
  let effectMatches := entry.effects.zipIdx.filterMap fun (effect, index) =>
    match effect with
    | .readCell readCell readDestination (.uint maximum) =>
      if readCell == cellName && readDestination == destination && maximum == uint128Maximum
      then some index else none
    | _ => none
  let effectIndex ← match effectMatches with
    | [index] => pure index
    | _ => throw s!"expected one direct UInt128 read of '{cellName}' as '{destination}'"
  if entry.effectGuardAt effectIndex |>.isSome then
    throw "guarded ledger reads do not have an unconditional UInt128 bound"

  let checkedEntry := Noctium.Passes.pruneEntrypoint entry
  let expected ← (Backend.Native.expectedEntrypoint contract.state checkedEntry).mapError
    (fun diagnostic => diagnostic.message)
  let inputIdentifier := "%input_" ++ destination
  let matchingInputs := expected.inputs.filter (·.identifier == inputIdentifier)
  let inputRequirement ← match matchingInputs with
    | [requirement] => pure requirement
    | _ => throw "UInt128 ledger read does not map to one unique source input"
  if expected.rawInputs.any (·.identifier == inputIdentifier) then
    throw "UInt128 ledger read input collides with a call argument"
  unless inputRequirement.visibility == .«public» && inputRequirement.ty == .uint uint128Maximum do
    throw "UInt128 ledger read input does not match its public source type"
  let (plan, boundaries) ←
    (Backend.Impact.lowerWithEffectBoundaries contract.state checkedEntry).mapError
    (fun diagnostic => diagnostic.message)
  let readMatches := plan.reads.filter (·.name == destination)
  let read ← match readMatches with
    | [read] => pure read
    | _ => throw s!"expected one Impact read for '{destination}'"
  unless read.ty == .uint uint128Maximum && read.components.isEmpty && read.schema.isNone &&
      read.guard.isNone do
    throw s!"Impact read '{destination}' does not match a scalar UInt128 ledger input"
  let some (sourceCell, sourceSlot, popeqFields) := read.rootCellRead
    | throw s!"Impact read '{destination}' has no direct root-cell provenance"
  unless sourceCell == cellName && sourceSlot == cellSlot do
    throw "Impact read provenance does not bind the requested root cell"
  let popeqInput ← match popeqFields with
    | [.native 0x0c, .native 1, .native 16, .cast .native (.ref name)] => pure name
    | _ => throw "Impact read is not an exact UInt128 Bytes(16) Popeq"
  unless popeqInput == destination do
    throw "Impact Popeq fields do not bind the requested read input"

  let inputPlan ← (Backend.Impact.publicInputPlan entry.circuit.inputs).mapError id
  let start ← if effectIndex == 0 then pure inputPlan.operations.length else do
    let some previousEnd := boundaries[effectIndex - 1]?
      | throw "missing prior Impact effect boundary"
    pure previousEnd
  let some operationEnd := boundaries[effectIndex]?
    | throw "missing Impact effect boundary for the source read"
  unless operationEnd == start + 3 do
    throw "UInt128 read did not lower to exactly three ledger operations"
  if !plan.activityGuards.isEmpty then
    unless (plan.activityGuards.drop start |>.take 3).all Option.isNone do
      throw "UInt128 read has a conditional Impact operation"

  let popeqOperation := start + 2
  let popeqGroup := (plan.operations.take popeqOperation).foldl
    (fun count operation => count + operation.fieldGroups.length) 0
  pure {
    contractName := contract.name
    entrypointName
    cellName
    cellSlot
    readInput := inputIdentifier
    popeqOperation
    popeqGroup
    popeqFields
  }

end Noctium.Backend.LedgerReadBound
