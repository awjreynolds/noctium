import Noctium.Verification.UInt128ReadBound
import Noctium.Frontend

open Noctium
open scoped Noctium

noctium_circuit readGuard where
  public enabled : Bool
end

noctium_circuit directRead where
end

noctium_contract UInt128LedgerReadBoundFixture where
  cell totalSupply : UInt 128 alignedBytes
  cell ordinary : UInt 128
  entry directSupply uses directRead where
    read totalSupply as direct
    return amount : UInt 128 := direct
  end
  entry getSupply uses readGuard where
    read totalSupply as current
    when enabled read totalSupply as guarded
    return currentAmount : UInt 128 := current
    return guardedAmount : UInt 128 := guarded
  end
end

open Noctium.Backend.LedgerReadBound

#guard match check UInt128LedgerReadBoundFixture "getSupply" "totalSupply" "current" with
  | .ok certificate =>
      certificate.cellSlot == 0 && certificate.readInput == "%input_current" &&
        certificate.popeqOperation == 4 &&
        certificate.popeqGroup == 4 &&
        (match certificate.popeqFields with
        | [.native 0x0c, .native 1, .native 16, .cast .native (.ref "current")] => _root_.Bool.true
        | _ => _root_.Bool.false)
  | .error _ => _root_.Bool.false

#guard match check UInt128LedgerReadBoundFixture "getSupply" "totalSupply" "guarded" with
  | .ok _ => _root_.Bool.false
  | .error message => message == "guarded ledger reads do not have an unconditional UInt128 bound"

private def dropAlignment (declaration : StateDecl) : StateDecl :=
  if declaration.name == "totalSupply" then
    {declaration with cellAlignment? := none}
  else declaration

private def unalignedFixture : Contract :=
  {UInt128LedgerReadBoundFixture with
    state := UInt128LedgerReadBoundFixture.state.map dropAlignment}

#guard match check unalignedFixture "getSupply" "totalSupply" "current" with
  | .ok _ => _root_.Bool.false
  | .error message => message == "state cell 'totalSupply' is not an aligned UInt 128 root cell"

#guard match Backend.LedgerReadOptimization.lower
    UInt128LedgerReadBoundFixture "directSupply" "totalSupply" "direct" with
  | .ok operation =>
    operation.rangeIndex == 1 && operation.proofInput == "%input_direct" &&
      match Backend.Native.arrayField operation.strict "instructions",
          Backend.Native.arrayField operation.optimized "instructions" with
      | .ok original, .ok optimized =>
        original.size == optimized.size + 1 &&
          (Backend.RangeDedup.key? original[operation.rangeIndex]!) == some ("%input_direct", 128)
      | _, _ => _root_.Bool.false
  | .error _ => _root_.Bool.false

private def collideReadInput (operation : Entrypoint) : Entrypoint :=
  if operation.name == "directSupply" then
    {operation with circuit := {operation.circuit with inputs := [
      {name := "direct", ty := .uint (2 ^ 128 - 1), visibility := .«private»}]}}
  else operation

private def collidingFixture : Contract :=
  {UInt128LedgerReadBoundFixture with
    entrypoints := UInt128LedgerReadBoundFixture.entrypoints.map collideReadInput}

#guard match check collidingFixture "directSupply" "totalSupply" "direct" with
  | .ok _ => _root_.Bool.false
  | .error _ => _root_.Bool.true
