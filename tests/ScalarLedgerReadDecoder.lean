import Noctium.Verification.GenericStateReadAuthentication

open Noctium Noctium.Backend Noctium.Verification

open Noctium.Verification.NativeRelation
open Noctium.Verification.GenericStateInputValues

private def scalarReadCandidates : List Noctium.Backend.Impact.Read :=
  [{name := "nativeRead", ty := .native},
   {name := "boolRead", ty := .bool},
   {name := "uintRead", ty := .uint 31}]

private def scalarReadWitness : Assignment := fun name =>
  if name == "%input_nativeRead" then scalar 17 else
  if name == "%input_boolRead" then one else
  if name == "%input_uintRead" then scalar 23 else zero

#guard match decodeReads scalarReadCandidates scalarReadWitness with
  | .ok values =>
    values == [("nativeRead", .native 17), ("boolRead", .bool true),
      ("uintRead", .uint 31 23)]
  | .error _ => false

#guard match decodeReads [{name := "bytesRead", ty := .bytes 32}] scalarReadWitness with
  | .error message => message == "unsupported non-scalar read type"
  | .ok _ => false


/-- A well-typed, in-range witness is accepted only if its field matches the
cell in the current encoded ledger. -/
private def checkedCounterRead (candidate : Nat) : Option (List NativeState.Cell) := do
  let declarations : List StateDecl := [{name := "counter", kind := .cell (.uint 31)}]
  let ledger : LedgerState := {cells := [("counter", .uint 31 23)]}
  let ctx : EvalContext := {modulus := Field.modulus, poseidon2 := fun _ _ _ => .ok 0}
  let plan ← (Impact.appendEffect declarations (.readCell "counter" "old" (.uint 31)) {}).toOption
  let values ← (decodeReads plan.reads (fun _ => scalar candidate)).toOption
  let operations ← (GenericStateOps.evalPlan ctx values plan).toOption
  let slots ← GenericStateEncoding.encodeState declarations ledger
  let result ← NativeState.run operations ⟨[.vector slots], []⟩
  return result.reads

#guard checkedCounterRead 23 == some [NativeState.field (scalar 23)]
#guard (checkedCounterRead 24).isNone
