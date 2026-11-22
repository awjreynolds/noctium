import Lean
import Noctium.Semantics
import BoundedScalars

namespace BoundedScalarsReplay

private def context : Noctium.EvalContext := {
  modulus := Noctium.Field.modulus
  poseidon2 := fun _ _ _ => .error "unused Poseidon oracle"
}

private def selectedEntrypoint : Noctium.Entrypoint :=
  BoundedScalars.entrypoints.headD {name := "", circuit := {name := ""}}

private def initialState : Noctium.LedgerState := {
  cells := [("total", Noctium.Value.uint 510 0)]
}

private def inputs (expected left right : Nat) : Noctium.EvalEnv := [
  ("expected", Noctium.Value.uint 510 expected),
  ("left", Noctium.Value.uint 255 left),
  ("right", Noctium.Value.uint 255 right)
]

private def stateTotal (state : Noctium.LedgerState) : Option Nat :=
  match state.cells.lookup "total" with
  | some (.uint 510 value) => some value
  | _ => none

private def runCall (expected left right : Nat) (state : Noctium.LedgerState) :=
  selectedEntrypoint.run context (inputs expected left right) state

def sourceSequenceChecks : Bool := Id.run do
  let .ok (_, afterZero1) := runCall 0 0 0 initialState | return false
  let .ok (_, afterZero2) := runCall 0 0 0 afterZero1 | return false
  let .ok (_, afterTwo) := runCall 2 1 1 afterZero2 | return false
  let circuitAcceptsThree := match boundedRelation.run context (inputs 3 1 2) with
    | .ok [(_, .uint 510 3)] => true
    | _ => false
  let thirdCall := runCall 3 1 2 afterTwo
  let thirdRejectedAtStateGuard := match thirdCall with
    | .error "state transition guard failed" => true
    | .ok _ => false
    | .error _ => false
  let noAcceptedSuccessor := match thirdCall with
    | .error _ => true
    | .ok _ => false
  return selectedEntrypoint.returns.isEmpty && circuitAcceptsThree &&
    thirdRejectedAtStateGuard && noAcceptedSuccessor &&
    stateTotal afterZero1 == some 0 &&
    stateTotal afterZero2 == some 0 &&
    stateTotal afterTwo == some 2

def oneSuccessPolicyAllows (successes : Nat) : Bool := successes == 0

def shortestPolicyCounterexample : Bool := Id.run do
  let .ok (_, afterFirst) := runCall 0 0 0 initialState | return false
  let sourceSecondAccepts := match runCall 0 0 0 afterFirst with
    | .ok _ => true
    | .error _ => false
  return sourceSecondAccepts &&
    oneSuccessPolicyAllows 0 &&
    !oneSuccessPolicyAllows 1

#guard sourceSequenceChecks
#guard shortestPolicyCounterexample

theorem at_most_one_success_rejects_second_call :
    oneSuccessPolicyAllows 1 = false := by decide

def printEvidence : IO Unit := do
  unless sourceSequenceChecks do
    throw <| IO.userError "BoundedScalars source sequence failed"
  unless shortestPolicyCounterexample do
    throw <| IO.userError "at-most-one-success counterexample failed"
  let evidence := Lean.Json.mkObj [
    ("source", Lean.Json.str "BoundedScalars.apply"),
    ("sourceConstraintAcceptsSumThree", Lean.Json.bool true),
    ("sourceAcceptedSequence", Lean.toJson [true, true, true, false]),
    ("fourthCallRejectionClass", Lean.Json.str "state transition guard"),
    ("acceptedDecodedStateTotals", Lean.toJson ["0", "0", "2"]),
    ("lastAcceptedStateAfterRejectedCall", Lean.Json.str "2"),
    ("committedCallReturns", Lean.Json.arr #[]),
    ("privateInputObservations", Lean.Json.bool false),
    ("separatePolicy", Lean.Json.mkObj [
      ("name", Lean.Json.str "at-most-one-success"),
      ("firstMismatchCall", Lean.toJson 2),
      ("shortestCounterexampleCalls", Lean.toJson 2),
      ("sourceAcceptsSecondZeroSum", Lean.Json.bool true),
      ("policyAcceptsSecondZeroSum", Lean.Json.bool false)
    ]),
    ("scope", Lean.Json.str "Lean source evaluator only")
  ]
  IO.println evidence.compress

end BoundedScalarsReplay

def main : IO Unit := BoundedScalarsReplay.printEvidence
