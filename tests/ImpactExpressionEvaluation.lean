import Noctium.Verification.ArtifactBytes
import Noctium.Verification.ImpactExpressionEvaluation
import Noctium.Verification.ImpactWireDecoder

open Lean Noctium Noctium.Verification

private def context : EvalContext := {
  modulus := Field.modulus
  poseidon2 := fun _ _ _ => .error "the partial-write fixture does not use Poseidon2"
}

private def inputs (left right wide : Nat) (approved : _root_.Bool) : EvalEnv :=
  [("enabled", .bool Bool.true), ("checkEnabled", .bool Bool.true),
    ("left", .uint 255 left), ("right", .uint 255 right),
    ("wide", .native wide), ("approved", .bool approved)]

def main (args : List String) : IO Unit := do
  let [artifact] := args | throw (IO.userError "expected the guarded partial-write Impact plan")
  let raw ← IO.ofExcept (ArtifactBytes.parse (← IO.FS.readBinFile artifact).data.toList)
  let schedule ← IO.ofExcept (ImpactWireDecoder.decodePlanOperations raw)
  let expressions := schedule.filterMap fun item =>
    match item.operation with
    | .push Bool.true "field" expression => some expression
    | _ => none
  let runWith := fun env => expressions.mapM (ImpactExpressionEvaluation.evaluate 64 context env)
  unless runWith (inputs 3 2 3 Bool.true) ==
      some [.native 1, .native 3, .native 7, .native 1, .native 3] do
    throw (IO.userError "decoded stored values differ from the guarded scalar fixture")
  unless (runWith (inputs 1 2 3 Bool.true)).isNone &&
      (runWith (inputs 3 2 8 Bool.true)).isNone &&
      (runWith (inputs 3 2 3 Bool.false)).isNone do
    throw (IO.userError "decoded evaluator accepted a partial scalar failure")
