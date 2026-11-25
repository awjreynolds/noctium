import Noctium.Verification.ImpactPlanAgreement

open Noctium Noctium.Verification

private def context : EvalContext := {
  modulus := Field.modulus
  poseidon2 := fun _ _ _ => .error "the partial-write fixture does not use Poseidon2"
}

private def inputs (enabled : _root_.Bool) (left right wide : Nat)
    (approved : _root_.Bool) : EvalEnv :=
  [("enabled", .bool enabled), ("checkEnabled", .bool enabled),
    ("left", .uint 255 left), ("right", .uint 255 right),
    ("wide", .native wide), ("approved", .bool approved)]

private def fieldCell (value : Nat) : NativeState.Cell :=
  NativeState.field (NativeRelation.scalar value)

private def machine (values : List Nat) : NativeState.Machine :=
  ⟨[.vector (values.map fun value => .cell (fieldCell value))], []⟩

def main (args : List String) : IO Unit := do
  let [artifact] := args | throw (IO.userError "expected the guarded partial-write Impact plan")
  let bytes := (← IO.FS.readBinFile artifact).data.toList
  let raw ← IO.ofExcept (ArtifactBytes.parse bytes)
  let initial := machine [0, 0, 0, 0, 0]
  let runWith := fun env => ImpactPlanAgreement.runPlanBytes 64 context env bytes initial
  let enabled := inputs Bool.true 3 2 3 Bool.true
  let expected : List Nat := [1, 3, 7, 1, 3]
  let operations : List NativeState.Op := expected.zipIdx.flatMap fun (value, index) =>
    [.push (fieldCell index) Bool.false, .push (fieldCell value) Bool.true, .insert 1]
  unless decide (ImpactPlanAgreement.evaluatePlan 64 context enabled raw = some operations) do
    throw (IO.userError "decoded operation order differs from the guarded scalar fixture")
  unless decide (runWith enabled = some (machine expected)) &&
      decide (runWith (inputs Bool.false 1 2 8 Bool.false) = some initial) do
    throw (IO.userError "decoded active or inactive state differs from the guarded scalar fixture")
  unless (runWith (inputs Bool.true 1 2 3 Bool.true)).isNone &&
      (runWith (inputs Bool.true 3 2 8 Bool.true)).isNone &&
      (runWith (inputs Bool.true 3 2 3 Bool.false)).isNone do
    throw (IO.userError "decoded schedule accepted a partial scalar failure")
