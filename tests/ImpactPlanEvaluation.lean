import Noctium.Verification.ImpactPreviewBinding
import Noctium.Verification.ImpactStatementScalar
import Noctium.Verification.ImpactPlanAgreement
import Noctium.Verification.ImpactTranscriptSchedule

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

-- A present empty partition consumes leading skips before the fallible program.
#guard
  match ImpactCallPreview.previewCall ⟨3, 2⟩
      ⟨some ⟨([] : List Nat), 7⟩, some ⟨[9], 11⟩⟩ [some 2, none, some 3] with
  | some ⟨some ⟨[.noop 2], 14⟩, some ⟨[.active 9, .noop 3], 20⟩⟩ => Bool.true
  | _ => Bool.false

def main (args : List String) : IO Unit := do
  let [artifact] := args | throw (IO.userError "expected the guarded partial-write Impact plan")
  let bytes := (← IO.FS.readBinFile artifact).data.toList
  let raw ← IO.ofExcept (ArtifactBytes.parse bytes)
  let initial := machine [0, 0, 0, 0, 0]
  let runWith := fun env => ImpactPlanAgreement.runPlanBytes 64 context env bytes initial
  let enabled := inputs Bool.true 3 2 3 Bool.true
  let disabled := inputs Bool.false 1 2 8 Bool.false
  let transcript := fun env => ImpactTranscriptSchedule.evaluateSchedule 64 context env (fun _ => none) raw
  let skipped : List (Option Nat) := (List.replicate 5 [some 5, some 5, some 1]).flatten
  unless transcript enabled == some (List.replicate 15 none) &&
      transcript disabled == some skipped do
    throw (IO.userError "decoded activity schedule differs from the guarded scalar fixture")
  -- The fixture supplies test bytes at the effects and parent commitment boundaries.
  let metadata : ImpactPreviewBinding.Metadata := {
    address := ByteArray.mk (Array.replicate 32 0)
    entryPoint := "update".toUTF8
    guaranteed := some ⟨1, 2, 3, ByteArray.mk #[13, 14]⟩
    fallible := none
    parentPedersen := ByteArray.mk (#[1] ++ Array.replicate 31 0)
  }
  let commitment := NativeRelation.scalar 5
  let inactiveBinding := NativeRelation.scalar
    28275337270660864951591803471226560440628912649504939734825220606033283957
  let activeBinding :=
    376973846635362786591406240642568956494276904876123793983990665364314846599
  let preview := fun program activity => ImpactCallPreview.previewCall
    {noopConstant := 3, noopCoefficient := 2}
    {guaranteed := some ⟨program, 7⟩, fallible := none} activity
  let inactivePreview := do
    let activity ← transcript disabled
    let program ← ImpactPlanAgreement.evaluatePlan 64 context disabled raw
    preview program activity
  match inactivePreview with
  | some call =>
      let some header := ImpactPreviewBinding.header metadata call commitment |
        throw (IO.userError "inactive binding serialization rejected")
      unless decide (ImpactCallStatement.publicInputs ImpactStatementScalar.opFields header call =
          some ([inactiveBinding, commitment] ++
            List.replicate 55 NativeRelation.zero)) do
        throw (IO.userError "inactive statement differs in header or skipped fields")
      match call with
      | ⟨some ⟨[.noop 55], 120⟩, none⟩ => pure ()
      | _ => throw (IO.userError "inactive preview differs in skipped width or compute time")
  | none => throw (IO.userError "inactive preview rejected")
  let activeStatement : Option (List NativeRelation.Scalar) := do
    let activity ← transcript enabled
    let program ← ImpactPlanAgreement.evaluatePlan 64 context enabled raw
    let call ← preview program activity
    let header ← ImpactPreviewBinding.header metadata call commitment
    ImpactCallStatement.publicInputs ImpactStatementScalar.opFields header call
  let expected : List Nat := [1, 3, 7, 1, 3]
  let writeFields : List Nat := expected.zipIdx.flatMap fun (value, index) =>
    [0x10, 1, 1, Field.modulus - 2, index,
      0x11, 1, 1, Field.modulus - 2, value, 0x91]
  unless decide (activeStatement = some (([activeBinding, 5] ++ writeFields).map NativeRelation.scalar)) do
    throw (IO.userError "active statement differs in the ordered native write fields")
  let operations : List NativeState.Op := expected.zipIdx.flatMap fun (value, index) =>
    [.push (fieldCell index) Bool.false, .push (fieldCell value) Bool.true, .insert 1]
  unless decide (ImpactPlanAgreement.evaluatePlan 64 context enabled raw = some operations) do
    throw (IO.userError "decoded operation order differs from the guarded scalar fixture")
  unless decide (runWith enabled = some (machine expected)) &&
      decide (runWith disabled = some initial) do
    throw (IO.userError "decoded active or inactive state differs from the guarded scalar fixture")
  unless (runWith (inputs Bool.true 1 2 3 Bool.true)).isNone &&
      (runWith (inputs Bool.true 3 2 8 Bool.true)).isNone &&
      (runWith (inputs Bool.true 3 2 3 Bool.false)).isNone do
    throw (IO.userError "decoded schedule accepted a partial scalar failure")
