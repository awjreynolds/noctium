import Noctium.Compiler
import Noctium.Verification.NativeRelationJson
import tests.UInt128BoundProbe

open Noctium

private def checkArtifact (path expected : String) : IO Unit := do
  let contents ← IO.FS.readFile path
  unless contents == expected ++ "\n" do
    throw (IO.userError s!"emitted artifact differs from production lowering at {path}")

private def exactUInt128ReadArtifacts : IO Unit := do
  let some directory ← IO.getEnv "NOCTIUM_UINT128_READ_BOUND_ARTIFACT_DIR"
    | throw (IO.userError "artifact check requires NOCTIUM_UINT128_READ_BOUND_ARTIFACT_DIR")
  let operation ← match Backend.LedgerReadOptimization.lower
      UInt128BoundProbe "readSupply" "totalSupply" "current" with
    | .ok operation => pure operation
    | .error error => throw (IO.userError s!"production UInt128 read lowering failed: {error}")
  let stem := "UInt128BoundProbe.readSupply"
  checkArtifact s!"{directory}/strict/{stem}.zkir" operation.strict.pretty
  checkArtifact s!"{directory}/optimized/{stem}.zkir" operation.optimized.pretty
  let some sourceEntry := UInt128BoundProbe.entrypoints.find? (·.name == "readSupply")
    | throw (IO.userError "UInt128BoundProbe is missing readSupply")
  let expectedImpact := Compiler.nativePlanJson TargetProfile.selected321
    (Lean.Name.mkSimple "UInt128BoundProbe") UInt128BoundProbe.state
    UInt128BoundProbe.constructor (Passes.pruneEntrypoint sourceEntry) operation.plan
    _root_.Bool.false
  checkArtifact s!"{directory}/strict/{stem}.impact.json" expectedImpact.compress
  checkArtifact s!"{directory}/optimized/{stem}.impact.json" expectedImpact.compress
  let strictRelation ← match Verification.NativeRelationJson.decode operation.strict with
    | .ok relation => pure relation
    | .error error => throw (IO.userError s!"fresh strict ZKIR was rejected: {error}")
  let optimizedRelation ← match Verification.NativeRelationJson.decode operation.optimized with
    | .ok relation => pure relation
    | .error error => throw (IO.userError s!"fresh optimized ZKIR was rejected: {error}")
  unless strictRelation.instructions.length == optimizedRelation.instructions.length + 1 &&
      strictRelation.instructions[operation.rangeIndex]? ==
        some (.bits (.reference operation.proofInput) 128) do
    throw (IO.userError "fresh optimized relation did not remove exactly its certified UInt128 range")
  let instructions ← match operation.optimized.getObjVal? "instructions" >>= Lean.Json.getArr? with
    | .ok instructions => pure instructions
    | .error error => throw (IO.userError s!"optimized ZKIR has no instructions: {error}")
  let wrongOutput := Lean.Json.mkObj [
    ("op", Lean.toJson ("output" : String)),
    ("vals", Lean.Json.arr #[Lean.toJson ("0x00" : String)])]
  let changedInstructions := instructions.pop.push wrongOutput
  let changedZkir := match operation.optimized with
    | .obj fields => Lean.Json.obj (fields.insert "instructions" (.arr changedInstructions))
    | _ => operation.optimized
  match Verification.NativeRelationJson.decode changedZkir with
  | .error error => throw (IO.userError s!"wrong-output mutation was rejected by the decoder: {error}")
  | .ok changedRelation => do
    let assignmentFn (identifier : String) :=
      if identifier == operation.proofInput then Verification.NativeRelation.one
      else Verification.NativeRelation.zero
    unless optimizedRelation.returns assignmentFn == [Verification.NativeRelation.one] do
      throw (IO.userError "reference optimized relation failed the nonzero return control")
    unless changedRelation.returns assignmentFn == [Verification.NativeRelation.zero] do
      throw (IO.userError "wrong-output mutation did not change the nonzero return to zero")

#eval exactUInt128ReadArtifacts
