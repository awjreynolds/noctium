import Noctium.Frontend
import Noctium.Verification.ArtifactBytes
import Noctium.Verification.RangeDedupKernel
import Noctium.Verification.NativeRelationJson

/-
This pilot exercises one public UInt 8 ledger entry with two casts of the same
immutable SSA input. The selected profile is ZKIR 3.2.1. The range-only pass
removes duplicate bounds. The source has no less-than comparisons, so comparison
reuse leaves the non-range instruction sequence unchanged.

The kernel theorem below proves the checked scalar relation fragment. The
retained ZKIR files supply literal octets, which the elected CLI check compares
against fresh output bytes. `ArtifactBytes.parse` and native
relation decoding reduce under `decide +kernel` for these exact artifacts.
The native backend and external verifier remain outside this Lean model. The
repository has no generic checked decoder for `.impact.json`; this fixture
checks both serialized typed Impact plans, while the paired CLI byte check
compares the complete files.
-/

open Lean Noctium
open Noctium.Backend
open Noctium.Verification.NativeRelation
open scoped Noctium

noctium_circuit rangeDedupArtifactPilot where
  public value : UInt 8
  public marker : Native
  output first : UInt 8 := disclose(cast(UInt 8, value))
  output middle : Native := disclose(marker)
  output last : UInt 8 := disclose(cast(UInt 8, value))
end

noctium_contract RangeDedupArtifactPilot where
  entry echo uses rangeDedupArtifactPilot where
    return firstResult : UInt 8 := first
    return middleResult : Native := middle
    return lastResult : UInt 8 := last
  end
end

private def echoEntrypoint : Entrypoint :=
  (RangeDedupArtifactPilot.entrypoints.find? (·.name == "echo")).getD
    {name := "missing", circuit := {name := "missing"}}

private def prunedEchoEntrypoint : Entrypoint := Passes.pruneEntrypoint echoEntrypoint

private def sourceExpected : Native.Expected :=
  (Native.expectedEntrypoint RangeDedupArtifactPilot.state prunedEchoEntrypoint).toOption.getD
    {mode := .ledgerCall, inputs := [], rawInputs := [], groups := [], returns := [], assertions := [], bounds := []}

local elab "fixture_bytes " name:str : term => do
  let source := System.FilePath.mk (← readThe Lean.Core.Context).fileName
  let some directory := source.parent | throwError "expected fixture source directory"
  let bytes ← IO.FS.readBinFile (directory / name.getString)
  Lean.Meta.mkListLit (mkConst ``UInt8) (bytes.data.toList.map fun byte =>
    mkApp (mkConst ``UInt8.ofNat) (mkNatLit byte.toNat))

private def defaultArtifactBytes : Noctium.Verification.ArtifactBytes.Bytes :=
  fixture_bytes "fixtures/range-dedup/default.zkir"

private def deduplicatedArtifactBytes : Noctium.Verification.ArtifactBytes.Bytes :=
  fixture_bytes "fixtures/range-dedup/deduplicated.zkir"

private def defaultArtifact : Json := Noctium.Verification.ArtifactBytes.tree defaultArtifactBytes
private def deduplicatedArtifact : Json := Noctium.Verification.ArtifactBytes.tree deduplicatedArtifactBytes
private def rangeInstructions (artifact : Json) : Array Json :=
  (Noctium.Verification.NativeRelationJson.arrayField artifact "instructions").toOption.getD #[]

private def emptyProgram : Program :=
  {instructions := [], outputArity := 0, communicationsCommitment := _root_.Bool.false}

private def decodedProgram (artifact : Json) : Program :=
  (Noctium.Verification.NativeRelationJson.decode artifact).toOption.getD emptyProgram

private def defaultInstructions : Array Json := rangeInstructions defaultArtifact
private def deduplicatedInstructions : Array Json := rangeInstructions deduplicatedArtifact
private def defaultProgram : Program := decodedProgram defaultArtifact
private def deduplicatedProgram : Program := decodedProgram deduplicatedArtifact

private def validArtifact (artifact : Json) : _root_.Bool :=
  match Noctium.Verification.NativeRelationJson.decode artifact with
  | .error _ => _root_.Bool.false
  | .ok _ => (Native.validate sourceExpected artifact).isOk

private def replaceInstructions (artifact : Json) (instructions : Array Json) : Json :=
  Json.mkObj (((artifact.getObj?).toOption.getD {}).toList.map fun (name, value) =>
    if name == "instructions" then (name, Json.arr instructions) else (name, value))

private def instructionIs (name : String) (instruction : Json) : _root_.Bool :=
  (Noctium.Verification.NativeRelationJson.stringField instruction "op").toOption == some name

private def firstTwoPublicInputs : Option (Nat × Nat) := do
  let indexes := defaultInstructions.toList.zipIdx.filterMap fun (instruction, index) =>
    if instructionIs "public_input" instruction then some index else none
  let first :: second :: _ := indexes | none
  pure (first, second)

private def swapEntries (items : Array Json) (first second : Nat) : Array Json := Id.run do
  let some left := items[first]? | return items
  let some right := items[second]? | return items
  return (items.set! first right).set! second left

private def removeFirstOp (name : String) (items : Array Json) : Array Json :=
  (go items.toList _root_.Bool.false).toArray
where
  go : List Json → _root_.Bool → List Json
    | [], _ => []
    | item :: rest, removed =>
      if !removed && instructionIs name item then go rest _root_.Bool.true
      else item :: go rest removed

private def replaceField (item : Json) (name : String) (value : Json) : Json :=
  Json.mkObj (((item.getObj?).toOption.getD {}).toList.filter (·.1 != name) ++ [(name, value)])

private def malformedRange : Array Json := Id.run do
  for index in [:defaultInstructions.size] do
    let item := defaultInstructions[index]!
    if instructionIs "constrain_bits" item then
      return defaultInstructions.set! index (replaceField item "bits" (toJson (0 : Nat)))
  return defaultInstructions

private def alteredRequiredRange : Array Json :=
  defaultInstructions.filter (fun item =>
    (Noctium.Verification.NativeRelationJson.stringField item "op").toOption != some "constrain_bits")

private theorem checkedDecode :
    ((Noctium.Verification.ArtifactBytes.parse defaultArtifactBytes).bind
      Noctium.Verification.NativeRelationJson.decode).isOk = .true ∧
    ((Noctium.Verification.ArtifactBytes.parse deduplicatedArtifactBytes).bind
      Noctium.Verification.NativeRelationJson.decode).isOk = .true := by
  decide +kernel

private theorem sameNonRangeInstructions :
    defaultProgram.instructions.filter Noctium.Verification.RangeDedup.nonRange =
      deduplicatedProgram.instructions.filter Noctium.Verification.RangeDedup.nonRange := by
  decide +kernel

private theorem equivalentInstructionMembership :
    ∀ instruction, instruction ∈ defaultProgram.instructions ↔
      instruction ∈ deduplicatedProgram.instructions := by
  have erased : defaultProgram.instructions.eraseDups = deduplicatedProgram.instructions := by
    decide +kernel
  intro instruction
  rw [← erased]
  exact List.mem_eraseDups.symm

#guard defaultProgram.outputArity == 3 && defaultProgram.communicationsCommitment
#guard deduplicatedProgram.outputArity == 3 && deduplicatedProgram.communicationsCommitment
#guard (defaultInstructions.filter (fun item =>
    (Noctium.Verification.NativeRelationJson.stringField item "op").toOption == some "constrain_bits")).size == 3
#guard (deduplicatedInstructions.filter (fun item =>
    (Noctium.Verification.NativeRelationJson.stringField item "op").toOption == some "constrain_bits")).size == 1
#guard (defaultInstructions.filter (fun item =>
    (Noctium.Verification.NativeRelationJson.stringField item "op").toOption != some "constrain_bits")) ==
  (deduplicatedInstructions.filter (fun item =>
    (Noctium.Verification.NativeRelationJson.stringField item "op").toOption != some "constrain_bits"))

#guard validArtifact defaultArtifact
#guard validArtifact deduplicatedArtifact
#guard !(validArtifact (replaceInstructions defaultArtifact alteredRequiredRange))
#guard !(validArtifact (match firstTwoPublicInputs with
  | some (first, second) => replaceInstructions defaultArtifact
      (swapEntries defaultInstructions first second)
  | none => defaultArtifact))
#guard !(validArtifact (replaceInstructions defaultArtifact (removeFirstOp "impact" defaultInstructions)))
#guard !(Noctium.Verification.NativeRelationJson.decode
  (replaceInstructions defaultArtifact malformedRange)).isOk

theorem exactArtifactKernelPreservation
    (hash : Hash) (streams : InputStreams) (assignment : Assignment)
    (groups : List (List Scalar)) (returns : List Scalar) :
      Satisfies hash defaultProgram streams assignment groups returns ↔
        Satisfies hash deduplicatedProgram streams assignment groups returns := by
  apply Noctium.Verification.RangeDedupKernel.satisfies_iff hash streams assignment
    groups returns sameNonRangeInstructions
  constructor
  · intro leftHolds instruction mem
    exact leftHolds instruction (equivalentInstructionMembership instruction |>.mpr mem)
  · intro rightHolds instruction mem
    exact rightHolds instruction (equivalentInstructionMembership instruction |>.mp mem)

private def evaluationContext : EvalContext := {
  modulus := Field.modulus
  poseidon2 := fun _ _ _ => .error "unused by the range dedup pilot"}

private def impactEnvironment : EvalEnv := [
  ("value", .uint 255 5), ("marker", .native 17),
  ("first", .uint 255 5), ("middle", .native 17), ("last", .uint 255 5)]

private def ledgerArtifactPair (deduplicate : _root_.Bool) :=
  Zkir.lowerPrunedEntrypoint RangeDedupArtifactPilot.state prunedEchoEntrypoint
    (if deduplicate then .rangeAndAssertions else .disabled)

#guard (ledgerArtifactPair _root_.Bool.false).isOk
#guard (ledgerArtifactPair _root_.Bool.true).isOk

#guard match ledgerArtifactPair _root_.Bool.false with
  | .ok (_, relation) => (Native.validate sourceExpected relation).isOk
  | .error _ => _root_.Bool.false
#guard match ledgerArtifactPair _root_.Bool.true with
  | .ok (_, relation) => (Native.validate sourceExpected relation).isOk
  | .error _ => _root_.Bool.false
#guard match ledgerArtifactPair _root_.Bool.false, ledgerArtifactPair _root_.Bool.true with
  | .ok (defaultPlan, _), .ok (deduplicatedPlan, _) =>
    match Impact.Plan.toJson evaluationContext impactEnvironment defaultPlan,
        Impact.Plan.toJson evaluationContext impactEnvironment deduplicatedPlan with
    | .ok defaultImpact, .ok deduplicatedImpact =>
      defaultImpact.compress == deduplicatedImpact.compress
    | _, _ => _root_.Bool.false
  | _, _ => _root_.Bool.false
