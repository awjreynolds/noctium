import Noctium.Frontend
import Noctium.Verification.ArtifactBytes
import Noctium.Verification.RangeDedupKernel
import Noctium.Verification.RangeDedupAcceptedArray
import Noctium.Verification.NativeRelationJson
import Noctium.Verification.ScalarInstructionEncoding

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

private def booleanRangeInstruction (opcode : String) (fields : List (String × Json)) : Json :=
  Json.mkObj (("op", toJson opcode) :: fields)

private def booleanRangeInput : Json := booleanRangeInstruction "private_input" [
  ("guard", Json.null), ("type", toJson ("Scalar<BLS12-381>" : String)),
  ("output", toJson ("%v0" : String))]

private def booleanRangeCheck : Json :=
  booleanRangeInstruction "constrain_to_boolean" [("val", toJson ("%v0" : String))]

private def booleanRangeLess (destination : String) : Json := booleanRangeInstruction "less_than" [
  ("a", toJson ("%v0" : String)), ("b", toJson ("0x01" : String)),
  ("bits", toJson (1 : Nat)), ("output", toJson destination)]

private def booleanRangeOutput : Json := booleanRangeInstruction "output" [
  ("vals", toJson ([] : List String))]

private def booleanRangeSource : Array Json := #[booleanRangeInput, booleanRangeCheck,
  booleanRangeLess "%v1", booleanRangeLess "%v2", booleanRangeOutput]

private def booleanRangeOptimized : Array Json :=
  Noctium.Backend.RangeDedup.reuseComparisons booleanRangeSource

private def booleanRangeOriginalInstructions : List Instruction := [
  .input .«private» "%v0",
  .boolean (.reference "%v0"),
  .lessThan (.reference "%v0") (.immediate (scalar 1)) 1 "%v1",
  .lessThan (.reference "%v0") (.immediate (scalar 1)) 1 "%v2",
  .output []]

private def booleanRangeOptimizedInstructions : List Instruction := [
  .input .«private» "%v0",
  .boolean (.reference "%v0"),
  .lessThan (.reference "%v0") (.immediate (scalar 1)) 1 "%v1",
  .equal (.reference "%v1") (.reference "%v2"),
  .output []]

private def booleanRangeOriginalProgram : Program := {
  instructions := booleanRangeOriginalInstructions
  outputArity := 0
  communicationsCommitment := _root_.Bool.false
}

private theorem booleanRangeSourceDecoded :
    booleanRangeSource.toList.mapM Noctium.Verification.NativeRelationJson.decodeInstruction =
      .ok booleanRangeOriginalInstructions := by
  have parsed : (booleanRangeSource.toList.mapM
      Noctium.Verification.NativeRelationJson.decodeInstruction).toOption =
      some booleanRangeOriginalInstructions := by
    decide +kernel
  cases result : booleanRangeSource.toList.mapM
      Noctium.Verification.NativeRelationJson.decodeInstruction with
  | error message => simp [result, Except.toOption] at parsed
  | ok instructions => simpa [result, Except.toOption] using parsed

private theorem booleanRangeEvidence :
    Noctium.Verification.RangeDedup.ComparisonBitChecks booleanRangeOriginalInstructions := by
  unfold Noctium.Verification.RangeDedup.ComparisonBitChecks
  intro left right width destination hmem
  simp [booleanRangeOriginalInstructions] at hmem
  rcases hmem with first | second
  · rcases first with ⟨rfl, rfl, rfl, rfl⟩
    constructor
    · exact Or.inr (Or.inr ⟨by decide, by simp [booleanRangeOriginalInstructions]⟩)
    · exact Or.inr (Or.inl ⟨scalar 1, rfl, by decide⟩)
  · rcases second with ⟨rfl, rfl, rfl, rfl⟩
    constructor
    · exact Or.inr (Or.inr ⟨by decide, by simp [booleanRangeOriginalInstructions]⟩)
    · exact Or.inr (Or.inl ⟨scalar 1, rfl, by decide⟩)

theorem booleanRangeReuseKernelPreservation
    (hash : Hash) (streams : InputStreams) (assignment : Assignment)
    (groups : List (List Scalar)) (returns : List Scalar) :
    ∃ optimized : Program,
      booleanRangeOptimized.toList.mapM Noctium.Verification.NativeRelationJson.decodeInstruction =
        .ok optimized.instructions ∧
      (Satisfies hash booleanRangeOriginalProgram streams assignment groups returns ↔
        Satisfies hash optimized streams assignment groups returns) := by
  obtain ⟨instructions, parsed, _, _⟩ :=
    Noctium.Verification.RangeDedup.reuseComparisons_preserves_decoded
      booleanRangeSource booleanRangeOriginalInstructions booleanRangeSourceDecoded booleanRangeEvidence
  let optimized : Program := {booleanRangeOriginalProgram with instructions}
  refine ⟨optimized, parsed, ?_⟩
  exact Noctium.Verification.RangeDedupKernel.parsed_reuseComparisons_preserves_kernel
    booleanRangeSource booleanRangeOriginalProgram optimized
    booleanRangeSourceDecoded parsed booleanRangeEvidence hash streams assignment groups returns

#guard (booleanRangeOptimized.toList.mapM
  Noctium.Verification.NativeRelationJson.decodeInstruction).toOption == some booleanRangeOptimizedInstructions

private def booleanRangeExpected : Native.Expected := {
  mode := .relation
  inputs := [{identifier := "%v0", visibility := .«private», ty := .native}]
  groups := []
  returns := []
  assertions := []
  bounds := []
}

private def booleanRangeRelation (instructions : Array Json) : Json := Json.mkObj [
  ("version", Json.mkObj [("major", toJson (3 : Nat)), ("minor", toJson (2 : Nat))]),
  ("inputs", Json.arr #[]), ("outputs", Json.arr #[]),
  ("do_communications_commitment", Json.bool (_root_.Bool.false)),
  ("instructions", Json.arr instructions)]

#guard (Native.validate booleanRangeExpected (booleanRangeRelation booleanRangeSource)).isOk
#guard (Native.validate booleanRangeExpected (booleanRangeRelation booleanRangeOptimized)).isOk
#guard (Native.validateInstructionLoop booleanRangeExpected
  (booleanRangeSource.toList.zipIdx) {}).isOk

private def booleanRangeOptimizedProgram : Program :=
  {booleanRangeOriginalProgram with instructions := booleanRangeOptimizedInstructions}

private theorem booleanRangeSupportsMeaning :
    ∀ raw ∈ booleanRangeSource.toList,
      Noctium.Verification.RangeDedupAcceptedArray.SupportsMeaning raw :=
  Noctium.Verification.RangeDedupAcceptedArray.supportsMeaning_of_checkedScalarOpcodeProfile
    booleanRangeSource booleanRangeSourceDecoded (by native_decide)

theorem booleanRangeAcceptedArrayReuseKernelPreservation
    (final : Native.State)
    (accepted : Native.validateInstructionLoop booleanRangeExpected
      (booleanRangeSource.toList.zipIdx) {} = .ok final)
    (runDecoded : (Noctium.Backend.RangeDedup.reuseComparisons booleanRangeSource).toList.mapM
      Noctium.Verification.NativeRelationJson.decodeInstruction =
        .ok booleanRangeOptimizedInstructions)
    (hash : Hash) (streams : InputStreams) (assignment : Assignment)
    (groups : List (List Scalar)) (returns : List Scalar) :
    Satisfies hash booleanRangeOriginalProgram streams assignment groups returns ↔
      Satisfies hash booleanRangeOptimizedProgram streams assignment groups returns := by
  exact Noctium.Verification.RangeDedupAcceptedArray.acceptedArrayReusePreservesKernel
    (initialMeaning := by
      intro hash candidate identifier fact hmem
      simp at hmem)
    (initialDefinitions := by
      intro identifier fact hmem
      simp at hmem)
    (inputSchema := by
      intro requirement hmem
      simp [booleanRangeExpected] at hmem
      subst requirement
      rfl)
    (steps := booleanRangeSupportsMeaning)
    (sourceDecoded := booleanRangeSourceDecoded)
    (runDecoded := runDecoded)
    (accepted := accepted)
    hash streams assignment groups returns

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
