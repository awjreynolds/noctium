import Noctium.Verification.GuardedImpactObservation
import Noctium.Verification.GuardedScalarRows
import Noctium.Verification.RangeDedupAcceptedEntrypoint

namespace Noctium.Verification.GuardedImpactTranscript

open Lean Backend NativeRelation GuardedScalarRows GuardedImpactObservation
open ScalarValidationMeaning ScalarValidationOutputMeaning RangeDedupAcceptedArray
open ScalarValidationArithmeticLoop (NativeDefinitions)
open ScalarValidationRawSeedMeaning

private theorem bind_ok {α β : Type} {first : Except ε α}
    {next : α → Except ε β} {result : β} :
    (first >>= next) = .ok result ↔
      ∃ value, first = .ok value ∧ next value = .ok result := by
  cases first <;> simp [Bind.bind, Except.bind]

/-- Check field-level constraints of the ordinary rows. Public input stream
consumption is a separate preprocessing obligation. Impact guards and their
payloads are interpreted through the ordered observation model below. -/
def ordinaryHolds (hash : Hash) (witness : Assignment) : Row → Prop
  | .strict instruction => instruction.Holds hash witness
  | .publicInput .. | .impact .. => True

/-- Interpret the Impact rows of an independently decoded stream in emission
order, preserving inactive groups and their padded widths. -/
def emittedObservations (witness : Assignment) : List Row → Option (List Observation)
  | [] => some []
  | .impact guard values :: rest => do
    let observation ← observeImpact (guard.read witness) (values.map (·.read witness))
    let tail ← emittedObservations witness rest
    pure (observation :: tail)
  | _ :: rest => emittedObservations witness rest

/-- Interpret the compiler's expected guard and payload at one group ordinal.
The guard defaults to true only when the whole guard schedule is empty. -/
def expectedObservationAt (hash : Hash) (inputs : Assignment) (expected : Native.Expected)
    (ordinal : Nat) : Option Observation := do
  let guard ← sourceImpactGuard expected {groupCount := ordinal}
  let group ← expected.groups[ordinal]?
  sourceObservation hash inputs guard group

def expectedObservations (hash : Hash) (inputs : Assignment) (expected : Native.Expected) :
    Option (List Observation) :=
  (List.range expected.groups.length).mapM (expectedObservationAt hash inputs expected)

private theorem classify_decoded_row {hash : Hash} {witness : Assignment} {raw : Json}
    {row : Row} (decoded : decodeRow raw = .ok row)
    (ordinary : ordinaryHolds hash witness row) : AcceptedMeaningStep hash witness raw := by
  cases row with
  | strict instruction =>
    have step := (decodeRow_strict decoded).1
    exact nativeDefinitionStep_supportsMeaning step hash witness (by
      intro found parsed
      have same := Except.ok.inj (parsed.symm.trans step.decoded)
      subst found
      exact ordinary)
  | publicInput output guard =>
    exact .native (.publicInput (decodeRow_publicInput_fields decoded).1)
  | impact guard values =>
    obtain ⟨opcode, guardDecoded, payloadDecoded⟩ := decodeRow_impact_fields decoded
    exact .guardedImpact opcode guardDecoded payloadDecoded

/-- Across a validated mixed scalar trace, each decoded Impact row consumes
one source group ordinal, including inactive rows. Ordinary and guarded public
input rows preserve the group ordinal. The same observation list is recovered
from the actual source schedule and the independently decoded row operands. -/
theorem checked_observation_schedule
    {hash : Hash} {inputs witness : Assignment} {expected : Native.Expected}
    {items : List (Json × Nat)} {rows : List Row} {initial final : Native.State}
    (decoded : (items.map Prod.fst).mapM decodeRow = .ok rows)
    (holds : ∀ row ∈ rows, ordinaryHolds hash witness row)
    (meaning : StateMeaning hash inputs witness initial)
    (definitions : NativeDefinitions initial)
    (inputSchema : ∀ requirement ∈ expected.inputs, requirement.ty.isForeign = false)
    (inputAgreement : ∀ requirement ∈ expected.inputs,
      witness requirement.identifier = inputs requirement.identifier)
    (accepted : Native.validateInstructionLoop expected items initial = .ok final) :
    ∃ observations,
      emittedObservations witness rows = some observations ∧
      final.groupCount = initial.groupCount + observations.length ∧
      (List.range' initial.groupCount observations.length).mapM
        (expectedObservationAt hash inputs expected) = some observations := by
  induction items generalizing initial final rows with
  | nil =>
    change Except.ok [] = Except.ok rows at decoded
    cases decoded
    have same : initial = final := by injection accepted
    subst final
    exact ⟨[], rfl, by simp, rfl⟩
  | cons item rest ih =>
    rcases item with ⟨raw, index⟩
    simp only [List.map_cons, List.mapM_cons, bind_ok] at decoded
    obtain ⟨row, rowDecoded, tail, tailDecoded, sameRows⟩ := decoded
    cases sameRows
    rw [Native.validateInstructionLoop, List.forIn_cons] at accepted
    cases checked : Native.validateInstruction expected initial raw with
    | error message => simp [checked, Bind.bind, Except.bind] at accepted
    | ok next =>
      simp only [checked, bind_pure_comp] at accepted
      have step := classify_decoded_row rowDecoded (holds row (by simp))
      have ⟨nextMeaning, nextDefinitions, _⟩ := acceptedMeaningStep_preserves
        meaning definitions inputSchema inputAgreement step checked
      obtain ⟨tailObservations, decodedTail, tailCount, sourceTail⟩ := ih
        tailDecoded (fun item member => holds item (List.mem_cons_of_mem _ member))
        nextMeaning nextDefinitions accepted
      have count := acceptedMeaningStep_groupCount_step definitions inputSchema step checked
      cases row with
      | strict instruction =>
        have notImpact := (decodeRow_strict rowDecoded).2
        have notImpactRow : impactOpcodeRow raw = false := by
          unfold impactOpcodeRow
          cases parsed : Native.stringField raw "op" with
          | error _ => rfl
          | ok opcode =>
            have ordinaryOpcode : opcode ≠ "impact" := by
              intro same
              subst opcode
              exact notImpact parsed
            simp [ordinaryOpcode]
        have sameOrdinal : next.groupCount = initial.groupCount := by
          simpa [notImpactRow] using count
        rw [sameOrdinal] at tailCount sourceTail
        exact ⟨tailObservations, decodedTail, tailCount, sourceTail⟩
      | publicInput output guard =>
        have opcode := (decodeRow_publicInput_fields rowDecoded).1
        have sameOrdinal : next.groupCount = initial.groupCount := by
          simpa [impactOpcodeRow, opcode] using count
        rw [sameOrdinal] at tailCount sourceTail
        exact ⟨tailObservations, decodedTail, tailCount, sourceTail⟩
      | impact guard values =>
        obtain ⟨opcode, guardDecoded, payloadDecoded⟩ := decodeRow_impact_fields rowDecoded
        obtain ⟨guardTerm, group, observation, selectedGuard, selectedGroup, nextShape,
          observedSource, observedRow, _⟩ :=
          accepted_impact_observation meaning checked opcode guardDecoded payloadDecoded
        have nextOrdinal : next.groupCount = initial.groupCount + 1 :=
          congrArg Native.State.groupCount nextShape
        have sourceHead : expectedObservationAt hash inputs expected initial.groupCount =
            some observation := by
          change (do
            let guard ← sourceImpactGuard expected initial
            let group ← expected.groups[initial.groupCount]?
            sourceObservation hash inputs guard group) = _
          simp [selectedGuard, selectedGroup, observedSource]
        refine ⟨observation :: tailObservations, ?_, ?_, ?_⟩
        · simp [emittedObservations, observedRow, decodedTail]
        · simp only [List.length_cons]
          omega
        · rw [List.length_cons, List.range'_succ, ← nextOrdinal]
          simp [List.mapM_cons, sourceHead, sourceTail]

/-- Tie every guarded Impact observation to the actual emitted ZKIR and
accepted expected schedule. A false guard preserves the group and its padded
field width. The transcript advances only through active payloads. -/
theorem lowerEntrypoint_guardedImpactTranscript
    {state : List StateDecl} {entry : Entrypoint} (rewrites : Zkir.Rewrites)
    {json : Json} {instructions : Array Json} {rows : List Row}
    (lowered : Zkir.lowerEntrypoint state entry rewrites = .ok json)
    (instructionsParsed : Native.arrayField json "instructions" = .ok instructions)
    (decoded : instructions.toList.mapM decodeRow = .ok rows)
    (schema : ∀ expected,
      Native.expectedEntrypoint state (Passes.pruneEntrypoint entry) = .ok expected →
        ∀ requirement ∈ expected.rawInputs ++ expected.inputs,
          requirement.ty.isForeign = false) :
    ∃ (plan : Impact.Plan) (expected : Native.Expected) (aliases : Native.AliasEnvironment),
      Impact.lower state (Passes.pruneEntrypoint entry) = .ok plan ∧
      Native.expectedEntrypoint state (Passes.pruneEntrypoint entry) = .ok expected ∧
      (∀ ordinal : Nat,
        ((GenericStateCircuitParts.activityGuardSources plan)[ordinal]?.mapM
          (GenericStateCircuitParts.normalizeActivityGuard (Passes.pruneEntrypoint entry) aliases)).map
            (Option.map (·.term)) = .ok expected.groupGuards[ordinal]?) ∧
      ∀ {hash witness}, (∀ row ∈ rows, ordinaryHolds hash witness row) →
        ∃ observations,
          emittedObservations witness rows = some observations ∧
          expectedObservations hash witness expected = some observations ∧
          ∀ transcript remaining,
            consumeTranscript observations transcript = some remaining ↔
              transcript = activePayloads observations ++ remaining := by
  obtain ⟨plan, expected, planAccepted, expectedAccepted, validated, _⟩ :=
    Zkir.lowerEntrypoint_validation_and_instructions_with_rewrites
      state entry rewrites json lowered
  let optimized := Zkir.optimizedExpected rewrites expected
  obtain ⟨actualInstructions, _, seed, final, driver⟩ :=
    ScalarValidationProjection.validate_driver_result (expected := optimized) validated
  have sameInstructions := Except.ok.inj (driver.instructionsParsed.symm.trans instructionsParsed)
  subst actualInstructions
  have indexedDecoded : (instructions.toList.zipIdx.map Prod.fst).mapM decodeRow = .ok rows := by
    simpa only [List.zipIdx_map_fst] using decoded
  have inputsUnchanged : optimized.rawInputs ++ optimized.inputs =
      expected.rawInputs ++ expected.inputs := by cases rewrites <;> rfl
  have schemaOptimized : ∀ requirement ∈ optimized.rawInputs ++ optimized.inputs,
      requirement.ty.isForeign = false := by
    simpa only [inputsUnchanged] using schema expected expectedAccepted
  have rawSchema : ∀ requirement ∈ optimized.rawInputs, requirement.ty.isForeign = false :=
    fun requirement member => schemaOptimized requirement (List.mem_append_left _ member)
  have inputSchema : ∀ requirement ∈ optimized.inputs, requirement.ty.isForeign = false :=
    fun requirement member => schemaOptimized requirement (List.mem_append_right _ member)
  have seedCount := seedRawInputs_groupCount rawSchema driver.seededRawInputs
  obtain ⟨guardPlan, aliases, guardPlanAccepted, sourceGuards⟩ :=
    GenericStateCircuitParts.expectedEntrypoint_activityGuard_at
      state (Passes.pruneEntrypoint entry) expected expectedAccepted
  have samePlan := Except.ok.inj (guardPlanAccepted.symm.trans planAccepted)
  subst guardPlan
  refine ⟨plan, expected, aliases, planAccepted, expectedAccepted, sourceGuards, ?_⟩
  intro hash witness holds
  obtain ⟨seedMeaning, seedDefinitions⟩ :=
    seedRawInputs_meaning_and_nativeDefinitions (hash := hash) (inputs := witness)
      (witness := witness) rawSchema (fun _ _ => rfl) driver.seededRawInputs
  obtain ⟨observations, emitted, count, source⟩ := checked_observation_schedule indexedDecoded
    holds seedMeaning seedDefinitions inputSchema (fun _ _ => rfl) driver.instructionTrace
  have countExact : optimized.groups.length = observations.length := by
    simpa only [driver.groupCount, seedCount, Nat.zero_add] using count
  have sourceExact : expectedObservations hash witness optimized = some observations := by
    simpa only [seedCount, ← List.range_eq_range', ← countExact, expectedObservations] using source
  have expectedUnchanged :
      expectedObservations hash witness optimized = expectedObservations hash witness expected := by
    cases rewrites <;> rfl
  exact ⟨observations, emitted, expectedUnchanged.symm.trans sourceExact, fun transcript remaining =>
    consumeTranscript_iff observations transcript remaining⟩

end Noctium.Verification.GuardedImpactTranscript
