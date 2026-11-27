import Noctium.Verification.GuardedImpactTranscript
import Noctium.Verification.GuardedScalarWitnessAssembly
import Noctium.Verification.RangeDedupAcceptedArray
import Noctium.Verification.ScalarValidationProjection
import Noctium.Verification.ScalarValidationRawSeedMeaning
import Noctium.Verification.ScalarNormalization
import Noctium.Verification.ScalarLowering

namespace Noctium.Verification.GuardedZkirRequirements

open Lean Backend Native NativeRelation GuardedScalarRows GuardedImpactTranscript
open ScalarValidationMeaning ScalarValidationProjection
open ScalarValidationArithmeticLoop (NativeDefinitions)
open ScalarValidationRawSeedMeaning
open ScalarNormalization (interpret)
open RangeDedupAssertMeaning (CheckedAssertions)
open RangeDedupAcceptedArray (AcceptedMeaningStep)

private theorem bind_ok {α β : Type} {first : Except String α}
    {next : α → Except String β} {result : β} :
    (first >>= next) = .ok result ↔
      ∃ value, first = .ok value ∧ next value = .ok result := by
  cases first <;> simp [Bind.bind, Except.bind]

private theorem mapM_decoded_member {items : List α} {decodedValues : List β}
    (decode : α → Except String β)
    (decoded : items.mapM decode = .ok decodedValues)
    {item : α} (present : item ∈ items) :
    ∃ value ∈ decodedValues, decode item = .ok value := by
  induction items generalizing decodedValues with
  | nil => simp at present
  | cons head tail ih =>
    cases headDecoded : decode head with
    | error reason => simp [List.mapM_cons, headDecoded, Bind.bind, Except.bind] at decoded
    | ok headValue =>
      cases tailDecoded : tail.mapM decode with
      | error reason =>
        simp [List.mapM_cons, headDecoded, tailDecoded, Bind.bind, Except.bind] at decoded
      | ok tailValues =>
        simp [List.mapM_cons, headDecoded, tailDecoded, Bind.bind, Except.bind,
          Pure.pure, Except.pure] at decoded
        subst decodedValues
        rcases List.mem_cons.mp present with same | later
        · subst item
          exact ⟨headValue, List.mem_cons_self .., headDecoded⟩
        · obtain ⟨value, inTail, itemDecoded⟩ := ih tailDecoded later
          exact ⟨value, List.mem_cons_of_mem _ inTail, itemDecoded⟩

/-- The accepted mixed-row fold exposes source requirements and the producer
meaning before and after each actual indexed row. Output consumers use the row
visit to interpret the output at its producer ordinal. -/
theorem lowerEntrypoint_guardedRows_meaning
    {state : List StateDecl} {entry : Entrypoint} (rewrites : Zkir.Rewrites)
    {json : Json} {instructions : Array Json} {rows : List Row}
    (lowered : Zkir.lowerEntrypoint state entry rewrites = .ok json)
    (instructionsParsed : Native.arrayField json "instructions" = .ok instructions)
    (decoded : instructions.toList.mapM GuardedScalarRows.decodeRow = .ok rows)
    (schema : ∀ expected,
      Native.expectedEntrypoint state (Passes.pruneEntrypoint entry) = .ok expected →
        ∀ requirement ∈ expected.rawInputs ++ expected.inputs,
          requirement.ty.isForeign = false) :
    ∃ expected,
      Native.expectedEntrypoint state (Passes.pruneEntrypoint entry) = .ok expected ∧
      Native.requireFinalOutput instructions.toList = .ok () ∧
      ∀ {hash : Hash} {witness : Assignment},
        (∀ row ∈ rows, GuardedImpactTranscript.ordinaryHolds hash witness row) →
          (∀ term ∈ expected.assertions, interpret hash witness term = some one) ∧
          (∀ requirement ∈ expected.bounds,
            ∃ value, interpret hash witness requirement.1 = some value ∧
              value.val ≤ requirement.2) ∧
          (∀ requirement ∈ expected.rawInputs ++ expected.inputs,
            requirement.ty.isForeign = false →
            requirement.canonicalJubjubScalar = false →
            (witness requirement.identifier).val ≤ Native.sourceMaximum requirement.ty) ∧
          (∀ raw index, (raw, index) ∈ instructions.toList.zipIdx →
            ∃ before after,
              ScalarValidationMeaning.StateMeaning hash witness witness before ∧
              Native.validateInstruction (Zkir.optimizedExpected rewrites expected)
                before raw = .ok after ∧
              ScalarValidationMeaning.StateMeaning hash witness witness after) := by
  obtain ⟨_, expected, _, expectedAccepted, accepted, _⟩ :=
    Zkir.lowerEntrypoint_validation_and_instructions_with_rewrites
      state entry rewrites json lowered
  let optimized := Zkir.optimizedExpected rewrites expected
  obtain ⟨parsedInstructions, rawInputs, seed, final, driver⟩ :=
    ScalarValidationProjection.validate_driver_result (expected := optimized) accepted
  have instructionsEq : parsedInstructions = instructions :=
    Except.ok.inj (driver.instructionsParsed.symm.trans instructionsParsed)
  subst parsedInstructions
  refine ⟨expected, expectedAccepted, driver.finalOutput, ?_⟩
  intro hash witness ordinary
  have optimizedInputs : optimized.rawInputs ++ optimized.inputs =
      expected.rawInputs ++ expected.inputs := by
    cases rewrites <;> rfl
  have rawSchema : ∀ requirement ∈ optimized.rawInputs,
      requirement.ty.isForeign = false := by
    intro requirement member
    apply schema expected expectedAccepted requirement
    rw [← optimizedInputs]
    exact List.mem_append_left _ member
  have inputSchema : ∀ requirement ∈ optimized.inputs,
      requirement.ty.isForeign = false := by
    intro requirement member
    apply schema expected expectedAccepted requirement
    rw [← optimizedInputs]
    exact List.mem_append_right _ member
  obtain ⟨seedMeaning, seedDefinitions⟩ :=
    seedRawInputs_meaning_and_nativeDefinitions
      (hash := hash) (inputs := witness) (witness := witness)
      rawSchema (fun _ _ => rfl) driver.seededRawInputs
  have seedAssertionCount := seedRawInputs_assertionCount rawSchema driver.seededRawInputs
  have initialAssertions :
      CheckedAssertions hash witness optimized seed.assertionCount := by
    simp [CheckedAssertions, seedAssertionCount]
  have driverTrace :
      Native.validateInstructionLoop optimized (instructions.toList.zipIdx) seed = .ok final :=
    driver.instructionTrace
  have steps : ∀ item ∈ instructions.toList.zipIdx,
      AcceptedMeaningStep hash witness item.1 := by
    intro item member
    have rawMember : item.1 ∈ instructions.toList := by
      have found : item.1 ∈ (instructions.toList.zipIdx).map Prod.fst :=
        List.mem_map.mpr ⟨item, member, rfl⟩
      simpa only [List.zipIdx_map_fst] using found
    obtain ⟨row, rowMember, rowDecoded⟩ := mapM_decoded_member decodeRow decoded rawMember
    exact GuardedImpactTranscript.classify_decoded_row rowDecoded (ordinary row rowMember)
  obtain ⟨finalMeaning, _, preserveAssertions, visits⟩ :=
    RangeDedupAcceptedArray.accepted_loop_meaning_assertions_at_steps
      seedMeaning seedDefinitions inputSchema (fun _ _ => rfl) steps driverTrace
  have optimizedAssertions : ∀ term ∈ optimized.assertions,
      interpret hash witness term = some one := by
    have checked := preserveAssertions initialAssertions
    simpa only [driver.assertionCount, CheckedAssertions, List.take_length] using checked
  have assertions : ∀ term ∈ expected.assertions,
      interpret hash witness term = some one := by
    intro term member
    apply optimizedAssertions term
    by_cases strict : rewrites == .disabled <;>
      simp [optimized, Zkir.optimizedExpected, strict, List.mem_eraseDups, member]
  have boundsUnchanged : optimized.bounds = expected.bounds := by
    cases rewrites <;> rfl
  have bounds : ∀ requirement ∈ expected.bounds,
      ∃ value, interpret hash witness requirement.1 = some value ∧
        value.val ≤ requirement.2 := by
    intro requirement member
    exact driver.rangeRequirements finalMeaning requirement (by
      rw [boundsUnchanged]
      exact member)
  have inputBounds : ∀ requirement ∈ expected.rawInputs ++ expected.inputs,
      requirement.ty.isForeign = false →
      requirement.canonicalJubjubScalar = false →
      (witness requirement.identifier).val ≤ Native.sourceMaximum requirement.ty := by
    intro requirement member nonforeign ordinaryScalar
    exact driver.inputBound finalMeaning
      (by rw [optimizedInputs]; exact member) nonforeign ordinaryScalar
  have rowMeanings : ∀ raw index, (raw, index) ∈ instructions.toList.zipIdx →
      ∃ before after,
        ScalarValidationMeaning.StateMeaning hash witness witness before ∧
        Native.validateInstruction optimized before raw = .ok after ∧
        ScalarValidationMeaning.StateMeaning hash witness witness after := by
    intro raw index member
    obtain ⟨before, after, beforeMeaning, _, checked, afterMeaning, _⟩ :=
      visits raw index member
    exact ⟨before, after, beforeMeaning, checked, afterMeaning⟩
  exact ⟨assertions, bounds, inputBounds, rowMeanings⟩

private theorem raw_of_decodedRow_member {items : List Json} {rows : List Row}
    (decoded : items.mapM decodeRow = .ok rows)
    {row : Row} (present : row ∈ rows) :
    ∃ raw ∈ items, decodeRow raw = .ok row := by
  induction items generalizing rows with
  | nil =>
    change (Except.ok [] : Except String (List Row)) = .ok rows at decoded
    cases decoded
    simp at present
  | cons head tail ih =>
    simp only [List.mapM_cons, bind_ok] at decoded
    obtain ⟨headRow, headDecoded, rest, restDecoded, same⟩ := decoded
    cases same
    rcases List.mem_cons.mp present with same | later
    · subst row
      exact ⟨head, List.mem_cons_self .., headDecoded⟩
    · obtain ⟨raw, member, checked⟩ := ih restDecoded later
      exact ⟨raw, List.mem_cons_of_mem _ member, checked⟩

private theorem accepted_rows_of_explicit_constraints
    {hash : Hash} {witness : Assignment} {expected : Native.Expected}
    {items : List (Json × Nat)} {rows : List Row} {initial final : Native.State}
    (inputSchema : ∀ requirement ∈ expected.inputs, requirement.ty.isForeign = false)
    (initialMeaning : ScalarValidationMeaning.StateMeaning hash witness witness initial)
    (initialDefinitions : NativeDefinitions initial)
    (decoded : (items.map Prod.fst).mapM decodeRow = .ok rows)
    (accepted : Native.validateInstructionLoop expected items initial = .ok final)
    (equations : GuardedScalarWitnessAssembly.DefinitionEquations hash witness
      (items.map Prod.fst) rows)
    (explicit : ∀ pair ∈ (items.map Prod.fst).zip rows,
      GuardedScalarWitnessAssembly.ExplicitConstraint hash witness pair.1 pair.2) :
    ∀ row ∈ rows, ordinaryHolds hash witness row := by
  induction items generalizing initial final rows with
  | nil =>
    change (Except.ok [] : Except String (List Row)) = .ok rows at decoded
    cases decoded
    simp
  | cons item rest ih =>
    rcases item with ⟨raw, ordinal⟩
    simp only [List.map_cons, List.mapM_cons, bind_ok] at decoded
    obtain ⟨row, headDecoded, tail, tailDecoded, sameRows⟩ := decoded
    cases sameRows
    rw [Native.validateInstructionLoop, List.forIn_cons] at accepted
    cases checked : Native.validateInstruction expected initial raw with
    | error reason => simp [checked, Bind.bind, Except.bind] at accepted
    | ok next =>
      simp only [checked, bind_pure_comp] at accepted
      have headMember : (raw, row) ∈
          (((raw, ordinal) :: rest).map Prod.fst).zip (row :: tail) := by simp
      have remaining := GuardedScalarWitnessAssembly.remainingConstraint_of_accepted_row
        headDecoded checked initialMeaning initialDefinitions (explicit _ headMember)
      have headHolds : ordinaryHolds hash witness row := by
        have headEquation := equations _ headMember
        cases row with
        | publicInput => trivial
        | impact => trivial
        | strict instruction =>
          exact GuardedScalarWitnessAssembly.strict_holds_from_equation
            hash witness raw instruction headEquation remaining
      have after := RangeDedupAcceptedArray.acceptedMeaningStep_preserves
        initialMeaning initialDefinitions inputSchema (fun _ _ => rfl)
        (classify_decoded_row headDecoded headHolds) checked
      have tailEquations : GuardedScalarWitnessAssembly.DefinitionEquations hash witness
          (rest.map Prod.fst) tail := fun pair present =>
        equations pair (List.mem_cons_of_mem _ present)
      have tailExplicit : ∀ pair ∈ (rest.map Prod.fst).zip tail,
          GuardedScalarWitnessAssembly.ExplicitConstraint hash witness pair.1 pair.2 :=
        fun pair present => explicit pair (List.mem_cons_of_mem _ present)
      intro found present
      rcases List.mem_cons.mp present with same | later
      · exact same.symm ▸ headHolds
      · exact ih after.1 after.2.1 tailDecoded accepted tailEquations tailExplicit found later

/-- Along accepted scalar lowering, the producer's bound on each Boolean
operand comes from its actual validated prefix. The assembled definitions
and explicitly emitted constraints suffice for all ordinary rows. -/
theorem lowerEntrypoint_guardedRows_of_explicit_constraints
    {state : List StateDecl} {sourceEntry : Entrypoint} {rewrites : Zkir.Rewrites}
    {expected : Native.Expected} {json : Json} {instructions : Array Json} {rows : List Row}
    {hash : Hash} {witness : Assignment}
    (lowered : Zkir.lowerEntrypoint state sourceEntry rewrites = .ok json)
    (expectedAccepted : Native.expectedEntrypoint state (Passes.pruneEntrypoint sourceEntry) =
      .ok expected)
    (schema : ∀ requirement ∈ expected.rawInputs ++ expected.inputs, requirement.ty.isForeign = false)
    (parsed : Native.arrayField json "instructions" = .ok instructions)
    (decoded : instructions.toList.mapM decodeRow = .ok rows)
    (equations : GuardedScalarWitnessAssembly.DefinitionEquations hash witness instructions.toList rows)
    (explicit : ∀ pair ∈ instructions.toList.zip rows,
      GuardedScalarWitnessAssembly.ExplicitConstraint hash witness pair.1 pair.2) :
    ∀ row ∈ rows, ordinaryHolds hash witness row := by
  obtain ⟨_, shape, _, shapeAccepted, validated, _⟩ :=
    Zkir.lowerEntrypoint_validation_and_instructions_with_rewrites state sourceEntry rewrites
      json lowered
  have same := Except.ok.inj (shapeAccepted.symm.trans expectedAccepted)
  subst shape
  let optimized := Zkir.optimizedExpected rewrites expected
  have rawSchema : ∀ requirement ∈ optimized.rawInputs, requirement.ty.isForeign = false := by
    intro requirement present
    apply schema requirement
    exact List.mem_append_left _ (by cases rewrites <;> exact present)
  have inputSchema : ∀ requirement ∈ optimized.inputs, requirement.ty.isForeign = false := by
    intro requirement present
    apply schema requirement
    exact List.mem_append_right _ (by cases rewrites <;> exact present)
  obtain ⟨items, _, initial, final, driver⟩ := validate_driver_result validated
  have sameArray := Except.ok.inj (driver.instructionsParsed.symm.trans parsed)
  subst items
  obtain ⟨meaning, definitions⟩ := seedRawInputs_meaning_and_nativeDefinitions
    (hash := hash) (inputs := witness) (witness := witness)
    rawSchema (fun _ _ => rfl) driver.seededRawInputs
  exact accepted_rows_of_explicit_constraints inputSchema meaning definitions
    (by simpa only [List.zipIdx_map_fst] using decoded) driver.instructionTrace
    (by simpa only [List.zipIdx_map_fst] using equations)
    (by simpa only [List.zipIdx_map_fst] using explicit)

/-- A witness from the actual unoptimized lower body satisfies the strict
constraints of the same checked guarded relation. The preprocessing rows
have no ordinary constraint and keep their separate transcript semantics. -/
theorem lowerEntrypoint_guardedRows_of_body_meaning
    {state : List StateDecl} {sourceEntry : Entrypoint} {plan : Impact.Plan}
    {json : Json} {instructions : Array Json} {rows : List Row}
    {hash : Hash} {witness : Assignment}
    (lowered : Zkir.lowerEntrypoint state sourceEntry .disabled = .ok json)
    (planAccepted : Impact.lower state (Passes.pruneEntrypoint sourceEntry) = .ok plan)
    (parsed : Native.arrayField json "instructions" = .ok instructions)
    (decoded : instructions.toList.mapM decodeRow = .ok rows)
    (meaning : ScalarLowering.LowerStateMeaning hash witness
      ((Zkir.lowerEntrypointBody (Passes.pruneEntrypoint sourceEntry) plan).run {}).2) :
    ∀ row ∈ rows, ordinaryHolds hash witness row := by
  obtain ⟨emittedPlan, _, emittedPlanAccepted, _, _, emitted⟩ :=
    Zkir.lowerEntrypoint_validation_and_instructions state sourceEntry json lowered
  have samePlan := Except.ok.inj (emittedPlanAccepted.symm.trans planAccepted)
  subst emittedPlan
  have exactArray := Except.ok.inj (emitted.symm.trans parsed)
  subst instructions
  obtain ⟨strictRows, strictDecoded⟩ := meaning.decoded
  intro row present
  cases row with
  | publicInput => trivial
  | impact => trivial
  | strict instruction =>
    obtain ⟨raw, rawPresent, rowDecoded⟩ := raw_of_decodedRow_member decoded present
    obtain ⟨strict, strictPresent, rawDecoded⟩ :=
      mapM_decoded_member NativeRelationJson.decodeInstruction strictDecoded rawPresent
    have sameInstruction := Except.ok.inj (rawDecoded.symm.trans (decodeRow_strict rowDecoded).1.decoded)
    subst strict
    exact meaning.holds strictRows strictDecoded instruction strictPresent

/-- Each comparison inherits its actual operand bounds from the state reached
by the accepted producer trace. The row's own result equation cannot establish
that premise because the equation is conditional on those bounds. -/
theorem lowerEntrypoint_guardedRows_comparison_bounds
    {state : List StateDecl} {sourceEntry : Entrypoint} (rewrites : Zkir.Rewrites)
    {json : Json} {instructions : Array Json} {rows : List Row}
    {hash : Hash} {witness : Assignment}
    (lowered : Zkir.lowerEntrypoint state sourceEntry rewrites = .ok json)
    (instructionsParsed : Native.arrayField json "instructions" = .ok instructions)
    (decoded : instructions.toList.mapM decodeRow = .ok rows)
    (schema : ∀ expected,
      Native.expectedEntrypoint state (Passes.pruneEntrypoint sourceEntry) = .ok expected →
        ∀ requirement ∈ expected.rawInputs ++ expected.inputs,
          requirement.ty.isForeign = false)
    (holds : ∀ row ∈ rows, ordinaryHolds hash witness row) :
    ∀ left right width destination, .strict (.lessThan left right width destination) ∈ rows →
      (left.read witness).val < 2 ^ width ∧ (right.read witness).val < 2 ^ width := by
  obtain ⟨_, _, _, meaning⟩ := lowerEntrypoint_guardedRows_meaning
    rewrites lowered instructionsParsed decoded schema
  obtain ⟨_, _, _, visits⟩ := meaning holds
  intro left right width destination present
  obtain ⟨raw, rawMember, rowDecoded⟩ := raw_of_decodedRow_member decoded present
  have indexed : raw ∈ instructions.toList.zipIdx.map Prod.fst := by
    simpa only [List.zipIdx_map_fst] using rawMember
  obtain ⟨⟨item, ordinal⟩, visit, same⟩ := List.mem_map.mp indexed
  change item = raw at same
  subst item
  obtain ⟨before, after, beforeMeaning, accepted, _⟩ := visits raw ordinal visit
  have step := (decodeRow_strict rowDecoded).1
  cases step.supported with
  | lessThan _ _ _ _ opcode =>
    exact RangeDedupAcceptedArray.accepted_lessThan_witnessBounds beforeMeaning opcode
      step.decoded accepted

/-- Accepted mixed ZKIR rows preserve the source assertions, source bounds,
and scalar input bounds. Strict rows use their ordinary circuit constraint;
guarded impact and public input rows pass through the guarded classifier. -/
theorem lowerEntrypoint_guardedRows_sourceRequirements
    {state : List StateDecl} {entry : Entrypoint} (rewrites : Zkir.Rewrites)
    {json : Json} {instructions : Array Json} {rows : List Row}
    (lowered : Zkir.lowerEntrypoint state entry rewrites = .ok json)
    (instructionsParsed : Native.arrayField json "instructions" = .ok instructions)
    (decoded : instructions.toList.mapM GuardedScalarRows.decodeRow = .ok rows)
    (schema : ∀ expected,
      Native.expectedEntrypoint state (Passes.pruneEntrypoint entry) = .ok expected →
        ∀ requirement ∈ expected.rawInputs ++ expected.inputs,
          requirement.ty.isForeign = false) :
    ∃ expected,
      Native.expectedEntrypoint state (Passes.pruneEntrypoint entry) = .ok expected ∧
      ∀ {hash : Hash} {witness : Assignment},
        (∀ row ∈ rows, GuardedImpactTranscript.ordinaryHolds hash witness row) →
          (∀ term ∈ expected.assertions, interpret hash witness term = some one) ∧
          (∀ requirement ∈ expected.bounds,
            ∃ value, interpret hash witness requirement.1 = some value ∧
              value.val ≤ requirement.2) ∧
          (∀ requirement ∈ expected.rawInputs ++ expected.inputs,
            requirement.ty.isForeign = false →
            requirement.canonicalJubjubScalar = false →
            (witness requirement.identifier).val ≤ Native.sourceMaximum requirement.ty) := by
  obtain ⟨expected, expectedAccepted, _, meaning⟩ :=
    lowerEntrypoint_guardedRows_meaning rewrites lowered instructionsParsed decoded schema
  refine ⟨expected, expectedAccepted, ?_⟩
  intro hash witness ordinary
  obtain ⟨assertions, bounds, inputBounds, _⟩ := meaning ordinary
  exact ⟨assertions, bounds, inputBounds⟩

end Noctium.Verification.GuardedZkirRequirements
