import Noctium.Verification.GuardedZkirArtifact
import Noctium.Verification.GuardedZkirRequirements
import Noctium.Verification.ScalarValidationOutputMeaning

namespace Noctium.Verification.GuardedOutputRows

open Lean Backend Native NativeRelation NativeRelationJson
open GuardedScalarRows GuardedImpactTranscript
open ScalarNormalization (interpret)

private theorem bind_ok {α β : Type} {first : Except String α}
    {next : α → Except String β} {result : β} :
    (first >>= next) = .ok result ↔
      ∃ value, first = .ok value ∧ next value = .ok result := by
  cases first <;> simp [Bind.bind, Except.bind]

/-- Return operands occur only in strict output rows. -/
private def outputOperands : Row → Option (List Operand)
  | .strict (.output operands) => some operands
  | _ => none

/-- Values carried by output rows, flattened in the original row and operand
order. Guarded preprocessing rows do not contribute source return values. -/
def emittedReturnValues (assignment : Assignment) (rows : List Row) : List Scalar :=
  (rows.filterMap outputOperands).flatMap fun operands =>
    operands.map (·.read assignment)

private theorem raw_output_test {raw : Json} {row : Row}
    (decoded : GuardedScalarRows.decodeRow raw = .ok row) :
    (Native.opcode raw == "output") = (outputOperands row).isSome := by
  cases row with
  | strict instruction =>
    obtain ⟨step, _⟩ := GuardedScalarRows.decodeRow_strict decoded
    cases instruction <;> cases step.supported <;>
      simp_all [Native.opcode, outputOperands, Except.toOption]
  | publicInput output guard =>
    have opcode := (GuardedScalarRows.decodeRow_publicInput_fields decoded).1
    simp [Native.opcode, outputOperands, Except.toOption, opcode]
  | impact guard inputs =>
    have opcode := (GuardedScalarRows.decodeRow_impact_fields decoded).1
    simp [Native.opcode, outputOperands, Except.toOption, opcode]

private theorem decoded_output_count {items : List (Json × Nat)} {rows : List Row}
    (decoded : (items.map Prod.fst).mapM GuardedScalarRows.decodeRow = .ok rows) :
    (items.map (Native.opcode ∘ Prod.fst)).count "output" =
      (rows.filterMap outputOperands).length := by
  induction items generalizing rows with
  | nil =>
    simp only [List.map_nil, List.mapM_nil] at decoded
    cases decoded
    rfl
  | cons item rest ih =>
    rcases item with ⟨raw, index⟩
    simp only [List.map_cons, List.mapM_cons, bind_ok] at decoded
    obtain ⟨row, rowDecoded, tailRows, tailDecoded, rowsEq⟩ := decoded
    cases rowsEq
    simp only [List.map_cons, Function.comp_apply, List.count_cons,
      List.filterMap_cons, raw_output_test rowDecoded]
    cases outputOperands row <;> simp [ih tailDecoded]

private theorem decoded_output_member {items : List (Json × Nat)} {rows : List Row}
    (decoded : (items.map Prod.fst).mapM GuardedScalarRows.decodeRow = .ok rows)
    {values : List Operand} (member : values ∈ rows.filterMap outputOperands) :
    ∃ raw index, (raw, index) ∈ items ∧
      Native.stringField raw "op" = .ok "output" ∧
      NativeRelationJson.decodeInstruction raw = .ok (.output values) := by
  induction items generalizing rows with
  | nil =>
    simp only [List.map_nil, List.mapM_nil] at decoded
    cases decoded
    simp at member
  | cons item rest ih =>
    rcases item with ⟨raw, index⟩
    simp only [List.map_cons, List.mapM_cons, bind_ok] at decoded
    obtain ⟨row, rowDecoded, tailRows, tailDecoded, rowsEq⟩ := decoded
    cases rowsEq
    simp only [List.filterMap_cons] at member
    cases output : outputOperands row with
    | none =>
      obtain ⟨source, offset, present, opcode, instruction⟩ :=
        ih tailDecoded (by simpa [output] using member)
      exact ⟨source, offset, List.mem_cons_of_mem _ present, opcode, instruction⟩
    | some operands =>
      have headOrTail : values ∈ operands :: tailRows.filterMap outputOperands := by
        simpa [output] using member
      rcases List.mem_cons.mp headOrTail with same | later
      · subst values
        cases row with
        | strict instruction =>
          have outputInstruction : instruction = .output operands := by
            cases instruction <;> simp_all [outputOperands]
          subst instruction
          obtain ⟨step, _⟩ := GuardedScalarRows.decodeRow_strict rowDecoded
          cases step.supported
          case output outputOperands opcode =>
            exact ⟨raw, index, by simp, opcode, step.decoded⟩
        | publicInput output guard => simp [outputOperands] at output
        | impact guard inputs => simp [outputOperands] at output
      · obtain ⟨source, offset, present, opcode, instruction⟩ :=
          ih tailDecoded later
        exact ⟨source, offset, List.mem_cons_of_mem _ present, opcode, instruction⟩

/-- Exact checked bytes and the producer's checked mixed-row execution expose
the ordered source return values. The unique output occurrence is located in
the original indexed stream, so its producer pre-state supplies the meaning
for each output operand. -/
theorem lowerEntrypoint_guardedOutputValues
    {state : List StateDecl} {entry : Entrypoint} (rewrites : Zkir.Rewrites)
    {bytes : ArtifactBytes.Bytes} {json : Json} {rows : List Row}
    (lowered : Zkir.lowerEntrypoint state entry rewrites = .ok json)
    (artifactChecked : GuardedZkirArtifact.check bytes json = .ok rows)
    (schema : ∀ expected,
      Native.expectedEntrypoint state (Passes.pruneEntrypoint entry) = .ok expected →
        ∀ requirement ∈ expected.rawInputs ++ expected.inputs,
          requirement.ty.isForeign = false)
    {hash : Hash} {assignment : Assignment}
    (ordinary : ∀ row ∈ rows, ordinaryHolds hash assignment row) :
    ∃ expected,
      Native.expectedEntrypoint state (Passes.pruneEntrypoint entry) = .ok expected ∧
      (∀ term ∈ expected.assertions, interpret hash assignment term = some one) ∧
      (∀ requirement ∈ expected.bounds,
        ∃ value, interpret hash assignment requirement.1 = some value ∧
          value.val ≤ requirement.2) ∧
      (∀ requirement ∈ expected.rawInputs ++ expected.inputs,
        requirement.ty.isForeign = false →
        requirement.canonicalJubjubScalar = false →
        (assignment requirement.identifier).val ≤ Native.sourceMaximum requirement.ty) ∧
      expected.returns.map (interpret hash assignment) =
        (emittedReturnValues assignment rows).map some := by
  obtain ⟨_exactBytes, instructions, instructionsParsed, decodedRows⟩ :=
    GuardedZkirArtifact.check_sound artifactChecked
  obtain ⟨expected, expectedAccepted, finalOutput, meaning⟩ :=
    GuardedZkirRequirements.lowerEntrypoint_guardedRows_meaning rewrites lowered
      instructionsParsed decodedRows schema
  refine ⟨expected, expectedAccepted, ?_⟩
  obtain ⟨assertions, bounds, inputBounds, rowMeanings⟩ := meaning ordinary
  have indexedDecoded :
      ((instructions.toList.zipIdx).map Prod.fst).mapM GuardedScalarRows.decodeRow =
        .ok rows := by
    simpa only [List.zipIdx_map_fst] using decodedRows
  have shape := (Native.final_output_required instructions.toList).mp finalOutput
  simp only [Native.finalOutputShape, Bool.and_eq_true, beq_iff_eq] at shape
  have rawCount : (instructions.toList.map Native.opcode).count "output" = 1 := shape.1.2
  have decodedCount := decoded_output_count indexedDecoded
  rw [← List.map_map, List.zipIdx_map_fst, rawCount] at decodedCount
  obtain ⟨values, singleton⟩ := List.length_eq_one_iff.mp decodedCount.symm
  obtain ⟨raw, index, member, opcode, decodedOutput⟩ :=
    decoded_output_member indexedDecoded (values := values) (by rw [singleton]; simp)
  obtain ⟨before, after, beforeMeaning, checked, _⟩ := rowMeanings raw index member
  have outputMeaning :=
    (ScalarValidationOutputMeaning.accepted_output_meaning beforeMeaning checked
      opcode decodedOutput).2
  have returnsSame : (Zkir.optimizedExpected rewrites expected).returns = expected.returns := by
    cases rewrites <;> rfl
  rw [returnsSame] at outputMeaning
  have returnEquation : expected.returns.map (interpret hash assignment) =
      (emittedReturnValues assignment rows).map some := by
    rw [emittedReturnValues, singleton]
    simpa using outputMeaning
  exact ⟨assertions, bounds, inputBounds, returnEquation⟩

end Noctium.Verification.GuardedOutputRows
