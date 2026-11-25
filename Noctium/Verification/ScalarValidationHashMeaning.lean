import Noctium.Verification.ScalarValidationArithmeticLoop
import Noctium.Verification.ScalarValidationOutputMeaning

namespace Noctium.Verification.ScalarValidationHashMeaning

open Lean Backend.Native NativeRelation
open ScalarNormalization ScalarValidationMeaning ScalarValidationArithmeticLoop

/-- The accepted hash reads the exact producer operand list and defines one
Native result. Both symbolic term forms are tied to the real combine call. -/
theorem accepted_hash_definition
    {expected : Expected} {state next : State} {raw : Json}
    (opcode : Backend.Native.stringField raw "op" = .ok "transient_hash")
    (accepted : validateInstruction expected state raw = .ok next) :
    ∃ values fact children,
      arguments state raw "inputs" = .ok values ∧
      combine ((conditionalSwapHash? (values.map (·.term))).getD (.hash (values.map (·.term))))
        (Field.modulus - 1) children = .ok fact ∧
      defineResult state raw fact = .ok next := by
  unfold validateInstruction at accepted
  simp only [bind_ok] at accepted
  obtain ⟨found, op, _, _, _, _, rest⟩ := accepted
  have same := Except.ok.inj (op.symm.trans opcode)
  subst found
  simp only [bind_ok] at rest
  obtain ⟨values, parsed, _, _, rest⟩ := rest
  change (do
    let found ← arguments state raw "inputs"
    found.forM (fun fact => Backend.Native.ensure
      (fact.valueType == NativeValueType.native)
      "native instruction operand must have Native type")
    pure found) = .ok values at parsed
  simp only [bind_ok] at parsed
  obtain ⟨found, argumentsParsed, _, _, result⟩ := parsed
  cases result
  cases recognized : conditionalSwapHash? (values.map (·.term)) with
  | none =>
    simp only [recognized, bind_ok] at rest
    obtain ⟨fact, combined, defined⟩ := rest
    refine ⟨values, fact, values, argumentsParsed, ?_, defined⟩
    simpa [recognized] using combined
  | some term =>
    simp only [recognized, bind_ok] at rest
    obtain ⟨fact, combined, defined⟩ := rest
    refine ⟨values, fact, values.take 1, argumentsParsed, ?_, defined⟩
    simpa [recognized] using combined

private theorem mapM_known_values {α β : Type} (interpretValue : α → Option β)
    {items : List α} {values : List β}
    (known : items.map interpretValue = values.map some) :
    items.mapM interpretValue = some values := by
  induction items generalizing values with
  | nil =>
    cases values <;> simp_all
  | cons item rest ih =>
    cases values with
    | nil => simp at known
    | cons value tail =>
      simp only [List.map_cons, List.cons.injEq] at known
      simp [List.mapM_cons, known.1, ih known.2]

/-- Every satisfying assignment gives the accepted hash row the source term's
value. The checker may record the mirrored-select hash marker internally. -/
theorem accepted_hash_step_meaning
    {hash : Hash} {inputs witness : Assignment} {expected : Expected}
    {state next : State} {raw : Json} {values : List Operand} {output : String}
    (meaning : StateMeaning hash inputs witness state)
    (definitions : NativeDefinitions state)
    (opcode : Backend.Native.stringField raw "op" = .ok "transient_hash")
    (decoded : NativeRelationJson.decodeInstruction raw = .ok (.hash values output))
    (holds : Instruction.Holds hash witness (.hash values output))
    (accepted : validateInstruction expected state raw = .ok next) :
    StateMeaning hash inputs witness next ∧ NativeDefinitions next := by
  obtain ⟨facts, fact, _, argumentsParsed, combined, defined⟩ :=
    accepted_hash_definition opcode accepted
  have fields := NativeRelationJson.decodeInstruction_hashFields opcode decoded
  have valuesMeaning := ScalarValidationOutputMeaning.arguments_decoded_meaning
    meaning argumentsParsed fields.1
  have termsMeaning : (facts.map (·.term)).mapM (interpret hash inputs) =
      some (values.map (·.read witness)) := by
    apply mapM_known_values
    simpa only [List.map_map, Function.comp_def] using valuesMeaning
  have hashMeaning : interpret hash inputs (.hash (facts.map (·.term))) =
      some (witness output) := by
    simp only [interpret_hash, termsMeaning, Option.bind_some]
    congr 1
    exact holds.symm
  have actualMeaning : interpret hash inputs
      ((conditionalSwapHash? (facts.map (·.term))).getD (.hash (facts.map (·.term)))) =
      some (witness output) := by
    cases recognized : conditionalSwapHash? (facts.map (·.term)) with
    | none => simpa only [Option.getD_none] using hashMeaning
    | some term =>
      simp only [Option.getD_some]
      exact (ScalarTermMeaning.interpret?_conditionalSwapHash hash inputs recognized).trans
        hashMeaning
  have factMeaning : FactMeaning hash inputs witness fact (witness output) :=
    combine_meaning combined actualMeaning (Nat.le_sub_one_of_lt (witness output).isLt)
  refine ⟨defineResult_meaning meaning ?_ defined,
    defineResult_nativeDefinitions definitions (combine_native combined) defined⟩
  intro identifier parsed
  have same := Except.ok.inj (parsed.symm.trans fields.2)
  subst identifier
  exact factMeaning

end Noctium.Verification.ScalarValidationHashMeaning
