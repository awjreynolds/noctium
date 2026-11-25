import Noctium.Verification.ScalarValidationOpcodeProfile

namespace Noctium.Verification.GuardedScalarRows

open Lean Backend.Native NativeRelation NativeRelationJson
open Noctium.Verification.ScalarValidationOpcodeProfile
open Noctium.Verification.ScalarValidationNativeDefinitions

private theorem bind_ok {α β : Type} {first : Except String α}
    {next : α → Except String β} {result : β} :
    (first >>= next) = .ok result ↔
      ∃ value, first = .ok value ∧ next value = .ok result := by
  cases first <;> simp [Bind.bind, Except.bind]

/-- A raw scalar row keeps the ordinary strict decoder separate from the two
preprocessing-aware row forms used by guarded activity. -/
inductive Row where
  | strict (instruction : Instruction)
  | publicInput (output : String) (guard : Option Operand)
  | impact (guard : Operand) (inputs : List Operand)
  deriving Repr, DecidableEq

private def decodeOptionalGuard (raw : Json) : Except String (Option Operand) := do
  let guardJson ← raw.getObjVal? "guard"
  if guardJson.isNull then pure none else some <$> decodeOperandField raw "guard"

private def decodePublicInput (raw : Json) : Except String Row := do
  exactFields raw ["op", "guard", "type", "output"]
  checkNativeType (← raw.getObjVal? "type")
  let output ← Backend.Native.stringField raw "output"
  NativeRelationJson.ensure (validIdentifier output) "invalid native SSA definition"
  let guard ← decodeOptionalGuard raw
  pure (.publicInput output guard)

private def decodeImpact (raw : Json) : Except String Row := do
  exactFields raw ["op", "guard", "inputs"]
  let guard ← decodeOperandField raw "guard"
  let inputs ← decodeOperands (← raw.getObjVal? "inputs")
  pure (.impact guard inputs)

private def decodeStrict (raw : Json) : Except String Instruction := do
  let instruction ← NativeRelationJson.decodeInstruction raw
  if supportedScalarOpcodeProfile raw instruction then pure instruction
  else throw "unsupported strict scalar opcode profile"

/-- Decode both guarded preprocessing row forms alongside the strict scalar
instructions. Preserve the original row operands and their order. -/
def decodeRow (raw : Json) : Except String Row := do
  let opcode ← Backend.Native.stringField raw "op"
  if opcode == "public_input" then decodePublicInput raw
  else if opcode == "impact" then decodeImpact raw
  else Row.strict <$> decodeStrict raw

private theorem publicInput_parts {raw : Json} {row : Row}
    (accepted : decodePublicInput raw = .ok row) :
    ∃ output guard, row = .publicInput output guard ∧
      Backend.Native.stringField raw "output" = .ok output ∧ decodeOptionalGuard raw = .ok guard := by
  unfold decodePublicInput at accepted
  simp only [bind_ok] at accepted
  obtain ⟨_, _, _, _, _, _, output, outputParsed, _, _, guard, guardParsed, shape⟩ := accepted
  exact ⟨output, guard, (Except.ok.inj shape).symm, outputParsed, guardParsed⟩

private theorem impact_parts {raw : Json} {row : Row}
    (accepted : decodeImpact raw = .ok row) :
    ∃ guard inputs, row = .impact guard inputs ∧
      decodeOperandField raw "guard" = .ok guard ∧
      (do decodeOperands (← raw.getObjVal? "inputs")) = .ok inputs := by
  unfold decodeImpact at accepted
  simp only [bind_ok] at accepted
  obtain ⟨_, _, guard, guardParsed, fields, fieldsParsed, inputs, inputsParsed, shape⟩ := accepted
  exact ⟨guard, inputs, (Except.ok.inj shape).symm, guardParsed,
    bind_ok.mpr ⟨fields, fieldsParsed, inputsParsed⟩⟩

private theorem strict_parts {raw : Json} {row : Row}
    (accepted : Row.strict <$> decodeStrict raw = .ok row) :
    ∃ instruction, row = .strict instruction ∧ NativeDefinitionStep raw instruction := by
  cases strict : decodeStrict raw with
  | error message => simp [strict, Functor.map, Except.map] at accepted
  | ok instruction =>
    have shape : row = .strict instruction := by
      simp [strict, Functor.map, Except.map] at accepted
      exact accepted.symm
    unfold decodeStrict at strict
    obtain ⟨parsed, parsedOk, profiled⟩ := bind_ok.mp strict
    by_cases profile : supportedScalarOpcodeProfile raw parsed = true
    · simp [profile] at profiled
      cases profiled
      exact ⟨_, shape, ⟨supportedScalarOpcode_of_profile profile, parsedOk⟩⟩
    · simp [profile, throw, throwThe] at profiled

private theorem optionalGuard_fields {raw : Json} {guard : Option Operand}
    (accepted : decodeOptionalGuard raw = .ok guard) :
    (guard = none → raw.getObjVal? "guard" = .ok Json.null) ∧
      (∀ operand, guard = some operand → decodeOperandField raw "guard" = .ok operand) := by
  unfold decodeOptionalGuard at accepted
  obtain ⟨found, foundParsed, shaped⟩ := bind_ok.mp accepted
  by_cases isNull : found.isNull = true
  · have jsonEq : found = Json.null := by cases found <;> simp [Json.isNull] at isNull ⊢
    subst found
    simp [Json.isNull, Pure.pure, Except.pure] at shaped
    subst guard
    exact ⟨fun _ => foundParsed, fun _ impossible => by cases impossible⟩
  · cases operand : decodeOperandField raw "guard" with
    | error message => simp [isNull, operand, Functor.map, Except.map] at shaped
    | ok value =>
      have guardEq : some value = guard := by
        have exactShape : (Except.ok (some value) : Except String (Option Operand)) = .ok guard := by
          simpa [isNull, operand, Functor.map, Except.map] using shaped
        exact Except.ok.inj exactShape
      subst guard
      constructor
      · intro impossible
        cases impossible
      · intro actual same
        cases same
        rfl

theorem decodeRow_strict {raw : Json} {instruction : Instruction}
    (accepted : decodeRow raw = .ok (.strict instruction)) :
    NativeDefinitionStep raw instruction ∧
      Backend.Native.stringField raw "op" ≠ .ok "impact" := by
  unfold decodeRow at accepted
  obtain ⟨opcode, opcodeParsed, branch⟩ := bind_ok.mp accepted
  by_cases publicOpcode : (opcode == "public_input") = true
  · simp only [publicOpcode, ite_true] at branch
    obtain ⟨_, _, impossible, _, _⟩ := publicInput_parts branch
    cases impossible
  · by_cases impactOpcode : (opcode == "impact") = true
    · simp only [publicOpcode, impactOpcode, ite_true] at branch
      obtain ⟨_, _, impossible, _, _⟩ := impact_parts branch
      cases impossible
    · simp only [publicOpcode, impactOpcode] at branch
      obtain ⟨_, shape, step⟩ := strict_parts branch
      cases shape
      refine ⟨step, ?_⟩
      intro same
      have opcodeEq := Except.ok.inj (opcodeParsed.symm.trans same)
      subst opcode
      simp at impactOpcode

theorem decodeRow_strict_not_publicInput {raw : Json} {instruction : Instruction}
    (accepted : decodeRow raw = .ok (.strict instruction)) :
    Backend.Native.stringField raw "op" ≠ .ok "public_input" := by
  intro opcode
  unfold decodeRow at accepted
  simp only [opcode, Bind.bind, Except.bind, beq_self_eq_true, ite_true] at accepted
  obtain ⟨_, _, impossible, _, _⟩ := publicInput_parts accepted
  cases impossible

theorem decodeRow_publicInput_fields {raw : Json} {output : String} {guard : Option Operand}
    (accepted : decodeRow raw = .ok (.publicInput output guard)) :
    Backend.Native.stringField raw "op" = .ok "public_input" ∧
      Backend.Native.stringField raw "output" = .ok output ∧
      (guard = none → raw.getObjVal? "guard" = .ok Json.null) ∧
      (∀ operand, guard = some operand → decodeOperandField raw "guard" = .ok operand) := by
  unfold decodeRow at accepted
  obtain ⟨opcode, opcodeParsed, branch⟩ := bind_ok.mp accepted
  by_cases publicOpcode : (opcode == "public_input") = true
  · simp only [publicOpcode, ite_true] at branch
    obtain ⟨_, _, shape, outputParsed, guardParsed⟩ := publicInput_parts branch
    cases shape
    exact ⟨opcodeParsed.trans (congrArg Except.ok (eq_of_beq publicOpcode)),
      outputParsed, optionalGuard_fields guardParsed⟩
  · by_cases impactOpcode : (opcode == "impact") = true
    · simp only [publicOpcode, impactOpcode, ite_true] at branch
      obtain ⟨_, _, impossible, _, _⟩ := impact_parts branch
      cases impossible
    · simp only [publicOpcode, impactOpcode] at branch
      obtain ⟨_, impossible, _⟩ := strict_parts branch
      cases impossible

theorem decodeRow_impact_fields {raw : Json} {guard : Operand} {inputs : List Operand}
    (accepted : decodeRow raw = .ok (.impact guard inputs)) :
    Backend.Native.stringField raw "op" = .ok "impact" ∧
      decodeOperandField raw "guard" = .ok guard ∧
      (do decodeOperands (← raw.getObjVal? "inputs")) = .ok inputs := by
  unfold decodeRow at accepted
  obtain ⟨opcode, opcodeParsed, branch⟩ := bind_ok.mp accepted
  by_cases publicOpcode : (opcode == "public_input") = true
  · simp only [publicOpcode, ite_true] at branch
    obtain ⟨_, _, impossible, _, _⟩ := publicInput_parts branch
    cases impossible
  · by_cases impactOpcode : (opcode == "impact") = true
    · simp only [publicOpcode, impactOpcode, ite_true] at branch
      obtain ⟨_, _, shape, guardParsed, inputsParsed⟩ := impact_parts branch
      cases shape
      exact ⟨opcodeParsed.trans (congrArg Except.ok (eq_of_beq impactOpcode)),
        guardParsed, inputsParsed⟩
    · simp only [publicOpcode, impactOpcode] at branch
      obtain ⟨_, impossible, _⟩ := strict_parts branch
      cases impossible

end Noctium.Verification.GuardedScalarRows
