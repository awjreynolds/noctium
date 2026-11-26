import Noctium.Verification.ScalarValidationNativeDefinitions

namespace Noctium.Verification.ScalarValidationOpcodeProfile

open Lean Backend.Native NativeRelation NativeRelationJson
open Noctium.Verification.ScalarValidationArithmeticLoop (NativeDefinitions)
open Noctium.Verification.ScalarValidationNativeDefinitions

/-- Check the raw opcode spelling before considering its decoded instruction. -/
def rawHasOpcode (raw : Json) (opcode : String) : Bool :=
  match Backend.Native.stringField raw "op" with
  | .ok found => found == opcode
  | .error _ => false

theorem rawHasOpcode_eq {raw : Json} {opcode : String}
    (checked : rawHasOpcode raw opcode = true) :
    Backend.Native.stringField raw "op" = .ok opcode := by
  unfold rawHasOpcode at checked
  cases parsed : Backend.Native.stringField raw "op" with
  | error message => simp [parsed] at checked
  | ok found =>
    simp only [parsed, beq_iff_eq] at checked
    cases checked
    rfl

theorem rawHasOpcode_of_eq {raw : Json} {opcode : String}
    (parsed : Backend.Native.stringField raw "op" = .ok opcode) :
    rawHasOpcode raw opcode = true := by
  unfold rawHasOpcode
  rw [parsed]
  simp

/-- An executable gate over both the producer spelling and the decoded shape.
Copy and constrain_eq both decode to equality, so their raw opcodes stay
separate here. -/
def supportedScalarOpcodeProfile (raw : Json) : Instruction → Bool
  | .input .«public» _ => rawHasOpcode raw "public_input"
  | .input .«private» _ => rawHasOpcode raw "private_input"
  | .add _ _ _ => rawHasOpcode raw "add"
  | .mul _ _ _ => rawHasOpcode raw "mul"
  | .neg _ _ => rawHasOpcode raw "neg"
  | .bits _ _ => rawHasOpcode raw "constrain_bits"
  | .boolean _ => rawHasOpcode raw "constrain_to_boolean"
  | .lessThan _ _ _ _ => rawHasOpcode raw "less_than"
  | .assert _ => rawHasOpcode raw "assert"
  | .testEq _ _ _ => rawHasOpcode raw "test_eq"
  | .equal _ (.reference _) =>
      rawHasOpcode raw "copy" || rawHasOpcode raw "constrain_eq"
  | .equal _ _ => rawHasOpcode raw "constrain_eq"
  | .impact _ _ => rawHasOpcode raw "impact"
  | .output _ => rawHasOpcode raw "output"
  | .hash _ _ => rawHasOpcode raw "transient_hash"
  | .not _ _ => rawHasOpcode raw "not"
  | .select _ _ _ _ => rawHasOpcode raw "cond_select"

/-- A successful check yields the corresponding producer-tagged opcode proof. -/
theorem supportedScalarOpcode_of_profile {raw : Json} {instruction : Instruction}
    (checked : supportedScalarOpcodeProfile raw instruction = true) :
    SupportedScalarOpcode raw instruction := by
  cases instruction with
  | input visibility output =>
    cases visibility with
    | «public» =>
      change rawHasOpcode raw "public_input" = true at checked
      exact .publicInput output (rawHasOpcode_eq checked)
    | «private» =>
      change rawHasOpcode raw "private_input" = true at checked
      exact .privateInput output (rawHasOpcode_eq checked)
  | add a b output =>
    change rawHasOpcode raw "add" = true at checked
    exact .add a b output (rawHasOpcode_eq checked)
  | mul a b output =>
    change rawHasOpcode raw "mul" = true at checked
    exact .mul a b output (rawHasOpcode_eq checked)
  | neg value output =>
    change rawHasOpcode raw "neg" = true at checked
    exact .neg value output (rawHasOpcode_eq checked)
  | bits value width =>
    change rawHasOpcode raw "constrain_bits" = true at checked
    exact .bits value width (rawHasOpcode_eq checked)
  | boolean value =>
    change rawHasOpcode raw "constrain_to_boolean" = true at checked
    exact .boolean value (rawHasOpcode_eq checked)
  | lessThan a b width output =>
    change rawHasOpcode raw "less_than" = true at checked
    exact .lessThan a b width output (rawHasOpcode_eq checked)
  | assert condition =>
    change rawHasOpcode raw "assert" = true at checked
    exact .assertion condition (rawHasOpcode_eq checked)
  | testEq a b output =>
    change rawHasOpcode raw "test_eq" = true at checked
    exact .testEq a b output (rawHasOpcode_eq checked)
  | equal left right =>
    cases right with
    | immediate rightValue =>
      change rawHasOpcode raw "constrain_eq" = true at checked
      exact .constrainEq _ _ (rawHasOpcode_eq checked)
    | reference rightName =>
      change rawHasOpcode raw "copy" || rawHasOpcode raw "constrain_eq" = true at checked
      cases copy : rawHasOpcode raw "copy" with
      | false =>
        simp [copy] at checked
        exact .constrainEq _ _ (rawHasOpcode_eq checked)
      | true =>
        exact .copy left rightName (rawHasOpcode_eq copy)
  | impact guard inputs =>
    change rawHasOpcode raw "impact" = true at checked
    exact .impact guard inputs (rawHasOpcode_eq checked)
  | output values =>
    change rawHasOpcode raw "output" = true at checked
    exact .output values (rawHasOpcode_eq checked)
  | hash inputs output =>
    change rawHasOpcode raw "transient_hash" = true at checked
    exact .hash inputs output (rawHasOpcode_eq checked)
  | not value output =>
    change rawHasOpcode raw "not" = true at checked
    exact .not value output (rawHasOpcode_eq checked)
  | select condition a b output =>
    change rawHasOpcode raw "cond_select" = true at checked
    exact .select condition a b output (rawHasOpcode_eq checked)

/-- The gate accepts every constructor in the scalar opcode profile. This
includes both equality spellings and each operation used by BoundedScalars.apply. -/
theorem profile_of_supportedScalarOpcode {raw : Json} {instruction : Instruction}
    (supported : SupportedScalarOpcode raw instruction) :
    supportedScalarOpcodeProfile raw instruction = true := by
  cases supported with
  | publicInput output opcode =>
    change rawHasOpcode raw "public_input" = true
    exact rawHasOpcode_of_eq opcode
  | privateInput output opcode =>
    change rawHasOpcode raw "private_input" = true
    exact rawHasOpcode_of_eq opcode
  | add a b output opcode =>
    change rawHasOpcode raw "add" = true
    exact rawHasOpcode_of_eq opcode
  | mul a b output opcode =>
    change rawHasOpcode raw "mul" = true
    exact rawHasOpcode_of_eq opcode
  | neg value output opcode =>
    change rawHasOpcode raw "neg" = true
    exact rawHasOpcode_of_eq opcode
  | bits value width opcode =>
    change rawHasOpcode raw "constrain_bits" = true
    exact rawHasOpcode_of_eq opcode
  | boolean value opcode =>
    change rawHasOpcode raw "constrain_to_boolean" = true
    exact rawHasOpcode_of_eq opcode
  | lessThan a b width output opcode =>
    change rawHasOpcode raw "less_than" = true
    exact rawHasOpcode_of_eq opcode
  | assertion condition opcode =>
    change rawHasOpcode raw "assert" = true
    exact rawHasOpcode_of_eq opcode
  | testEq a b output opcode =>
    change rawHasOpcode raw "test_eq" = true
    exact rawHasOpcode_of_eq opcode
  | copy source destination opcode =>
    change rawHasOpcode raw "copy" || rawHasOpcode raw "constrain_eq" = true
    rw [rawHasOpcode_of_eq opcode]
    simp
  | impact guard inputs opcode =>
    change rawHasOpcode raw "impact" = true
    exact rawHasOpcode_of_eq opcode
  | output values opcode =>
    change rawHasOpcode raw "output" = true
    exact rawHasOpcode_of_eq opcode
  | hash inputs output opcode =>
    change rawHasOpcode raw "transient_hash" = true
    exact rawHasOpcode_of_eq opcode
  | not value output opcode =>
    change rawHasOpcode raw "not" = true
    exact rawHasOpcode_of_eq opcode
  | select condition a b output opcode =>
    change rawHasOpcode raw "cond_select" = true
    exact rawHasOpcode_of_eq opcode
  | constrainEq a b opcode =>
    cases b with
    | immediate _ =>
      change rawHasOpcode raw "constrain_eq" = true
      exact rawHasOpcode_of_eq opcode
    | reference _ =>
      change rawHasOpcode raw "copy" || rawHasOpcode raw "constrain_eq" = true
      rw [rawHasOpcode_of_eq opcode]
      simp

/-- Every item and decoded instruction must pass the executable opcode-shape
gate, and the lists must have equal length. -/
def checkedScalarOpcodeProfile : List (Json × Nat) → List Instruction → Bool
  | [], [] => true
  | _ :: _, [] => false
  | [], _ :: _ => false
  | (raw, _) :: items, instruction :: instructions =>
      supportedScalarOpcodeProfile raw instruction &&
        checkedScalarOpcodeProfile items instructions

private theorem bind_ok {first : Except String α} {next : α → Except String β}
    {value : β} : (first >>= next) = .ok value ↔
    ∃ intermediate, first = .ok intermediate ∧ next intermediate = .ok value := by
  cases first <;> simp [Bind.bind, Except.bind]

private theorem supportedScalarOpcodeProfile_of_strict_decode {raw : Json}
    {instruction : Instruction}
    (decoded : NativeRelationJson.decodeInstruction raw = .ok instruction) :
    supportedScalarOpcodeProfile raw instruction = true := by
  unfold NativeRelationJson.decodeInstruction at decoded
  simp only [bind_ok] at decoded
  obtain ⟨opcode, parsed, decoded⟩ := decoded
  change Backend.Native.stringField raw "op" = .ok opcode at parsed
  split at decoded
  all_goals
    try simp only [bind_ok, Pure.pure, Except.pure, Except.ok.injEq] at decoded
  all_goals
    first
    | grind [supportedScalarOpcodeProfile, rawHasOpcode_of_eq]
    | skip
  case h_8 =>
    change (do
      exactFields raw ["op", "val", "output"]
      let source ← decodeOperandField raw "val"
      let output ← NativeRelationJson.stringField raw "output"
      NativeRelationJson.ensure (validIdentifier output) "invalid native SSA definition"
      return Instruction.equal source (.reference output)) = .ok instruction at decoded
    simp only [bind_ok, Pure.pure, Except.pure, Except.ok.injEq] at decoded
    obtain ⟨_, _, source, _, output, _, _, _, rfl⟩ := decoded
    simp [supportedScalarOpcodeProfile, rawHasOpcode_of_eq parsed]
  case h_10 =>
    obtain ⟨_, _, left, _, right, _, rfl⟩ := decoded
    cases right <;> simp [supportedScalarOpcodeProfile, rawHasOpcode_of_eq parsed]
  case h_16 =>
    obtain ⟨_, _, guard, _, decoded⟩ := decoded
    cases guard with
    | immediate active =>
      simp only [bind_ok, Except.ok.injEq] at decoded
      obtain ⟨_, _, _, _, inputs, _, rfl⟩ := decoded
      exact rawHasOpcode_of_eq parsed
    | reference _ =>
      change Except.error _ = .ok instruction at decoded
      contradiction
  case h_18 =>
    change Except.error _ = .ok instruction at decoded
    contradiction

/-- The strict decoder already checks the producer spelling and decoded shape
of every row, including copy and constrain_eq. -/
theorem checkedScalarOpcodeProfile_of_strict_decode
    {items : List (Json × Nat)} {instructions : List Instruction}
    (decoded : (items.map Prod.fst).mapM NativeRelationJson.decodeInstruction = .ok instructions) :
    checkedScalarOpcodeProfile items instructions = true := by
  induction items generalizing instructions with
  | nil =>
    cases decoded
    rfl
  | cons item items ih =>
    rcases item with ⟨raw, index⟩
    simp only [List.map_cons, List.mapM_cons, bind_ok, Pure.pure, Except.pure, Except.ok.injEq] at decoded
    obtain ⟨instruction, first, remaining, rest, rfl⟩ := decoded
    simp only [checkedScalarOpcodeProfile, supportedScalarOpcodeProfile_of_strict_decode first,
      ih rest, Bool.and_self]

theorem SupportedScalarOpcodeTrace.ofCheckedProfile
    {items : List (Json × Nat)} {instructions : List Instruction}
    (checked : checkedScalarOpcodeProfile items instructions = true) :
    SupportedScalarOpcodeTrace items instructions := by
  induction items generalizing instructions with
  | nil =>
    cases instructions with
    | nil => exact .nil
    | cons instruction instructions => simp [checkedScalarOpcodeProfile] at checked
  | cons item items ih =>
    rcases item with ⟨raw, index⟩
    cases instructions with
    | nil => simp [checkedScalarOpcodeProfile] at checked
    | cons instruction instructions =>
      simp only [checkedScalarOpcodeProfile, Bool.and_eq_true] at checked
      rcases checked with ⟨headChecked, tailChecked⟩
      exact .cons (supportedScalarOpcode_of_profile headChecked) (ih tailChecked)

/-- Successful decoding supplies the exact decoder proof for each item. The
checked profile supplies the opcode constructors, so callers need no manually
authored SupportedScalarOpcodeTrace. -/
theorem NativeDefinitionTrace.ofDecodedCheckedProfile
    {items : List (Json × Nat)} {instructions : List Instruction}
    (decoded : (items.map Prod.fst).mapM NativeRelationJson.decodeInstruction = .ok instructions)
    (checked : checkedScalarOpcodeProfile items instructions = true) :
    NativeDefinitionTrace items instructions :=
  NativeDefinitionTrace.ofDecodedSupportedOpcodes
    (SupportedScalarOpcodeTrace.ofCheckedProfile checked) decoded

/-- An accepted producer fold preserves native definitions once its decoded
instructions pass the scalar opcode gate. -/
theorem validateInstructionLoop_nativeDefinitions_of_checkedProfile
    {expected : Expected} {items : List (Json × Nat)} {instructions : List Instruction}
    {initial final : State}
    (inputSchema : ∀ requirement ∈ expected.inputs, requirement.ty.isForeign = false)
    (initialNativeDefinitions : NativeDefinitions initial)
    (decoded : (items.map Prod.fst).mapM NativeRelationJson.decodeInstruction = .ok instructions)
    (profile : checkedScalarOpcodeProfile items instructions = true)
    (accepted : validateInstructionLoop expected items initial = .ok final) :
    NativeDefinitions final :=
  validateInstructionLoop_nativeDefinitions_of_trace inputSchema initialNativeDefinitions
    (NativeDefinitionTrace.ofDecodedCheckedProfile decoded profile) accepted

end Noctium.Verification.ScalarValidationOpcodeProfile
