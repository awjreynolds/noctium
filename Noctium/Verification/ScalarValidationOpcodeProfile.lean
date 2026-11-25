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
  | .equal (.reference _) (.reference _) =>
      rawHasOpcode raw "copy" || rawHasOpcode raw "constrain_eq"
  | .equal _ _ => rawHasOpcode raw "constrain_eq"
  | .impact _ _ => rawHasOpcode raw "impact"
  | .output _ => rawHasOpcode raw "output"
  | .hash _ _ => rawHasOpcode raw "transient_hash"
  | .not _ _ | .select _ _ _ _ => false

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
    cases left with
    | immediate leftValue =>
      cases right with
      | immediate rightValue =>
        change rawHasOpcode raw "constrain_eq" = true at checked
        exact .constrainEq _ _ (rawHasOpcode_eq checked)
      | reference rightName =>
        change rawHasOpcode raw "constrain_eq" = true at checked
        exact .constrainEq _ _ (rawHasOpcode_eq checked)
    | reference leftName =>
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
          exact .copy leftName rightName (rawHasOpcode_eq copy)
  | impact guard inputs =>
    change rawHasOpcode raw "impact" = true at checked
    exact .impact guard inputs (rawHasOpcode_eq checked)
  | output values =>
    change rawHasOpcode raw "output" = true at checked
    exact .output values (rawHasOpcode_eq checked)
  | hash inputs output =>
    change rawHasOpcode raw "transient_hash" = true at checked
    exact .hash inputs output (rawHasOpcode_eq checked)
  | not _ _ => simp [supportedScalarOpcodeProfile] at checked
  | select _ _ _ _ => simp [supportedScalarOpcodeProfile] at checked

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
  | constrainEq a b opcode =>
    cases a with
    | immediate _ =>
      change rawHasOpcode raw "constrain_eq" = true
      exact rawHasOpcode_of_eq opcode
    | reference _ =>
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
