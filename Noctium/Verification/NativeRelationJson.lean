import Lean
import Noctium.Backend.NativeProducer
import Noctium.Verification.NativeRelation

namespace Noctium.Verification.NativeRelationJson

open Lean
open Noctium.Verification.NativeRelation

private theorem bind_ok {ε α β} {first : Except ε α} {next : α → Except ε β}
    {value : β} : (first >>= next) = .ok value ↔
    ∃ intermediate, first = .ok intermediate ∧ next intermediate = .ok value := by
  cases first <;> simp [Bind.bind, Except.bind]

def ensure (condition : Bool) (message : String) : Except String Unit :=
  if condition then .ok () else .error message

def objectFields (value : Json) : Except String (List String) := do
  pure ((← value.getObj?).toList.map Prod.fst)

def exactFields (value : Json) (expected : List String) : Except String Unit := do
  let actual ← objectFields value
  ensure (actual.length == expected.length && actual.eraseDups.length == actual.length &&
    actual.all expected.contains && expected.all actual.contains)
    "missing, unknown or mismatched native JSON fields"

def stringField (value : Json) (name : String) : Except String String := do
  (← value.getObjVal? name).getStr?

def arrayField (value : Json) (name : String) : Except String (Array Json) := do
  (← value.getObjVal? name).getArr?

def naturalField (value : Json) (name : String) : Except String Nat := do
  let item ← value.getObjVal? name
  match item with
  | .num number => do
    ensure (number.exponent == 0) "native JSON version values must be integer numbers"
    match number.mantissa with
    | .ofNat natural => pure natural
    | .negSucc _ => throw "native JSON version values must be natural numbers"
  | _ => throw "native JSON version values must be natural numbers"

def nativeType : Json := toJson ("Scalar<BLS12-381>" : String)

def checkNativeType (value : Json) : Except String Unit := do
  ensure ((← value.getStr?) == "Scalar<BLS12-381>") "unsupported native value type/encoding"

def hexDigit (value : Char) : Option Nat :=
  if '0' ≤ value && value ≤ '9' then some (value.toNat - '0'.toNat)
  else if 'a' ≤ value && value ≤ 'f' then some (value.toNat - 'a'.toNat + 10)
  else none

def decodeHexBytes : List Char → Except String (List Nat)
  | [] => pure []
  | high :: low :: rest => do
    let some high := hexDigit high | throw "invalid native hexadecimal immediate"
    let some low := hexDigit low | throw "invalid native hexadecimal immediate"
    pure ((high * 16 + low) :: (← decodeHexBytes rest))
  | _ => throw "native immediate must contain complete lowercase hexadecimal bytes"

def littleEndianValue : List Nat → Nat
  | [] => 0
  | byte :: rest => byte + 256 * littleEndianValue rest

/-- Decode the producer's canonical little-endian byte spelling for a scalar.
This handles the full canonical field range, including the claim's 0, 1, 2,
and 3 constants. -/
def decodeImmediate (text : String) : Except String Nat := do
  ensure (text.startsWith "0x") "native immediate must start with lowercase 0x"
  let bytes ← decodeHexBytes (text.toList.drop 2)
  ensure (!bytes.isEmpty && bytes.length ≤ 32) "native immediate has an invalid byte width"
  ensure (bytes.length == 1 || bytes.getLast? != some 0) "nonminimal native immediate"
  let number := littleEndianValue bytes
  ensure (number < Field.modulus) "noncanonical native field immediate"
  pure number

def validIdentifier (name : String) : Bool :=
  name.startsWith "%" && name.length > 1 && name.utf8ByteSize ≤ 1024

/-- A percent-prefixed SSA reference cannot be parsed as a hexadecimal
immediate. -/
theorem reference_not_immediate {text : String} (reference : text.startsWith "%" = true) :
    text.startsWith "0x" = false := by
  have prefixed : ['%'] <+: text.toList := by simpa using reference
  rcases prefixed with ⟨tail, equal⟩
  apply String.startsWith_string_eq_false_iff.mpr
  rw [← equal]
  simp

private theorem digitChar_byteSize (digit : Nat) (single : digit < 10) :
    (String.singleton digit.digitChar).utf8ByteSize = 1 := by
  have decimal : ∀ digit : Fin 10,
      (String.singleton digit.val.digitChar).utf8ByteSize = 1 := by decide
  exact decimal ⟨digit, single⟩

private theorem repr_byteSize_eq_length (index : Nat) :
    index.repr.utf8ByteSize = index.repr.length := by
  induction index using Nat.strongRecOn with
  | ind index smaller =>
    by_cases single : index < 10
    · rw [Nat.repr_of_lt single, digitChar_byteSize index single, String.length_singleton]
    · have quotient : index / 10 < index := Nat.div_lt_self (by omega) (by decide)
      rw [Nat.repr_of_ge (by omega), String.utf8ByteSize_append, String.length_append,
        smaller _ quotient, digitChar_byteSize _ (by omega), String.length_singleton]

/-- Generated numeric SSA names fit the identifier limit whenever the
index uses at most eight decimal digits. -/
theorem generatedIdentifier_valid (index : Nat) (bounded : index < 10 ^ 8) :
    validIdentifier s!"%v{index}" = true := by
  have digits : index.repr.length ≤ 8 :=
    (Nat.length_repr_le_iff (by decide)).mpr bounded
  have size : index.repr.utf8ByteSize ≤ 8 := by simpa [repr_byteSize_eq_length] using digits
  change validIdentifier ("%v" ++ index.repr) = true
  unfold validIdentifier
  have starts : ("%v" ++ index.repr).startsWith "%" = true := by
    apply String.startsWith_string_iff.mpr
    rw [String.toList_append]
    have head : "%v".toList = ['%', 'v'] := by decide
    have marker : "%".toList = ['%'] := by decide
    rw [head, marker]
    exact ⟨'v' :: index.repr.toList, rfl⟩
  have length : ("%v" ++ index.repr).length > 1 := by
    rw [String.length_append]
    have head : "%v".length = 2 := by decide
    rw [head]
    omega
  have bytes : ("%v" ++ index.repr).utf8ByteSize ≤ 1024 := by
    rw [String.utf8ByteSize_append]
    have head : "%v".utf8ByteSize = 2 := by decide
    rw [head]
    omega
  simp only [starts, length, bytes, decide_true, Bool.true_and]

/-- Generated SSA identifiers fit the decoder's 1024-byte limit at every
index permitted by the native output-slot capacity. -/
theorem generatedIdentifier_fits_output_capacity (index : Nat)
    (bounded : index < Noctium.Backend.Native.maxInstructions *
      Noctium.Backend.Native.maxVectorLength) :
    validIdentifier s!"%v{index}" = true := by
  apply generatedIdentifier_valid
  have capacity : Noctium.Backend.Native.maxInstructions *
      Noctium.Backend.Native.maxVectorLength < 10 ^ 8 := by
    decide
  omega

def decodeOperand (value : Json) : Except String Operand := do
  let text ← value.getStr?
  if text.startsWith "0x" then
    return .immediate (scalar (← decodeImmediate text))
  ensure (validIdentifier text) "invalid native SSA reference"
  return .reference text

def decodeOperands (value : Json) : Except String (List Operand) := do
  let values ← value.getArr?
  values.toList.mapM decodeOperand

def decodeOperandField (value : Json) (name : String) : Except String Operand := do
  decodeOperand (← value.getObjVal? name)

private def decodeCopy (value : Json) : Except String Instruction := do
  exactFields value ["op", "val", "output"]
  let source ← stringField value "val"
  ensure (validIdentifier source) "invalid native SSA reference"
  let output ← stringField value "output"
  ensure (validIdentifier output) "invalid native SSA definition"
  return .equal (.reference source) (.reference output)

def decodeInstruction (value : Json) : Except String Instruction := do
  let opcode ← stringField value "op"
  match opcode with
  | "public_input" | "private_input" => do
    exactFields value ["op", "guard", "type", "output"]
    ensure ((← value.getObjVal? "guard").isNull)
      "preprocessing-only native input guards are unsupported"
    checkNativeType (← value.getObjVal? "type")
    let output ← stringField value "output"
    ensure (validIdentifier output) "invalid native SSA definition"
    return .input (if opcode == "public_input" then .«public» else .«private» ) output
  | "constrain_to_boolean" => do
    exactFields value ["op", "val"]
    return .boolean (← decodeOperandField value "val")
  | "constrain_bits" => do
    exactFields value ["op", "val", "bits"]
    let bits ← naturalField value "bits"
    ensure (0 < bits && bits ≤ Noctium.ScalarPolicy.maxBits) "unsupported native bit width"
    return .bits (← decodeOperandField value "val") bits
  | "less_than" => do
    exactFields value ["op", "a", "b", "bits", "output"]
    let bits ← naturalField value "bits"
    ensure (0 < bits && bits ≤ Noctium.ScalarPolicy.maxBits) "unsupported native bit width"
    let a ← decodeOperandField value "a"
    let b ← decodeOperandField value "b"
    let output ← stringField value "output"
    ensure (validIdentifier output) "invalid native SSA definition"
    return .lessThan a b bits output
  | "add" => do
    exactFields value ["op", "a", "b", "output"]
    let a ← decodeOperandField value "a"
    let b ← decodeOperandField value "b"
    let output ← stringField value "output"
    ensure (validIdentifier output) "invalid native SSA definition"
    return .add a b output
  | "mul" => do
    exactFields value ["op", "a", "b", "output"]
    let a ← decodeOperandField value "a"
    let b ← decodeOperandField value "b"
    let output ← stringField value "output"
    ensure (validIdentifier output) "invalid native SSA definition"
    return .mul a b output
  | "copy" => decodeCopy value
  | "neg" => do
    exactFields value ["op", "a", "output"]
    let a ← decodeOperandField value "a"
    let output ← stringField value "output"
    ensure (validIdentifier output) "invalid native SSA definition"
    return .neg a output
  | "constrain_eq" => do
    exactFields value ["op", "a", "b"]
    return .equal (← decodeOperandField value "a") (← decodeOperandField value "b")
  | "test_eq" => do
    exactFields value ["op", "a", "b", "output"]
    let a ← decodeOperandField value "a"
    let b ← decodeOperandField value "b"
    let output ← stringField value "output"
    ensure (validIdentifier output) "invalid native SSA definition"
    return .testEq a b output
  | "not" => do
    exactFields value ["op", "a", "output"]
    let a ← decodeOperandField value "a"
    let output ← stringField value "output"
    ensure (validIdentifier output) "invalid native SSA definition"
    return .not a output
  | "cond_select" => do
    exactFields value ["op", "bit", "a", "b", "output"]
    let condition ← decodeOperandField value "bit"
    let a ← decodeOperandField value "a"
    let b ← decodeOperandField value "b"
    let output ← stringField value "output"
    ensure (validIdentifier output) "invalid native SSA definition"
    return .select condition a b output
  | "transient_hash" => do
    exactFields value ["op", "inputs", "output"]
    let inputs ← decodeOperands (← value.getObjVal? "inputs")
    let output ← stringField value "output"
    ensure (validIdentifier output) "invalid native SSA definition"
    return .hash inputs output
  | "assert" => do
    exactFields value ["op", "cond"]
    return .assert (← decodeOperandField value "cond")
  | "impact" => do
    exactFields value ["op", "guard", "inputs"]
    let guard ← decodeOperandField value "guard"
    match guard with
    | .immediate active => ensure (decide (active = one)) "only literal-one always-active Impact is supported"
    | .reference _ => throw "only literal-one always-active Impact is supported"
    let inputs ← decodeOperands (← value.getObjVal? "inputs")
    return .impact guard inputs
  | "output" => do
    exactFields value ["op", "vals"]
    return .output (← decodeOperands (← value.getObjVal? "vals"))
  | _ => throw s!"unsupported native instruction '{opcode}'"

/-- The exact Copy object emitted for a reused comparison decodes to the field
equality between its source and destination references. Copy's `val` and
`output` are SSA bindings, so immediate sources are rejected. Freshness remains
the native producer's admission check. -/
private theorem decode_comparisonCopyJson (source destination : String)
    (sourceValid : validIdentifier source = true)
    (destinationValid : validIdentifier destination = true) :
    decodeCopy (Json.mkObj [
      ("op", toJson ("copy" : String)), ("val", toJson source),
      ("output", toJson destination)]) =
        .ok (.equal (.reference source) (.reference destination)) := by
  let copyJson := Json.mkObj [
    ("op", toJson ("copy" : String)), ("val", toJson source),
    ("output", toJson destination)]
  have fields : exactFields copyJson ["op", "val", "output"] = .ok () := by
    rfl
  have sourceField : stringField copyJson "val" = .ok source := by
    rfl
  have outputField : stringField copyJson "output" = .ok destination := by
    rfl
  change decodeCopy copyJson = .ok (.equal (.reference source) (.reference destination))
  unfold decodeCopy
  simp [Bind.bind, Except.bind, Pure.pure, Except.pure, fields, sourceField, ensure, sourceValid,
    outputField, destinationValid]

/-- The parser dispatches a Copy object to the strict Copy decoder. -/
theorem decodeInstruction_copyJson (source destination : String)
    (sourceValid : validIdentifier source = true)
    (destinationValid : validIdentifier destination = true) :
    decodeInstruction (Json.mkObj [
      ("op", toJson ("copy" : String)), ("val", toJson source),
      ("output", toJson destination)]) =
        .ok (.equal (.reference source) (.reference destination)) := by
  let copyJson := Json.mkObj [
    ("op", toJson ("copy" : String)), ("val", toJson source),
    ("output", toJson destination)]
  have opcode : stringField copyJson "op" = .ok "copy" := by
    rfl
  have decoded : decodeCopy copyJson = .ok (.equal (.reference source) (.reference destination)) := by
    exact decode_comparisonCopyJson source destination sourceValid destinationValid
  change decodeInstruction copyJson = .ok (.equal (.reference source) (.reference destination))
  unfold decodeInstruction
  rw [opcode]
  simpa only [Bind.bind, Except.bind] using decoded

/-- Any successfully decoded Copy exposes the same source and destination
strings in its raw fields. -/
theorem decodeInstruction_copyFields {raw : Json} {source destination : String}
    (opcode : stringField raw "op" = .ok "copy")
    (decoded : decodeInstruction raw =
      .ok (.equal (.reference source) (.reference destination))) :
    stringField raw "val" = .ok source ∧
      stringField raw "output" = .ok destination ∧
      validIdentifier source = true := by
  unfold decodeInstruction at decoded
  simp only [bind_ok] at decoded
  rcases decoded with ⟨opcodeName, opcodeParsed, body⟩
  have opcodeEq : opcodeName = "copy" := Except.ok.inj (opcodeParsed.symm.trans opcode)
  subst opcodeName
  unfold decodeCopy at body
  simp only [bind_ok] at body
  rcases body with ⟨_, _, sourceName, sourceParsed, _, sourceValid, _, outputParsed, result⟩
  rcases result with ⟨_, rest⟩
  rcases rest with ⟨_, pureResult⟩
  simp only [Pure.pure, Except.pure] at pureResult
  have resultEq := Except.ok.inj pureResult
  injection resultEq with sourceEq destinationEq
  injection sourceEq with sourceTextEq
  injection destinationEq with destinationTextEq
  have sourceValidBool : validIdentifier sourceName = true := by
    unfold ensure at sourceValid
    by_cases valid : validIdentifier sourceName
    · exact valid
    · simp [valid] at sourceValid
  have sourceIdentifierValid : validIdentifier source = true := by
    rw [← sourceTextEq]
    exact sourceValidBool
  constructor
  · rw [← sourceTextEq]
    exact sourceParsed
  constructor
  · rw [← destinationTextEq]
    exact outputParsed
  · exact sourceIdentifierValid

theorem decodeOperandField_reference_of_stringField {raw : Json} {name text : String}
    (parsed : stringField raw name = .ok text)
    (reference : validIdentifier text = true) :
    decodeOperandField raw name = .ok (.reference text) := by
  unfold stringField at parsed
  unfold decodeOperandField
  simp only [bind_ok] at parsed
  rcases parsed with ⟨json, jsonParsed, textParsed⟩
  rw [jsonParsed]
  unfold decodeOperand
  have startsPercent : text.startsWith "%" = true := by
    have validShape : (text.startsWith "%" && text.length > 1 &&
        text.utf8ByteSize ≤ 1024) = true := by simpa [validIdentifier] using reference
    exact (Bool.and_eq_true_iff.mp (Bool.and_eq_true_iff.mp validShape).1).1
  have noHex : ¬ (['0', 'x'] <+: text.toList) := by
    have pref : ['%'] <+: text.toList := by simpa using startsPercent
    rcases pref with ⟨tail, equal⟩
    rw [← equal]
    simp
  simp [Bind.bind, Except.bind, Pure.pure, Except.pure, textParsed, noHex, reference, ensure]

/-- Decode the exact ZKIR 3.2 root and typed Native relation subset represented
by `NativeRelation`. This checks JSON shape and encoding only. -/
def decode (json : Json) : Except String Program := do
  exactFields json ["version", "inputs", "outputs", "do_communications_commitment", "instructions"]
  let version ← json.getObjVal? "version"
  exactFields version ["major", "minor"]
  ensure ((← naturalField version "major") == 3 && (← naturalField version "minor") == 2)
    "unsupported native producer IR version"
  let inputs ← arrayField json "inputs"
  ensure inputs.isEmpty "native root input declarations are unsupported"
  let outputs ← arrayField json "outputs"
  for output in outputs do checkNativeType output
  let communicationsCommitment ← (← json.getObjVal? "do_communications_commitment").getBool?
  let instructions ← arrayField json "instructions"
  let decoded ← instructions.toList.mapM decodeInstruction
  pure {
    instructions := decoded
    outputArity := outputs.size
    communicationsCommitment
  }

private def hexByte (value : Nat) : String :=
  let digit (n : Nat) : Char := Char.ofNat ((if n < 10 then '0'.toNat else 'a'.toNat - 10) + n)
  String.ofList [digit (value / 16), digit (value % 16)]

private def littleEndianBytes (value : Nat) : Nat → List Nat
  | 0 => []
  | fuel + 1 => value % 256 :: littleEndianBytes (value / 256) fuel

private def encodeImmediate (value : Scalar) : Json :=
  let bytes := littleEndianBytes value.val (value.val.log2 / 8 + 1)
  toJson ("0x" ++ String.join (bytes.map hexByte))

private def encodeOperand : Operand → Json
  | .immediate value => encodeImmediate value
  | .reference name => toJson name

private def encodeOperands (values : List Operand) : Json :=
  Json.arr (values.toArray.map encodeOperand)

private def instruction (opcode : String) (fields : List (String × Json)) : Json :=
  Json.mkObj (("op", toJson opcode) :: fields)

private def visibilityOpcode (visibility : Noctium.Visibility) : String :=
  match visibility with
  | Noctium.Visibility.public => "public_input"
  | Noctium.Visibility.«private» => "private_input"

private def encodeInstruction : Instruction → Json
  | .input visibility output => instruction (visibilityOpcode visibility)
      [("guard", Json.null), ("type", nativeType), ("output", toJson output)]
  | .boolean value => instruction "constrain_to_boolean" [("val", encodeOperand value)]
  | .bits value width => instruction "constrain_bits"
      [("val", encodeOperand value), ("bits", toJson width)]
  | .lessThan a b width output => instruction "less_than"
      [("a", encodeOperand a), ("b", encodeOperand b), ("bits", toJson width),
        ("output", toJson output)]
  | .add a b output => instruction "add"
      [("a", encodeOperand a), ("b", encodeOperand b), ("output", toJson output)]
  | .mul a b output => instruction "mul"
      [("a", encodeOperand a), ("b", encodeOperand b), ("output", toJson output)]
  | .neg a output => instruction "neg" [("a", encodeOperand a), ("output", toJson output)]
  | .equal a b => instruction "constrain_eq" [("a", encodeOperand a), ("b", encodeOperand b)]
  | .testEq a b output => instruction "test_eq"
      [("a", encodeOperand a), ("b", encodeOperand b), ("output", toJson output)]
  | .not a output => instruction "not" [("a", encodeOperand a), ("output", toJson output)]
  | .select condition a b output => instruction "cond_select"
      [("bit", encodeOperand condition), ("a", encodeOperand a), ("b", encodeOperand b),
        ("output", toJson output)]
  | .hash inputs output => instruction "transient_hash"
      [("inputs", encodeOperands inputs), ("output", toJson output)]
  | .assert condition => instruction "assert" [("cond", encodeOperand condition)]
  | .impact guard inputs => instruction "impact"
      [("guard", encodeOperand guard), ("inputs", encodeOperands inputs)]
  | .output values => instruction "output" [("vals", encodeOperands values)]

/-- Encode the typed relation as the exact standalone ZKIR 3.2 root shape. -/
def encode (program : Program) : Json := Json.mkObj [
  ("version", Json.mkObj [("major", toJson (3 : Nat)), ("minor", toJson (2 : Nat))]),
  ("inputs", Json.arr #[]),
  ("outputs", Json.arr (Array.replicate program.outputArity nativeType)),
  ("do_communications_commitment", toJson program.communicationsCommitment),
  ("instructions", Json.arr (program.instructions.toArray.map encodeInstruction))]

end Noctium.Verification.NativeRelationJson
