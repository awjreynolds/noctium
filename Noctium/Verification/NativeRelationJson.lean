import Lean
import Noctium.Verification.NativeRelation

namespace Noctium.Verification.NativeRelationJson

open Lean
open Noctium.Verification.NativeRelation

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
