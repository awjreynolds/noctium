import Noctium.Verification.NativeRelationJson

namespace Noctium.Verification.NativeTypedBoolRelation

open Lean
open Noctium.Verification.NativeRelation
open Noctium.Verification.NativeRelationJson

/-- The exact two-constant Bool `and`, one-output `encode`, and Native output
fragment supported by the scoped ZKIR witness relation below. -/
structure AndOutput where
  leftName : String
  leftValue : Bool
  rightName : String
  rightValue : Bool
  gateName : String
  encodedName : String
  outputName : String
  outputLinked : outputName = encodedName
  deriving Repr, DecidableEq

private def decodeBoolConstant (instruction : Json) : Except String (String × Bool) := do
  exactFields instruction ["op", "type", "encoding", "output"]
  ensure ((← stringField instruction "op") == "load_constant")
    "expected Bool load_constant"
  ensure ((← stringField instruction "type") == "Bool")
    "expected Bool load_constant"
  let output ← stringField instruction "output"
  ensure (validIdentifier output) "invalid typed Bool SSA definition"
  let encodings ← arrayField instruction "encoding"
  ensure (encodings.size == 1) "Bool constant must have one encoding element"
  let immediate ← (encodings[0]!).getStr?
  let value ← decodeImmediate immediate
  ensure (value ≤ 1) "Bool constant must encode zero or one"
  pure (output, value == 1)

private def decodeAnd (instruction : Json) : Except String (String × String × String) := do
  exactFields instruction ["op", "inputs", "output"]
  ensure ((← stringField instruction "op") == "and") "expected typed Bool and"
  let output ← stringField instruction "output"
  ensure (validIdentifier output) "invalid typed Bool SSA definition"
  let inputs ← arrayField instruction "inputs"
  ensure (inputs.size == 2) "typed Bool and must have two inputs"
  let left ← inputs[0]!.getStr?
  let right ← inputs[1]!.getStr?
  ensure (validIdentifier left && validIdentifier right) "invalid typed Bool SSA reference"
  pure (left, right, output)

private def decodeBoolEncode (instruction : Json) : Except String (String × String) := do
  exactFields instruction ["op", "input", "outputs"]
  ensure ((← stringField instruction "op") == "encode") "expected Bool encode"
  let input ← stringField instruction "input"
  ensure (validIdentifier input) "invalid typed Bool encode input"
  let outputs ← arrayField instruction "outputs"
  ensure (outputs.size == 1) "Bool encode must have one Native output"
  let output ← outputs[0]!.getStr?
  ensure (validIdentifier output) "invalid Native encode output"
  pure (input, output)

/-- Decode one complete, adjacent Bool-to-Native slice. The output instruction
is checked by the existing strict Native decoder. -/
def decodeAndOutput (instructions : Array Json) : Except String AndOutput := do
  ensure (instructions.size == 5) "typed Bool slice must contain five instructions"
  let (leftName, leftValue) ← decodeBoolConstant instructions[0]!
  let (rightName, rightValue) ← decodeBoolConstant instructions[1]!
  let (gateLeft, gateRight, gateName) ← decodeAnd instructions[2]!
  ensure (gateLeft == leftName && gateRight == rightName)
    "typed Bool and inputs must name the two preceding constants in order"
  let (encodeInput, encodedName) ← decodeBoolEncode instructions[3]!
  ensure (encodeInput == gateName) "Bool encode must consume the preceding and result"
  let definedNames := [leftName, rightName, gateName, encodedName]
  ensure (definedNames.eraseDups.length == definedNames.length)
    "typed Bool slice must use fresh SSA definitions"
  let output ← NativeRelationJson.decodeInstruction instructions[4]!
  let outputName ← match output with
    | .output [.reference name] => pure name
    | _ => throw "typed Bool slice must end in one Native output reference"
  if outputNameEq : outputName == encodedName then
    pure ⟨leftName, leftValue, rightName, rightValue, gateName, encodedName,
      outputName, eq_of_beq outputNameEq⟩
  else
    throw "Native output must name the Bool encode result"

/-- Decode a standalone ZKIR 3.2 root with no declared inputs, one Native
output, and exactly the scoped instruction fragment. Output authentication and
communications commitments stay outside this relation. -/
def decodeAndOutputRoot (json : Json) : Except String AndOutput := do
  exactFields json ["version", "inputs", "outputs", "do_communications_commitment", "instructions"]
  let version ← json.getObjVal? "version"
  exactFields version ["major", "minor"]
  ensure ((← naturalField version "major") == 3 && (← naturalField version "minor") == 2)
    "unsupported native producer IR version"
  let inputs ← arrayField json "inputs"
  ensure inputs.isEmpty "typed Bool root inputs are unsupported"
  let outputs ← arrayField json "outputs"
  ensure (outputs.size == 1) "typed Bool root must declare one Native output"
  checkNativeType outputs[0]!
  let _commitment ← (← json.getObjVal? "do_communications_commitment").getBool?
  decodeAndOutput (← arrayField json "instructions")

/-- Actual typed Bool assignments and their one-field Native encoding. A load
constant fixes its Bool wire, `and` constrains its result, and `encode` equates
the Native wire with that canonical field bit. -/
def Satisfies (slice : AndOutput) (witness : Assignment) : Prop :=
  witness slice.leftName = bit slice.leftValue ∧
  witness slice.rightName = bit slice.rightValue ∧
  witness slice.gateName =
    scalar ((witness slice.leftName).val * (witness slice.rightName).val) ∧
  witness slice.encodedName = witness slice.gateName

theorem output_of_satisfies (slice : AndOutput) (witness : Assignment)
    (satisfied : Satisfies slice witness) :
    witness slice.outputName = bit (slice.leftValue && slice.rightValue) := by
  rcases satisfied with ⟨leftWire, rightWire, gate, encoded⟩
  have gateMeaning : witness slice.gateName = bit (slice.leftValue && slice.rightValue) := by
    rw [gate, leftWire, rightWire]
    have modulusBound : 1 < Field.modulus := by decide
    cases slice.leftValue <;> cases slice.rightValue <;>
      simp [bit, scalar, zero, one, Nat.mod_eq_of_lt modulusBound]
  rw [slice.outputLinked, encoded]
  exact gateMeaning

/-- Decoder output and circuit satisfaction for the same ZKIR instruction
array. -/
def DecodedSatisfies (instructions : Array Json) (slice : AndOutput)
    (witness : Assignment) : Prop :=
  decodeAndOutput instructions = .ok slice ∧ Satisfies slice witness

/-- The exact decoded instruction array's witness constraints derive its
observed Native bit without a separate output-value premise. -/
theorem decoded_satisfaction (instructions : Array Json)
    (witness : Assignment) (slice : AndOutput)
    (decoded : DecodedSatisfies instructions slice witness) :
    witness slice.outputName = bit (slice.leftValue && slice.rightValue) :=
  output_of_satisfies slice witness decoded.2

/-- Root-level decoder output and circuit satisfaction for the same standalone
ZKIR root. -/
def DecodedRootSatisfies (json : Json) (slice : AndOutput)
    (witness : Assignment) : Prop :=
  decodeAndOutputRoot json = .ok slice ∧ Satisfies slice witness

/-- The decoded standalone root's witness constraints determine its sole
Native output bit. -/
theorem root_output_of_satisfies (json : Json) (witness : Assignment)
    (slice : AndOutput) (decoded : DecodedRootSatisfies json slice witness) :
    witness slice.outputName = bit (slice.leftValue && slice.rightValue) :=
  output_of_satisfies slice witness decoded.2

private def boolConstant (name : String) (value : String) : Json := Json.mkObj [
  ("op", toJson ("load_constant" : String)), ("type", toJson ("Bool" : String)),
  ("encoding", toJson ([value] : List String)), ("output", toJson name)]

private def andInstruction : Json := Json.mkObj [
  ("op", toJson ("and" : String)),
  ("inputs", toJson (["%bool_left", "%bool_right"] : List String)),
  ("output", toJson ("%bool_result" : String))]

private def encodeInstruction : Json := Json.mkObj [
  ("op", toJson ("encode" : String)), ("input", toJson ("%bool_result" : String)),
  ("outputs", toJson (["%native_result"] : List String))]

private def outputInstruction : Json := Json.mkObj [
  ("op", toJson ("output" : String)),
  ("vals", toJson (["%native_result"] : List String))]

private def root (instructions : Array Json) : Json := Json.mkObj [
  ("version", Json.mkObj [
    ("major", toJson (3 : Nat)), ("minor", toJson (2 : Nat))]),
  ("inputs", Json.arr #[]), ("outputs", Json.arr #[nativeType]),
  ("do_communications_commitment", toJson false), ("instructions", Json.arr instructions)]

private def fixture (left right : Bool) : Array Json := #[
  boolConstant "%bool_left" (if left then "0x01" else "0x00"),
  boolConstant "%bool_right" (if right then "0x01" else "0x00"),
  andInstruction, encodeInstruction, outputInstruction]

#guard match decodeAndOutputRoot (root (fixture true false)) with
  | .ok slice => slice.leftName == "%bool_left" && slice.leftValue == true &&
      slice.rightName == "%bool_right" && slice.rightValue == false &&
      slice.gateName == "%bool_result" && slice.encodedName == "%native_result" &&
      slice.outputName == "%native_result"
  | .error _ => false

#guard match decodeAndOutputRoot (root #[
    boolConstant "%bool_left" "0x02",
    boolConstant "%bool_right" "0x01",
    andInstruction, encodeInstruction, outputInstruction]) with
  | .error _ => true
  | .ok _ => false

end Noctium.Verification.NativeTypedBoolRelation
