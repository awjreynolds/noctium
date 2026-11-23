import Noctium.Backend.Zkir

open Noctium

private def name : String := "a\"\\b,(\"x\", \"y\")💠"
private def left : Expr .native := .ref name
private def right : Expr .native := .ref "right"
private def expression : Expr .native := .letE "shadow" (.add left right)
  (.letE "shadow" (.mul (.ref "shadow") right)
    (.add (.ref "shadow") (.mul (.add left right) right)))

private def fixture : Circuit := {
  name := "scalarCseParity"
  inputs := [{name, ty := .native, visibility := .«public»},
    {name := "right", ty := .native, visibility := .«public»},
    {name := "flag", ty := .bool, visibility := .«public»}]
  outputs := [
    {name := "add", ty := .native, value := .add left right},
    {name := "repeat", ty := .native, value := .add left right},
    {name := "mul", ty := .native, value := .mul left right},
    {name := "sub", ty := .native, value := .sub left right},
    {name := "select", ty := .native, value := .select (.ref "flag") left right},
    {name := "selectRepeat", ty := .native, value := .select (.ref "flag") left right},
    {name := "hashZero", ty := .native, value := .poseidon2 0 left right},
    {name := "hashOne", ty := .native, value := .poseidon2 1 left right},
    {name := "hashRepeat", ty := .native, value := .poseidon2 1 left right},
    {name := "shadowing", ty := .native, value := expression}]
}

#guard (Backend.Zkir.lowerCircuit fixture).isOk

private def key (opcode : String) (operands : List String) (domain : Option Nat := none) : Backend.Zkir.ExpressionKey :=
  (opcode, operands, domain)

#guard key "add" [name, "right"] == key "add" [name, "right"]
#guard key "add" [name, "right"] != key "mul" [name, "right"]
#guard key "neg" [name] != key "neg" [name, "right"]
#guard key "add" [name, "right"] != key "add" ["right", name]
#guard key "transient_hash" [name, "right"] (some 0) != key "transient_hash" [name, "right"] (some 1)
#guard key "transient_hash" [name, "right"] none != key "transient_hash" [name, "right"] (some 0)

private def semanticMutant (program : Lean.Json) : Lean.Json := Id.run do
  let .ok fields := program.getObj? | return .null
  let .ok instructions := program.getObjValAs? (Array Lean.Json) "instructions" | return .null
  let changed := instructions.map fun instruction =>
    match instruction.getObj? with
    | .error _ => instruction
    | .ok fields => Lean.Json.mkObj (fields.toList.map fun (name, value) =>
      (name, if name == "op" && value == Lean.toJson ("add" : String) then Lean.toJson ("mul" : String) else value))
  return Lean.Json.mkObj (fields.toList.map fun (name, value) =>
    (name, if name == "instructions" then Lean.Json.arr changed else value))

#guard match Backend.Zkir.lowerCircuit fixture, Backend.Native.expectedCircuit fixture with
  | .ok program, .ok expected => !(Backend.Native.validate expected (semanticMutant program)).isOk
  | _, _ => false

private def nativeZeroFixture : Circuit := {
  name := "nativeZeroAdd"
  inputs := [{name := "witness", ty := .native, visibility := .private},
    {name := "visible", ty := .native, visibility := .«public»}]
  constraints := [.eq
    (.add (.native 0)
      (.assertE (.eq (.ref "witness" : Expr .native) (.native 5)) (.ref "witness")))
    (.ref "visible")]
  outputs := [
    { name := "value"
      ty := .native
      value := .add (.letE "alias" (.ref "visible" : Expr .native) (.ref "alias")) (.native 0) }]
}

#guard match Backend.Zkir.lowerCircuit nativeZeroFixture with
  | .error _ => false
  | .ok program => Id.run do
    let .ok instructions := program.getObjValAs? (Array Lean.Json) "instructions"
      | return false
    let opcodes := instructions.map Backend.Native.opcode
    let inputs := instructions.filter fun instruction =>
      let op := Backend.Native.opcode instruction
      op == "private_input" || op == "public_input"
    let names := inputs.map fun instruction => (instruction.getObjValAs? String "output").toOption
    let .ok output := instructions.back!.getObjValAs? (Array String) "vals" | return false
    return !opcodes.contains "add" && (opcodes.filter (· == "assert")).size == 2 &&
      names == #[some "%input_witness", some "%input_visible"] && output == #["%input_visible"]

/-- Emit the actual relation for before/after byte-parity checks. -/
def main : IO Unit := do
  match Backend.Zkir.lowerCircuit fixture with
  | .error diagnostic => throw (IO.userError diagnostic.message)
  | .ok program => IO.println program.compress
