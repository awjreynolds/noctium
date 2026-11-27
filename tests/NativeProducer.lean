import Noctium.Backend.Zkir
import Noctium.Claim

open Lean Noctium
open Noctium.Backend
open Noctium.Backend.Native

private def op (name : String) (fields : List (String × Json) := []) : Json :=
  Json.mkObj (("op", toJson name) :: fields)
private def output : Json := op "output" [("vals", toJson ([] : List String))]
private def input : Json := op "private_input" [("guard", Json.null),
  ("type", toJson ("Scalar<BLS12-381>" : String)), ("output", toJson ("%x" : String))]
private def expected : Expected := {
  mode := .relation
  inputs := [{identifier := "%x", visibility := .«private», ty := .native}]
  groups := []
  returns := []
  assertions := []
  bounds := []
}
private def program (instructions : List Json) : Json := Json.mkObj [
  ("version", Json.mkObj [("major", toJson (3 : Nat)), ("minor", toJson (2 : Nat))]),
  ("inputs", Json.arr #[]), ("outputs", Json.arr #[]),
  ("do_communications_commitment", toJson false), ("instructions", toJson instructions)]
private def accepted (value : Except String α) : Bool := match value with | .ok _ => true | _ => false
private def rejected (value : Except String α) : Bool := !accepted value
private def check (body : List Json) : Except String Unit := Native.validate expected (program (input :: body ++ [output]))
private def decodeBytes (target value : String) : Json := op "from_bytes" [
  ("bytes", toJson value), ("type", toJson target), ("output", toJson ("%decoded" : String))]
private def emptyBytes64 : Json := op "bytes_from_natives" [
  ("inputs", toJson (["0x00", "0x00", "0x00"] : List String)),
  ("len", toJson (64 : Nat)), ("output", toJson ("%bytes64" : String))]
private def unary (name value result : String) : Json := op name [("a", toJson value), ("output", toJson result)]
private def binary (name left right result : String) : Json := op name [
  ("a", toJson left), ("b", toJson right), ("output", toJson result)]
private def constrain (name value : String) : Json := op name [("val", toJson value)]
private def assertion (value : String) : Json := op "assert" [("cond", toJson value)]
private def bits (value : String) (count : Nat) : Json := op "constrain_bits" [("val", toJson value), ("bits", toJson count)]
private def less (left right result : String) (count : Nat) : Json := op "less_than" [
  ("a", toJson left), ("b", toJson right), ("bits", toJson count), ("output", toJson result)]
private def replace (value : Json) (name : String) (replacement : Json) : Json :=
  match value.getObj? with
  | .error _ => value
  | .ok object => Json.mkObj ((object.toList.filter (·.1 != name)) ++ [(name, replacement)])

-- Only a prior check on the same operand covers an equal or wider check.
#guard
  let narrow := bits "%x" 8
  let wide := bits "%x" 16
  let other := bits "%y" 8
  let guarded := replace narrow "guard" (toJson ("%condition" : String))
  let immediate := bits "0x01" 8
  let malformed := bits "%x" 249
  let impact := op "impact" [("guard", Json.null), ("inputs", toJson (["%x"] : List String))]
  RangeDedup.run #[input, wide, impact, narrow, other, wide, narrow, impact, guarded, guarded, immediate, malformed, output] ==
    #[input, wide, impact, narrow, other, impact, guarded, guarded, immediate, malformed, output]

#guard
  let first := less "%x" "0x03" "%first" 8
  let wider := less "%x" "0x03" "%wider" 16
  let duplicate := less "%x" "0x03" "%duplicate" 8
  let different := less "%x" "0x02" "%different" 8
  let reused := op "copy" [("val", toJson ("%first" : String)), ("output", toJson ("%duplicate" : String))]
  let optimized := RangeDedup.reuseComparisons #[
    bits "%x" 8, first, assertion "%first", wider, different, duplicate, assertion "%duplicate"]
  optimized == #[bits "%x" 8, first, assertion "%first", wider, different, reused, assertion "%duplicate"] &&
    accepted (check optimized.toList)

-- Only repeated direct SSA asserts disappear. Lone, guarded and immediate
-- asserts, plus all surrounding instructions, keep their original order.
#guard
  let repeated := assertion "%same"
  let lone := assertion "%lone"
  let guarded := replace repeated "guard" (toJson ("%guard" : String))
  let immediate := assertion "0x01"
  RangeDedup.removeDuplicateAssertions
    #[input, repeated, repeated, lone, guarded, guarded, immediate, immediate, output] ==
    #[input, repeated, lone, guarded, guarded, immediate, immediate, output]

#guard instructionNames.length == 47
#guard valueTypeNames.length == 15
#guard instructionNames.eraseDups.length == 47
#guard valueTypeNames.eraseDups.length == 15
#guard (instructionNames.filter (fun name => accepted (requireInstruction name))).length == 40
#guard rejected (requireInstruction "new_native_without_metadata")
#guard match check [op "div_mod_power_of_two"] with
  | .error message => message.startsWith "native instruction 1: unsupported native instruction 'div_mod_power_of_two'"
  | .ok _ => false
#guard rejected (check [decodeBytes "Scalar<BLS12-381>" "%x"])
#guard rejected (check [emptyBytes64, decodeBytes "Bool" "%bytes64"])
#guard rejected (check [emptyBytes64, decodeBytes "Point<Jubjub>" "%bytes64"])
#guard accepted (check [op "transient_hash" [
  ("inputs", toJson ([] : List String)), ("output", toJson ("%h" : String))]])
#guard accepted (check [op "transient_hash" [
  ("inputs", toJson (List.replicate 1024 ("0x00" : String))), ("output", toJson ("%h" : String))]])
#guard rejected (check [op "transient_hash" [
  ("inputs", toJson (List.replicate 1025 ("0x00" : String))), ("output", toJson ("%h" : String))]])
#guard rejected (check [
  op "jubjub_scalar_from_native" [("native", toJson ("%x" : String)), ("output", toJson ("%s" : String))],
  op "transient_hash" [("inputs", toJson (["%s"] : List String)), ("output", toJson ("%h" : String))]])
#guard accepted (requireInstruction "inv")
#guard accepted (requireInstruction "copy")
#guard valueTypeNames.all fun name => match valueTypeSupport name with
  | .ok (.supported _) => true
  | _ => false

private def packedBytes : Fact := {
  term := .input "%bytes"
  maximum := 0
  valueType := .bytes 64}

private def nativeCopy (value result : String) : Json := op "copy" [
  ("val", toJson value), ("output", toJson result)]

#guard accepted (check [bits "%x" 8, nativeCopy "%x" "%alias", less "%alias" "0xff" "%b" 8])
#guard rejected (check [nativeCopy "%future" "%alias"])
#guard rejected (check [nativeCopy "%x" "%x"])
#guard rejected (check [nativeCopy "%x" "%alias", less "%alias" "0xff" "%b" 8])

private def packingState (fact : Fact) : State :=
  {definitions := [("%bytes", fact)]}

private def packBytes64 (outputs : List String) : Json :=
  op "bytes_into_natives" [("bytes", toJson ("%bytes" : String)), ("outputs", toJson outputs)]

#guard match validateInstruction expected (packingState packedBytes)
    (packBytes64 ["%low", "%middle", "%high"]) with
  | .ok state =>
    match state.definitions.lookup "%low", state.definitions.lookup "%middle",
        state.definitions.lookup "%high" with
    | some low, some middle, some high =>
      low.term == encodedBytesChunkTerm 64 packedBytes.term 0 &&
      middle.term == encodedBytesChunkTerm 64 packedBytes.term 1 &&
      high.term == encodedBytesChunkTerm 64 packedBytes.term 2 &&
      low.maximum == 2 ^ (31 * 8) - 1 && middle.maximum == 2 ^ (31 * 8) - 1 &&
      high.maximum == 2 ^ (2 * 8) - 1
    | _, _, _ => false
  | .error _ => false

#guard rejected (validateInstruction expected (packingState packedBytes)
  (packBytes64 ["%low", "%middle"]))
#guard rejected (validateInstruction expected
  (packingState {packedBytes with valueType := .bytes 0}) (packBytes64 []))
private def chunkNames (count : Nat) : List String :=
  (List.range count).map fun index => s!"%chunk{index}"

#guard match validateInstruction expected
    (packingState {packedBytes with valueType := .bytes 1025})
    (packBytes64 (chunkNames 34)) with
  | .ok state => (state.definitions.lookup "%chunk33").map Fact.maximum == some (2 ^ 16 - 1)
  | .error _ => false
#guard rejected (validateInstruction expected
  (packingState {packedBytes with valueType := .bytes 1055})
  (packBytes64 (chunkNames 35)))
#guard rejected (validateInstruction expected
  (packingState {packedBytes with valueType := .native})
  (packBytes64 ["%low", "%middle", "%high"]))

private def coordinateState : State := {
  definitions := [("%point", {
    term := .input "%point"
    maximum := Field.modulus - 1
    valueType := .jubjubPoint
  })]
}

private def coordinateInstruction : Json := op "into_coordinates" [
  ("point", toJson ("%point" : String)),
  ("outputs", toJson (["%x", "%y"] : List String))]

#guard match validateInstruction expected coordinateState coordinateInstruction with
  | .ok _ => outputDefinitionsInInstruction coordinateInstruction == 2
  | .error _ => false

-- A primitive cannot acquire default privacy/effect behavior silently.
example : True := by
  fail_if_success
    have missingMetadata : Descriptor := {
      operands := .nativeUnary
      encoding := .canonicalNative
      precondition := .canonicalNative
      guards := .noGuard
      binding := .none
      fields := ["a", "output"]
    }
  trivial

-- Canonical Native immediates use minimal little-endian bytes.
#guard match immediate "0x0001" with | .ok 256 => true | _ => false
#guard rejected (immediate "0x")
#guard rejected (immediate "0x0")
#guard rejected (immediate "0X01")
#guard rejected (immediate "-0x01")
#guard rejected (immediate "0x0000")
#guard rejected (immediate "0xFF")
#guard rejected (immediate (Zkir.fieldImmediate Field.modulus))
#guard accepted (immediate (Zkir.fieldImmediate (Field.modulus - 1)))

-- SSA, exact fields, type encodings and output structure fail closed.
#guard accepted (check [])
#guard rejected (check [binary "add" "%future" "0x00" "%v0"])
#guard rejected (check [binary "add" "%x" "0x00" "%x"])
#guard rejected (check [op "add" [("a", toJson ("%x" : String)), ("output", toJson ("%v0" : String))]])
#guard rejected (check [replace (binary "add" "%x" "0x00" "%v0") "unknown" Json.null])
#guard rejected (Native.validate expected (program [input]))
#guard rejected (Native.validate expected (program [output]))
#guard rejected (Native.validate expected (program [input, output, output]))
#guard rejected (Native.validate expected (program [input, output, binary "add" "%x" "0x00" "%v0"]))
#guard rejected (Native.validate expected (program [replace input "type" (toJson ("Boolean" : String)), output]))
#guard rejected (Native.validate expected (program [replace input "output" (toJson ("x" : String)), output]))
#guard rejected (Native.validate expected (replace (program [input, output]) "extra" Json.null))
#guard rejected (Native.validate expected (replace (program [input, output]) "do_communications_commitment" (toJson true)))
#guard match Native.validate
  {expected with inputs := (List.replicate (Native.maxInputs + 1)
    ({identifier := "%x", visibility := .«private», ty := .native} : InputRequirement))}
  (program [input, output]) with
  | .error message => message == "native producer resource limit exceeded"
  | .ok _ => false
#guard match Native.validate expected
  (program (List.replicate (Native.maxInstructions + 1) input)) with
  | .error message => message == "native producer resource limit exceeded"
  | .ok _ => false

-- Native Assert is safe only after a genuine 0/1 fact. Nonzero is insufficient.
#guard rejected (check [assertion "%x"])
#guard rejected (check [assertion "0x02"])
#guard accepted (check [constrain "constrain_to_boolean" "%x", assertion "%x"])
#guard accepted (check [binary "test_eq" "%x" "0x00" "%b", assertion "%b"])
#guard rejected (check [unary "not" "%x" "%b"])
#guard rejected (check [op "cond_select" [("bit", toJson ("%x" : String)),
  ("a", toJson ("0x01" : String)), ("b", toJson ("0x00" : String)), ("output", toJson ("%v0" : String))]])
#guard rejected (check [assertion "%x", constrain "constrain_to_boolean" "%x"])

-- LessThan requires both operands in range before its use, not later.
#guard rejected (check [less "%x" "0xff" "%b" 8])
#guard rejected (check [less "%x" "0xff" "%b" 8, bits "%x" 8])
#guard rejected (check [bits "%x" 8, less "%x" "0x0001" "%b" 8])
#guard accepted (check [bits "%x" 8, less "%x" "0xff" "%b" 8, assertion "%b"])
#guard rejected (check [bits "%x" 0])
#guard rejected (check [bits "%x" 249])
#guard rejected (check [bits "0x0001" 8])
#guard rejected (Native.validate {expected with inputs := [{identifier := "%x", visibility := .«private», ty := .bool}]}
  (program [input, output]))
#guard rejected (Native.validate {expected with inputs := [{identifier := "%x", visibility := .«private», ty := .uint 510}]}
  (program [input, bits "%x" 9, output]))
#guard accepted (Native.validate {expected with inputs := [{identifier := "%x", visibility := .«private», ty := .uint 510}]}
  (program [input, bits "%x" 9, less "%x" "0xff01" "%bounded" 9, assertion "%bounded", output]))
#guard rejected (check [op "inv" [("a", toJson ("0x00" : String)), ("output", toJson ("%inverse" : String))]])

-- Input guards only alter preprocessing. They do not authorize partial
-- operations, inactive source execution, disclosure, or public activation.
#guard rejected (Native.validate expected (program [replace input "guard" (toJson ("0x00" : String)), output]))
#guard rejected (Native.validate expected (program [replace input "guard" (toJson ("0x01" : String)), output]))
#guard rejected (check [op "impact" [("guard", toJson ("%x" : String)), ("inputs", toJson ([] : List String))]])
#guard rejected (check [op "impact" [("guard", toJson ("0x00" : String)), ("inputs", toJson ([] : List String))]])

private def publicCircuit : Circuit := {
  name := "public", inputs := [{name := "public", ty := .native, visibility := .«public»}],
  constraints := [.eq (.ref "public" : Expr .native) (.native 7),
    .eq (.ref "public" : Expr .native) (.native 8)],
  outputs := [{name := "result", ty := .native, value := .native 7}]}

private def checkMutation (change : List Json → List Json) : Except String Unit := do
  let required ← (expectedCircuit publicCircuit).mapError (·.message)
  let json ← (Zkir.lowerCircuit publicCircuit).mapError (·.message)
  let instructions ← (← json.getObjVal? "instructions").getArr?
  Native.validate required (replace json "instructions" (toJson (change instructions.toList)))

private def repeatedAssertionCircuit : Circuit := {
  name := "repeatedAssertions"
  inputs := [
    {name := "flag", ty := .bool, visibility := .«private»},
    {name := "other", ty := .bool, visibility := .«private»}]
  constraints := [
    (.ref "flag" : Expr .bool),
    (.ref "flag" : Expr .bool),
    (.ref "other" : Expr .bool)]
  outputs := []
}

private def assertionConditions (instructions : Array Json) : Array Json :=
  instructions.filterMap fun instruction =>
    if (instruction.getObjValD "op").getStr?.toOption == some "assert" then
      (instruction.getObjValD "cond").getStr?.toOption.map toJson
    else none

private def optimizedAssertionExpected : Except Diagnostic Expected := do
  let expected ← Native.expectedCircuit repeatedAssertionCircuit
  pure {expected with assertions := expected.assertions.eraseDups}

private def checkOptimizedAssertionMutation
    (change : Array Json → Array Json) : Except String Unit := do
  let expected ← optimizedAssertionExpected |>.mapError (·.message)
  let json ← (Zkir.lowerCircuit repeatedAssertionCircuit .rangeAndAssertions).mapError (·.message)
  let instructions ← Native.arrayField json "instructions"
  Native.validate expected (replace json "instructions" (Json.arr (change instructions)))

#guard match Zkir.lowerCircuit repeatedAssertionCircuit,
    Zkir.lowerCircuit repeatedAssertionCircuit .rangeAndAssertions with
  | .ok ordinary, .ok optimized =>
    match Native.arrayField ordinary "instructions", Native.arrayField optimized "instructions" with
    | .ok plainItems, .ok optimizedItems =>
      assertionConditions plainItems == #[toJson ("%input_flag" : String),
        toJson ("%input_flag" : String), toJson ("%input_other" : String)] &&
      assertionConditions optimizedItems == #[toJson ("%input_flag" : String),
        toJson ("%input_other" : String)] &&
      plainItems.filter (fun item => (item.getObjValD "op").getStr?.toOption != some "assert") ==
        optimizedItems.filter (fun item => (item.getObjValD "op").getStr?.toOption != some "assert")
    | _, _ => false
  | _, _ => false

#guard accepted (checkOptimizedAssertionMutation id)
#guard rejected (checkOptimizedAssertionMutation fun instructions =>
  instructions.filter fun item =>
    (item.getObjValD "op").getStr?.toOption != some "assert" ||
      (item.getObjValD "cond").getStr?.toOption != some "%input_other")
#guard rejected (checkOptimizedAssertionMutation fun instructions =>
  let assertions := instructions.filter fun item =>
    (item.getObjValD "op").getStr?.toOption == some "assert"
  let body := instructions.filter fun item =>
    (item.getObjValD "op").getStr?.toOption != some "assert" &&
      (item.getObjValD "op").getStr?.toOption != some "output"
  let outputs := instructions.filter fun item =>
    (item.getObjValD "op").getStr?.toOption == some "output"
  body ++ assertions.reverse ++ outputs)

#guard accepted (checkMutation id)
#guard rejected (checkMutation (List.filter (fun value => (value.getObjValD "op").getStr?.toOption != some "impact")))
#guard rejected (checkMutation (List.filter (fun value => (value.getObjValD "op").getStr?.toOption != some "assert")))
#guard rejected (checkMutation (fun instructions =>
  let assertions := instructions.filter (fun value => (value.getObjValD "op").getStr?.toOption == some "assert")
  let outputs := instructions.filter (fun value => (value.getObjValD "op").getStr?.toOption == some "output")
  let body := instructions.filter (fun value =>
    (value.getObjValD "op").getStr?.toOption != some "assert" &&
    (value.getObjValD "op").getStr?.toOption != some "output")
  body ++ assertions.reverse ++ outputs))
#guard rejected (checkMutation (fun instructions => instructions.map fun value =>
  if (value.getObjValD "op").getStr?.toOption == some "impact" then
    replace value "inputs" (toJson (["0x00"] : List String)) else value))
#guard rejected (checkMutation (fun instructions => instructions.map fun value =>
  if (value.getObjValD "op").getStr?.toOption == some "impact" then
    replace value "inputs" (toJson (["%input_public", "%input_public"] : List String)) else value))
#guard rejected (checkMutation (fun instructions => instructions.map fun value =>
  if (value.getObjValD "op").getStr?.toOption == some "impact" then
    let fields := (value.getObjValD "inputs").getArr?.toOption.getD #[]
    replace value "inputs" (if fields == #[toJson ("%input_public" : String)] then
      toJson (["0x07"] : List String) else toJson (["%input_public"] : List String))
  else value))

private def boolEntry : Entrypoint := {
  name := "bool"
  circuit := {name := "bool", inputs := [{name := "flag", ty := .bool, visibility := .«public»}]}
  effects := [.readCell "enabled" "old" .bool,
    .require (.eq (.ref "old" : Expr .bool) (.ref "flag")), .writeCell "enabled" .bool (.ref "flag")]
}
private def boolState : List StateDecl := [{name := "enabled", kind := .cell .bool}]

-- Bool state/public input materialization must use a typed Native cast.
#guard match Impact.lower boolState boolEntry with
  | .error _ => false
  | .ok plan => match plan.toJson {modulus := Field.modulus, poseidon2 := fun _ _ _ => .error "unused"}
      [("flag", .bool false), ("old", .bool false)] with
    | .ok _ => true | _ => false
#guard match Impact.lower boolState boolEntry with
  | .error _ => false
  | .ok plan => match plan.toJson {modulus := Field.modulus, poseidon2 := fun _ _ _ => .error "unused"}
      [("flag", .bool true), ("old", .bool true)] with
    | .ok _ => true | _ => false
#guard match Zkir.lowerEntrypoint boolState boolEntry with | .ok _ => true | _ => false
#guard rejected (Impact.Plan.validate {
  operations := [.push (.field (.ref "flag")) false]
  reads := [{name := "flag", ty := .bool}]
} boolEntry)

example (fact : Fact) (value : Nat) (hmax : fact.maximum ≤ 1) (hvalue : value ≤ fact.maximum) :
    value = 0 ∨ value = 1 := established_boolean_range fact value hmax hvalue

example (instructions : List Json) : requireFinalOutput instructions = .ok () ↔
    finalOutputShape instructions = true := final_output_required instructions

def main (args : List String) : IO Unit := do
  let printPrivacy := args == ["--privacy-inventory"]
  let path := "docs/compatibility/zkir-feature-matrix.json"
  let matrix ← IO.ofExcept (Json.parse (← IO.FS.readFile path))
  let version ← IO.ofExcept (matrix.getObjVal? "privacyDescriptors" >>=
    (·.getObjVal? "schemaVersion") >>= Json.getNat?)
  unless version == 1 do
    throw (IO.userError "native privacy descriptor schema version mismatch")
  let target ← IO.ofExcept (matrix.getObjVal? "target")
  let revision ← IO.ofExcept ((← IO.ofExcept (target.getObjVal? "zkirRevision")).getStr?)
  unless revision == inventoryRevision do
    throw (IO.userError "native descriptor source pin drifted from inventory")
  let rows ← IO.ofExcept ((← IO.ofExcept (matrix.getObjVal? "entries")).getArr?)
  let mut operations := []
  let mut types := []
  let mut privacyRows := #[]
  for row in rows do
    let kind ← IO.ofExcept ((← IO.ofExcept (row.getObjVal? "kind")).getStr?)
    let (name, support) ← if kind == "instruction" then do
      let name ← IO.ofExcept (row.getObjVal? "jsonOpcode" >>= Json.getStr?)
      pure (name, instructionSupport name)
    else if kind == "value-type" then do
      let name ← IO.ofExcept (row.getObjVal? "symbol" >>= Json.getStr?)
      pure (name, valueTypeSupport name)
    else continue
    if kind == "instruction" then operations := operations ++ [name]
    else types := types ++ [name]
    let privacy := match ← IO.ofExcept support with
      | .supported descriptor => descriptor.privacyJson
      | .unsupported reason => Json.mkObj [("status", toJson ("gated" : String)), ("reason", toJson reason)]
    if printPrivacy then
      privacyRows := privacyRows.push (Json.mkObj [("name", toJson name), ("privacy", privacy)])
    else
      let recorded ← IO.ofExcept (row.getObjVal? "privacyDescriptor")
      unless recorded == privacy do
        throw (IO.userError s!"native privacy descriptor for '{name}' drifted from inventory")
  unless operations == instructionNames && types == valueTypeNames do
    throw (IO.userError "native descriptor registry drifted from pinned 47/15 inventory")
  if printPrivacy then
    IO.println (Json.arr privacyRows).pretty
    return
  let claim ← IO.ofExcept (Claim.contract {})
  let some entry := claim.entrypoints.head? | throw (IO.userError "missing claim")
  discard (IO.ofExcept ((Zkir.lowerEntrypoint claim.state entry).mapError (·.message)))
  IO.println "Native producer inventory, malformed programs, typed bindings and Bool materialization passed"
