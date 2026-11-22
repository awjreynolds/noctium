import Noctium.Backend.Native
import Noctium.Backend.NativeMeaning
import Lean

namespace Noctium.Backend.Native
open Lean

def maxInstructions : Nat := 8192
-- Keep the bytewise Source Bytes1024 ABI within a bounded aggregate input budget.
def maxInputs : Nat := 2048
def maxVectorLength : Nat := 4096
def maxSymbolicNodes : Nat := 65536
def maxSymbolicDepth : Nat := 256

def ensure (condition : Bool) (message : String) : Except String Unit :=
  if condition then pure () else throw message

private def objectFields (value : Json) : Except String (List String) := do
  pure ((← value.getObj?).toList.map Prod.fst)

private def fields (value : Json) (expected : List String) : Except String Unit := do
  let actual ← objectFields value
  ensure (actual.length == expected.length && actual.eraseDups.length == actual.length &&
    actual.all expected.contains && expected.all actual.contains)
    "missing, unknown or mismatched native instruction fields"

def stringField (value : Json) (name : String) : Except String String := do
  (← value.getObjVal? name).getStr?

def arrayField (value : Json) (name : String) : Except String (Array Json) := do
  (← value.getObjVal? name).getArr?

def natField (value : Json) (name : String) : Except String Nat := do
  let item ← value.getObjVal? name
  let number ← item.getNat?
  ensure (item.compress == toString number) "native integer metadata must use canonical natural JSON numbers"
  pure number

def hexDigit (value : Char) : Option Nat :=
  if '0' ≤ value && value ≤ '9' then some (value.toNat - '0'.toNat)
  else if 'a' ≤ value && value ≤ 'f' then some (value.toNat - 'a'.toNat + 10)
  else none

def hexBytes : List Char → Option (List Nat)
  | [] => some []
  | high :: low :: rest => do
    let high ← hexDigit high
    let low ← hexDigit low
    pure ((high * 16 + low) :: (← hexBytes rest))
  | _ => none

/-- Exactly the canonical little-endian field syntax emitted by this producer. -/
def immediate (text : String) : Except String Nat := do
  ensure (text.startsWith "0x") "native immediate must start with lowercase 0x"
  let some bytes := hexBytes (text.toList.drop 2) | throw "invalid native hexadecimal immediate"
  ensure (!bytes.isEmpty && bytes.length ≤ 32) "native immediate has an invalid byte width"
  ensure (bytes.length == 1 || bytes.getLast? != some 0) "nonminimal native immediate"
  let number := littleEndian bytes
  ensure (number < Field.modulus) "noncanonical native field immediate"
  pure number

private def validIdentifier (name : String) : Bool :=
  name.startsWith "%" && name.length > 1 && name.utf8ByteSize ≤ 1024

inductive NativeValueType where
  | native | bool | byte | bytes32 | bytes (length : Nat) | jubjubScalar | jubjubPoint
  | foreign (kind : Foreign.Kind)
  deriving Repr, BEq, DecidableEq

private def byteLength? : NativeValueType → Option Nat
  | .bytes32 => some 32
  | .bytes length => some length
  | _ => none

private def byteValueType (length : Nat) : NativeValueType :=
  if length == 32 then .bytes32 else .bytes length

structure Fact where
  term : Term
  maximum : Nat
  valueType : NativeValueType := .native
  /-- Native typed decoding or a checked codec established this foreign value. -/
  foreignValid : Bool := false
  foreignNonidentity : Bool := false
  nodes : Nat := 1
  depth : Nat := 1
  assertedLessThan : Option (String × Nat) := none
  deriving Repr

structure State where
  definitions : List (String × Fact) := []
  inputCount : Nat := 0
  groupCount : Nat := 0
  assertionCount : Nat := 0
  establishedAssertions : List Term := []
  canonicalScalarInputs : List String := []
  requiredCoordinateEqualities : List (Term × Term) := []
  establishedCoordinateEqualities : List (Term × Term) := []

def combine (term : Term) (maximum : Nat) (children : List Fact) : Except String Fact := do
  let nodes := 1 + (children.map (·.nodes)).sum
  let depth := 1 + (children.map (·.depth)).foldl max 0
  unless nodes ≤ maxSymbolicNodes && depth ≤ maxSymbolicDepth do
    throw s!"native symbolic expression resource limit exceeded ({nodes} nodes, depth {depth})"
  pure {term, maximum, nodes, depth}

def operand (state : State) (text : String) : Except String Fact := do
  if text.startsWith "0x" then
    let value ← immediate text
    pure {term := .constant value, maximum := value}
  else
    ensure (validIdentifier text) "invalid native SSA reference"
    let some fact := state.definitions.lookup text | throw s!"native use before definition: {text}"
    pure fact

private def requireNative (fact : Fact) : Except String Unit :=
  ensure (fact.valueType == .native) "native instruction operand must have Native type"

private def requireForeignValid (fact : Fact) : Except String Unit :=
  match fact.valueType with
  | .foreign _ => ensure fact.foreignValid "foreign value lacks canonical typed validation"
  | _ => pure ()

private def isForeignType : NativeValueType → Bool
  | .foreign _ => true
  | _ => false

private def foreignResult (kind : Foreign.Kind) (term : Term) (children : List Fact) : Except String Fact := do
  children.forM requireForeignValid
  let fact ← combine term 0 children
  pure {fact with valueType := .foreign kind, foreignValid := true}

private def nativeOperand (state : State) (text : String) : Except String Fact := do
  let fact ← operand state text
  requireNative fact
  pure fact

def argument (state : State) (instruction : Json) (name : String) : Except String Fact := do
  operand state (← stringField instruction name)

private def nativeArgument (state : State) (instruction : Json) (name : String) : Except String Fact := do
  nativeOperand state (← stringField instruction name)

def define (state : State) (name : String) (fact : Fact) : Except String State := do
  ensure (validIdentifier name) "invalid native SSA definition"
  ensure ((state.definitions.lookup name).isNone) s!"duplicate native SSA definition: {name}"
  pure {state with definitions := state.definitions ++ [(name, fact)]}

def defineResult (state : State) (instruction : Json) (fact : Fact) : Except String State := do
  define state (← stringField instruction "output") fact

private def defineByteChunks (state : State) (input : Fact) (length : Nat)
    (outputs : Array Json) : Except String State := do
  ensure (0 < length && length ≤ Types.defaultLimits.maxVectorLength)
    "byte encoding length is unsupported"
  ensure (outputs.size == bytesChunkCount length) "byte encode chunk count mismatch"
  let mut state := state
  for index in List.range outputs.size do
    let name ← outputs[index]!.getStr?
    let fact ← combine (encodedBytesChunkTerm length input.term index)
      (2 ^ (8 * bytesChunkWidth length index) - 1) [input]
    state ← define state name fact
  pure state

def refine (state : State) (text : String) (maximum : Nat) : Except String State := do
  let fact ← operand state text
  requireNative fact
  if text.startsWith "%" then
    pure {state with definitions := state.definitions.map fun (name, value) =>
      (name, if name == text then {value with maximum := min value.maximum maximum} else value)}
  else
    ensure (fact.maximum ≤ maximum) "constant violates native range/equality constraint"
    pure state

def requireBoolean (fact : Fact) : Except String Unit :=
  ensure (fact.maximum ≤ 1) "native Boolean precondition is not established"

def width (instruction : Json) : Except String Nat := do
  let bits ← natField instruction "bits"
  ensure (0 < bits && bits ≤ ScalarPolicy.maxBits) "unsupported native bit width"
  pure bits

def arguments (state : State) (instruction : Json) (name : String) : Except String (List Fact) := do
  let values ← arrayField instruction name
  ensure (values.size ≤ maxVectorLength) "native operand vector resource limit exceeded"
  values.toList.mapM fun item => do operand state (← item.getStr?)

private def nativeArguments (state : State) (instruction : Json) (name : String) : Except String (List Fact) := do
  let values ← arguments state instruction name
  values.forM requireNative
  pure values

private def nativeType (value : Json) : Except String Unit := do
  ensure ((← value.getStr?) == "Scalar<BLS12-381>") "unsupported native value type/encoding"

private def bytes32Alignment : Json := Json.arr #[Json.mkObj [
  ("tag", toJson ("atom" : String)),
  ("value", Json.mkObj [("tag", toJson ("bytes" : String)), ("length", toJson (32 : Nat))])]]

private def bytes32Atom : Json := Json.mkObj [
  ("tag", toJson ("atom" : String)),
  ("value", Json.mkObj [("tag", toJson ("bytes" : String)), ("length", toJson (32 : Nat))])]

private def nativeFieldAlignment : Json := Json.arr #[Json.mkObj [
  ("tag", toJson ("atom" : String)),
  ("value", Json.mkObj [("tag", toJson ("field" : String))])]]

private def nativeFieldAtom : Json := Json.mkObj [
  ("tag", toJson ("atom" : String)),
  ("value", Json.mkObj [("tag", toJson ("field" : String))])]

/-- Accept only the single fixed-byte source preimage, or the empty preimage.
Canonical comparison rejects mixed atoms, extra fields and alternate number forms. -/
private def fixedByteHashLength (alignment : Json) : Except String Nat := do
  let atoms ← alignment.getArr?
  if atoms.isEmpty then return 0
  ensure (atoms.size == 1) "byte hash requires exactly one byte alignment atom"
  let atom := atoms[0]!
  let value ← atom.getObjVal? "value"
  let length ← natField value "length"
  ensure (0 < length && length ≤ Types.defaultLimits.maxVectorLength)
    "byte hash preimage length is unsupported"
  let canonical := Json.arr #[Json.mkObj [
    ("tag", toJson ("atom" : String)),
    ("value", Json.mkObj [("tag", toJson ("bytes" : String)), ("length", toJson length)])]]
  ensure (alignment == canonical) "byte hash requires canonical fixed-byte alignment"
  pure length

private def checkedFixedByteHashTerm (opcode : String) (alignment : Json)
    (values : List Fact) : Except String Term := do
  let length ← fixedByteHashLength alignment
  ensure (values.length == bytesChunkCount length) "byte hash aligned field count mismatch"
  for (value, index) in values.reverse.zipIdx do
    ensure (value.maximum ≤ 2 ^ (8 * bytesChunkWidth length index) - 1)
      "byte hash operand lacks its exact chunk range bound"
  pure (fixedByteHashTerm opcode length (values.map (·.term)))

private def bytes32FromChunksTerm (low31 highByte : Term) : Term :=
  .unary "bytes32_from_chunks" (.hash [low31, highByte])

private def toBytes32Term (valueType : NativeValueType) (value : Term) : Except String Term := do
  match valueType with
  | .native => pure (.unary "to_bytes32_native" value)
  | .jubjubScalar => pure (.unary "to_bytes32_jubjub_scalar" value)
  | .jubjubPoint => pure (.unary "to_bytes32_jubjub_point" value)
  | _ => throw "to_bytes requires Native, JubjubScalar or JubjubPoint"

private def scalarFromBytesTerm (typeName : String) (length : Nat) (value : Term) :
    Except String (NativeValueType × Term × Nat) := do
  match typeName with
  | "Scalar<BLS12-381>" =>
    let (term, maximum) ← typedScalarFromBytesTerm .native length value
    pure (.native, term, maximum)
  | "Scalar<Jubjub>" =>
    let (term, maximum) ← typedScalarFromBytesTerm .jubjubScalar length value
    pure (.jubjubScalar, term, maximum)
  | _ => throw "from_bytes has an unsupported output type"

private def fromBytes32Term (typeName : String) (value : Term) : Except String (NativeValueType × Term × Nat) := do
  match typeName with
  | "Scalar<BLS12-381>" | "Scalar<Jubjub>" => scalarFromBytesTerm typeName 32 value
  | "Point<Jubjub>" =>
    pure (.jubjubPoint, .unary "from_bytes32_jubjub_point" value, Field.modulus - 1)
  | _ => throw "from_bytes has an unsupported output type"

private def alignedBytes32Pairs : List Fact → Except String (List (Term × Term))
  | [] => pure []
  | highByte :: low31 :: rest => do
    ensure (highByte.maximum ≤ 255 && low31.maximum ≤ 2 ^ (31 * 8) - 1)
      "Bytes32 persistent_hash operands lack byte-aligned range constraints"
    pure ((highByte.term, low31.term) :: (← alignedBytes32Pairs rest))
  | _ => throw "Bytes32 persistent_hash requires two fields per aligned value"

private def fabAlignmentDescriptor (atom : Json) : Except String String := do
  ensure ((← stringField atom "tag") == "atom") "mixed FAB alignment entry must be an atom"
  let value ← atom.getObjVal? "value"
  match ← stringField value "tag" with
  | "field" =>
    fields value ["tag"]
    pure "field"
  | "bytes" => do
    fields value ["tag", "length"]
    let length ← natField value "length"
    ensure (length > 0 && length ≤ 32) "mixed FAB byte atom width is unsupported"
    pure s!"bytes:{length}"
  | _ => throw "mixed FAB alignment has an unsupported atom"

private def checkedFabHashOperands (alignment : Json) (values : List Fact) :
    Except String (List String × List Term) := do
  let atoms ← alignment.getArr?
  ensure (atoms.size > 0 && (atoms.size ≤ 32 ||
    (atoms.size == 33 && atoms[0]? == some bytes32Atom)))
    "mixed FAB alignment must contain 1 to 32 payload atoms, with an optional opening"
  let descriptors ← atoms.toList.mapM fabAlignmentDescriptor
  let mut remaining := values
  let mut terms := []
  for descriptor in descriptors do
    match descriptor with
    | "field" =>
      let some value := remaining.head? | throw "mixed FAB field atom lacks an operand"
      remaining := remaining.drop 1
      terms := terms ++ [value.term]
    | descriptor =>
      let some width := (descriptor.drop 6).toNat? | throw "mixed FAB byte atom width is malformed"
      if width == 32 then
        let some highByte := remaining[0]? | throw "mixed FAB Bytes32 atom lacks its high byte"
        let some low31 := remaining[1]? | throw "mixed FAB Bytes32 atom lacks its low 31 bytes"
        ensure (highByte.maximum ≤ 255 && low31.maximum ≤ 2 ^ (31 * 8) - 1)
          "mixed FAB Bytes32 operands lack canonical byte ranges"
        remaining := remaining.drop 2
        terms := terms ++ [highByte.term, low31.term]
      else do
        let some value := remaining.head? | throw "mixed FAB byte atom lacks an operand"
        ensure (value.maximum ≤ 2 ^ (8 * width) - 1)
          "mixed FAB byte operand lacks its exact byte-width range"
        remaining := remaining.drop 1
        terms := terms ++ [value.term]
  ensure remaining.isEmpty "mixed FAB alignment and operand counts differ"
  pure (descriptors, terms)

private def equalityPairMatches (left right : Term) (pair : Term × Term) : Bool :=
  (left == pair.1 && right == pair.2) || (left == pair.2 && right == pair.1)

private def canonicalScalarInputMatches (expected : Expected) (left right : Term) : List String :=
  (expected.rawInputs ++ expected.inputs).filterMap fun input =>
    if !input.canonicalJubjubScalar then none else
    let raw := Term.input input.identifier
    let reduced := Term.unary "jubjub_scalar_from_native" raw
    let encoded := Term.unary "jubjub_scalar_to_native" reduced
    if (left == raw && right == encoded) || (left == encoded && right == raw) then
      some input.identifier else none

def validateInstruction (expected : Expected) (state : State) (instruction : Json) : Except String State := do
  let opcode ← stringField instruction "op"
  let descriptor ← requireInstruction opcode
  fields instruction ("op" :: descriptor.fields)
  match opcode with
  | "public_input" | "private_input" =>
    let some required := expected.inputs[state.inputCount]? | throw "unexpected native transcript input"
    let valueType ← match required.ty with
      | .foreign kind => do
        ensure ((← stringField instruction "type") == kind.nativeName) "foreign input type differs from source"
        pure (NativeValueType.foreign kind)
      | _ => do
        nativeType (← instruction.getObjVal? "type")
        pure NativeValueType.native
    match required.activityGuard with
    | none =>
      ensure ((← instruction.getObjVal? "guard") == Json.null)
        "unexpected native input activity guard"
    | some expectedGuard =>
      ensure (expected.mode == .ledgerCall && descriptor.privacy.guard == .sourceBoundPublicRead)
        "conditional inputs require a source-bound public ledger read"
      let guard ← nativeOperand state (← stringField instruction "guard")
      requireBoolean guard
      ensure (guard.term == expectedGuard) "native read activity guard mismatch"
    let output ← stringField instruction "output"
    ensure (output == required.identifier &&
      descriptor.privacy.inputVisibility == some required.visibility)
      "native transcript input schema/order mismatch"
    let foreignValid := isForeignType valueType
    let state ← define state output {
      term := .input output
      valueType
      foreignValid
      maximum := if foreignValid then 0 else Field.modulus - 1
    }
    pure {state with inputCount := state.inputCount + 1}
  | "copy" => defineResult state instruction (← argument state instruction "val")
  | "mul" => do
    let left ← argument state instruction "a"
    let right ← argument state instruction "b"
    if let .foreign kind := left.valueType then do
      ensure (right.valueType == left.valueType && kind.modulus?.isSome)
        "foreign multiplication requires matching prime fields"
      defineResult state instruction (← foreignResult kind (foreignBinaryTerm "mul" kind left.term right.term) [left, right])
    else do
      requireNative left
      requireNative right
      let bound := left.maximum * right.maximum
      let maximum := if bound < Field.modulus then bound else Field.modulus - 1
      defineResult state instruction (← combine (.binary opcode left.term right.term) maximum [left, right])
  | "inv" => do
    let value ← operand state (← stringField instruction "a")
    if let .foreign kind := value.valueType then do
      ensure kind.modulus?.isSome "foreign inverse requires a prime field"
      ensure (state.establishedAssertions.contains (foreignNonzeroTerm kind value.term))
        "foreign inverse lacks its explicit nonzero assertion"
      defineResult state instruction (← foreignResult kind (foreignUnaryTerm "inv" kind value.term) [value])
    else do
      let (termOpcode, maximum) ← match value.valueType with
        | .native => pure ("inverse_native", Field.modulus - 1)
        | .jubjubScalar => pure ("inverse_jubjub_scalar", Jubjub.scalarOrder - 1)
        | _ => throw "inv supports only qualified prime-field operands"
      ensure (value.maximum ≤ maximum) "inv operand range precondition is not established"
      ensure (value.maximum > 0) "inv cannot invert an operand known to be zero"
      let fact ← combine (.unary termOpcode value.term) maximum [value]
      defineResult state instruction {fact with valueType := value.valueType}
  | "add" | "test_eq" => do
    let left ← argument state instruction "a"
    let right ← argument state instruction "b"
    ensure (left.valueType == right.valueType)
      "native equality/add operands have different typed values"
    if opcode == "test_eq" then do
      requireForeignValid left
      requireForeignValid right
      ensure ((byteLength? left.valueType).isNone) "typed byte equality is unsupported by this source surface"
      let fact ← combine (.binary "test_eq" left.term right.term) 1 [left, right]
      defineResult state instruction fact
    else if let .foreign kind := left.valueType then do
      defineResult state instruction (← foreignResult kind (foreignBinaryTerm "add" kind left.term right.term) [left, right])
    else if left.valueType == .jubjubPoint then do
      let fact ← combine (.binary "add_jubjub_point" left.term right.term)
        (Field.modulus - 1) [left, right]
      defineResult state instruction {fact with valueType := .jubjubPoint}
    else do
      requireNative left
      requireNative right
      let bound := left.maximum + right.maximum
      let maximum := if bound < Field.modulus then bound else Field.modulus - 1
      defineResult state instruction (← combine (.binary "add" left.term right.term) maximum [left, right])
  | "neg" | "not" => do
    let value ← argument state instruction "a"
    if opcode == "not" then do
      requireNative value
      requireBoolean value
      defineResult state instruction (← combine (.unary "not" value.term) 1 [value])
    else if let .foreign kind := value.valueType then do
      defineResult state instruction (← foreignResult kind (foreignUnaryTerm "neg" kind value.term) [value])
    else if value.valueType == .jubjubPoint then do
      let fact ← combine (.unary "neg_jubjub_point" value.term) (Field.modulus - 1) [value]
      defineResult state instruction {fact with valueType := .jubjubPoint}
    else do
      requireNative value
      let maximum := if value.maximum == 0 then 0 else Field.modulus - 1
      defineResult state instruction (← combine (.unary "neg" value.term) maximum [value])
  | "load_constant" => do
    let typeName ← stringField instruction "type"
    let encoding ← arrayField instruction "encoding"
    if typeName == "Bool" then do
      ensure (encoding.size == 1) "Bool constant requires exactly one encoded field"
      let value ← immediate (← encoding[0]!.getStr?)
      ensure (value ≤ 1) "Bool constant encoding must be zero or one"
      defineResult state instruction {term := typedBoolConstantTerm value, maximum := value, valueType := .bool}
    else do
      let some kind := Foreign.kinds.find? (·.nativeName == typeName)
        | throw "load_constant codec is not qualified"
      ensure (encoding.size == kind.encodedFieldCount) "foreign constant encoded field count mismatch"
      let values ← encoding.toList.mapM fun item => do immediate (← item.getStr?)
      match kind with
      | .base _ | .scalar _ => discard (Foreign.decodeField kind values)
      | .point curve => do
        let point ← Foreign.decodePoint curve values
        ensure ((← Foreign.encodePoint curve point) == values) "foreign point constant encoding is not canonical"
      defineResult state instruction {
        term := foreignConstantTerm kind values
        maximum := 0
        valueType := .foreign kind
        foreignValid := true
      }
  | "and" | "or" | "xor" => do
    let values ← arguments state instruction "inputs"
    ensure (!values.isEmpty) "typed Boolean gate requires at least one operand"
    for value in values do
      ensure (value.valueType == .bool) "typed Boolean gate requires Bool operands"
      requireBoolean value
    let fact ← combine (typedBoolGateTerm opcode (values.map (·.term))) 1 values
    defineResult state instruction {fact with valueType := .bool}
  | "cond_select" =>
    let condition ← nativeArgument state instruction "bit"
    requireBoolean condition
    let yes ← argument state instruction "a"
    let no ← argument state instruction "b"
    ensure (yes.valueType == no.valueType && (yes.valueType == .native || yes.valueType == .bool || isForeignType yes.valueType))
      "cond_select requires matched Native, Bool or qualified foreign arms"
    requireForeignValid yes
    requireForeignValid no
    if yes.valueType == .bool then do
      requireBoolean yes
      requireBoolean no
    let term := if yes.valueType == .bool && yes.term == typedBoolConstantTerm 1 &&
        no.term == typedBoolConstantTerm 0 then nativeToBoolTerm condition.term
      else .select condition.term yes.term no.term
    let fact ← combine term (max yes.maximum no.maximum) [condition, yes, no]
    defineResult state instruction {fact with
      valueType := yes.valueType
      foreignValid := isForeignType yes.valueType && yes.foreignValid && no.foreignValid
    }
  | "constrain_to_boolean" => refine state (← stringField instruction "val") 1
  | "constrain_bits" =>
    refine state (← stringField instruction "val") (2 ^ (← width instruction) - 1)
  | "constrain_eq" =>
    let leftText ← stringField instruction "a"
    let rightText ← stringField instruction "b"
    let left ← operand state leftText
    let right ← operand state rightText
    ensure (left.valueType == right.valueType)
      "constrain_eq operands have different native types"
    if left.valueType == .native then do
      let maximum := min left.maximum right.maximum
      let state ← refine state leftText maximum
      let state ← refine state rightText maximum
      let canonical := canonicalScalarInputMatches expected left.term right.term
      let coordinatePairs := state.requiredCoordinateEqualities.filter fun pair =>
        equalityPairMatches left.term right.term pair
      pure {state with
        canonicalScalarInputs := (state.canonicalScalarInputs ++ canonical).eraseDups
        establishedCoordinateEqualities :=
          (state.establishedCoordinateEqualities ++ coordinatePairs).eraseDups}
    else
      ensure (left.valueType == .jubjubScalar || left.valueType == .jubjubPoint || isForeignType left.valueType)
        "constrain_eq supports only qualified typed values"
      requireForeignValid left
      requireForeignValid right
      pure state
  | "less_than" =>
    let leftText ← stringField instruction "a"
    let left ← nativeOperand state leftText
    let right ← nativeArgument state instruction "b"
    let bits ← width instruction
    ensure (left.maximum < 2 ^ bits && right.maximum < 2 ^ bits)
      "less_than operand range precondition is not established"
    let fact ← combine (.binary s!"less_than:{bits}" left.term right.term) 1 [left, right]
    let assumption := match right.term with
      | .constant bound => if leftText.startsWith "%" then some (leftText, bound) else none
      | _ => none
    defineResult state instruction {fact with assertedLessThan := assumption}
  | "assert" =>
    let value ← nativeArgument state instruction "cond"
    requireBoolean value
    let state := if expected.assertions[state.assertionCount]? == some value.term then
      {state with assertionCount := state.assertionCount + 1} else state
    let state := {state with establishedAssertions := (value.term :: state.establishedAssertions).eraseDups}
    if let some (identifier, exclusive) := value.assertedLessThan then
      ensure (exclusive > 0) "asserted less_than has an impossible zero bound"
      refine state identifier (exclusive - 1)
    else pure state
  | "sha512" | "keccak256" => do
    let values ← nativeArguments state instruction "inputs"
    let alignment ← instruction.getObjVal? "alignment"
    let atoms ← alignment.getArr?
    ensure (atoms.size ≤ 32) "FAB byte hash alignment exceeds 32 atoms"
    let singleByteAtom := if atoms.size == 1 then
      match atoms[0]!.getObjVal? "value" with
      | .ok value => (stringField value "tag").toOption == some "bytes"
      | .error _ => false
      else false
    let term ← if atoms.isEmpty || singleByteAtom then
      checkedFixedByteHashTerm opcode alignment values
    else do
      let (descriptors, operands) ← checkedFabHashOperands alignment values
      pure (fabByteHashTerm opcode descriptors operands)
    let fact ← combine term 0 values
    defineResult state instruction {fact with valueType := byteValueType (if opcode == "sha512" then 64 else 32)}
  | "persistent_hash" => do
    let alignment ← instruction.getObjVal? "alignment"
    let values ← nativeArguments state instruction "inputs"
    let term ← if alignment == bytes32Alignment then do
        let pairs ← alignedBytes32Pairs values
        match pairs with
        | [pair] => pure (persistentHashVector32Term [pair])
        | _ => throw "Bytes32 persistent_hash requires exactly two aligned field operands"
      else if alignment == nativeFieldAlignment then do
        match values with
        | [value] => pure (persistentHashNativeTerm value.term)
        | _ => throw "Native persistent_hash requires exactly one field operand"
      else do
        let atoms ← alignment.getArr?
        if atoms.size ≥ 1 && atoms.size ≤ 32 && atoms.all (· == nativeFieldAtom) then do
          ensure (values.length == atoms.size)
            "Native vector persistent_hash field count differs from its alignment"
          pure (persistentHashNativeVectorTerm (values.map (·.term)))
        else if atoms.size ≤ 1 then
          checkedFixedByteHashTerm opcode alignment values
        else if atoms.any (fun atom =>
            match atom.getObjVal? "value" with
            | .ok value =>
              match value.getObjVal? "tag" with
              | .ok tag => match tag.getStr? with
                | .ok "field" => true
                | _ => false
              | .error _ => false
            | .error _ => false) || atoms.any (fun atom =>
              match atom.getObjVal? "value" with
              | .ok value =>
                match value.getObjVal? "tag", value.getObjVal? "length" with
                | .ok tag, .ok length =>
                  match tag.getStr?, length.getNat? with
                  | .ok "bytes", .ok width => width > 0 && width < 32
                  | _, _ => false
                | _, _ => false
              | .error _ => false) then do
          let (descriptors, operands) ← checkedFabHashOperands alignment values
          pure (persistentHashFabTerm descriptors operands)
        else do
          ensure (atoms.size ≥ 1 && atoms.size ≤ 33 && atoms.all (· == bytes32Atom))
            "persistent_hash supports only bounded Bytes32 or Native field vectors"
          ensure (values.length == atoms.size * 2)
            "Bytes32 vector persistent_hash requires two fields per aligned value"
          let pairs ← alignedBytes32Pairs values
          pure (persistentHashVector32Term pairs)
    let fact ← combine term (Field.modulus - 1) values
    let output ← stringField instruction "output"
    define state output {fact with valueType := .bytes32}
  | "nth" => do
    let bytes ← argument state instruction "bytes"
    let some length := byteLength? bytes.valueType | throw "nth requires typed bytes"
    let index ← natField instruction "index"
    ensure (index < length) "nth byte index is out of range"
    let fact ← combine (bytesByteAtTerm length bytes.term index) 255 [bytes]
    defineResult state instruction {fact with valueType := .byte}
  | "encode" => do
    let input ← argument state instruction "input"
    let outputs ← arrayField instruction "outputs"
    if let .foreign kind := input.valueType then do
      requireForeignValid input
      ensure (outputs.size == kind.encodedFieldCount) "foreign encode field count mismatch"
      let mut state := state
      for index in List.range outputs.size do
        let name ← outputs[index]!.getStr?
        let fact ← combine (foreignEncodedFieldTerm kind input.term index)
          (foreignEncodedFieldMaximum kind index) [input]
        state ← define state name fact
      pure state
    else if let some length := byteLength? input.valueType then do
      defineByteChunks state input length outputs
    else if input.valueType == .bool then do
      ensure (outputs.size == 1) "Bool encode requires exactly one Native output"
      requireBoolean input
      let output ← outputs[0]!.getStr?
      let fact ← combine (boolToNativeTerm input.term) 1 [input]
      define state output fact
    else if input.valueType == .jubjubScalar then do
      ensure (outputs.size == 1) "JubjubScalar encode requires exactly one Native output"
      let output ← outputs[0]!.getStr?
      let fact ← combine (Term.unary "jubjub_scalar_to_native" input.term)
        (Jubjub.scalarOrder - 1) [input]
      define state output fact
    else if input.valueType == .byte then do
      ensure (outputs.size == 1) "Byte encode requires exactly one Native output"
      ensure (input.maximum ≤ 255) "Byte encode operand lacks its byte range precondition"
      let output ← outputs[0]!.getStr?
      define state output {input with valueType := .native}
    else throw "encode accepts only qualified typed bytes, Bool, Byte or JubjubScalar values"
  | "to_bytes" => do
    let input ← argument state instruction "input"
    if let .foreign kind := input.valueType then do
      requireForeignValid input
      let fact ← combine (foreignUnaryTerm "to_bytes" kind input.term) 0 [input]
      defineResult state instruction {fact with valueType := byteValueType kind.byteLength}
    else do
      let term ← toBytes32Term input.valueType input.term
      let fact ← combine term 0 [input]
      defineResult state instruction {fact with valueType := .bytes32}
  | "bytes_into_natives" => do
    let bytes ← argument state instruction "bytes"
    let some length := byteLength? bytes.valueType
      | throw "bytes_into_natives requires typed bytes"
    let outputs ← arrayField instruction "outputs"
    defineByteChunks state bytes length outputs
  | "reverse" => do
    let bytes ← argument state instruction "bytes"
    let some length := byteLength? bytes.valueType | throw "reverse requires typed bytes"
    ensure (0 < length && length ≤ Types.defaultLimits.maxVectorLength) "reverse byte length is unsupported"
    let fact ← combine (reverseBytesTerm length bytes.term) 0 [bytes]
    defineResult state instruction {fact with valueType := byteValueType length}
  | "slice" => do
    let bytes ← argument state instruction "bytes"
    let some length := byteLength? bytes.valueType | throw "slice requires typed bytes"
    let start ← natField instruction "start"
    let count ← natField instruction "len"
    ensure (0 < count && start + count ≤ length && length ≤ Types.defaultLimits.maxVectorLength)
      "native slice requires a nonempty in-bounds byte range"
    let fact ← combine (sliceBytesTerm length start (start + count) bytes.term) 0 [bytes]
    defineResult state instruction {fact with valueType := byteValueType count}
  | "concat" => do
    let values ← arguments state instruction "inputs"
    let [left, right] := values | throw "source concat requires exactly two byte operands"
    let some leftLength := byteLength? left.valueType | throw "concat requires typed bytes"
    let some rightLength := byteLength? right.valueType | throw "concat requires typed bytes"
    ensure (0 < leftLength && 0 < rightLength && leftLength + rightLength ≤ Types.defaultLimits.maxVectorLength)
      "concat byte length is unsupported"
    let fact ← combine (concatBytesTerm leftLength rightLength left.term right.term) 0 values
    defineResult state instruction {fact with valueType := byteValueType (leftLength + rightLength)}
  | "bytes_from_natives" => do
    let values ← nativeArguments state instruction "inputs"
    let length ← natField instruction "len"
    ensure (0 < length && length ≤ Types.defaultLimits.maxVectorLength)
      "bytes_from_natives length is unsupported"
    ensure (values.length == bytesChunkCount length) "bytes_from_natives chunk count mismatch"
    for (value, index) in values.zipIdx do
      ensure (value.maximum ≤ 2 ^ (8 * bytesChunkWidth length index) - 1)
        "bytes_from_natives operand lacks its exact chunk range bound"
    let terms := values.map (·.term)
    -- Exact complementary chunks represent the same original Bytes32 once.
    let children := if length == 32 && (reassembledBytes32? terms).isSome then
      values.take 1 else values
    let fact ← combine (bytesFromChunksTerm length terms) 0 children
    defineResult state instruction {fact with valueType := byteValueType length}
  | "from_bytes" => do
    let bytes ← argument state instruction "bytes"
    let typeName ← stringField instruction "type"
    if let some kind := Foreign.kinds.find? (·.nativeName == typeName) then do
      let some length := byteLength? bytes.valueType | throw "foreign from_bytes requires typed bytes"
      ensure (0 < length && length ≤ Types.defaultLimits.maxVectorLength)
        "foreign from_bytes length is unsupported"
      if let .point _ := kind then
        ensure (length == kind.byteLength) "foreign point decoding requires the curve's exact byte length"
      let fact ← combine (foreignFromBytesTerm kind length bytes.term) 0 [bytes]
      defineResult state instruction {fact with valueType := .foreign kind, foreignValid := true}
    else do
      let some length := byteLength? bytes.valueType | throw "from_bytes requires typed bytes"
      ensure (0 < length && length ≤ Types.defaultLimits.maxVectorLength)
        "from_bytes length is unsupported"
      let (valueType, term, maximum) ←
        if typeName == "Point<Jubjub>" then do
          ensure (bytes.valueType == .bytes32) "Jubjub point decoding requires a typed Bytes32 operand"
          fromBytes32Term typeName bytes.term
        else scalarFromBytesTerm typeName length bytes.term
      let fact ← combine term maximum [bytes]
      defineResult state instruction {fact with valueType}
  | "jubjub_scalar_from_native" => do
    let value ← nativeArgument state instruction "native"
    let term := Term.unary "jubjub_scalar_from_native" value.term
    let fact ← combine term (Jubjub.scalarOrder - 1) [value]
    defineResult state instruction {fact with valueType := .jubjubScalar}
  | "hash_to_curve" => do
    let values ← nativeArguments state instruction "inputs"
    ensure (values.length ≤ Types.defaultLimits.maxVectorLength)
      "hash_to_curve exceeds the source field-vector bound"
    let fact ← combine (hashToCurveTerm (values.map (·.term))) (Field.modulus - 1) values
    defineResult state instruction {fact with valueType := .jubjubPoint}
  | "ec_mul_generator" => do
    let scalar ← argument state instruction "scalar"
    if let .foreign (.scalar curve) := scalar.valueType then do
      defineResult state instruction (← foreignResult (.point curve)
        (foreignUnaryTerm "mulGenerator" (.scalar curve) scalar.term) [scalar])
    else do
      ensure (scalar.valueType == .jubjubScalar) "ec_mul_generator requires a qualified curve scalar"
      let fact ← combine (.unary "ec_mul_generator_jubjub" scalar.term) (Field.modulus - 1) [scalar]
      defineResult state instruction {fact with valueType := .jubjubPoint}
  | "ec_mul" => do
    let point ← argument state instruction "a"
    let scalar ← argument state instruction "scalar"
    if let .foreign (.point curve) := point.valueType then do
      ensure (scalar.valueType == .foreign (.scalar curve)) "foreign ec_mul scalar family mismatch"
      defineResult state instruction (← foreignResult (.point curve)
        (foreignBinaryTerm "ecMul" (.point curve) point.term scalar.term) [point, scalar])
    else do
      ensure (point.valueType == .jubjubPoint && scalar.valueType == .jubjubScalar)
        "ec_mul requires a matching point and scalar"
      let fact ← combine (.binary "ec_mul_jubjub" point.term scalar.term) (Field.modulus - 1) [point, scalar]
      defineResult state instruction {fact with valueType := .jubjubPoint}
  | "from_coordinates" => do
    let inputs ← arguments state instruction "inputs"
    let [x, y] := inputs | throw "from_coordinates requires exactly two inputs"
    if let .foreign (.base curve) := x.valueType then do
      ensure (y.valueType == x.valueType) "foreign coordinate field family mismatch"
      let fact ← foreignResult (.point curve)
        (foreignBinaryTerm "fromCoordinates" (.base curve) x.term y.term) [x, y]
      defineResult state instruction {
        fact with foreignNonidentity := coordinateExtractionRequiresNonidentity curve}
    else do
      requireNative x
      requireNative y
      let pointTerm := Term.binary "from_coordinates_jubjub" x.term y.term
      let fact ← combine pointTerm (Field.modulus - 1) [x, y]
      let state ← defineResult state instruction {fact with valueType := .jubjubPoint}
      let required := [(x.term, Term.unary "jubjub_x" pointTerm), (y.term, Term.unary "jubjub_y" pointTerm)]
      pure {state with requiredCoordinateEqualities := (state.requiredCoordinateEqualities ++ required).eraseDups}
  | "into_coordinates" => do
    let point ← argument state instruction "point"
    let outputs ← arrayField instruction "outputs"
    ensure (outputs.size == 2) "into_coordinates requires exactly two outputs"
    let xName ← outputs[0]!.getStr?
    let yName ← outputs[1]!.getStr?
    if let .foreign (.point curve) := point.valueType then do
      if coordinateExtractionRequiresNonidentity curve then
        ensure (point.foreignNonidentity || state.establishedAssertions.contains (foreignNonzeroTerm (.point curve) point.term))
          "foreign coordinate extraction lacks its nonidentity assertion"
      let x ← foreignResult (.base curve) (foreignUnaryTerm "x" (.point curve) point.term) [point]
      let state ← define state xName x
      let y ← foreignResult (.base curve) (foreignUnaryTerm "y" (.point curve) point.term) [point]
      define state yName y
    else do
      ensure (point.valueType == .jubjubPoint) "into_coordinates requires a qualified point"
      let x ← combine (.unary "jubjub_x" point.term) (Field.modulus - 1) [point]
      let state ← define state xName x
      let y ← combine (.unary "jubjub_y" point.term) (Field.modulus - 1) [point]
      define state yName y
  | "transient_hash" =>
    let values ← nativeArguments state instruction "inputs"
    ensure (values.length ≤ Types.defaultLimits.maxVectorLength)
      "transient_hash exceeds the source field-vector bound"
    let terms := values.map (·.term)
    let fact ← match conditionalSwapHash? terms with
      | some term => combine term (Field.modulus - 1) (values.take 1)
      | none => combine (.hash terms) (Field.modulus - 1) values
    defineResult state instruction fact
  | "impact" =>
    ensure (descriptor.privacy == .publicBindingSink) "native Impact lacks a public binding policy"
    let guardText ← stringField instruction "guard"
    let guard ← nativeOperand state guardText
    requireBoolean guard
    let values ← nativeArguments state instruction "inputs"
    let some group := expected.groups[state.groupCount]? | throw "unexpected native activity group"
    let expectedGuard ← if expected.groupGuards.isEmpty then pure (.constant 1) else
      match expected.groupGuards[state.groupCount]? with
      | some guard => pure guard
      | none => throw "source activity guard schedule is incomplete"
    ensure (guard.term == expectedGuard)
      "native Impact guard differs from the source-derived activity guard"
    let actualTerms := values.map (·.term)
    ensure (actualTerms == group) "native transcript activity grouping/payload mismatch"
    pure {state with groupCount := state.groupCount + 1}
  | "output" =>
    ensure (descriptor.privacy == .publicReturn) "native output lacks a public return policy"
    let values ← nativeArguments state instruction "vals"
    ensure (values.map (·.term) == expected.returns) "native return signature/value mismatch"
    pure state
  | _ => throw "registered native descriptor has no executable validation rule"

def opcode (instruction : Json) : String :=
  (stringField instruction "op").toOption.getD ""

def finalOutputShape (instructions : List Json) : Bool :=
  !instructions.isEmpty && (instructions.map opcode).count "output" == 1 &&
    (instructions.getLast?.map opcode).getD "" == "output"

def requireFinalOutput (instructions : List Json) : Except String Unit :=
  ensure (finalOutputShape instructions) "native program requires exactly one final Output"

def sourceMaximum : Ty → Nat
  | .native => Field.modulus - 1
  | .bool => 1
  | .uint maximum => maximum
  | .bytes _ => 0
  | .opaqueBytes => Field.modulus - 1
  | .opaqueString => Field.modulus - 1
  | .jubjubScalar => Jubjub.scalarOrder - 1
  | .jubjubPoint | .foreign _ => 0

def checkBound (state : State) (term : Term) (maximum : Nat) : Except String Unit := do
  let bounded := match term with
    | .constant value => value ≤ maximum
    | _ => state.definitions.any fun (_, fact) => fact.term == term && fact.maximum ≤ maximum
  ensure bounded "typed source range/Boolean requirement is absent from native constraints"

/-- Validate a generated Native-scalar program against an independently derived
typed statement/schedule. This does not authenticate a raw caller's Expected. -/
def validate (expected : Expected) (program : Json) : Except String Unit := do
  ensure (expected.groupGuards.isEmpty || expected.groupGuards.length == expected.groups.length)
    "source activity guard schedule length mismatch"
  fields program ["version", "inputs", "outputs", "do_communications_commitment", "instructions"]
  let version ← program.getObjVal? "version"
  fields version ["major", "minor"]
  ensure ((← natField version "major") == 3 && (← natField version "minor") == 2)
    "unsupported native producer IR version"
  let instructions ← arrayField program "instructions"
  ensure (instructions.size ≤ maxInstructions &&
    expected.rawInputs.length + expected.inputs.length ≤ maxInputs &&
    expected.returns.length ≤ 256 && expected.groups.length ≤ maxInstructions &&
    expected.assertions.length ≤ maxInstructions)
    "native producer resource limit exceeded"
  let rawInputs ← arrayField program "inputs"
  ensure (rawInputs.size == expected.rawInputs.length)
    "native raw call input header count mismatch"
  let rawNames := expected.rawInputs.map (·.identifier)
  let instructionNames := expected.inputs.map (·.identifier)
  ensure ((rawNames ++ instructionNames).eraseDups.length == rawNames.length + instructionNames.length)
    "native raw and instruction input names collide"
  let mut state : State := {}
  for (rawInput, index) in rawInputs.toList.zipIdx do
    let some required := expected.rawInputs[index]? | throw "unexpected native raw call input"
    fields rawInput ["name", "type"]
    ensure (required.visibility == .«private» && !required.ty.isBytes)
      "native raw call inputs require private scalar projections"
    let name ← stringField rawInput "name"
    ensure (name == required.identifier) "native raw call input name/order mismatch"
    let valueType ← match required.ty with
      | .foreign kind => do
        ensure ((← stringField rawInput "type") == kind.nativeName) "native raw call input type mismatch"
        pure (.foreign kind : NativeValueType)
      | _ => do
        nativeType (← rawInput.getObjVal? "type")
        pure .native
    let foreignValid := isForeignType valueType
    state ← define state name {
      term := .input name
      valueType
      foreignValid
      maximum := if foreignValid then 0 else Field.modulus - 1
    }
  let returns ← arrayField program "outputs"
  ensure (returns.size == expected.returns.length) "native output header count mismatch"
  for output in returns do nativeType output
  ensure ((← (← program.getObjVal? "do_communications_commitment").getBool?) ==
    (expected.mode == .ledgerCall)) "native communication commitment policy mismatch"
  requireFinalOutput instructions.toList
  for (instruction, index) in instructions.toList.zipIdx do
    match validateInstruction expected state instruction with
    | .ok next => state := next
    | .error message => throw s!"native instruction {index}: {message}"
  ensure (state.inputCount == expected.inputs.length) "missing native transcript input"
  ensure (state.groupCount == expected.groups.length) "missing native transcript activity group"
  ensure (state.assertionCount == expected.assertions.length) "missing or reordered typed source assertion"
  for input in expected.rawInputs ++ expected.inputs do
    ensure (!input.ty.isBytes) "Bytes32 must be expanded into UInt8 native inputs"
    match input.ty with
    | .foreign kind => do
      let value ← operand state input.identifier
      ensure (value.valueType == .foreign kind) "foreign input lost its source type"
      requireForeignValid value
    | _ => do
      let maximum := if input.canonicalJubjubScalar then Jubjub.scalarOrder - 1
        else sourceMaximum input.ty
      checkBound state (.input input.identifier) maximum
    if input.canonicalJubjubScalar then
      ensure (state.canonicalScalarInputs.contains input.identifier)
        "typed JubjubScalar input lacks its canonical reduce/encode equality bridge"
  for pair in state.requiredCoordinateEqualities do
    ensure (state.establishedCoordinateEqualities.contains pair)
      "Jubjub FromCoordinates lacks exact Native x/y roundtrip constraints"
  for (term, maximum) in expected.bounds do checkBound state term maximum

theorem final_output_required (instructions : List Json) :
    requireFinalOutput instructions = .ok () ↔ finalOutputShape instructions = true := by
  simp [requireFinalOutput, ensure]
  cases finalOutputShape instructions <;> simp
  rfl

theorem established_boolean_range (fact : Fact) (value : Nat)
    (hmax : fact.maximum ≤ 1) (hvalue : value ≤ fact.maximum) : value = 0 ∨ value = 1 := by omega

theorem require_boolean_iff (fact : Fact) :
    requireBoolean fact = .ok () ↔ fact.maximum ≤ 1 := by
  simp [requireBoolean, ensure]
  split <;> simp_all
  rfl

end Noctium.Backend.Native
