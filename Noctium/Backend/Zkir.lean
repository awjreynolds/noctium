import Noctium.IR
import Noctium.Backend.Impact
import Noctium.Passes
import Noctium.Backend.NativeExpected
import Noctium.Backend.NativeProducer
import Noctium.Backend.RangeDedup

namespace Noctium.Backend.Zkir

open Lean

/-- Initial relation producer. Ledger transcript/state integration is separate. -/
private def nativeType : Json := toJson ("Scalar<BLS12-381>" : String)

theorem nativeType_eq : nativeType = toJson ("Scalar<BLS12-381>" : String) := rfl

private def validateProduced (span : SourceSpan) (expected : Native.Expected) (program : Json) :
    Except Diagnostic Json :=
  match Native.validate expected program with
  | .ok _ => .ok program
  | .error message => .error {span, message := "native producer invariant: " ++ message}

theorem validateProduced_ok (span : SourceSpan) (expected : Native.Expected) (program result : Json) :
    validateProduced span expected program = .ok result ↔
      result = program ∧ Native.validate expected program = .ok () := by
  cases checked : Native.validate expected program <;> simp [validateProduced, checked]
  constructor <;> intro equal <;> exact equal.symm

inductive Rewrites where
  | disabled
  | rangeAndAssertions
  | includingComparisons
  deriving BEq

private def optimizedInstructions (rewrites : Rewrites) (instructions : Array Json) : Array Json :=
  match rewrites with
  | .disabled => instructions
  | .rangeAndAssertions => RangeDedup.removeDuplicateAssertions (RangeDedup.run instructions)
  | .includingComparisons =>
    RangeDedup.removeDuplicateAssertions (RangeDedup.reuseComparisons (RangeDedup.run instructions))

private def optimizedExpected (rewrites : Rewrites) (expected : Native.Expected) : Native.Expected :=
  if rewrites == .disabled then expected
  else {expected with assertions := expected.assertions.eraseDups}

private theorem bind_ok (first : Except ε α) (next : α → Except ε β) (value : β) :
    Except.bind first next = .ok value ↔ ∃ intermediate, first = .ok intermediate ∧ next intermediate = .ok value := by
  cases first <;> simp [Except.bind]

def nativeModulus : Nat :=
  52435875175126190479447740508185965837690552500527637822603658699938581184513

mutual
private def checkConstants : Expr ty → Except String Unit
  | .native n => if n < nativeModulus then pure () else throw "noncanonical Native constant"
  | .bool _ | .ref _ | .opaqueBytesEmpty | .opaqueStringEmpty => pure ()
  | .foreignBase curve value => discard (Foreign.encodeField (.base curve) value)
  | .foreignScalar curve value => discard (Foreign.encodeField (.scalar curve) value)
  | .foreignPoint curve value => discard (Foreign.encodePoint curve value)
  | .foreignEncodedField value _ | .foreignUnary _ value | .foreignToBytes value
  | .foreignFromBytes _ value => checkConstants value
  | .foreignBinary _ left right => do checkConstants left; checkConstants right
  | .uint maximum value =>
    if maximum ≤ ScalarPolicy.maxUint && value ≤ maximum then pure ()
    else throw "noncanonical unsigned constant"
  | .bytesField value _ | .bytesAt value _ => checkConstants value
  | .opaqueBytesProjection value => checkConstants value
  | .opaqueStringProjection value => checkConstants value
  | .toBytes32 value => checkConstants value
  | .copyValue value | .reverseBytes32 value | .reverseBytes value | .sliceBytes value _ _ => checkConstants value
  | .concatBytes left right => do checkConstants left; checkConstants right
  | .bytesLiteral _ _ => pure ()
  | .fromBytes32 value => checkConstants value
  | .fromBytes value => checkConstants value
  | .inv value => checkConstants value
  | .sha256 value | .sha512 value | .keccak256 value
  | .keccak256Secp256k1Point value | .persistentHash32 value => checkConstants value
  | .bytes32Literal _ => pure ()
  | .persistentHashVector32 _ => pure ()
  | .persistentHashNative value => checkConstants value
  | .persistentHashFab _ _ values | .transientHashFab _ _ values => checkFabConstants values
  | .sha512Fab _ _ values | .keccak256Fab _ _ values => checkFabConstants values
  | .persistentCommitFab _ _ opening values => do
    checkConstants opening
    checkFabConstants values
  | .transientCommitFab _ _ opening values => do
    checkConstants opening
    checkFabConstants values
  | .hashToCurve values | .persistentHashNativeVector values | .transientHash values => checkNativeConstants values
  | .hashToCurveFab _ _ values => checkFabConstants values
  | .jubjubScalarFromNative value | .jubjubScalarToNative value
  | .jubjubMulGenerator value | .jubjubNeg value
  | .jubjubCoordinate value _ => checkConstants value
  | .jubjubMul point scalar | .jubjubAdd point scalar => do
    checkConstants point
    checkConstants scalar
  | .jubjubFromCoordinates x y => do
    checkConstants x
    checkConstants y
  | .boolAnd a b | .boolOr a b | .boolXor a b
  | .add a b | .mul a b | .sub a b | .eq a b
  | .uadd a b | .usub a b | .umul a b => do checkConstants a; checkConstants b
  | .cast _ value => checkConstants value
  | .letE _ value body => do checkConstants value; checkConstants body
  | .assertE condition body => do checkConstants condition; checkConstants body
  | .disclose _ value => checkConstants value
  | .select c a b => do checkConstants c; checkConstants a; checkConstants b
  | .poseidon2 domain a b => do
    unless domain < nativeModulus do throw "noncanonical Poseidon domain tag"
    checkConstants a
    checkConstants b
termination_by value => sizeOf value
decreasing_by
  all_goals simp_wf
  all_goals first
    | exact sizeOfSigmaExprHeadLt _ _
    | exact sizeOfSigmaExprValueLt _
    | have h := sizeOfMemberListLt (by assumption); omega
    | omega

private def checkFabConstants : List (Sigma Expr) → Except String Unit
  | [] => pure ()
  | ⟨_, value⟩ :: rest => do
    checkConstants value
    checkFabConstants rest
termination_by values => sizeOf values
decreasing_by
  all_goals simp_wf
  all_goals first
    | exact sizeOfSigmaExprHeadLt _ _
    | omega

private def checkNativeConstants : List (Expr .native) → Except String Unit
  | [] => pure ()
  | value :: rest => do
    checkConstants value
    checkNativeConstants rest
termination_by values => sizeOf values
decreasing_by all_goals simp_wf <;> omega
end

def instruction (op : String) (fields : List (String × Json)) : Json :=
  Json.mkObj (("op", toJson op) :: fields)

/-- ZKIR field immediates use little-endian bytes, including leading zero bytes. -/
def fieldImmediate (n : Nat) : String :=
  "0x" ++ go n (n.log2 / 8 + 1)
where
  go (n : Nat) : Nat → String
    | 0 => ""
    | fuel + 1 =>
      let byte := n % 256
      let digits := "0123456789abcdef".toList.toArray
      String.singleton digits[byte / 16]! ++ String.singleton digits[byte % 16]! ++
        go (n / 256) fuel

/-- CSE compares actual opcode, ordered operands and optional hash domain.
Structural keys make cache-hit meaning available to kernel proofs. -/
abbrev ExpressionKey := String × List String × Option Nat

/-- Byte leaves and encoded chunks must remain distinct, including Bytes1. -/
structure ByteOperands where
  values : List String
  packed : Bool := false

structure LowerState where
  next : Nat := 0
  instructions : Array Json := #[]
  expressions : List (ExpressionKey × String) := []
  aliases : List (String × String) := []
  byteAliases : List (String × ByteOperands) := []
  pointCoordinates : List (String × (String × String)) := []

/-- Count the result names described by this state's actual native instructions.
This stays derived from the emitted vector, rather than a second mutable counter. -/
def LowerState.outputDefinitions (state : LowerState) : Nat :=
  Native.outputDefinitionsInInstructions state.instructions.toList

private theorem outputDefinitionsInInstructions_append (first second : List Json) :
    Native.outputDefinitionsInInstructions (first ++ second) =
      Native.outputDefinitionsInInstructions first +
        Native.outputDefinitionsInInstructions second := by
  induction first with
  | nil => simp [Native.outputDefinitionsInInstructions]
  | cons instruction rest ih =>
    simp [Native.outputDefinitionsInInstructions, ih, Nat.add_assoc]

theorem LowerState.outputDefinitions_append (state : LowerState) (suffix : List Json) :
    ({state with instructions := state.instructions ++ suffix.toArray}).outputDefinitions =
      state.outputDefinitions + Native.outputDefinitionsInInstructions suffix := by
  simp only [LowerState.outputDefinitions, Array.toList_append]
  rw [outputDefinitionsInInstructions_append]

theorem LowerState.outputDefinitions_push (state : LowerState) (value : Json) :
    ({state with instructions := state.instructions.push value}).outputDefinitions =
      state.outputDefinitions + Native.outputDefinitionsInInstruction value := by
  simpa [Array.toList_push, Native.outputDefinitionsInInstructions] using
    LowerState.outputDefinitions_append state [value]

/-- A lowering step allocates no more fresh SSA names than the output slots in
its actual emitted native instructions. -/
structure OutputCapacityFrame (before after : LowerState) : Prop where
  next : before.next ≤ after.next
  definitions : before.outputDefinitions + (after.next - before.next) ≤
    after.outputDefinitions

theorem OutputCapacityFrame.refl (state : LowerState) :
    OutputCapacityFrame state state := by
  constructor <;> simp

theorem OutputCapacityFrame.trans {before middle after : LowerState}
    (first : OutputCapacityFrame before middle)
    (second : OutputCapacityFrame middle after) :
    OutputCapacityFrame before after := by
  rcases first with ⟨firstNext, firstDefinitions⟩
  rcases second with ⟨secondNext, secondDefinitions⟩
  constructor <;> omega

private theorem OutputCapacityFrame.of_instruction_push
    {before after : LowerState} (emitted : Json)
    (next : before.next ≤ after.next)
    (instructions : after.instructions = before.instructions.push emitted)
    (definitions : after.next - before.next ≤ Native.outputDefinitionsInInstruction emitted) :
    OutputCapacityFrame before after := by
  constructor
  · exact next
  · change before.outputDefinitions + (after.next - before.next) ≤ after.outputDefinitions
    unfold LowerState.outputDefinitions at *
    rw [instructions, Array.toList_push, outputDefinitionsInInstructions_append]
    simp only [Native.outputDefinitionsInInstructions]
    omega

def PreservesOutputCapacityFrame (operation : StateM LowerState α) : Prop :=
  ∀ state, OutputCapacityFrame state (operation.run state).2

private theorem modify_preservesOutputCapacityFrame (update : LowerState → LowerState)
    (next : ∀ state, (update state).next = state.next)
    (instructions : ∀ state, (update state).instructions = state.instructions) :
    PreservesOutputCapacityFrame (modify update) := by
  intro state
  change OutputCapacityFrame state (update state)
  constructor
  · rw [next state]
    exact Nat.le_refl _
  · change state.outputDefinitions + ((update state).next - state.next) ≤
      (update state).outputDefinitions
    rw [next state, Nat.sub_self]
    unfold LowerState.outputDefinitions
    rw [instructions state]
    omega

theorem pure_preservesOutputCapacityFrame (value : α) :
    PreservesOutputCapacityFrame (pure value) := by
  intro state
  exact OutputCapacityFrame.refl state

theorem bind_preservesOutputCapacityFrame (first : StateM LowerState α)
    (next : α → StateM LowerState β)
    (firstFrame : PreservesOutputCapacityFrame first)
    (nextFrame : ∀ value, PreservesOutputCapacityFrame (next value)) :
    PreservesOutputCapacityFrame (first >>= next) := by
  intro state
  change OutputCapacityFrame state ((next (first.run state).1).run (first.run state).2).2
  exact (firstFrame state).trans (nextFrame _ _)

theorem OutputCapacityFrame.next_le_outputDefinitions
    {before after : LowerState} (frame : OutputCapacityFrame before after)
    (beforeBound : before.next ≤ before.outputDefinitions) :
    after.next ≤ after.outputDefinitions := by
  rcases frame with ⟨next, definitions⟩
  omega

/-- Apply the producer's checked output-capacity bound to a state reached from
the empty allocator state. The producer's instruction-count cap remains the
source of `capacity`, while this frame accounts for generated SSA names. -/
theorem OutputCapacityFrame.next_le_producerCapacity
    {after : LowerState} (frame : OutputCapacityFrame {} after)
    (capacity : after.outputDefinitions ≤ Native.maxInstructions * Native.maxVectorLength) :
    after.next ≤ Native.maxInstructions * Native.maxVectorLength := by
  have names := frame.next_le_outputDefinitions (by simp [LowerState.outputDefinitions])
  exact Nat.le_trans names capacity

private abbrev LowerM := StateM LowerState

def emit (op : String) (fields : List (String × Json)) : LowerM Unit :=
  modify fun s => { s with instructions := s.instructions.push (instruction op fields) }

private theorem emit_preservesOutputCapacityFrame (op : String)
    (fields : List (String × Json)) :
    PreservesOutputCapacityFrame (emit op fields) := by
  intro state
  apply OutputCapacityFrame.of_instruction_push (instruction op fields)
  · change state.next ≤ state.next
    exact Nat.le_refl _
  · rfl
  · change state.next - state.next ≤ Native.outputDefinitionsInInstruction (instruction op fields)
    omega

/-- Keep the state-only lowering monad total while ensuring rejected source
shapes still fail the mandatory native validator. -/
-- shortcut: replace validator poison with typed lowering errors when extending byte expressions.
private def rejectLowering (message : String) : LowerM Unit :=
  emit "noctium_invalid_lowering" [("message", toJson message)]

def fresh : LowerM String := do
  let s ← get
  set { s with next := s.next + 1 }
  return s!"%v{s.next}"

def binary (op a b : String) : LowerM String := do
  let key : ExpressionKey := (op, [a, b], none)
  if let some existing := (← get).expressions.lookup key then return existing
  let output ← fresh
  emit op [("a", toJson a), ("b", toJson b), ("output", toJson output)]
  modify fun s => {s with expressions := (key, output) :: s.expressions}
  return output

/-- Lower Native addition while retaining both operands' eager lowering effects.
Literal-zero operands need no ZKIR `add` instruction. -/
def nativeAdd (leftIsZero rightIsZero : Bool) (left right : String) : LowerM String :=
  if leftIsZero then pure right else if rightIsZero then pure left else binary "add" left right

def unary (op a : String) (operandField : String := "a") : LowerM String := do
  let key : ExpressionKey := (op, [a], none)
  if let some existing := (← get).expressions.lookup key then return existing
  let output ← fresh
  emit op [(operandField, toJson a), ("output", toJson output)]
  modify fun s => {s with expressions := (key, output) :: s.expressions}
  return output

/-- less_than assumes bounded operands. Range-check the value first and only
compare against a constant fitting the same width. Power-of-two limits need no comparison. -/
def constrainUnsigned (maximum : Nat) (value : String) : LowerM Unit := do
  if maximum == 0 then
    emit "constrain_eq" [("a", toJson value), ("b", toJson ("0x00" : String))]
  else
    let bits := maximum.log2 + 1
    emit "constrain_bits" [("val", toJson value), ("bits", toJson bits)]
    unless maximum + 1 == 2 ^ bits do
      let output ← fresh
      emit "less_than" [("a", toJson value), ("b", toJson (fieldImmediate (maximum + 1))),
        ("bits", toJson bits), ("output", toJson output)]
      emit "assert" [("cond", toJson output)]

/-- Lower bounded unsigned addition. The output keeps the source sum bound even
when a literal-zero operand lets the arithmetic instruction disappear. -/
def nativeUIntAdd (maximum : Nat) (leftIsZero rightIsZero : Bool)
    (left right : String) : LowerM String := do
  let output ← nativeAdd leftIsZero rightIsZero left right
  constrainUnsigned maximum output
  pure output

def constrainType (ty : Ty) (value : String) : LowerM Unit :=
  match ty with
  | .native => pure ()
  | .bool => emit "constrain_to_boolean" [("val", toJson value)]
  | .uint maximum => constrainUnsigned maximum value
  | .bytes _ => rejectLowering "Bytes32 must be expanded into byte inputs"
  | .opaqueBytes => pure ()
  | .opaqueString => pure ()
  | .jubjubScalar | .jubjubPoint | .foreign _ => rejectLowering "opaque values require their typed input bridge"

private def lowerInputRequirement (op : String) (raw : Bool)
    (spec : Native.InputRequirement) : LowerM Unit := do
  unless raw do
    emit op [("guard", Json.null), ("type", nativeType), ("output", toJson spec.identifier)]
  constrainType spec.ty spec.identifier

private def lowerInputRequirements (op : String) (raw : Bool) :
    List Native.InputRequirement → LowerM Unit
  | [] => pure ()
  | spec :: rest => do
    lowerInputRequirement op raw spec
    lowerInputRequirements op raw rest

private def lowerJubjubScalarFromNative (native : String) : LowerM String := do
  let key : ExpressionKey := ("jubjub_scalar_from_native", [native], none)
  if let some existing := (← get).expressions.lookup key then return existing
  let output ← fresh
  emit "jubjub_scalar_from_native" [("native", toJson native), ("output", toJson output)]
  modify fun state => {state with expressions := (key, output) :: state.expressions}
  pure output

private def lowerJubjubScalarToNative (scalar : String) : LowerM String := do
  let key : ExpressionKey := ("encode_jubjub_scalar", [scalar], none)
  if let some existing := (← get).expressions.lookup key then return existing
  let output ← fresh
  emit "encode" [("input", toJson scalar), ("outputs", toJson [output])]
  modify fun state => {state with expressions := (key, output) :: state.expressions}
  pure output

private def lowerPointCoordinates (point : String) : LowerM (String × String) := do
  if let some outputs := (← get).pointCoordinates.lookup point then return outputs
  let x ← fresh
  let y ← fresh
  emit "into_coordinates" [("point", toJson point), ("outputs", toJson [x, y])]
  modify fun state => {state with pointCoordinates := (point, (x, y)) :: state.pointCoordinates}
  pure (x, y)

/-- Every coordinate reconstruction checks both affine limbs after the pinned
FromCoordinates operation. This closes the source/native x roundtrip gap. -/
private def lowerPointFromCoordinates (x y : String) : LowerM String := do
  let key : ExpressionKey := ("from_coordinates_jubjub", [x, y], none)
  if let some existing := (← get).expressions.lookup key then return existing
  let point ← fresh
  emit "from_coordinates" [("inputs", toJson [x, y]), ("output", toJson point)]
  let (actualX, actualY) ← lowerPointCoordinates point
  emit "constrain_eq" [("a", toJson x), ("b", toJson actualX)]
  emit "constrain_eq" [("a", toJson y), ("b", toJson actualY)]
  modify fun state => {state with expressions := (key, point) :: state.expressions}
  pure point

private def lowerForeignConstant (kind : Foreign.Kind) (encoding : Except String (List Nat)) : LowerM String := do
  let values ← match encoding with
    | .ok values => pure values
    | .error message => do
      rejectLowering message
      pure []
  let operands := values.map fieldImmediate
  let key : ExpressionKey := ("load_constant:" ++ kind.nativeName, operands, none)
  if let some existing := (← get).expressions.lookup key then return existing
  let output ← fresh
  emit "load_constant" [("type", toJson kind.nativeName), ("encoding", toJson operands), ("output", toJson output)]
  modify fun state => {state with expressions := (key, output) :: state.expressions}
  pure output

private def encodeForeign (kind : Foreign.Kind) (value : String) : LowerM (List String) := do
  let keys := (List.range kind.encodedFieldCount).map fun index =>
    (("encode_foreign:" ++ kind.nativeName, [value], some index) : ExpressionKey)
  let expressions := (← get).expressions
  let cached := keys.map (fun key => expressions.lookup key)
  if cached.all Option.isSome then return cached.filterMap id
  let outputs ← keys.mapM fun _ => fresh
  emit "encode" [("input", toJson value), ("outputs", toJson outputs)]
  modify fun state => {state with expressions := keys.zip outputs ++ state.expressions}
  pure outputs

private def assertEqual (left right : String) : LowerM Unit := do
  let equal ← binary "test_eq" left right
  emit "assert" [("cond", toJson equal)]

private def assertForeignNonzero (kind : Foreign.Kind) (value : String) : LowerM Unit := do
  let zero ← lowerForeignConstant kind (match kind with
    | .point curve => .ok (Foreign.identityEncoding curve)
    | _ => Foreign.encodeField kind 0)
  let equal ← binary "test_eq" value zero
  let nonzero ← unary "not" equal
  emit "assert" [("cond", toJson nonzero)]

private def lowerForeignUnary (op : Foreign.UnaryOp) (value : String) : LowerM String := do
  match op with
  | .neg _ => unary "neg" value
  | .inv field => do
    assertForeignNonzero field.kind value
    unary "inv" value
  | .x curve | .y curve => do
    if Noctium.Backend.Native.coordinateExtractionRequiresNonidentity curve then
      assertForeignNonzero (.point curve) value
    let (x, y) ← lowerPointCoordinates value
    pure (match op with | .x _ => x | _ => y)
  | .mulGenerator curve => do
    let key : ExpressionKey := ("ec_mul_generator:" ++ curve.name, [value], none)
    if let some existing := (← get).expressions.lookup key then return existing
    let output ← fresh
    emit "ec_mul_generator" [("scalar", toJson value), ("output", toJson output)]
    modify fun state => {state with expressions := (key, output) :: state.expressions}
    pure output

private def lowerForeignBinary (op : Foreign.BinaryOp) (left right : String) : LowerM String := do
  match op with
  | .add _ => binary "add" left right
  | .sub _ => binary "add" left (← unary "neg" right)
  | .mul _ => binary "mul" left right
  | .ecMul curve => do
    let key : ExpressionKey := ("ec_mul:" ++ curve.name, [left, right], none)
    if let some existing := (← get).expressions.lookup key then return existing
    let output ← fresh
    emit "ec_mul" [("a", toJson left), ("scalar", toJson right), ("output", toJson output)]
    modify fun state => {state with expressions := (key, output) :: state.expressions}
    pure output
  | .fromCoordinates curve => do
    let key : ExpressionKey := ("from_coordinates:" ++ curve.name, [left, right], none)
    let output ← match (← get).expressions.lookup key with
      | some existing => pure existing
      | none => do
        let output ← fresh
        emit "from_coordinates" [("inputs", toJson [left, right]), ("output", toJson output)]
        modify fun state => {state with expressions := (key, output) :: state.expressions}
        pure output
    let (x, y) ← lowerPointCoordinates output
    assertEqual left x
    assertEqual right y
    pure output

private def lowerTypedBoolConstant (value : Bool) : LowerM String := do
  let encoded := if value then "0x01" else "0x00"
  let key : ExpressionKey := ("load_constant:Bool", [encoded], none)
  if let some existing := (← get).expressions.lookup key then return existing
  let output ← fresh
  emit "load_constant" [("type", toJson ("Bool" : String)),
    ("encoding", toJson [encoded]), ("output", toJson output)]
  modify fun state => {state with expressions := (key, output) :: state.expressions}
  pure output

private def selectOperands (bit yes no : String) : LowerM String := do
  let key : ExpressionKey := ("cond_select", [bit, yes, no], none)
  if let some existing := (← get).expressions.lookup key then return existing
  let output ← fresh
  emit "cond_select" [("bit", toJson bit), ("a", toJson yes),
    ("b", toJson no), ("output", toJson output)]
  modify fun state => {state with expressions := (key, output) :: state.expressions}
  return output

private def lowerNativeToBool (value : String) : LowerM String := do
  let key : ExpressionKey := ("native_to_bool", [value], none)
  if let some existing := (← get).expressions.lookup key then return existing
  let yes ← lowerTypedBoolConstant true
  let no ← lowerTypedBoolConstant false
  let output ← fresh
  emit "cond_select" [("bit", toJson value), ("a", toJson yes),
    ("b", toJson no), ("output", toJson output)]
  modify fun state => {state with expressions := (key, output) :: state.expressions}
  pure output

private def lowerBoolGate (opcode left right : String) : LowerM String := do
  let left ← lowerNativeToBool left
  let right ← lowerNativeToBool right
  let key : ExpressionKey := ("typed_bool:" ++ opcode, [left, right], none)
  if let some existing := (← get).expressions.lookup key then return existing
  let result ← fresh
  emit opcode [("inputs", toJson [left, right]), ("output", toJson result)]
  let output ← fresh
  emit "encode" [("input", toJson result), ("outputs", toJson [output])]
  modify fun state => {state with expressions := (key, output) :: state.expressions}
  pure output

private def packBytes : List String → LowerM String
  | [] => pure "0x00"
  | [byte] => pure byte
  | byte :: rest => do
    let suffix ← packBytes rest
    let scaled ← binary "mul" "0x0001" suffix
    binary "add" byte scaled

private def bytes32Alignment : Json := Json.arr #[Json.mkObj [
  ("tag", toJson ("atom" : String)),
  ("value", Json.mkObj [("tag", toJson ("bytes" : String)), ("length", toJson (32 : Nat))])]]

private def bytes32Atom : Json := Json.mkObj [
  ("tag", toJson ("atom" : String)),
  ("value", Json.mkObj [("tag", toJson ("bytes" : String)), ("length", toJson (32 : Nat))])]

private def bytes32VectorAlignment (length : Nat) : Json :=
  Json.arr ((List.replicate length bytes32Atom).toArray)

private def nativeFieldAtom : Json := Json.mkObj [
  ("tag", toJson ("atom" : String)),
  ("value", Json.mkObj [("tag", toJson ("field" : String))])]

private def bytesAlignmentAtom (length : Nat) : Json := Json.mkObj [
  ("tag", toJson ("atom" : String)),
  ("value", Json.mkObj [("tag", toJson ("bytes" : String)), ("length", toJson length)])]

private def fabHashAlignmentAtoms (layout : Types.Layout) : List Json :=
  match Noctium.fabHashLayoutAtoms layout with
  | .ok descriptors => descriptors.map fun descriptor =>
      if descriptor == "field" then nativeFieldAtom
      else match (descriptor.drop 6).toNat? with
        | some width => bytesAlignmentAtom width
        | none => Json.null
  | .error _ => []

private def nativeFieldAlignment : Json := Json.arr #[nativeFieldAtom]

private def nativeFieldVectorAlignment (length : Nat) : Json :=
  Json.arr ((List.replicate length nativeFieldAtom).toArray)

private theorem nativeOutputDefinitionsInInstruction_single
    {value : Json} {opcode : String}
    (opcodeOk : Native.stringField value "op" = .ok opcode)
    (outputOk : (Native.stringField value "output").isOk = true)
    (ordinary : opcode ≠ "encode" ∧ opcode ≠ "bytes_into_natives" ∧
      opcode ≠ "into_coordinates") :
    Native.outputDefinitionsInInstruction value = 1 := by
  unfold Native.outputDefinitionsInInstruction
  rw [opcodeOk]
  simp [ordinary, outputOk]

private theorem instruction_scalarOutputDefinitions
    (opcode : String) (fields : List (String × Json))
    (opcodeOk : Native.stringField (instruction opcode fields) "op" = .ok opcode)
    (ordinary : opcode ≠ "encode" ∧ opcode ≠ "bytes_into_natives" ∧
      opcode ≠ "into_coordinates")
    (outputOk : (Native.stringField (instruction opcode fields) "output").isOk = true) :
    Native.outputDefinitionsInInstruction (instruction opcode fields) = 1 := by
  exact nativeOutputDefinitionsInInstruction_single opcodeOk outputOk ordinary

private theorem addInstruction_outputDefinitions (left right output : String) :
    Native.outputDefinitionsInInstruction
      (instruction "add" [("a", toJson left), ("b", toJson right),
        ("output", toJson output)]) = 1 := by
  let fields := [("a", toJson left), ("b", toJson right),
    ("output", toJson output)]
  have opcodeOk : Native.stringField (instruction "add" fields) "op" = .ok "add" := by
    simp [fields, Native.stringField, instruction, Json.getObjVal?, Json.mkObj, Json.getStr?,
      Std.TreeMap.Raw.get?_eq_getElem?, Std.TreeMap.Raw.getElem?_ofList_of_mem,
      Lean.ToJson.toJson]
    rfl
  have outputOk : (Native.stringField (instruction "add" fields) "output").isOk = true := by
    simp [fields, Native.stringField, instruction, Json.getObjVal?, Json.mkObj, Json.getStr?,
      Std.TreeMap.Raw.get?_eq_getElem?, Lean.ToJson.toJson]
    rfl
  simpa [fields] using instruction_scalarOutputDefinitions "add" fields opcodeOk
    ⟨by decide, by decide, by decide⟩ outputOk

private theorem binaryAdd_preservesOutputCapacityFrame (left right : String) :
    PreservesOutputCapacityFrame (binary "add" left right) := by
  intro state
  cases hit : state.expressions.lookup ("add", [left, right], none) with
  | some existing =>
    simp [binary, hit, StateT.run_bind, StateT.run_get, StateT.run_pure]
    exact OutputCapacityFrame.refl state
  | none =>
    simp [binary, hit, fresh, emit, StateT.run_bind, StateT.run_get, StateT.run_modify,
      StateT.run_set, instruction, toJson]
    let output := "%v" ++ state.next.repr
    let fields := [("a", toJson left), ("b", toJson right), ("output", toJson output)]
    let emitted := instruction "add" fields
    let afterNext := {state with next := state.next + 1}
    let afterInstructions := {afterNext with instructions := afterNext.instructions.push emitted}
    let after := {afterInstructions with
      expressions := (("add", [left, right], none), output) :: afterInstructions.expressions}
    change OutputCapacityFrame state after
    have emittedCount : Native.outputDefinitionsInInstruction emitted = 1 := by
      simpa [emitted, fields, output, toJson, List.toJson, Array.toJson] using
        addInstruction_outputDefinitions left right output
    apply OutputCapacityFrame.of_instruction_push emitted
    · change state.next ≤ state.next + 1
      omega
    · rfl
    · rw [emittedCount]
      change state.next + 1 - state.next ≤ 1
      omega

theorem nativeAdd_preservesOutputCapacityFrame (leftIsZero rightIsZero : Bool)
    (left right : String) :
    PreservesOutputCapacityFrame (nativeAdd leftIsZero rightIsZero left right) := by
  cases leftIsZero <;> cases rightIsZero <;>
    simp [nativeAdd, pure_preservesOutputCapacityFrame,
      binaryAdd_preservesOutputCapacityFrame]

private theorem bytesIntoNativesInstruction_outputDefinitions
    (bytes : String) (outputs : List String) :
    Native.outputDefinitionsInInstruction
      (instruction "bytes_into_natives"
        [("bytes", toJson bytes), ("outputs", toJson outputs)]) = outputs.length := by
  have opcodeOk : Native.stringField
      (instruction "bytes_into_natives"
        [("bytes", toJson bytes), ("outputs", toJson outputs)]) "op" =
      .ok "bytes_into_natives" := by
    simp [Native.stringField, instruction, Json.getObjVal?, Json.mkObj, Json.getStr?,
      Std.TreeMap.Raw.get?_eq_getElem?, Std.TreeMap.Raw.getElem?_ofList_of_mem,
      Lean.ToJson.toJson]
    rfl
  have outputsOk : Native.arrayField
      (instruction "bytes_into_natives"
        [("bytes", toJson bytes), ("outputs", toJson outputs)]) "outputs" =
      .ok ((outputs.map Json.str).toArray) := by
    simp [Native.arrayField, instruction, Json.getObjVal?, Json.mkObj, Json.getArr?,
      Std.TreeMap.Raw.get?_eq_getElem?, Std.TreeMap.Raw.getElem?_ofList_of_mem,
      Lean.ToJson.toJson, Lean.List.toJson, Lean.Array.toJson]
    rfl
  simp [Native.outputDefinitionsInInstruction, opcodeOk, outputsOk, Except.toOption]

private theorem freshLessThan_preservesOutputCapacityFrame (a b : String) (bits : Nat) :
    PreservesOutputCapacityFrame (do
      let output ← fresh
      emit "less_than" [("a", toJson a), ("b", toJson b), ("bits", toJson bits),
        ("output", toJson output)]
      pure output) := by
  intro state
  simp [fresh, emit, StateT.run_bind, StateT.run_get, StateT.run_modify,
    StateT.run_set, instruction, toJson, List.toJson, Array.toJson]
  let output := "%v" ++ state.next.repr
  let fields := [("a", toJson a), ("b", toJson b), ("bits", toJson bits),
    ("output", toJson output)]
  let emitted := instruction "less_than"
    [("a", toJson a), ("b", toJson b), ("bits", toJson bits), ("output", toJson output)]
  change OutputCapacityFrame state
    {state with next := state.next + 1, instructions := state.instructions.push emitted}
  have opcodeOk : Native.stringField (instruction "less_than" fields) "op" =
      .ok "less_than" := by
    simp [fields, Native.stringField, instruction, Json.getObjVal?, Json.mkObj, Json.getStr?,
      Std.TreeMap.Raw.get?_eq_getElem?, Std.TreeMap.Raw.getElem?_ofList_of_mem,
      Lean.ToJson.toJson]
    rfl
  have outputOk :
      (Native.stringField (instruction "less_than" fields) "output").isOk = true := by
    simp [fields, Native.stringField, instruction, Json.getObjVal?, Json.mkObj, Json.getStr?,
      Std.TreeMap.Raw.get?_eq_getElem?, Lean.ToJson.toJson]
    rfl
  have outputCount := instruction_scalarOutputDefinitions "less_than" fields opcodeOk
    ⟨by decide, by decide, by decide⟩ outputOk
  have emittedCount : Native.outputDefinitionsInInstruction emitted = 1 := by
    simpa [emitted, fields, output, toJson, List.toJson, Array.toJson] using outputCount
  apply OutputCapacityFrame.of_instruction_push emitted
  · change state.next ≤ state.next + 1
    omega
  · rfl
  · rw [emittedCount]
    change state.next + 1 - state.next ≤ 1
    omega

private theorem constrainUnsigned_preservesOutputCapacityFrame (maximum : Nat)
    (value : String) : PreservesOutputCapacityFrame (constrainUnsigned maximum value) := by
  intro state
  by_cases isZero : maximum = 0
  · simpa [constrainUnsigned, isZero] using
      (emit_preservesOutputCapacityFrame "constrain_eq"
        [("a", toJson value), ("b", toJson ("0x00" : String))] state)
  · by_cases exactPower : maximum + 1 = 2 ^ (maximum.log2 + 1)
    · simpa [constrainUnsigned, isZero, exactPower] using
        (emit_preservesOutputCapacityFrame "constrain_bits"
          [("val", toJson value), ("bits", toJson (maximum.log2 + 1))] state)
    · have suffixFrame : PreservesOutputCapacityFrame (do
          let output ← fresh
          emit "less_than" [("a", toJson value),
            ("b", toJson (fieldImmediate (maximum + 1))),
            ("bits", toJson (maximum.log2 + 1)), ("output", toJson output)]
          emit "assert" [("cond", toJson output)]) := by
        have combined := bind_preservesOutputCapacityFrame _ _
          (freshLessThan_preservesOutputCapacityFrame value
            (fieldImmediate (maximum + 1)) (maximum.log2 + 1))
          (fun output => emit_preservesOutputCapacityFrame "assert" [("cond", toJson output)])
        simpa [StateT.run_bind, StateT.run_pure] using combined
      have bodyFrame : PreservesOutputCapacityFrame (do
          emit "constrain_bits" [("val", toJson value), ("bits", toJson (maximum.log2 + 1))]
          let output ← fresh
          emit "less_than" [("a", toJson value),
            ("b", toJson (fieldImmediate (maximum + 1))),
            ("bits", toJson (maximum.log2 + 1)), ("output", toJson output)]
          emit "assert" [("cond", toJson output)]) := by
        apply bind_preservesOutputCapacityFrame _ _
          (emit_preservesOutputCapacityFrame "constrain_bits"
            [("val", toJson value), ("bits", toJson (maximum.log2 + 1))])
        intro _
        exact suffixFrame
      simpa [constrainUnsigned, isZero, exactPower] using bodyFrame state

theorem nativeUIntAdd_preservesOutputCapacityFrame (maximum : Nat)
    (leftIsZero rightIsZero : Bool) (left right : String) :
    PreservesOutputCapacityFrame (nativeUIntAdd maximum leftIsZero rightIsZero left right) := by
  apply bind_preservesOutputCapacityFrame _ _
    (nativeAdd_preservesOutputCapacityFrame leftIsZero rightIsZero left right)
  intro output
  apply bind_preservesOutputCapacityFrame _ _
    (constrainUnsigned_preservesOutputCapacityFrame maximum output)
  intro _
  exact pure_preservesOutputCapacityFrame output

private theorem constrainType_preservesOutputCapacityFrame (ty : Ty) (value : String) :
    PreservesOutputCapacityFrame (constrainType ty value) := by
  cases ty with
  | native => exact pure_preservesOutputCapacityFrame ()
  | bool => exact emit_preservesOutputCapacityFrame "constrain_to_boolean" [("val", toJson value)]
  | uint maximum => exact constrainUnsigned_preservesOutputCapacityFrame maximum value
  | bytes _ =>
    simpa [constrainType, rejectLowering] using
      emit_preservesOutputCapacityFrame "noctium_invalid_lowering"
        [("message", toJson "Bytes32 must be expanded into byte inputs")]
  | opaqueBytes => exact pure_preservesOutputCapacityFrame ()
  | opaqueString => exact pure_preservesOutputCapacityFrame ()
  | jubjubScalar =>
    simpa [constrainType, rejectLowering] using
      emit_preservesOutputCapacityFrame "noctium_invalid_lowering"
        [("message", toJson "opaque values require their typed input bridge")]
  | jubjubPoint =>
    simpa [constrainType, rejectLowering] using
      emit_preservesOutputCapacityFrame "noctium_invalid_lowering"
        [("message", toJson "opaque values require their typed input bridge")]
  | foreign _ =>
    simpa [constrainType, rejectLowering] using
      emit_preservesOutputCapacityFrame "noctium_invalid_lowering"
        [("message", toJson "opaque values require their typed input bridge")]

private theorem lowerInputRequirement_preservesOutputCapacityFrame (op : String)
    (raw : Bool) (spec : Native.InputRequirement) :
    PreservesOutputCapacityFrame (lowerInputRequirement op raw spec) := by
  by_cases isRaw : raw
  · simpa [lowerInputRequirement, isRaw] using
      (constrainType_preservesOutputCapacityFrame spec.ty spec.identifier)
  · have bodyFrame : PreservesOutputCapacityFrame (do
        emit op [("guard", Json.null), ("type", nativeType),
          ("output", toJson spec.identifier)]
        constrainType spec.ty spec.identifier) := by
      apply bind_preservesOutputCapacityFrame _ _
        (emit_preservesOutputCapacityFrame op
          [("guard", Json.null), ("type", nativeType), ("output", toJson spec.identifier)])
      intro _
      exact constrainType_preservesOutputCapacityFrame spec.ty spec.identifier
    simpa [lowerInputRequirement, isRaw] using bodyFrame

private theorem lowerInputRequirements_preservesOutputCapacityFrame (op : String)
    (raw : Bool) (requirements : List Native.InputRequirement) :
    PreservesOutputCapacityFrame (lowerInputRequirements op raw requirements) := by
  induction requirements with
  | nil => exact pure_preservesOutputCapacityFrame ()
  | cons spec rest ih =>
    apply bind_preservesOutputCapacityFrame _ _
      (lowerInputRequirement_preservesOutputCapacityFrame op raw spec)
    intro _
    exact ih

/-- Emit the two Native limbs of one Bytes32 value. The native validator reads
both names from this instruction's `outputs` vector. -/
private def encodeBytes32Fresh (bytes : String) : LowerM (String × String) := do
  let lowKey : ExpressionKey := ("encode_bytes32", [bytes], some 0)
  let highKey : ExpressionKey := ("encode_bytes32", [bytes], some 1)
  let low ← fresh
  let high ← fresh
  emit "bytes_into_natives" [("bytes", toJson bytes), ("outputs", toJson [low, high])]
  modify fun state => {state with expressions :=
    (lowKey, low) :: (highKey, high) :: state.expressions}
  pure (low, high)

private theorem encodeBytes32Fresh_preservesOutputCapacityFrame (bytes : String) :
    PreservesOutputCapacityFrame (encodeBytes32Fresh bytes) := by
  intro state
  simp [encodeBytes32Fresh, fresh, emit, StateT.run_bind, StateT.run_get,
    StateT.run_modify, StateT.run_set, toJson, List.toJson, Array.toJson]
  let low := "%v" ++ state.next.repr
  let high := "%v" ++ (state.next + 1).repr
  let emitted := instruction "bytes_into_natives"
    [("bytes", Json.str bytes), ("outputs", Json.arr #[Json.str low, Json.str high])]
  change OutputCapacityFrame state
    {state with
      next := state.next + 1 + 1
      instructions := state.instructions.push emitted
      expressions := (("encode_bytes32", [bytes], some 0), low) ::
        (("encode_bytes32", [bytes], some 1), high) :: state.expressions}
  have emittedCount : Native.outputDefinitionsInInstruction emitted = 2 := by
    have count := bytesIntoNativesInstruction_outputDefinitions bytes [low, high]
    simpa [emitted, low, high, toJson, List.toJson, Array.toJson] using count
  apply OutputCapacityFrame.of_instruction_push emitted
  · change state.next ≤ state.next + 2
    omega
  · rfl
  · rw [emittedCount]
    change state.next + 1 + 1 - state.next ≤ 2
    omega

/-- Emit the one native SHA-256 result before encoding its Bytes32 chunks. -/
private def lowerPersistentHashFresh (alignment : Json) (operands : List String)
    (hashKey : ExpressionKey) : LowerM String := do
  let output ← fresh
  emit "persistent_hash" [
    ("alignment", alignment),
    ("inputs", toJson operands),
    ("output", toJson output)]
  modify fun state => {state with expressions := (hashKey, output) :: state.expressions}
  pure output

private theorem lowerPersistentHashFresh_preservesOutputCapacityFrame
    (alignment : Json) (operands : List String) (hashKey : ExpressionKey) :
    PreservesOutputCapacityFrame (lowerPersistentHashFresh alignment operands hashKey) := by
  intro state
  simp [lowerPersistentHashFresh, fresh, emit, StateT.run_bind, StateT.run_get,
    StateT.run_modify, StateT.run_set, toJson, List.toJson, Array.toJson]
  let output := "%v" ++ state.next.repr
  let fields := [
    ("alignment", alignment),
    ("inputs", toJson operands),
    ("output", toJson output)]
  let emitted := instruction "persistent_hash"
    [("alignment", alignment), ("inputs", Json.arr (operands.map Json.str).toArray),
      ("output", Json.str output)]
  change OutputCapacityFrame state
    {state with
      next := state.next + 1
      instructions := state.instructions.push emitted
      expressions := (hashKey, output) :: state.expressions}
  have opcodeOk : Native.stringField (instruction "persistent_hash" fields) "op" =
      .ok "persistent_hash" := by
    simp [fields, Native.stringField, instruction, Json.getObjVal?, Json.mkObj, Json.getStr?,
      Std.TreeMap.Raw.get?_eq_getElem?, Std.TreeMap.Raw.getElem?_ofList_of_mem,
      Lean.ToJson.toJson]
    rfl
  have outputOk : (Native.stringField (instruction "persistent_hash" fields) "output").isOk =
      true := by
    simp [fields, Native.stringField, instruction, Json.getObjVal?, Json.mkObj, Json.getStr?,
      Std.TreeMap.Raw.get?_eq_getElem?, Lean.ToJson.toJson]
    rfl
  have outputCount := instruction_scalarOutputDefinitions "persistent_hash" fields
    opcodeOk ⟨by decide, by decide, by decide⟩ outputOk
  have emittedCount : Native.outputDefinitionsInInstruction emitted = 1 := by
    simpa [emitted, fields, output, toJson, List.toJson, Array.toJson] using outputCount
  apply OutputCapacityFrame.of_instruction_push emitted
  · change state.next ≤ state.next + 1
    omega
  · rfl
  · rw [emittedCount]
    change state.next + 1 - state.next ≤ 1
    omega

private def encodeBytes32 (bytes : String) : LowerM (String × String) := do
  let lowKey : ExpressionKey := ("encode_bytes32", [bytes], some 0)
  let highKey : ExpressionKey := ("encode_bytes32", [bytes], some 1)
  match ((← get).expressions.lookup lowKey, (← get).expressions.lookup highKey) with
  | (some low, some high) => pure (low, high)
  | _ => encodeBytes32Fresh bytes

private theorem encodeBytes32_preservesOutputCapacityFrame (bytes : String) :
    PreservesOutputCapacityFrame (encodeBytes32 bytes) := by
  intro state
  let lowKey : ExpressionKey := ("encode_bytes32", [bytes], some 0)
  let highKey : ExpressionKey := ("encode_bytes32", [bytes], some 1)
  cases lowHit : state.expressions.lookup lowKey with
  | some low =>
    cases highHit : state.expressions.lookup highKey with
    | some high =>
      simp [encodeBytes32, lowKey, highKey, lowHit, highHit,
        StateT.run_bind, StateT.run_get, StateT.run_pure]
      exact OutputCapacityFrame.refl state
    | none =>
      simpa [encodeBytes32, lowKey, highKey, lowHit, highHit] using
        (encodeBytes32Fresh_preservesOutputCapacityFrame bytes state)
  | none =>
    cases highHit : state.expressions.lookup highKey with
    | some _ =>
      simpa [encodeBytes32, lowKey, highKey, lowHit, highHit] using
        (encodeBytes32Fresh_preservesOutputCapacityFrame bytes state)
    | none =>
      simpa [encodeBytes32, lowKey, highKey, lowHit, highHit] using
        (encodeBytes32Fresh_preservesOutputCapacityFrame bytes state)

/-- Emit/reuse one typed aligned SHA-256 operation and its typed byte-packing outputs.
The key includes the preimage kind, so identical field strings under different
FAB alignments never share a digest. The returned chunks use Encode order. -/
private def lowerPersistentHash (preimageKind : String) (alignment : Json)
    (operands : List String) : LowerM (List String) := do
  let hashKey : ExpressionKey := ("persistent_hash:" ++ preimageKind, operands, none)
  let hashOutput ← match (← get).expressions.lookup hashKey with
    | some existing => pure existing
    | none => lowerPersistentHashFresh alignment operands hashKey
  let chunks ← encodeBytes32 hashOutput
  pure [chunks.1, chunks.2]

private theorem lowerPersistentHash_preservesOutputCapacityFrame (preimageKind : String)
    (alignment : Json) (operands : List String) :
    PreservesOutputCapacityFrame (lowerPersistentHash preimageKind alignment operands) := by
  intro state
  let hashKey : ExpressionKey := ("persistent_hash:" ++ preimageKind, operands, none)
  cases hashHit : state.expressions.lookup hashKey with
  | some hashOutput =>
    have tailFrame : PreservesOutputCapacityFrame (do
      let chunks ← encodeBytes32 hashOutput
      pure [chunks.1, chunks.2]) := by
      apply bind_preservesOutputCapacityFrame _ _
        (encodeBytes32_preservesOutputCapacityFrame hashOutput)
      intro chunks
      exact pure_preservesOutputCapacityFrame [chunks.1, chunks.2]
    simpa [lowerPersistentHash, hashKey, hashHit, StateT.run_bind,
      StateT.run_get, StateT.run_pure] using tailFrame state
  | none =>
    have tailFrame : PreservesOutputCapacityFrame (do
      let hashOutput ← lowerPersistentHashFresh alignment operands hashKey
      let chunks ← encodeBytes32 hashOutput
      pure [chunks.1, chunks.2]) := by
      apply bind_preservesOutputCapacityFrame _ _
        (lowerPersistentHashFresh_preservesOutputCapacityFrame alignment operands hashKey)
      intro hashOutput
      apply bind_preservesOutputCapacityFrame _ _
        (encodeBytes32_preservesOutputCapacityFrame hashOutput)
      intro chunks
      exact pure_preservesOutputCapacityFrame [chunks.1, chunks.2]
    simpa [lowerPersistentHash, hashKey, hashHit, StateT.run_bind,
      StateT.run_get, StateT.run_pure] using tailFrame state

private def encodeByte (byte : String) : LowerM String := do
  let key : ExpressionKey := ("encode_byte", [byte], none)
  if let some existing := (← get).expressions.lookup key then return existing
  let output ← fresh
  emit "encode" [("input", toJson byte), ("outputs", toJson [output])]
  modify fun state => {state with expressions := (key, output) :: state.expressions}
  pure output

private def lowerToBytes32 (value : String) : LowerM (String × String) := do
  let bytesKey : ExpressionKey := ("to_bytes", [value], none)
  let bytes ← match (← get).expressions.lookup bytesKey with
    | some existing => pure existing
    | none => do
      let output ← fresh
      emit "to_bytes" [("input", toJson value), ("output", toJson output)]
      modify fun state => {state with expressions := (bytesKey, output) :: state.expressions}
      pure output
  encodeBytes32 bytes

private def bytes32Chunks (values : List String) : LowerM (String × String) := do
  match values.length with
  | 2 => pure (values[0]!, values[1]!)
  | 32 => pure (← packBytes (values.take 31), values[31]!)
  | _ => do
    rejectLowering "Bytes32 source has wrong aligned encoding"
    pure ("0x00", "0x00")

private def lowerBytesFromChunks (low31 highByte : String) : LowerM String := do
  let key : ExpressionKey := ("bytes_from_natives", [low31, highByte], some 32)
  if let some existing := (← get).expressions.lookup key then return existing
  let output ← fresh
  emit "bytes_from_natives" [
    ("inputs", toJson [low31, highByte]),
    ("len", toJson (32 : Nat)),
    ("output", toJson output)]
  modify fun state => {state with expressions := (key, output) :: state.expressions}
  pure output

private def lowerComputedBytes32ByteAt (values : List String) (index : Nat) : LowerM String := do
  if index ≥ 32 then do
    rejectLowering "Bytes32 byte index is out of range"
    pure "0x00"
  else do
    let (low31, highByte) ← bytes32Chunks values
    let bytes ← lowerBytesFromChunks low31 highByte
    let key : ExpressionKey := ("nth", [bytes], some index)
    let byte ← match (← get).expressions.lookup key with
      | some existing => pure existing
      | none => do
        let output ← fresh
        emit "nth" [("bytes", toJson bytes), ("index", toJson index), ("output", toJson output)]
        modify fun state => {state with expressions := (key, output) :: state.expressions}
        pure output
    encodeByte byte

private def byteChunks (length : Nat) (bytes : ByteOperands) : LowerM (List String) := do
  if bytes.packed then
    if bytes.values.length != Noctium.bytesChunkCount length then
      rejectLowering "byte chunk count mismatch"
    pure bytes.values
  else if bytes.values.length != length then
    rejectLowering "byte leaf count mismatch"
    pure []
  else
    (List.range (Noctium.bytesChunkCount length)).mapM fun index =>
      packBytes ((bytes.values.drop (index * 31)).take 31)

private def lowerFixedBytesFromChunks (length : Nat) (chunks : List String) : LowerM String := do
  if length == 0 then
    rejectLowering "native Bytes0 values are not supported"
    return "0x00"
  let key : ExpressionKey := ("bytes_from_natives", chunks, some length)
  if let some existing := (← get).expressions.lookup key then return existing
  let output ← fresh
  emit "bytes_from_natives" [("inputs", toJson chunks), ("len", toJson length), ("output", toJson output)]
  modify fun state => {state with expressions := (key, output) :: state.expressions}
  pure output

private def encodeFixedBytes (length : Nat) (bytes : String) : LowerM ByteOperands := do
  if length == 32 then
    let (low, high) ← encodeBytes32 bytes
    return {values := [low, high], packed := true}
  let keys := (List.range (Noctium.bytesChunkCount length)).map fun index =>
    (("encode_bytes:" ++ toString length, [bytes], some index) : ExpressionKey)
  -- Lookups are collected before mutation so partial cache hits never reorder outputs.
  let expressions := (← get).expressions
  let cached := keys.map (fun key => expressions.lookup key)
  if cached.all Option.isSome then
    return {values := cached.filterMap id, packed := true}
  let outputs ← keys.mapM fun _ => fresh
  emit "bytes_into_natives" [("bytes", toJson bytes), ("outputs", toJson outputs)]
  modify fun state => {state with expressions := keys.zip outputs ++ state.expressions}
  pure {values := outputs, packed := true}

private def lowerAlignedDigest (algorithm : String) (outputLength : Nat)
    (alignment : Json) (operands : List String) (key : ExpressionKey) : LowerM ByteOperands := do
  let output ← match (← get).expressions.lookup key with
    | some existing => pure existing
    | none => do
      let output ← fresh
      emit algorithm [("alignment", alignment), ("inputs", toJson operands), ("output", toJson output)]
      modify fun state => {state with expressions := (key, output) :: state.expressions}
      pure output
  encodeFixedBytes outputLength output

/-- Hash one fixed byte preimage. FAB consumes chunks in the reverse of Encode
order. Empty preimages use empty alignment and no operands, never Bytes0. -/
private def lowerFixedByteHash (algorithm : String) (length outputLength : Nat)
    (value : ByteOperands) : LowerM ByteOperands := do
  let operands := (← byteChunks length value).reverse
  let alignment := if length == 0 then Json.arr #[] else Json.arr #[Json.mkObj [
    ("tag", toJson ("atom" : String)),
    ("value", Json.mkObj [("tag", toJson ("bytes" : String)), ("length", toJson length)])]]
  lowerAlignedDigest algorithm outputLength alignment operands (algorithm, operands, some length)

private def lowerForeignToBytes (kind : Foreign.Kind) (value : String) : LowerM ByteOperands := do
  let key : ExpressionKey := ("foreign_to_bytes:" ++ kind.nativeName, [value], none)
  let output ← match (← get).expressions.lookup key with
    | some existing => pure existing
    | none => do
      let output ← fresh
      emit "to_bytes" [("input", toJson value), ("output", toJson output)]
      modify fun state => {state with expressions := (key, output) :: state.expressions}
      pure output
  encodeFixedBytes kind.byteLength output

private def lowerForeignFromBytes (kind : Foreign.Kind) (length : Nat) (value : ByteOperands) : LowerM String := do
  if let .point _ := kind then
    unless length == kind.byteLength do
      rejectLowering "foreign point decoding requires the curve's exact byte length"
  let chunks ← byteChunks length value
  if length == 0 then return ← lowerForeignConstant kind (Foreign.encodeField kind 0)
  let bytes ← lowerFixedBytesFromChunks length chunks
  let key : ExpressionKey := ("foreign_from_bytes:" ++ kind.nativeName, [bytes], some length)
  let output ← match (← get).expressions.lookup key with
    | some existing => pure existing
    | none => do
      let output ← fresh
      emit "from_bytes" [("bytes", toJson bytes), ("type", toJson kind.nativeName), ("output", toJson output)]
      modify fun state => {state with expressions := (key, output) :: state.expressions}
      pure output
  if let .point _ := kind then
    let roundtrip ← lowerForeignToBytes kind output
    for (original, encoded) in chunks.zip roundtrip.values do assertEqual original encoded
  pure output

private def lowerFixedReverse (length : Nat) (value : ByteOperands) : LowerM ByteOperands := do
  if length == 0 then return {values := []}
  let input ← lowerFixedBytesFromChunks length (← byteChunks length value)
  let key : ExpressionKey := ("reverse", [input], none)
  let output ← match (← get).expressions.lookup key with
    | some existing => pure existing
    | none => do
      let output ← fresh
      emit "reverse" [("bytes", toJson input), ("output", toJson output)]
      modify fun state => {state with expressions := (key, output) :: state.expressions}
      pure output
  encodeFixedBytes length output

private def lowerFixedSlice (length start end_ : Nat) (value : ByteOperands) : LowerM ByteOperands := do
  if !(start ≤ end_ && end_ ≤ length) then
    rejectLowering "byte slice is out of range"
    return {values := []}
  if start == end_ then return {values := []}
  if !value.packed then
    if value.values.length != length then
      rejectLowering "byte leaf count mismatch"
    return {values := (value.values.drop start).take (end_ - start)}
  let input ← lowerFixedBytesFromChunks length (← byteChunks length value)
  let key : ExpressionKey := ("slice:" ++ toString start, [input], some (end_ - start))
  let output ← match (← get).expressions.lookup key with
    | some existing => pure existing
    | none => do
      let output ← fresh
      emit "slice" [("bytes", toJson input), ("start", toJson start),
        ("len", toJson (end_ - start)), ("output", toJson output)]
      modify fun state => {state with expressions := (key, output) :: state.expressions}
      pure output
  encodeFixedBytes (end_ - start) output

private def lowerFixedConcat (leftLength rightLength : Nat)
    (left right : ByteOperands) : LowerM ByteOperands := do
  if leftLength == 0 then return right
  if rightLength == 0 then return left
  if !left.packed && !right.packed then
    if left.values.length != leftLength || right.values.length != rightLength then
      rejectLowering "byte leaf count mismatch"
    return {values := left.values ++ right.values}
  -- An aligned prefix ends between complete Encode chunks.
  if leftLength % 31 == 0 then
    let leftChunks ← byteChunks leftLength left
    let rightChunks ← byteChunks rightLength right
    return {values := leftChunks ++ rightChunks, packed := true}
  let left ← lowerFixedBytesFromChunks leftLength (← byteChunks leftLength left)
  let right ← lowerFixedBytesFromChunks rightLength (← byteChunks rightLength right)
  let key : ExpressionKey := ("concat", [left, right], none)
  let output ← match (← get).expressions.lookup key with
    | some existing => pure existing
    | none => do
      let output ← fresh
      emit "concat" [("inputs", toJson [left, right]), ("output", toJson output)]
      modify fun state => {state with expressions := (key, output) :: state.expressions}
      pure output
  encodeFixedBytes (leftLength + rightLength) output

private def lowerFixedByteAt (length index : Nat) (value : ByteOperands) : LowerM String := do
  if index ≥ length then
    rejectLowering "byte index is out of range"
    return "0x00"
  if !value.packed then
    if value.values.length != length then
      rejectLowering "byte leaf count mismatch"
      return "0x00"
    return value.values[index]!
  let input ← lowerFixedBytesFromChunks length (← byteChunks length value)
  let key : ExpressionKey := ("nth", [input], some index)
  let byte ← match (← get).expressions.lookup key with
    | some existing => pure existing
    | none => do
      let output ← fresh
      emit "nth" [("bytes", toJson input), ("index", toJson index), ("output", toJson output)]
      modify fun state => {state with expressions := (key, output) :: state.expressions}
      pure output
  encodeByte byte

private def nativeTypeName : Ty → String
  | .native => "Scalar<BLS12-381>"
  | .jubjubScalar => "Scalar<Jubjub>"
  | .jubjubPoint => "Point<Jubjub>"
  | .foreign kind => kind.nativeName
  | _ => "Unsupported"

private def lowerFromBytes32 (target : Ty) (values : List String) : LowerM String := do
  let (low31, highByte) ← bytes32Chunks values
  let bytes ← lowerBytesFromChunks low31 highByte
  let typeName := nativeTypeName target
  let key : ExpressionKey := ("from_bytes:" ++ typeName, [bytes], none)
  let output ← match (← get).expressions.lookup key with
    | some existing => pure existing
    | none => do
      let output ← fresh
      emit "from_bytes" [
        ("bytes", toJson bytes),
        ("type", toJson typeName),
        ("output", toJson output)]
      modify fun state => {state with expressions := (key, output) :: state.expressions}
      pure output
  if target == .jubjubPoint then do
    let (roundtripLow, roundtripHigh) ← lowerToBytes32 output
    let highEq ← binary "test_eq" highByte roundtripHigh
    emit "assert" [("cond", toJson highEq)]
    let lowEq ← binary "test_eq" low31 roundtripLow
    emit "assert" [("cond", toJson lowEq)]
  pure output

private def lowerFromBytes (target : Ty) (length : Nat) (value : ByteOperands) : LowerM String := do
  let chunks ← byteChunks length value
  if length == 0 then
    match target with
    | .native => pure "0x00"
    | .jubjubScalar => lowerJubjubScalarFromNative "0x00"
    | _ => do
      rejectLowering "fromBytes supports only Native and JubjubScalar"
      pure "0x00"
  else
    match target with
    | .native | .jubjubScalar => do
      let bytes ← lowerFixedBytesFromChunks length chunks
      let typeName := nativeTypeName target
      let key : ExpressionKey := ("from_bytes:" ++ typeName, [bytes], none)
      match (← get).expressions.lookup key with
      | some existing => pure existing
      | none => do
        let output ← fresh
        emit "from_bytes" [
          ("bytes", toJson bytes),
          ("type", toJson typeName),
          ("output", toJson output)]
        modify fun state => {state with expressions := (key, output) :: state.expressions}
        pure output
    | _ => do
      rejectLowering "fromBytes supports only Native and JubjubScalar"
      pure "0x00"

private def alignedBytes32Fields (values : List String) : LowerM (String × String) := do
  match values.length with
  | 32 =>
    let low31 ← packBytes (values.take 31)
    pure (values[31]!, low31)
  | 2 => pure (values[1]!, values[0]!)
  | _ => do
    rejectLowering "Bytes32 source has wrong aligned encoding"
    pure ("0x00", "0x00")

private def alignedBytes32Value (source : Expr (.bytes 32))
    (operands : List String) : LowerM (String × String) :=
  match source with
  | .bytes32Literal bytes =>
    if bytes.length == 32 && bytes.all (· ≤ 255) then
      pure (fieldImmediate bytes[31]!, fieldImmediate (Native.littleEndian (bytes.take 31)))
    else alignedBytes32Fields operands
  | _ => alignedBytes32Fields operands

private def lowerByteInput (input : Input) (raw : Bool := false) : LowerM Unit := do
  let op := if input.visibility == .«public» then "public_input" else "private_input"
  let read (identifier : String) (ty : Json := nativeType) :=
    unless raw do emit op [("guard", Json.null), ("type", ty), ("output", toJson identifier)]
  if raw then
    if let .bytes _ := input.ty then
      let requirements := Native.Input.callArgumentRequirements input
      lowerInputRequirements op true requirements
      modify fun state => {state with byteAliases := (input.name,
        {values := (requirements.map (·.identifier)).reverse, packed := true}) :: state.byteAliases}
      return
  match input.ty with
  | .foreign kind => do
    let output := "%input_" ++ input.name
    read output (toJson kind.nativeName)
    modify fun state => {state with aliases := (input.name, output) :: state.aliases}
  | .opaqueBytes | .opaqueString => do
    let output := "%input_" ++ input.name
    read output
    modify fun state => {state with aliases := (input.name, output) :: state.aliases}
  | .bytes _ => do
    let requirements := Native.Input.requirements input
    lowerInputRequirements op raw requirements
    let values := requirements.map (·.identifier)
    let packed := input.visibility == .«public»
    modify fun state => {state with byteAliases := (input.name,
      {values := if packed then values.reverse else values, packed}) :: state.byteAliases}
  | .jubjubScalar => do
    let native := input.nativeIdentifiers.head!
    read native
    let scalar ← lowerJubjubScalarFromNative native
    let encoded ← lowerJubjubScalarToNative scalar
    emit "constrain_eq" [("a", toJson native), ("b", toJson encoded)]
    modify fun state => {state with aliases := (input.name, scalar) :: state.aliases}
  | .jubjubPoint => do
    let x := input.nativeIdentifiers[0]!
    let y := input.nativeIdentifiers[1]!
    for identifier in [x, y] do
      read identifier
    let point ← lowerPointFromCoordinates x y
    modify fun state => {state with aliases := (input.name, point) :: state.aliases}
  | _ =>
    let output := input.nativeIdentifiers.head!
    read output
    constrainType input.ty output

theorem lowerByteInput_fixedBytes_preservesOutputCapacityFrame (name : String)
    (length : Nat) (visibility : Visibility) (raw : Bool) (span : SourceSpan := {}) :
    PreservesOutputCapacityFrame
      (lowerByteInput {name, ty := .bytes length, visibility, span} raw) := by
  intro state
  let input : Input := {name, ty := .bytes length, visibility, span}
  let op := if visibility == .«public» then "public_input" else "private_input"
  cases raw with
  | false =>
    let requirements := Native.Input.requirements input
    let values := requirements.map (·.identifier)
    let byteOperands : ByteOperands := {
      values := if visibility == .«public» then values.reverse else values,
      packed := visibility == .«public»}
    let update (state : LowerState) :=
      {state with byteAliases := (name, byteOperands) :: state.byteAliases}
    have updateNext : ∀ state, (update state).next = state.next := by
      intro state
      rfl
    have updateInstructions : ∀ state, (update state).instructions = state.instructions := by
      intro state
      rfl
    have updateFrame := modify_preservesOutputCapacityFrame update updateNext updateInstructions
    have combined := bind_preservesOutputCapacityFrame
      (lowerInputRequirements op false requirements) (fun _ => modify update)
      (lowerInputRequirements_preservesOutputCapacityFrame op false requirements)
      (fun _ => updateFrame)
    simpa [lowerByteInput, input, requirements, values, op, update] using combined state
  | true =>
    let requirements := Native.Input.callArgumentRequirements input
    let byteOperands : ByteOperands := {
      values := (requirements.map (·.identifier)).reverse, packed := true}
    let update (state : LowerState) :=
      {state with byteAliases := (name, byteOperands) :: state.byteAliases}
    have updateNext : ∀ state, (update state).next = state.next := by
      intro state
      rfl
    have updateInstructions : ∀ state, (update state).instructions = state.instructions := by
      intro state
      rfl
    have updateFrame := modify_preservesOutputCapacityFrame update updateNext updateInstructions
    have combined := bind_preservesOutputCapacityFrame
      (lowerInputRequirements op true requirements) (fun _ => modify update)
      (lowerInputRequirements_preservesOutputCapacityFrame op true requirements)
      (fun _ => updateFrame)
    simpa [lowerByteInput, input, requirements, op, update] using combined state

private theorem publicBytes32Requirements (name : String) :
    Native.Input.requirements {name, ty := .bytes 32, visibility := .«public»} = [
      {identifier := "%input__noctium_bytes32_" ++ name ++ "_high", visibility := .«public», ty := .uint 255},
      {identifier := "%input__noctium_bytes32_" ++ name ++ "_low31", visibility := .«public»,
        ty := .uint (2 ^ 248 - 1)}] := by
  rfl

/-- A public Bytes32 input's 1-byte and 31-byte range constraints allocate no SSA names. -/
theorem lowerByteInput_publicBytes32_next (name : String) (state : LowerState) :
    (lowerByteInput {name, ty := .bytes 32, visibility := .«public»}).run state |>.2.next =
      state.next := by
  simp [lowerByteInput, publicBytes32Requirements, constrainType, constrainUnsigned, emit]
  rfl

mutual
private def lowerOpaqueBytes : Expr .opaqueBytes → LowerM String
  | .opaqueBytesEmpty => pure "0x00"
  | .ref name => do
    pure ((← get).aliases.lookup name |>.getD ("%input_" ++ name))
  | .disclose _ value => lowerOpaqueBytes value
  | .copyValue value => do
    unary "copy" (← lowerOpaqueBytes value) "val"
  | @Expr.letE .bool .opaqueBytes name value body => do
    let value ← lowerExpr value
    let aliases := (← get).aliases
    modify fun state => {state with aliases := (name, value) :: aliases}
    let result ← lowerOpaqueBytes body
    modify fun state => {state with aliases}
    pure result
  | @Expr.letE .opaqueBytes _ name value body => do
    let value ← lowerOpaqueBytes value
    let aliases := (← get).aliases
    modify fun state => {state with aliases := (name, value) :: aliases}
    let result ← lowerOpaqueBytes body
    modify fun state => {state with aliases}
    pure result
  | .assertE condition body => do
    emit "assert" [("cond", toJson (← lowerExpr condition))]
    lowerOpaqueBytes body
  | _ => do
    rejectLowering "unsupported OpaqueBytes expression in Compress projection"
    pure "0x00"
termination_by value => sizeOf value
decreasing_by
  all_goals simp_wf <;> omega

private def lowerOpaqueString : Expr .opaqueString → LowerM String
  | .opaqueStringEmpty => pure "0x00"
  | .ref name => do
    pure ((← get).aliases.lookup name |>.getD ("%input_" ++ name))
  | .disclose _ value => lowerOpaqueString value
  | .copyValue value => do
    unary "copy" (← lowerOpaqueString value) "val"
  | @Expr.letE .bool .opaqueString name value body => do
    let value ← lowerExpr value
    let aliases := (← get).aliases
    modify fun state => {state with aliases := (name, value) :: aliases}
    let result ← lowerOpaqueString body
    modify fun state => {state with aliases}
    pure result
  | @Expr.letE .opaqueString _ name value body => do
    let value ← lowerOpaqueString value
    let aliases := (← get).aliases
    modify fun state => {state with aliases := (name, value) :: aliases}
    let result ← lowerOpaqueString body
    modify fun state => {state with aliases}
    pure result
  | .assertE condition body => do
    emit "assert" [("cond", toJson (← lowerExpr condition))]
    lowerOpaqueString body
  | _ => do
    rejectLowering "unsupported OpaqueString expression in Compress projection"
    pure "0x00"
termination_by value => sizeOf value
decreasing_by
  all_goals simp_wf <;> omega

private def lowerBytes : Expr (.bytes length) → LowerM ByteOperands
  | .ref name => do
    match (← get).byteAliases.lookup name with
    | some values => pure values
    | none =>
      rejectLowering s!"unbound Bytes32 source symbol '{name}'"
      pure {values := []}
  | .disclose _ value => lowerBytes value
  | .copyValue value => do
    let operand ← lowerBytes value
    pure {operand with values := ← operand.values.mapM (fun value => unary "copy" value "val")}
  | .bytes32Literal values | .bytesLiteral _ values => pure {values := values.map fieldImmediate}
  | .reverseBytes (length := length) value => do
    lowerFixedReverse length (← lowerBytes value)
  | .sliceBytes (length := length) value start end_ => do
    lowerFixedSlice length start end_ (← lowerBytes value)
  | .concatBytes (leftLength := leftLength) (rightLength := rightLength) left right => do
    let left ← lowerBytes left
    let right ← lowerBytes right
    lowerFixedConcat leftLength rightLength left right
  | .sha256 (length := length) value => do
    let values ← lowerBytes value
    if length == 32 then
      let (highByte, low31) ← alignedBytes32Fields values.values
      pure {values := ← lowerPersistentHash "bytes32" bytes32Alignment [highByte, low31], packed := true}
    else
      lowerFixedByteHash "persistent_hash" length 32 values
  | .sha512 (length := length) value => do
    lowerFixedByteHash "sha512" length 64 (← lowerBytes value)
  | .sha512Fab environment type values => do
    match validateFabHashLayout environment type values with
    | .error message =>
      rejectLowering message
      pure {values := []}
    | .ok compiled => do
      let fields ← match fabHashLayoutFields compiled with
        | .ok fields => pure fields
        | .error message =>
          rejectLowering message
          pure []
      let operands ← lowerFabHashFields fields values
      let alignment := Json.arr (fields.flatMap (fun field => fabHashAlignmentAtoms field.2)).toArray
      lowerAlignedDigest "sha512" 64 alignment operands
        ("sha512_fab:" ++ type.fingerprint environment, operands, none)
  | .keccak256Fab environment type values => do
    match validateFabHashLayout environment type values with
    | .error message =>
      rejectLowering message
      pure {values := []}
    | .ok compiled => do
      let fields ← match fabHashLayoutFields compiled with
        | .ok fields => pure fields
        | .error message =>
          rejectLowering message
          pure []
      let operands ← lowerFabHashFields fields values
      let alignment := Json.arr (fields.flatMap (fun field => fabHashAlignmentAtoms field.2)).toArray
      lowerAlignedDigest "keccak256" 32 alignment operands
        ("keccak256_fab:" ++ type.fingerprint environment, operands, none)
  | .keccak256 (length := length) value => do
    lowerFixedByteHash "keccak256" length 32 (← lowerBytes value)
  | .keccak256Secp256k1Point value => do
    let point ← lowerExpr value
    let fields ← encodeForeign (.point .secp256k1) point
    let alignment := Json.arr (fabHashAlignmentAtoms (.curve (.foreign (.point .secp256k1)))).toArray
    lowerAlignedDigest "keccak256" 32 alignment fields ("keccak256", fields, some 96)
  | .persistentHash32 value => do
    let operands ← lowerBytes value
    let (highByte, low31) ← alignedBytes32Value value operands.values
    pure {values := ← lowerPersistentHash "bytes32" bytes32Alignment [highByte, low31], packed := true}
  | .persistentHashVector32 values => do
    let operands ← lowerBytes32VectorFields values
    if values.length == 1 then
      pure {values := ← lowerPersistentHash "bytes32" bytes32Alignment operands, packed := true}
    else
      let result ← lowerPersistentHash ("bytes32-vector:" ++ toString values.length)
        (bytes32VectorAlignment values.length) operands
      pure {values := result, packed := true}
  | .persistentHashNative value => do
    let native ← lowerExpr value
    pure {values := ← lowerPersistentHash "native-field" nativeFieldAlignment [native], packed := true}
  | .persistentHashNativeVector values => do
    let operands ← lowerNativeVectorFields values
    if values.length == 1 then
      pure {values := ← lowerPersistentHash "native-field" nativeFieldAlignment operands, packed := true}
    else
      let result ← lowerPersistentHash ("native-field-vector:" ++ toString values.length)
        (nativeFieldVectorAlignment values.length) operands
      pure {values := result, packed := true}
  | .persistentHashFab environment type values => do
    match validateFabHashLayout environment type values with
    | .error message =>
      rejectLowering message
      pure {values := []}
    | .ok compiled => do
      let fields ← match fabHashLayoutFields compiled with
        | .ok fields => pure fields
        | .error message =>
          rejectLowering message
          pure []
      let operands ← lowerFabHashFields fields values
      let alignment := Json.arr (fields.flatMap (fun field => fabHashAlignmentAtoms field.2)).toArray
      let result ← lowerPersistentHash ("fab:" ++ type.fingerprint environment) alignment operands
      pure {values := result, packed := true}
  | .persistentCommitFab environment type opening values => do
    match validateFabHashLayout environment type values with
    | .error message =>
      rejectLowering message
      pure {values := []}
    | .ok compiled => do
      let fields ← match fabHashLayoutFields compiled with
        | .ok fields => pure fields
        | .error message =>
          rejectLowering message
          pure []
      unless fabHashEncodedFieldCount fields + 2 ≤ fabHashNativeOperandLimit do
        rejectLowering "mixed FAB persistent commitment exceeds the native operand-vector budget"
      let openingBytes ← lowerBytes opening
      let (openingHighByte, openingLow31) ← alignedBytes32Value opening openingBytes.values
      let payloadOperands ← lowerFabHashFields fields values
      let alignment := Json.arr
        (#[bytesAlignmentAtom 32] ++
          (fields.flatMap (fun field => fabHashAlignmentAtoms field.2)).toArray)
      let result ← lowerPersistentHash
        ("fab-commit:" ++ type.fingerprint environment) alignment
        ([openingHighByte, openingLow31] ++ payloadOperands)
      pure {values := result, packed := true}
  | .foreignToBytes (kind := kind) value => do
    lowerForeignToBytes kind (← lowerExpr value)
  | .toBytes32 value => do
    let input ← lowerExpr value
    if Native.isWidenedByte value then
      return {values := input :: List.replicate 31 "0x00"}
    let (low, high) ← lowerToBytes32 input
    pure {values := [low, high], packed := true}
  | .reverseBytes32 value => do
    lowerFixedReverse 32 (← lowerBytes value)
  | .select condition yes no => do
    let condition ← lowerExpr condition
    let yes ← byteChunks length (← lowerBytes yes)
    let no ← byteChunks length (← lowerBytes no)
    let values ← (yes.zip no).mapM fun (yes, no) =>
      selectOperands condition yes no
    pure {values, packed := true}
  | @Expr.letE (.bytes _) _ name value body => do
    let values ← lowerBytes value
    let aliases := (← get).byteAliases
    modify fun state => {state with byteAliases := (name, values) :: aliases}
    let result ← lowerBytes body
    modify fun state => {state with byteAliases := aliases}
    pure result
  | @Expr.letE _ _ name value body => do
    let value ← lowerExpr value
    let aliases := (← get).aliases
    modify fun state => {state with aliases := (name, value) :: aliases}
    let result ← lowerBytes body
    modify fun state => {state with aliases}
    pure result
  | .assertE condition body => do
    emit "assert" [("cond", toJson (← lowerExpr condition))]
    lowerBytes body
  | _ => do
    rejectLowering "unsupported Bytes32 expression in native lowering"
    pure {values := []}
termination_by value => sizeOf value
decreasing_by
  all_goals simp_wf <;> omega

private def lowerFabHashFields : List (String × Types.Layout) → List (Sigma Expr) → LowerM (List String)
  | [], [] => pure []
  | field :: fields, value :: rest => do
    let aligned ← match field.2, value with
      | .bytes length .byteField, ⟨.bytes _, expression⟩ => do
        let bytes ← lowerBytes expression
        if length == 32 then do
          let (highByte, low31) ← match value with
            | ⟨.bytes 32, source⟩ => alignedBytes32Value source bytes.values
            | _ => alignedBytes32Fields bytes.values
          pure [highByte, low31]
        else do pure ((← byteChunks length bytes).reverse)
      | .scalar .nativeField, ⟨.native, expression⟩ => pure [← lowerExpr expression]
      | .scalar .booleanField, ⟨.bool, expression⟩ => pure [← lowerExpr expression]
      | .scalar (.boundedUnsignedField _), ⟨.uint _, expression⟩ => pure [← lowerExpr expression]
      | .enumeration _ (.enumTagField _) _ 0 _ _, ⟨.uint _, expression⟩ =>
        pure [← lowerExpr expression]
      | .curve .jubjubScalar, ⟨.jubjubScalar, expression⟩ => do
        let scalar ← lowerExpr expression
        pure [← lowerJubjubScalarToNative scalar]
      | .curve .jubjubPoint, ⟨.jubjubPoint, expression⟩ => do
        let point ← lowerExpr expression
        let (x, y) ← lowerPointCoordinates point
        pure [x, y]
      | .curve (.foreign expected), ⟨.foreign actual, expression⟩ => do
        unless expected == actual do
          rejectLowering "mixed FAB curve type differs from its checked layout"
        encodeForeign actual (← lowerExpr expression)
      | _, _ => do
        rejectLowering "mixed FAB field type differs from its checked layout"
        pure []
    pure (aligned ++ (← lowerFabHashFields fields rest))
  | _, _ => do
    rejectLowering "mixed FAB field count differs from its checked layout"
    pure []
termination_by _ values => sizeOf values
decreasing_by
  all_goals simp_wf
  all_goals first
    | exact sizeOfSigmaExprHeadLt _ _
    | omega

private def lowerBytes32VectorFields : List (Expr (.bytes 32)) → LowerM (List String)
  | [] => pure []
  | value :: rest => do
    let operands ← lowerBytes value
    let (highByte, low31) ← alignedBytes32Value value operands.values
    pure ([highByte, low31] ++ (← lowerBytes32VectorFields rest))
termination_by values => sizeOf values
decreasing_by
  all_goals simp_wf <;> omega

private def lowerNativeVectorFields : List (Expr .native) → LowerM (List String)
  | [] => pure []
  | value :: rest => do
    let first ← lowerExpr value
    pure (first :: (← lowerNativeVectorFields rest))
termination_by values => sizeOf values
decreasing_by
  all_goals simp_wf <;> omega

/-- Source Bool values retain the constrained Native 0/1 ABI. Typed gates bridge locally. -/
def lowerExpr : Expr ty → LowerM String
  | .copyValue value => do unary "copy" (← lowerExpr value) "val"
  | .native n => pure (fieldImmediate n)
  | .uint _ n => pure (fieldImmediate n)
  | .bool b => pure (if b then "0x01" else "0x00")
  | .foreignUnary op value => do
    lowerForeignUnary op (← lowerExpr value)
  | .foreignBinary op left right => do
    let left ← lowerExpr left
    let right ← lowerExpr right
    lowerForeignBinary op left right
  | .foreignFromBytes (length := length) kind value => do
    lowerForeignFromBytes kind length (← lowerBytes value)
  | .opaqueBytesProjection value => lowerOpaqueBytes value
  | .opaqueStringProjection value => lowerOpaqueString value
  | .opaqueBytesEmpty | .opaqueStringEmpty => pure "0x00"
  | .foreignBase curve value => lowerForeignConstant (.base curve) (Foreign.encodeField (.base curve) value)
  | .foreignScalar curve value => lowerForeignConstant (.scalar curve) (Foreign.encodeField (.scalar curve) value)
  | .foreignPoint curve value => lowerForeignConstant (.point curve) (Foreign.encodePoint curve value)
  | .foreignEncodedField (kind := kind) value index => do
    let value ← lowerExpr value
    let fields ← encodeForeign kind value
    match fields[index]? with
    | some output => pure output
    | none => do
      rejectLowering "foreign encoding projection index is out of range"
      pure "0x00"
  | .boolAnd left right => do
    let left ← lowerExpr left
    let right ← lowerExpr right
    lowerBoolGate "and" left right
  | .boolOr left right => do
    let left ← lowerExpr left
    let right ← lowerExpr right
    lowerBoolGate "or" left right
  | .boolXor left right => do
    let leftValue ← lowerExpr left
    let rightValue ← lowerExpr right
    match left, right with
    | .bool true, _ => unary "not" rightValue
    | _, .bool true => unary "not" leftValue
    | _, _ => lowerBoolGate "xor" leftValue rightValue
  | .ref name => do
    match ty with
    | .bytes _ | .opaqueBytes | .opaqueString => do
      rejectLowering "byte strings require their typed FAB alignment"
      pure "0x00"
    | .jubjubScalar | .jubjubPoint =>
      match (← get).aliases.lookup name with
      | some value => pure value
      | none => do
        rejectLowering "unbound typed Jubjub source symbol"
        pure "0x00"
    | _ => pure ((← get).aliases.lookup name |>.getD ("%input_" ++ name))
  | .bytesField (length := length) value index => do
    let value ← lowerBytes value
    if index ≥ Noctium.bytesChunkCount length then
      rejectLowering "byte field chunk index is out of range"
      return "0x00"
    if value.packed then
      if value.values.length != Noctium.bytesChunkCount length then
        rejectLowering "byte chunk count mismatch"
        return "0x00"
      pure value.values.reverse[index]!
    else
      if value.values.length != length then
        rejectLowering "byte leaf count mismatch"
        return "0x00"
      packBytes ((value.values.drop ((Noctium.bytesChunkCount length - 1 - index) * 31)).take 31)
  | .bytesAt (length := length) value index => do
    lowerFixedByteAt length index (← lowerBytes value)
  | .jubjubScalarFromNative value => do
    lowerJubjubScalarFromNative (← lowerExpr value)
  | .jubjubScalarToNative value => do
    lowerJubjubScalarToNative (← lowerExpr value)
  | .hashToCurve values => do
    let operands ← lowerNativeVectorFields values
    let key : ExpressionKey := ("hash_to_curve", operands, none)
    if let some existing := (← get).expressions.lookup key then return existing
    let output ← fresh
    emit "hash_to_curve" [("inputs", toJson operands), ("output", toJson output)]
    modify fun state => {state with expressions := (key, output) :: state.expressions}
    pure output
  | .hashToCurveFab environment type values => do
    match validateFabHashLayout environment type values with
    | .error message =>
      rejectLowering message
      pure "0x00"
    | .ok compiled => do
      let fields ← match fabHashLayoutFields compiled with
        | .ok fields => pure fields
        | .error message =>
          rejectLowering message
          pure []
      unless fabHashEncodedFieldCount fields ≤ Types.defaultLimits.maxVectorLength do
        rejectLowering s!"hash_to_curve input count exceeds the maximum of {Types.defaultLimits.maxVectorLength}"
      let operands ← lowerFabHashFields fields values
      let key : ExpressionKey := ("hash_to_curve", operands, none)
      if let some existing := (← get).expressions.lookup key then return existing
      let output ← fresh
      emit "hash_to_curve" [("inputs", toJson operands), ("output", toJson output)]
      modify fun state => {state with expressions := (key, output) :: state.expressions}
      pure output
  | .transientHash values => do
    let operands ← lowerNativeVectorFields values
    let key : ExpressionKey := ("transient_hash", operands, none)
    if let some existing := (← get).expressions.lookup key then return existing
    let output ← fresh
    emit "transient_hash" [("inputs", toJson operands), ("output", toJson output)]
    modify fun state => {state with expressions := (key, output) :: state.expressions}
    pure output
  | .transientHashFab environment type values => do
    match validateTransientFabHashFields environment type values with
    | .error message =>
      rejectLowering message
      pure "0x00"
    | .ok fields => do
      let operands ← lowerFabHashFields fields values
      let key : ExpressionKey := ("transient_hash", operands, none)
      if let some existing := (← get).expressions.lookup key then return existing
      let output ← fresh
      emit "transient_hash" [("inputs", toJson operands), ("output", toJson output)]
      modify fun state => {state with expressions := (key, output) :: state.expressions}
      pure output
  | .transientCommitFab environment type opening values => do
    match validateFabHashLayout environment type values with
    | .error message =>
      rejectLowering message
      pure "0x00"
    | .ok compiled => do
      let fields ← match fabHashLayoutFields compiled with
        | .ok fields => pure fields
        | .error message =>
          rejectLowering message
          pure []
      unless fabHashEncodedFieldCount fields + 1 ≤ Types.defaultLimits.maxVectorLength do
        rejectLowering "mixed FAB transient commitment exceeds the native field-vector budget"
      let opening ← lowerExpr opening
      let payload ← lowerFabHashFields fields values
      let operands := opening :: payload
      let key : ExpressionKey := ("transient_hash", operands, none)
      if let some existing := (← get).expressions.lookup key then return existing
      let output ← fresh
      emit "transient_hash" [("inputs", toJson operands), ("output", toJson output)]
      modify fun state => {state with expressions := (key, output) :: state.expressions}
      pure output
  | .jubjubMulGenerator scalar => do
    let scalar ← lowerExpr scalar
    let key : ExpressionKey := ("ec_mul_generator", [scalar], none)
    if let some existing := (← get).expressions.lookup key then return existing
    let output ← fresh
    emit "ec_mul_generator" [("scalar", toJson scalar), ("output", toJson output)]
    modify fun state => {state with expressions := (key, output) :: state.expressions}
    pure output
  | .jubjubMul point scalar => do
    let point ← lowerExpr point
    let scalar ← lowerExpr scalar
    let key : ExpressionKey := ("ec_mul", [point, scalar], none)
    if let some existing := (← get).expressions.lookup key then return existing
    let output ← fresh
    emit "ec_mul" [("a", toJson point), ("scalar", toJson scalar), ("output", toJson output)]
    modify fun state => {state with expressions := (key, output) :: state.expressions}
    pure output
  | .jubjubAdd left right => do
    binary "add" (← lowerExpr left) (← lowerExpr right)
  | .jubjubNeg point => do unary "neg" (← lowerExpr point)
  | .jubjubCoordinate point index => do
    let point ← lowerExpr point
    let (x, y) ← lowerPointCoordinates point
    match index with
    | 0 => pure x
    | 1 => pure y
    | _ => do
      rejectLowering "Jubjub coordinate index must be 0 or 1"
      pure "0x00"
  | .jubjubFromCoordinates x y => do
    lowerPointFromCoordinates (← lowerExpr x) (← lowerExpr y)
  | .fromBytes32 value => do
    let values ← lowerBytes value
    lowerFromBytes32 ty values.values
  | .fromBytes (length := length) value => do
    let bytes ← lowerBytes value
    lowerFromBytes ty length bytes
  | .add a b => do
    let leftIsZero := Native.isLiteralNativeZero a
    let rightIsZero := Native.isLiteralNativeZero b
    let left ← lowerExpr a
    let right ← lowerExpr b
    nativeAdd leftIsZero rightIsZero left right
  | .mul a b => do binary "mul" (← lowerExpr a) (← lowerExpr b)
  | .sub a b => do binary "add" (← lowerExpr a) (← unary "neg" (← lowerExpr b))
  | .uadd (m := m) (n := n) a b => do
    let leftIsZero := Native.isLiteralUIntZero a
    let rightIsZero := Native.isLiteralUIntZero b
    let left ← lowerExpr a
    let right ← lowerExpr b
    nativeUIntAdd (m + n) leftIsZero rightIsZero left right
  | .umul (m := m) (n := n) a b => do
    let output ← binary "mul" (← lowerExpr a) (← lowerExpr b)
    constrainUnsigned (m * n) output
    pure output
  | .inv value => do
    let operand ← lowerExpr value
    let nonzeroOperand ← match ty with
      | .native => pure operand
      | .jubjubScalar => lowerJubjubScalarToNative operand
      | _ => do
        rejectLowering "inv supports only Native and JubjubScalar values"
        pure operand
    let isZero ← binary "test_eq" nonzeroOperand "0x00"
    let isNonzero ← unary "not" isZero
    emit "assert" [("cond", toJson isNonzero)]
    unary "inv" operand
  | .usub (m := m) a b => do
    let output ← binary "add" (← lowerExpr a) (← unary "neg" (← lowerExpr b))
    constrainUnsigned m output
    pure output
  | .cast target value => do
    let output ← lowerExpr value
    match target with
    | .native => pure output
    | .bool =>
      let zero ← binary "test_eq" output "0x00"
      unary "not" zero
    | .uint maximum => do
      constrainUnsigned maximum output
      pure output
    | .bytes _ => do
      rejectLowering "byte strings do not support scalar casts"
      pure "0x00"
    | .opaqueBytes => do
      rejectLowering "opaque byte strings do not support scalar casts"
      pure "0x00"
    | .opaqueString => do
      rejectLowering "opaque strings do not support scalar casts"
      pure "0x00"
    | .jubjubScalar | .jubjubPoint | .foreign _ => do
      rejectLowering "opaque values do not support generic scalar casts"
      pure "0x00"
  | @Expr.letE (.bytes _) _ name value body => do
    let value ← lowerBytes value
    let byteAliases := (← get).byteAliases
    modify fun state => {state with byteAliases := (name, value) :: byteAliases}
    let result ← lowerExpr body
    modify fun state => {state with byteAliases}
    pure result
  | .letE name value body => do
    let value ← lowerExpr value
    let aliases := (← get).aliases
    modify fun s => {s with aliases := (name, value) :: aliases}
    let result ← lowerExpr body
    modify fun s => {s with aliases := aliases}
    pure result
  | .assertE condition body => do
    emit "assert" [("cond", toJson (← lowerExpr condition))]
    lowerExpr body
  | .disclose _ value => lowerExpr value
  | .eq a b => do binary "test_eq" (← lowerExpr a) (← lowerExpr b)
  | .select condition yes no => do
    let bit ← lowerExpr condition
    let a ← lowerExpr yes
    let b ← lowerExpr no
    selectOperands bit a b
  | .poseidon2 domain a b => do
    let a ← lowerExpr a
    let b ← lowerExpr b
    let key : ExpressionKey := ("transient_hash", [fieldImmediate domain, a, b], none)
    if let some existing := (← get).expressions.lookup key then return existing
    let output ← fresh
    emit "transient_hash" [("inputs", toJson [fieldImmediate domain, a, b]),
      ("output", toJson output)]
    modify fun s => {s with expressions := (key, output) :: s.expressions}
    return output
  | .foreignToBytes _ | .sha256 _ | .sha512 _ | .keccak256 _ | .keccak256Secp256k1Point _
  | .bytesLiteral _ _ | .reverseBytes _ | .sliceBytes _ _ _ | .concatBytes _ _
  | .bytes32Literal _ | .persistentHash32 _ | .persistentHashVector32 _
  | .persistentHashNative _ | .persistentHashNativeVector _ | .persistentHashFab _ _ _
  | .sha512Fab _ _ _ | .keccak256Fab _ _ _
  | .persistentCommitFab _ _ _ _
  | .toBytes32 _ | .reverseBytes32 _ => do
    rejectLowering "Bytes32 expressions must be consumed with their typed FAB alignment"
    pure "0x00"
termination_by value => sizeOf value
decreasing_by
  all_goals simp_wf <;> omega
end
def bindPublic (values : List String) : LowerM Unit :=
  emit "impact" [("guard", toJson ("0x01" : String)), ("inputs", toJson values)]

/-- The public fixed-byte input prefix used by `lowerBody`, including its
Impact binding. It keeps the original input record and source span. -/
def lowerPublicFixedBytesInputPrefix (input : Input) : LowerM Unit := do
  lowerByteInput input
  match input.ty with
  | .bytes 0 => pure ()
  | .bytes _ => bindPublic input.nativeIdentifiers
  | _ => pure ()

theorem lowerPublicFixedBytesInputPrefix_preservesOutputCapacityFrame
    (name : String) (length : Nat) (span : SourceSpan := {}) :
    PreservesOutputCapacityFrame
      (lowerPublicFixedBytesInputPrefix {name, ty := .bytes length, visibility := .«public», span}) := by
  unfold lowerPublicFixedBytesInputPrefix
  apply bind_preservesOutputCapacityFrame _ _
    (lowerByteInput_fixedBytes_preservesOutputCapacityFrame name length .«public» false span)
  intro _
  by_cases empty : length = 0
  · simpa [empty, bindPublic] using pure_preservesOutputCapacityFrame ()
  · simpa [empty, bindPublic] using
      (emit_preservesOutputCapacityFrame "impact"
        [("guard", toJson ("0x01" : String)),
          ("inputs", toJson (Input.nativeIdentifiers
            {name, ty := .bytes length, visibility := .«public», span}))])

def bindPublicGuarded (guard : Expr .bool) (values : List String) : LowerM Unit := do
  emit "impact" [("guard", toJson (← lowerExpr guard)), ("inputs", toJson values)]

def lowerBody (c : Circuit) : LowerM Unit := do
  for input in c.inputs do
    if input.visibility == .«public» then
      match input.ty with
      | .bytes _ => lowerPublicFixedBytesInputPrefix input
      | _ => do
        lowerByteInput input
        match input.ty with
        | .foreign kind => do
          for output in (← encodeForeign kind ("%input_" ++ input.name)) do bindPublic [output]
        | .bytes 0 => pure ()
        | .bytes _ => bindPublic input.nativeIdentifiers
        | _ => for output in input.nativeIdentifiers do bindPublic [output]
    else
      lowerByteInput input
  for condition in c.constraints do
    let value ← lowerExpr condition
    emit "assert" [("cond", toJson value)]
  let mut outputs := []
  for output in c.outputs do
    match output with
    | {ty := .bytes 0, value, ..} => discard (lowerBytes value)
    | _ => pure ()
    match output.nativeReturnFields with
    | .error message => rejectLowering message
    | .ok fields =>
      for field in fields do
        outputs := outputs ++ [← lowerExpr field]
  if !outputs.isEmpty then bindPublic outputs
  emit "output" [("vals", toJson outputs)]

/-- Produce a ZKIR v3.2 relation, not a deployable contract bundle.
Public values are explicitly bound with Impact. The surrounding contract must
still bind this public-input sequence to its accepted ledger call transcript. -/
private def loweringCapabilities : Capabilities :=
  { poseidon2 := true, persistentHash32 := true,
    persistentHashVector32 := true, persistentHashNative := true,
    bytes32Conversions := true, sha512 := true, keccak256 := true, typedBoolean := true, hashToCurve := true, foreignValues := true, foreignArithmetic := true, foreignByteConversions := true, jubjub := true }

def lowerCircuit (c : Circuit) (rewrites : Rewrites := .disabled) : Except Diagnostic Json := do
  Disclosure.circuit c
  let c := Passes.pruneCircuit c
  c.validate loweringCapabilities
  for condition in c.constraints do
    match checkConstants condition with
    | .error message => throw {span := c.span, message}
    | .ok _ => pure ()
  for output in c.outputs do
    match checkConstants output.value with
    | .error message => throw {span := output.span, message}
    | .ok _ => pure ()
  let (_, result) := (lowerBody c).run {}
  let program := Json.mkObj [
    ("version", Json.mkObj [("major", toJson (3 : Nat)), ("minor", toJson (2 : Nat))]),
    ("inputs", Json.arr #[]),
    ("outputs", Json.arr ((c.outputs.flatMap fun output =>
      List.replicate output.nativeReturnFieldCount nativeType).toArray)),
    ("do_communications_commitment", toJson false),
    ("instructions", Json.arr (optimizedInstructions rewrites result.instructions))]
  let expected ← Native.expectedCircuit c
  validateProduced c.span (optimizedExpected rewrites expected) program

/-- Successful lowering necessarily passes the existing mandatory validation
against the independently reconstructed statement of the actual pruned source. -/
theorem lowerCircuit_validated (circuit : Circuit) (program : Json)
    (accepted : lowerCircuit circuit = .ok program) :
    ∃ expected, Native.expectedCircuit (Passes.pruneCircuit circuit) = .ok expected ∧
      Native.validate expected program = .ok () := by
  simp only [lowerCircuit, bind, bind_ok] at accepted
  rcases accepted with ⟨_, disclosure, _, validation, _, constants, _, outputConstants, gate⟩
  cases produced : (lowerBody (Passes.pruneCircuit circuit)).run {} with
  | mk value state =>
    simp only [produced] at gate
    rw [bind_ok] at gate
    rcases gate with ⟨expected, expectedAccepted, producerAccepted⟩
    obtain ⟨equal, checked⟩ := (validateProduced_ok _ _ _ _).mp producerAccepted
    exact ⟨expected, expectedAccepted, by rw [equal]; exact checked⟩

/-- Relate the accepted JSON instruction vector to the actual lowerBody run. -/
theorem lowerCircuit_instructions (circuit : Circuit) (program : Json)
    (accepted : lowerCircuit circuit = .ok program) :
    Native.arrayField program "instructions" =
      .ok ((lowerBody (Passes.pruneCircuit circuit)).run {}).2.instructions := by
  simp only [lowerCircuit, bind, bind_ok] at accepted
  rcases accepted with ⟨_, disclosure, _, validation, _, constants, _, outputConstants, gate⟩
  cases produced : (lowerBody (Passes.pruneCircuit circuit)).run {} with
  | mk value state =>
    simp only [produced] at gate
    rw [bind_ok] at gate
    rcases gate with ⟨expected, expectedAccepted, producerAccepted⟩
    obtain ⟨equal, checked⟩ := (validateProduced_ok _ _ _ _).mp producerAccepted
    rw [equal]
    rfl

def lowerEntrypointBody (entry : Entrypoint) (plan : Impact.Plan) : LowerM Unit := do
  for input in entry.circuit.inputs do
    lowerByteInput input (entry.callInputs.contains input.name)
  for condition in entry.circuit.constraints do
    emit "assert" [("cond", toJson (← lowerExpr condition))]
  for output in entry.circuit.outputs do
    match output with
    | {name, ty := .bytes _, value, ..} =>
      let value ← lowerBytes value
      modify fun s => {s with byteAliases := (name, value) :: s.byteAliases}
    | {name, value, ..} =>
      let value ← lowerExpr value
      modify fun s => {s with aliases := (name, value) :: s.aliases}
  -- Public parameters were read above in declaration order. Remaining reads
  -- come from ledger cells and the VM membership result in transcript order.
  let publicCount := Impact.publicInputReadCount entry.circuit.inputs
  for read in plan.reads.drop publicCount do
    for scalarRead in Impact.Read.scalarReads read do
      let activity ← match scalarRead.guard with
        | none => pure none
        | some guard => pure (some (← lowerExpr guard))
      let activityJson := (activity.map toJson).getD Json.null
      for (name, ty) in scalarRead.bindings do
        let output := "%input_" ++ name
        match ty with
        | .jubjubScalar => do
          emit "public_input" [
            ("guard", activityJson),
            ("type", nativeType), ("output", toJson output)]
          let scalar ← lowerJubjubScalarFromNative output
          let encoded ← lowerJubjubScalarToNative scalar
          emit "constrain_eq" [("a", toJson output), ("b", toJson encoded)]
          modify fun state => {state with aliases := (scalarRead.name, scalar) :: state.aliases}
        | .foreign kind =>
          emit "public_input" [
            ("guard", activityJson),
            ("type", toJson kind.nativeName), ("output", toJson output)]
        | _ =>
          emit "public_input" [
            ("guard", activityJson),
            ("type", nativeType), ("output", toJson output)]
          constrainType ty output
      if let .bytes _ := scalarRead.ty then do
        let values ← scalarRead.bindings.mapM fun (name, ty) => do
          match scalarRead.guard, ty with
          | some guard, .uint maximum =>
            lowerExpr (.select guard (.ref name : Expr (.uint maximum)) (.uint maximum 0))
          | _, _ => pure ("%input_" ++ name)
        modify fun state => {state with byteAliases :=
          (scalarRead.name, {values := values.reverse, packed := true}) :: state.byteAliases}
      if scalarRead.ty == .jubjubPoint then do
        let xName := scalarRead.bindings[0]!.1
        let yName := scalarRead.bindings[1]!.1
        let x := "%input_" ++ xName
        let y := "%input_" ++ yName
        let x ← match scalarRead.guard with
          | none => pure x
          | some guard => lowerExpr (.select guard (.ref xName : Expr .native) (.native 0))
        let y ← match scalarRead.guard with
          | none => pure y
          | some guard => lowerExpr (.select guard (.ref yName : Expr .native) (.native 1))
        let point ← lowerPointFromCoordinates x y
        modify fun state => {state with aliases := (scalarRead.name, point) :: state.aliases}
    for condition in read.inactiveDefaultConstraints do
      emit "assert" [("cond", toJson (← lowerExpr condition))]
  for condition in plan.guards do
    emit "assert" [("cond", toJson (← lowerExpr condition))]
  -- The ledger consumes one activity/skip entry per VM opcode. Compound
  -- Impact operations split their field vectors at each native opcode.
  for (operation, index) in plan.operations.zipIdx do
    let guard := ((plan.activityGuards[index]?).getD none).getD (.bool true)
    for fields in operation.fieldGroups do
      bindPublicGuarded guard (← fields.mapM lowerExpr)
  -- Entrypoint returns are public outputs committed with the call statement.
  let mut returned := []
  for output in entry.returns do
    match output with
    | {ty := .bytes 0, value, ..} => discard (lowerBytes value)
    | _ => pure ()
    match output.nativeReturnFields with
    | .error message => rejectLowering message
    | .ok fields =>
      for field in fields do
        returned := returned ++ [← lowerExpr field]
  emit "output" [("vals", toJson returned)]

/-- Lower an already-pruned entrypoint and return its plan with the checked
ledger relation. The producer check still derives its schedule from source. -/
def lowerPrunedEntrypoint (state : List StateDecl) (entry : Entrypoint)
    (rewrites : Rewrites := .disabled) : Except Diagnostic (Impact.Plan × Json) := do
  let plan ← Impact.lower state entry
  let (_, result) := (lowerEntrypointBody entry plan).run {}
  let callInputs := (entry.callArguments.flatMap Native.Input.callArgumentRequirements).map fun input =>
    let ty := match input.ty with | .foreign kind => toJson kind.nativeName | _ => nativeType
    Json.mkObj [("name", toJson input.identifier), ("type", ty)]
  let program := Json.mkObj [
    ("version", Json.mkObj [("major", toJson (3 : Nat)), ("minor", toJson (2 : Nat))]),
    ("inputs", toJson callInputs),
    ("outputs", Json.arr ((entry.returns.flatMap fun output =>
      List.replicate output.nativeReturnFieldCount nativeType).toArray)),
    -- Ledger ContractCall.public_inputs always includes the commitment after
    -- binding input. Standalone relations above deliberately keep it disabled.
    ("do_communications_commitment", toJson true),
    ("instructions", Json.arr (optimizedInstructions rewrites result.instructions))]
  let expected ← Native.expectedEntrypoint state entry
  let relation ← validateProduced entry.span (optimizedExpected rewrites expected) program
  pure (plan, relation)

/-- Compile a native ledger transcript relation. Public-input binding includes
all opcode, alignment, key, read-result and write-value fields. The caller must
execute the matching Impact plan, not the standalone circuit artifact. -/
def lowerEntrypoint (state : List StateDecl) (entry : Entrypoint)
    (rewrites : Rewrites := .disabled) : Except Diagnostic Json := do
  let result ← lowerPrunedEntrypoint state (Passes.pruneEntrypoint entry) rewrites
  pure result.2

/-- Accepted ledger-call JSON retains the exact instruction vector emitted by
the production body over the actual accepted pruned plan. -/
theorem lowerEntrypoint_instructions (state : List StateDecl) (entry : Entrypoint)
    (program : Json) (accepted : lowerEntrypoint state entry = .ok program) :
    ∃ plan, Impact.lower state (Passes.pruneEntrypoint entry) = .ok plan ∧
      Native.arrayField program "instructions" =
        .ok ((lowerEntrypointBody (Passes.pruneEntrypoint entry) plan).run {}).2.instructions := by
  simp only [lowerEntrypoint, bind, bind_ok] at accepted
  obtain ⟨⟨resultPlan, relation⟩, lowered, result⟩ := accepted
  cases result
  simp only [lowerPrunedEntrypoint, bind, bind_ok] at lowered
  rcases lowered with ⟨plan, planAccepted, gate⟩
  cases produced : (lowerEntrypointBody (Passes.pruneEntrypoint entry) plan).run {} with
  | mk value result =>
    simp only [produced] at gate
    simp only [bind_ok] at gate
    rcases gate with ⟨expected, _, _, producerAccepted, output⟩
    cases output
    obtain ⟨equal, _⟩ := (validateProduced_ok _ _ _ _).mp producerAccepted
    refine ⟨_, planAccepted, ?_⟩
    rw [equal, produced]
    rfl

end Noctium.Backend.Zkir
