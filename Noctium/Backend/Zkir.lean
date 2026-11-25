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

def optimizedExpected (rewrites : Rewrites) (expected : Native.Expected) : Native.Expected :=
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

private theorem OutputCapacityFrame.of_sameInstructions {before after : LowerState}
    (next : before.next = after.next)
    (instructions : before.instructions = after.instructions) : OutputCapacityFrame before after := by
  constructor
  · omega
  · unfold LowerState.outputDefinitions
    rw [instructions, next]
    simp

def PreservesOutputCapacityFrame (operation : StateM LowerState α) : Prop :=
  ∀ state, OutputCapacityFrame state (operation.run state).2

theorem modify_preservesOutputCapacityFrame (update : LowerState → LowerState)
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

private theorem forIn_preservesOutputCapacityFrame (items : List α) (initial : β)
    (body : α → β → StateM LowerState (ForInStep β))
    (preserves : ∀ item accumulator, PreservesOutputCapacityFrame (body item accumulator)) :
    PreservesOutputCapacityFrame (forIn items initial body) := by
  induction items generalizing initial with
  | nil => exact pure_preservesOutputCapacityFrame _
  | cons item rest ih =>
    rw [List.forIn_cons]
    apply bind_preservesOutputCapacityFrame _ _ (preserves item initial)
    intro step
    cases step with
    | done result => exact pure_preservesOutputCapacityFrame _
    | yield result => exact ih result

theorem forIn_preservesOutputCapacityFrame_of_mem (items : List α) (initial : β)
    (body : α → β → StateM LowerState (ForInStep β))
    (preserves : ∀ item ∈ items, ∀ accumulator,
      PreservesOutputCapacityFrame (body item accumulator)) :
    PreservesOutputCapacityFrame (forIn items initial body) := by
  induction items generalizing initial with
  | nil => exact pure_preservesOutputCapacityFrame _
  | cons item rest ih =>
    rw [List.forIn_cons]
    apply bind_preservesOutputCapacityFrame _ _
      (preserves item (by simp) initial)
    intro step
    cases step with
    | done result => exact pure_preservesOutputCapacityFrame _
    | yield result =>
      exact ih result (fun value member => preserves value (List.mem_cons_of_mem _ member))

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

theorem emit_preservesOutputCapacityFrame (op : String)
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

private def lowerInputRead (op : String) (raw : Bool) (identifier : String)
    (ty : Json := nativeType) : LowerM Unit :=
  unless raw do emit op [("guard", Json.null), ("type", ty), ("output", toJson identifier)]

private def lowerInputRequirement (op : String) (raw : Bool)
    (spec : Native.InputRequirement) : LowerM Unit := do
  lowerInputRead op raw spec.identifier
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
private def lowerPointFromCoordinatesFresh (x y : String) : LowerM String := do
  let point ← fresh
  emit "from_coordinates" [
    ("inputs", toJson [x, y]),
    ("output", toJson point)]
  pure point

private def lowerPointFromCoordinatesFinish (key : ExpressionKey)
    (x y point : String) : LowerM String := do
  let (actualX, actualY) ← lowerPointCoordinates point
  emit "constrain_eq" [("a", toJson x), ("b", toJson actualX)]
  emit "constrain_eq" [("a", toJson y), ("b", toJson actualY)]
  modify fun state => {state with expressions := (key, point) :: state.expressions}
  pure point

private def lowerPointFromCoordinates (x y : String) : LowerM String := do
  let key : ExpressionKey := ("from_coordinates_jubjub", [x, y], none)
  if let some existing := (← get).expressions.lookup key then return existing
  let point ← lowerPointFromCoordinatesFresh x y
  lowerPointFromCoordinatesFinish key x y point

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

private def encodeFreshOutputs (opcode inputField value : String)
    (keys : List ExpressionKey) : LowerM (List String) := do
  let outputs ← keys.mapM fun _ => fresh
  emit opcode [(inputField, toJson value), ("outputs", toJson outputs)]
  modify fun state => {state with expressions := keys.zip outputs ++ state.expressions}
  pure outputs

/-- Read the entire group before allocating any new outputs. A partial cache
hit therefore cannot change the ordering or arity of an encoded value. -/
private def encodeCachedOutputs (opcode inputField value : String)
    (keys : List ExpressionKey) : LowerM (List String) := do
  let expressions := (← get).expressions
  let cached := keys.map (fun key => expressions.lookup key)
  if cached.all Option.isSome then return cached.filterMap id
  encodeFreshOutputs opcode inputField value keys

private def encodeForeign (kind : Foreign.Kind) (value : String) : LowerM (List String) :=
  let keys := (List.range kind.encodedFieldCount).map fun index =>
    (("encode_foreign:" ++ kind.nativeName, [value], some index) : ExpressionKey)
  encodeCachedOutputs "encode" "input" value keys

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
  if yes == no then return yes
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

private def scalePackedBytes (zeroCount : Nat) (value : String) : LowerM String := do
  if zeroCount == 0 || value == "0x00" then pure value
  else
    -- A byte chunk holds at most 31 bytes. Reduce the constant modulo the
    -- field so this helper stays canonical even for an accidental wider use.
    binary "mul" (fieldImmediate (256 ^ zeroCount % nativeModulus)) value

private def packBytesRecAux (zeroCount : Nat) : List String → LowerM String
  | [] => pure "0x00"
  | byte :: rest => do
    if byte == "0x00" then
      packBytesRecAux (zeroCount + 1) rest
    else
      let suffix ← packBytesRecAux 0 rest
      let packed ← if suffix == "0x00" then pure byte else do
        let scaled ← binary "mul" "0x0001" suffix
        binary "add" byte scaled
      scalePackedBytes zeroCount packed
termination_by bytes => bytes.length
decreasing_by all_goals simp_wf

private def packBytesRec (bytes : List String) : LowerM String :=
  packBytesRecAux 0 bytes

/-- Skip symbolic packing when every already-lowered byte is canonical zero.
The one linear scan runs before the byte recurrence. -/
private def packBytes (bytes : List String) : LowerM String :=
  if bytes.all (fun byte => byte == "0x00") then pure "0x00" else packBytesRec bytes

private theorem packBytes_zero_exact (bytes : List String) (state : LowerState)
    (allZero : bytes.all (fun byte => byte == "0x00") = true) :
    (packBytes bytes).run state = ("0x00", state) := by
  simp [packBytes, allZero]
  rfl

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

private theorem cachedScalarOutput_preservesOutputCapacityFrame
    (key : ExpressionKey) (opcode : String) (fields : String → List (String × Json))
    (outputCount : ∀ output,
      Native.outputDefinitionsInInstruction (instruction opcode (fields output)) = 1) :
    PreservesOutputCapacityFrame (do
      if let some existing := (← get).expressions.lookup key then return existing
      let output ← fresh
      emit opcode (fields output)
      modify fun state => {state with expressions := (key, output) :: state.expressions}
      pure output) := by
  intro state
  cases hit : state.expressions.lookup key with
  | some existing =>
    simp [hit, StateT.run_bind, StateT.run_get, StateT.run_pure]
    exact OutputCapacityFrame.refl state
  | none =>
    simp [hit, fresh, emit, StateT.run_bind, StateT.run_get,
      StateT.run_modify, StateT.run_set]
    let output := "%v" ++ state.next.repr
    let emitted := instruction opcode (fields output)
    change OutputCapacityFrame state {state with
      next := state.next + 1
      instructions := state.instructions.push emitted
      expressions := (key, output) :: state.expressions}
    refine OutputCapacityFrame.of_instruction_push emitted (by simp) rfl ?_
    change state.next + 1 - state.next ≤ Native.outputDefinitionsInInstruction emitted
    rw [show Native.outputDefinitionsInInstruction emitted = 1 from outputCount output]
    omega

theorem ordinaryBinary_preservesOutputCapacityFrame (opcode left right : String)
    (ordinary : opcode ≠ "encode" ∧ opcode ≠ "bytes_into_natives" ∧
      opcode ≠ "into_coordinates") :
    PreservesOutputCapacityFrame (binary opcode left right) := by
  unfold binary
  apply cachedScalarOutput_preservesOutputCapacityFrame
  intro output
  apply instruction_scalarOutputDefinitions _ _ _ ordinary _
  all_goals
    simp [Native.stringField, instruction, Json.getObjVal?, Json.mkObj, Json.getStr?,
      Std.TreeMap.Raw.get?_eq_getElem?, Std.TreeMap.Raw.getElem?_ofList_of_mem, Lean.ToJson.toJson]
    rfl

private theorem scalePackedBytes_preservesOutputCapacityFrame (zeroCount : Nat)
    (value : String) : PreservesOutputCapacityFrame (scalePackedBytes zeroCount value) := by
  by_cases skip : zeroCount == 0 || value == "0x00"
  · simp [scalePackedBytes, skip]
    exact pure_preservesOutputCapacityFrame value
  · simp [scalePackedBytes, skip]
    exact ordinaryBinary_preservesOutputCapacityFrame "mul"
      (fieldImmediate (256 ^ zeroCount % nativeModulus)) value
      ⟨by decide, by decide, by decide⟩

theorem ordinaryUnary_preservesOutputCapacityFrame (opcode operand : String)
    (ordinary : opcode ≠ "encode" ∧ opcode ≠ "bytes_into_natives" ∧
      opcode ≠ "into_coordinates") :
    PreservesOutputCapacityFrame (unary opcode operand) := by
  unfold unary
  apply cachedScalarOutput_preservesOutputCapacityFrame
  intro output
  apply instruction_scalarOutputDefinitions _ _ _ ordinary _
  all_goals
    simp [Native.stringField, instruction, Json.getObjVal?, Json.mkObj, Json.getStr?,
      Std.TreeMap.Raw.get?_eq_getElem?, Std.TreeMap.Raw.getElem?_ofList_of_mem, Lean.ToJson.toJson]
    rfl

theorem copyVal_preservesOutputCapacityFrame (operand : String) :
    PreservesOutputCapacityFrame (unary "copy" operand "val") := by
  unfold unary
  apply cachedScalarOutput_preservesOutputCapacityFrame
  intro output
  apply instruction_scalarOutputDefinitions _ _ _ ⟨by decide, by decide, by decide⟩ _
  all_goals
    simp [Native.stringField, instruction, Json.getObjVal?, Json.mkObj, Json.getStr?,
      Std.TreeMap.Raw.get?_eq_getElem?, Std.TreeMap.Raw.getElem?_ofList_of_mem, Lean.ToJson.toJson]
    rfl

private theorem binaryAdd_preservesOutputCapacityFrame (left right : String) :
    PreservesOutputCapacityFrame (binary "add" left right) :=
  ordinaryBinary_preservesOutputCapacityFrame "add" left right ⟨by decide, by decide, by decide⟩

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

private theorem encodeInstruction_outputDefinitions (value : String) (outputs : List String) :
    Native.outputDefinitionsInInstruction
      (instruction "encode" [("input", toJson value), ("outputs", toJson outputs)]) =
      outputs.length := by
  have opcodeOk : Native.stringField
      (instruction "encode" [("input", toJson value), ("outputs", toJson outputs)]) "op" =
      .ok "encode" := by
    simp [Native.stringField, instruction, Json.getObjVal?, Json.mkObj, Json.getStr?,
      Std.TreeMap.Raw.get?_eq_getElem?, Std.TreeMap.Raw.getElem?_ofList_of_mem,
      Lean.ToJson.toJson]
    rfl
  have outputsOk : Native.arrayField
      (instruction "encode" [("input", toJson value), ("outputs", toJson outputs)]) "outputs" =
      .ok ((outputs.map Json.str).toArray) := by
    simp [Native.arrayField, instruction, Json.getObjVal?, Json.mkObj, Json.getArr?,
      Std.TreeMap.Raw.get?_eq_getElem?, Std.TreeMap.Raw.getElem?_ofList_of_mem,
      Lean.ToJson.toJson, Lean.List.toJson, Lean.Array.toJson]
    rfl
  simp [Native.outputDefinitionsInInstruction, opcodeOk, outputsOk, Except.toOption]

private theorem freshList_state (items : List α) (state : LowerState) :
    ((items.mapM (fun _ => fresh) : LowerM (List String)).run state).2 =
      {state with next := state.next + items.length} := by
  induction items generalizing state with
  | nil => rfl
  | cons item rest ih =>
    simp only [List.mapM_cons, StateT.run_bind, fresh,
      StateT.run_get, StateT.run_set]
    change (StateT.run (List.mapM (fun _ => fresh) rest)
      {state with next := state.next + 1}).2 = _
    rw [ih]
    simp [List.length_cons, Nat.add_comm, Nat.add_left_comm]

private theorem freshList_length (items : List α) (state : LowerState) :
    ((items.mapM (fun _ => fresh) : LowerM (List String)).run state).1.length =
      items.length := by
  induction items generalizing state with
  | nil => rfl
  | cons item rest ih =>
    simp only [List.mapM_cons, StateT.run_bind, fresh,
      StateT.run_get, StateT.run_set]
    change ((toString "%v" ++ state.next.repr) ::
      (StateT.run (List.mapM (fun _ => fresh) rest)
        {state with next := state.next + 1}).1).length = _
    rw [List.length_cons, ih]
    simp

private theorem selectOperands_preservesOutputCapacityFrame (bit yes no : String) :
    PreservesOutputCapacityFrame (selectOperands bit yes no) := by
  by_cases equal : yes == no
  · simp [selectOperands, equal]
    exact pure_preservesOutputCapacityFrame yes
  · simp only [selectOperands, equal, Bool.false_eq_true, ↓reduceIte]
    apply cachedScalarOutput_preservesOutputCapacityFrame
    intro output
    apply instruction_scalarOutputDefinitions _ _ _ ⟨by decide, by decide, by decide⟩ _
    all_goals
      simp [Native.stringField, instruction, Json.getObjVal?, Json.mkObj, Json.getStr?,
        Std.TreeMap.Raw.get?_eq_getElem?, Std.TreeMap.Raw.getElem?_ofList_of_mem,
        Lean.ToJson.toJson]
      rfl

private theorem encodeFreshOutputs_preservesOutputCapacityFrame
    (op inputField value : String) (keys : List ExpressionKey)
    (outputCount : ∀ outputs : List String,
      Native.outputDefinitionsInInstruction
        (instruction op [(inputField, toJson value), ("outputs", toJson outputs)]) =
        outputs.length) :
    PreservesOutputCapacityFrame (encodeFreshOutputs op inputField value keys) := by
  intro state
  unfold encodeFreshOutputs
  simp only [StateT.run_bind]
  cases allocatedResult :
      ((keys.mapM (fun _ => fresh) : LowerM (List String)).run state) with
  | mk outputs allocated =>
    have allocatedState : allocated = {state with next := state.next + keys.length} := by
      simpa [allocatedResult] using freshList_state keys state
    have outputLength : outputs.length = keys.length := by
      simpa [allocatedResult] using freshList_length keys state
    rw [allocatedState]
    let emitted := instruction op [(inputField, toJson value), ("outputs", toJson outputs)]
    change OutputCapacityFrame state {state with
      next := state.next + keys.length
      instructions := state.instructions.push emitted
      expressions := keys.zip outputs ++ state.expressions}
    apply OutputCapacityFrame.of_instruction_push emitted
    · simp
    · rfl
    · change state.next + keys.length - state.next ≤
        Native.outputDefinitionsInInstruction emitted
      rw [show Native.outputDefinitionsInInstruction emitted = outputs.length from outputCount _,
        outputLength]
      omega

private theorem encodeCachedOutputs_preservesOutputCapacityFrame
    (op inputField value : String) (keys : List ExpressionKey)
    (outputCount : ∀ outputs : List String,
      Native.outputDefinitionsInInstruction
        (instruction op [(inputField, toJson value), ("outputs", toJson outputs)]) =
        outputs.length) :
    PreservesOutputCapacityFrame (encodeCachedOutputs op inputField value keys) := by
  intro state
  let cached := keys.map (fun key => state.expressions.lookup key)
  change OutputCapacityFrame state
    ((if cached.all Option.isSome then
        (pure (cached.filterMap id) : LowerM (List String))
      else encodeFreshOutputs op inputField value keys).run state).2
  cases cached.all Option.isSome
  · exact encodeFreshOutputs_preservesOutputCapacityFrame op inputField value keys outputCount state
  · exact OutputCapacityFrame.refl state

private theorem encodeForeign_preservesOutputCapacityFrame (kind : Foreign.Kind) (value : String) :
    PreservesOutputCapacityFrame (encodeForeign kind value) := by
  unfold encodeForeign
  apply encodeCachedOutputs_preservesOutputCapacityFrame
  exact encodeInstruction_outputDefinitions value

private theorem intoCoordinatesInstruction_outputDefinitions
    (point x y : String) :
    Native.outputDefinitionsInInstruction
      (instruction "into_coordinates" [("point", toJson point),
        ("outputs", toJson [x, y])]) = 2 := by
  have opcodeOk : Native.stringField
      (instruction "into_coordinates" [("point", toJson point),
        ("outputs", toJson [x, y])]) "op" = .ok "into_coordinates" := by
    simp [Native.stringField, instruction, Json.getObjVal?, Json.mkObj, Json.getStr?,
      Std.TreeMap.Raw.get?_eq_getElem?, Std.TreeMap.Raw.getElem?_ofList_of_mem,
      Lean.ToJson.toJson]
    rfl
  have outputsOk : Native.arrayField
      (instruction "into_coordinates" [("point", toJson point),
        ("outputs", toJson [x, y])]) "outputs" =
      .ok #[Json.str x, Json.str y] := by
    simp [Native.arrayField, instruction, Json.getObjVal?, Json.mkObj, Json.getArr?,
      Std.TreeMap.Raw.get?_eq_getElem?, Std.TreeMap.Raw.getElem?_ofList_of_mem,
      Lean.ToJson.toJson, Lean.List.toJson, Lean.Array.toJson]
    rfl
  simp [Native.outputDefinitionsInInstruction, opcodeOk, outputsOk, Except.toOption]

private theorem lowerJubjubScalarFromNative_preservesOutputCapacityFrame (native : String) :
    PreservesOutputCapacityFrame (lowerJubjubScalarFromNative native) := by
  intro state
  cases hit : state.expressions.lookup ("jubjub_scalar_from_native", [native], none) with
  | some output =>
    simp [lowerJubjubScalarFromNative, hit]
    exact OutputCapacityFrame.refl _
  | none =>
    simp [lowerJubjubScalarFromNative, hit, fresh, emit,
      StateT.run_bind, StateT.run_get, StateT.run_modify, StateT.run_set,
]
    change OutputCapacityFrame state
      {state with
        next := state.next + 1
        instructions := state.instructions.push (instruction "jubjub_scalar_from_native"
          [("native", toJson native),
            ("output", toJson ("%v" ++ state.next.repr))])
        expressions := (("jubjub_scalar_from_native", [native], none),
          "%v" ++ state.next.repr) :: state.expressions}
    let fields := [("native", toJson native),
      ("output", toJson ("%v" ++ state.next.repr))]
    have opcodeOk : Native.stringField
        (instruction "jubjub_scalar_from_native" fields) "op" =
          .ok "jubjub_scalar_from_native" := by
      simp [fields, Native.stringField, instruction, Json.getObjVal?, Json.mkObj, Json.getStr?,
        Std.TreeMap.Raw.get?_eq_getElem?, Std.TreeMap.Raw.getElem?_ofList_of_mem,
        Lean.ToJson.toJson]
      rfl
    have outputOk : (Native.stringField (instruction "jubjub_scalar_from_native" fields)
        "output").isOk = true := by
      simp [fields, Native.stringField, instruction, Json.getObjVal?, Json.mkObj, Json.getStr?,
        Std.TreeMap.Raw.get?_eq_getElem?, Lean.ToJson.toJson]
      rfl
    have outputCount := instruction_scalarOutputDefinitions "jubjub_scalar_from_native"
      fields opcodeOk ⟨by decide, by decide, by decide⟩ outputOk
    refine OutputCapacityFrame.of_instruction_push _ (by simp) rfl ?_
    rw [outputCount]
    simp

private theorem lowerJubjubScalarToNative_preservesOutputCapacityFrame (scalar : String) :
    PreservesOutputCapacityFrame (lowerJubjubScalarToNative scalar) := by
  intro state
  cases hit : state.expressions.lookup ("encode_jubjub_scalar", [scalar], none) with
  | some output =>
    simp [lowerJubjubScalarToNative, hit]
    exact OutputCapacityFrame.refl _
  | none =>
    simp [lowerJubjubScalarToNative, hit, fresh, emit,
      StateT.run_bind, StateT.run_get, StateT.run_modify, StateT.run_set,
      toJson, List.toJson, Array.toJson]
    change OutputCapacityFrame state
      {state with
        next := state.next + 1
        instructions := state.instructions.push (instruction "encode"
          [("input", Json.str scalar),
            ("outputs", Json.arr #[Json.str ("%v" ++ state.next.repr)])])
        expressions := (("encode_jubjub_scalar", [scalar], none),
          "%v" ++ state.next.repr) :: state.expressions}
    have outputCount := encodeInstruction_outputDefinitions scalar
      ["%v" ++ state.next.repr]
    refine OutputCapacityFrame.of_instruction_push _ (by simp) rfl ?_
    have emittedCount : Native.outputDefinitionsInInstruction
        (instruction "encode"
          [("input", Json.str scalar),
            ("outputs", Json.arr #[Json.str ("%v" ++ state.next.repr)])]) = 1 := by
      simpa [toJson, List.toJson, Array.toJson] using outputCount
    rw [emittedCount]
    simp

private theorem lowerPointCoordinates_preservesOutputCapacityFrame (point : String) :
    PreservesOutputCapacityFrame (lowerPointCoordinates point) := by
  intro state
  cases hit : state.pointCoordinates.lookup point with
  | some outputs =>
    simp [lowerPointCoordinates, hit]
    exact OutputCapacityFrame.refl _
  | none =>
    simp [lowerPointCoordinates, hit, fresh, emit,
      StateT.run_bind, StateT.run_get, StateT.run_modify, StateT.run_set,
      toJson, List.toJson, Array.toJson]
    change OutputCapacityFrame state
      {state with
        next := state.next + 1 + 1
        instructions := state.instructions.push (instruction "into_coordinates"
          [("point", Json.str point),
            ("outputs", Json.arr #[Json.str ("%v" ++ state.next.repr),
              Json.str ("%v" ++ (state.next + 1).repr)])])
        pointCoordinates := (point,
          ("%v" ++ state.next.repr, "%v" ++ (state.next + 1).repr)) ::
          state.pointCoordinates}
    have outputCount := intoCoordinatesInstruction_outputDefinitions point
      ("%v" ++ state.next.repr) ("%v" ++ (state.next + 1).repr)
    refine OutputCapacityFrame.of_instruction_push _ ?_ rfl ?_
    · change state.next ≤ state.next + 2
      omega
    have emittedCount : Native.outputDefinitionsInInstruction
        (instruction "into_coordinates"
          [("point", Json.str point),
            ("outputs", Json.arr #[Json.str ("%v" ++ state.next.repr),
              Json.str ("%v" ++ (state.next + 1).repr)])]) = 2 := by
      simpa [toJson, List.toJson, Array.toJson] using outputCount
    change state.next + 1 + 1 - state.next ≤ _
    rw [emittedCount]
    omega

private theorem lowerPointFromCoordinatesFresh_preservesOutputCapacityFrame (x y : String) :
    PreservesOutputCapacityFrame (lowerPointFromCoordinatesFresh x y) := by
  intro state
  simp [lowerPointFromCoordinatesFresh, fresh, emit,
    StateT.run_bind, StateT.run_get, StateT.run_modify, StateT.run_set,
    toJson, List.toJson, Array.toJson]
  change OutputCapacityFrame state
    {state with
      next := state.next + 1
      instructions := state.instructions.push (instruction "from_coordinates"
        [("inputs", Json.arr #[Json.str x, Json.str y]),
          ("output", Json.str ("%v" ++ state.next.repr))])}
  let fields := [("inputs", toJson [x, y]),
    ("output", toJson ("%v" ++ state.next.repr))]
  have opcodeOk : Native.stringField (instruction "from_coordinates" fields) "op" =
      .ok "from_coordinates" := by
    simp [fields, Native.stringField, instruction, Json.getObjVal?, Json.mkObj, Json.getStr?,
      Std.TreeMap.Raw.get?_eq_getElem?, Std.TreeMap.Raw.getElem?_ofList_of_mem,
      Lean.ToJson.toJson]
    rfl
  have outputOk : (Native.stringField (instruction "from_coordinates" fields)
      "output").isOk = true := by
    simp [fields, Native.stringField, instruction, Json.getObjVal?, Json.mkObj, Json.getStr?,
      Std.TreeMap.Raw.get?_eq_getElem?, Lean.ToJson.toJson, List.toJson, Array.toJson]
    rfl
  have outputCount := instruction_scalarOutputDefinitions "from_coordinates" fields
    opcodeOk ⟨by decide, by decide, by decide⟩ outputOk
  have emittedCount : Native.outputDefinitionsInInstruction
      (instruction "from_coordinates"
        [("inputs", Json.arr #[Json.str x, Json.str y]),
          ("output", Json.str ("%v" ++ state.next.repr))]) = 1 := by
    simpa [fields, toJson, List.toJson, Array.toJson] using outputCount
  refine OutputCapacityFrame.of_instruction_push _ (by simp) rfl ?_
  rw [emittedCount]
  simp

private theorem lowerPointFromCoordinatesFinish_preservesOutputCapacityFrame
    (key : ExpressionKey) (x y point : String) :
    PreservesOutputCapacityFrame (lowerPointFromCoordinatesFinish key x y point) := by
  unfold lowerPointFromCoordinatesFinish
  apply bind_preservesOutputCapacityFrame _ _ (lowerPointCoordinates_preservesOutputCapacityFrame point)
  intro coordinates
  apply bind_preservesOutputCapacityFrame _ _ (emit_preservesOutputCapacityFrame _ _)
  intro ignored
  apply bind_preservesOutputCapacityFrame _ _ (emit_preservesOutputCapacityFrame _ _)
  intro ignored
  apply bind_preservesOutputCapacityFrame _ _
    (modify_preservesOutputCapacityFrame (fun state =>
      {state with expressions := (key, point) :: state.expressions})
      (fun _ => rfl) (fun _ => rfl))
  intro ignored
  exact pure_preservesOutputCapacityFrame _

private theorem lowerPointFromCoordinates_preservesOutputCapacityFrame (x y : String) :
    PreservesOutputCapacityFrame (lowerPointFromCoordinates x y) := by
  intro state
  cases hit : state.expressions.lookup ("from_coordinates_jubjub", [x, y], none) with
  | some point =>
    simp [lowerPointFromCoordinates, hit]
    exact OutputCapacityFrame.refl _
  | none =>
    have result := bind_preservesOutputCapacityFrame
      (lowerPointFromCoordinatesFresh x y)
      (fun point => lowerPointFromCoordinatesFinish
        ("from_coordinates_jubjub", [x, y], none) x y point)
      (lowerPointFromCoordinatesFresh_preservesOutputCapacityFrame x y)
      (fun point => lowerPointFromCoordinatesFinish_preservesOutputCapacityFrame
        ("from_coordinates_jubjub", [x, y], none) x y point)
    simpa [lowerPointFromCoordinates, hit, StateT.run_bind, StateT.run_get] using
      result state

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

theorem constrainUnsigned_preservesOutputCapacityFrame (maximum : Nat)
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

theorem constrainType_preservesOutputCapacityFrame (ty : Ty) (value : String) :
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

private theorem lowerInputRead_preservesOutputCapacityFrame (op : String) (raw : Bool)
    (identifier : String) (ty : Json := nativeType) :
    PreservesOutputCapacityFrame (lowerInputRead op raw identifier ty) := by
  cases raw
  · simpa [lowerInputRead] using emit_preservesOutputCapacityFrame op
      [("guard", Json.null), ("type", ty), ("output", toJson identifier)]
  · simp [lowerInputRead]
    exact pure_preservesOutputCapacityFrame ()

private theorem lowerInputRequirement_preservesOutputCapacityFrame (op : String)
    (raw : Bool) (spec : Native.InputRequirement) :
    PreservesOutputCapacityFrame (lowerInputRequirement op raw spec) := by
  unfold lowerInputRequirement
  apply bind_preservesOutputCapacityFrame _ _
    (lowerInputRead_preservesOutputCapacityFrame op raw spec.identifier)
  intro _
  exact constrainType_preservesOutputCapacityFrame spec.ty spec.identifier

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

private def lowerToBytes32Bytes (value : String) : LowerM String := do
  let bytesKey : ExpressionKey := ("to_bytes", [value], none)
  match (← get).expressions.lookup bytesKey with
    | some existing => pure existing
    | none => do
      let output ← fresh
      emit "to_bytes" [("input", toJson value), ("output", toJson output)]
      modify fun state => {state with expressions := (bytesKey, output) :: state.expressions}
      pure output

private def lowerToBytes32 (value : String) : LowerM (String × String) := do
  let bytes ← lowerToBytes32Bytes value
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

private theorem listMapM_preservesOutputCapacityFrame_of_mem (items : List α)
    (operation : α → LowerM β)
    (preserves : ∀ item ∈ items, PreservesOutputCapacityFrame (operation item)) :
    PreservesOutputCapacityFrame (items.mapM operation) := by
  induction items with
  | nil => exact pure_preservesOutputCapacityFrame []
  | cons item rest ih =>
    simp only [List.mapM_cons]
    apply bind_preservesOutputCapacityFrame _ _ (preserves item (by simp))
    intro output
    apply bind_preservesOutputCapacityFrame _ _
      (ih (fun value member => preserves value (List.mem_cons_of_mem _ member)))
    intro outputs
    exact pure_preservesOutputCapacityFrame (output :: outputs)

private theorem listMapM_preservesOutputCapacityFrame (items : List α)
    (operation : α → LowerM β) (preserves : ∀ item, PreservesOutputCapacityFrame (operation item)) :
    PreservesOutputCapacityFrame (items.mapM operation) :=
  listMapM_preservesOutputCapacityFrame_of_mem items operation (fun item _ => preserves item)

private theorem packBytesRecAux_preservesOutputCapacityFrame (zeroCount : Nat)
    (bytes : List String) :
    PreservesOutputCapacityFrame (packBytesRecAux zeroCount bytes) := by
  induction bytes generalizing zeroCount with
  | nil =>
    rw [packBytesRecAux.eq_1]
    exact pure_preservesOutputCapacityFrame "0x00"
  | cons byte rest ih =>
    rw [packBytesRecAux.eq_2]
    by_cases zeroByte : byte == "0x00"
    · simp [zeroByte]
      exact ih (zeroCount + 1)
    · simp [zeroByte]
      apply bind_preservesOutputCapacityFrame _ _ (ih 0)
      intro suffix
      by_cases zeroSuffix : suffix == "0x00"
      · have suffixEq : suffix = "0x00" := eq_of_beq zeroSuffix
        simp [suffixEq]
        exact scalePackedBytes_preservesOutputCapacityFrame _ byte
      · have suffixNe : suffix ≠ "0x00" := by
          intro equal
          apply zeroSuffix
          simp [equal]
        simp [suffixNe]
        apply bind_preservesOutputCapacityFrame _ _
          (ordinaryBinary_preservesOutputCapacityFrame "mul" "0x0001" suffix
            ⟨by decide, by decide, by decide⟩)
        intro shifted
        apply bind_preservesOutputCapacityFrame _ _
          (binaryAdd_preservesOutputCapacityFrame byte shifted)
        intro packed
        exact scalePackedBytes_preservesOutputCapacityFrame _ packed

private theorem packBytesRec_preservesOutputCapacityFrame (bytes : List String) :
    PreservesOutputCapacityFrame (packBytesRec bytes) := by
  simpa [packBytesRec] using packBytesRecAux_preservesOutputCapacityFrame 0 bytes

private theorem packBytes_preservesOutputCapacityFrame (bytes : List String) :
    PreservesOutputCapacityFrame (packBytes bytes) := by
  unfold packBytes
  split
  · exact pure_preservesOutputCapacityFrame _
  · exact packBytesRec_preservesOutputCapacityFrame bytes

private theorem rejectThenPure_preservesOutputCapacityFrame (message : String) (value : α) :
    PreservesOutputCapacityFrame (do rejectLowering message; pure value) := by
  unfold rejectLowering
  apply bind_preservesOutputCapacityFrame _ _ (emit_preservesOutputCapacityFrame _ _)
  intro _
  exact pure_preservesOutputCapacityFrame value

private theorem byteChunks_preservesOutputCapacityFrame (length : Nat) (bytes : ByteOperands) :
    PreservesOutputCapacityFrame (byteChunks length bytes) := by
  intro state
  cases packed : bytes.packed with
  | false =>
    by_cases count : bytes.values.length = length
    · have mapped := listMapM_preservesOutputCapacityFrame
        (List.range (Noctium.bytesChunkCount length))
        (fun index => packBytes ((bytes.values.drop (index * 31)).take 31))
        (by intro index; exact packBytes_preservesOutputCapacityFrame _)
      simpa [byteChunks, packed, count] using mapped state
    · simpa [byteChunks, packed, count] using
        (rejectThenPure_preservesOutputCapacityFrame "byte leaf count mismatch"
          ([] : List String) state)
  | true =>
    by_cases count : bytes.values.length = Noctium.bytesChunkCount length
    · simpa [byteChunks, packed, count] using
        (pure_preservesOutputCapacityFrame bytes.values state)
    · simpa [byteChunks, packed, count] using
        (rejectThenPure_preservesOutputCapacityFrame "byte chunk count mismatch"
          bytes.values state)

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
  let outputs ← encodeCachedOutputs "bytes_into_natives" "bytes" bytes keys
  pure {values := outputs, packed := true}

private theorem encodeFixedBytes_preservesOutputCapacityFrame (length : Nat) (bytes : String) :
    PreservesOutputCapacityFrame (encodeFixedBytes length bytes) := by
  unfold encodeFixedBytes
  split
  · apply bind_preservesOutputCapacityFrame _ _
      (encodeBytes32_preservesOutputCapacityFrame bytes)
    intro result
    exact pure_preservesOutputCapacityFrame _
  · apply bind_preservesOutputCapacityFrame _ _
      (encodeCachedOutputs_preservesOutputCapacityFrame _ _ _ _
        (bytesIntoNativesInstruction_outputDefinitions bytes))
    intro result
    exact pure_preservesOutputCapacityFrame _

private def lowerAlignedDigestFresh (algorithm : String) (alignment : Json)
    (operands : List String) (key : ExpressionKey) : LowerM String := do
  let output ← fresh
  emit algorithm [
    ("alignment", alignment),
    ("inputs", toJson operands),
    ("output", toJson output)]
  modify fun state => {state with expressions := (key, output) :: state.expressions}
  pure output

private theorem lowerAlignedDigestFresh_preservesOutputCapacityFrame (algorithm : String)
    (alignment : Json) (operands : List String) (key : ExpressionKey)
    (ordinary : algorithm ≠ "encode" ∧ algorithm ≠ "bytes_into_natives" ∧
      algorithm ≠ "into_coordinates") :
    PreservesOutputCapacityFrame (lowerAlignedDigestFresh algorithm alignment operands key) := by
  intro state
  simp [lowerAlignedDigestFresh, fresh, emit, StateT.run_bind, StateT.run_get,
    StateT.run_modify, StateT.run_set, toJson, List.toJson, Array.toJson]
  let output := "%v" ++ state.next.repr
  let fields := [
    ("alignment", alignment),
    ("inputs", toJson operands),
    ("output", toJson output)]
  let emitted := instruction algorithm
    [("alignment", alignment), ("inputs", Json.arr (operands.map Json.str).toArray),
      ("output", Json.str output)]
  change OutputCapacityFrame state
    {state with
      next := state.next + 1
      instructions := state.instructions.push emitted
      expressions := (key, output) :: state.expressions}
  have opcodeOk : Native.stringField (instruction algorithm fields) "op" = .ok algorithm := by
    simp [fields, Native.stringField, instruction, Json.getObjVal?, Json.mkObj, Json.getStr?,
      Std.TreeMap.Raw.get?_eq_getElem?, Std.TreeMap.Raw.getElem?_ofList_of_mem,
      Lean.ToJson.toJson]
    rfl
  have outputOk : (Native.stringField (instruction algorithm fields) "output").isOk = true := by
    simp [fields, Native.stringField, instruction, Json.getObjVal?, Json.mkObj, Json.getStr?,
      Std.TreeMap.Raw.get?_eq_getElem?, Lean.ToJson.toJson]
    rfl
  have outputCount := instruction_scalarOutputDefinitions algorithm fields opcodeOk ordinary outputOk
  have emittedCount : Native.outputDefinitionsInInstruction emitted = 1 := by
    simpa [emitted, fields, output, toJson, List.toJson, Array.toJson] using outputCount
  refine OutputCapacityFrame.of_instruction_push emitted ?_ rfl ?_
  · change state.next ≤ state.next + 1
    omega
  rw [emittedCount]
  change state.next + 1 - state.next ≤ 1
  omega

private def lowerAlignedDigest (algorithm : String) (outputLength : Nat)
    (alignment : Json) (operands : List String) (key : ExpressionKey) : LowerM ByteOperands := do
  let output ← match (← get).expressions.lookup key with
    | some existing => pure existing
    | none => lowerAlignedDigestFresh algorithm alignment operands key
  encodeFixedBytes outputLength output

private theorem lowerAlignedDigest_preservesOutputCapacityFrame (algorithm : String)
    (outputLength : Nat) (alignment : Json) (operands : List String) (key : ExpressionKey)
    (ordinary : algorithm ≠ "encode" ∧ algorithm ≠ "bytes_into_natives" ∧
      algorithm ≠ "into_coordinates") :
    PreservesOutputCapacityFrame (lowerAlignedDigest algorithm outputLength alignment operands key) := by
  intro state
  cases hit : state.expressions.lookup key with
  | some output =>
    have frame := encodeFixedBytes_preservesOutputCapacityFrame outputLength output state
    simpa [lowerAlignedDigest, hit, StateT.run_bind, StateT.run_get] using frame
  | none =>
    have frame : PreservesOutputCapacityFrame (do
      let output ← lowerAlignedDigestFresh algorithm alignment operands key
      encodeFixedBytes outputLength output) := by
      apply bind_preservesOutputCapacityFrame _ _
        (lowerAlignedDigestFresh_preservesOutputCapacityFrame algorithm alignment operands key ordinary)
      intro output
      exact encodeFixedBytes_preservesOutputCapacityFrame outputLength output
    simpa [lowerAlignedDigest, hit, StateT.run_bind, StateT.run_get] using (frame state)

/-- Hash one fixed byte preimage. FAB consumes chunks in the reverse of Encode
order. Empty preimages use empty alignment and no operands, never Bytes0. -/
private def lowerFixedByteHash (algorithm : String) (length outputLength : Nat)
    (value : ByteOperands) : LowerM ByteOperands := do
  let operands := (← byteChunks length value).reverse
  let alignment := if length == 0 then Json.arr #[] else Json.arr #[Json.mkObj [
    ("tag", toJson ("atom" : String)),
    ("value", Json.mkObj [("tag", toJson ("bytes" : String)), ("length", toJson length)])]]
  lowerAlignedDigest algorithm outputLength alignment operands (algorithm, operands, some length)

private theorem lowerFixedByteHash_preservesOutputCapacityFrame
    (algorithm : String) (length outputLength : Nat) (value : ByteOperands)
    (ordinary : algorithm ≠ "encode" ∧ algorithm ≠ "bytes_into_natives" ∧
      algorithm ≠ "into_coordinates") :
    PreservesOutputCapacityFrame (lowerFixedByteHash algorithm length outputLength value) := by
  unfold lowerFixedByteHash
  apply bind_preservesOutputCapacityFrame _ _ (byteChunks_preservesOutputCapacityFrame length value)
  intro chunks
  exact lowerAlignedDigest_preservesOutputCapacityFrame algorithm outputLength _ _ _ ordinary

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

private def lowerByteAtFromBytes (index : Nat) (bytes : String) : LowerM String := do
  let key : ExpressionKey := ("nth", [bytes], some index)
  let byte ← match (← get).expressions.lookup key with
    | some existing => pure existing
    | none => do
      let output ← fresh
      emit "nth" [("bytes", toJson bytes), ("index", toJson index), ("output", toJson output)]
      modify fun state => {state with expressions := (key, output) :: state.expressions}
      pure output
  encodeByte byte

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
  lowerByteAtFromBytes index input

private def lowerRawFixedByteAt (length index : Nat) (bytes : String) : LowerM String := do
  if index ≥ length then
    rejectLowering "byte index is out of range"
    return "0x00"
  lowerByteAtFromBytes index bytes

/-- Projecting a fixed Bytes32 byte from its reversal maps to the source byte
at the mirrored index. Evaluate the byte operand before checking the index, as
the ordinary `byteAt` lowering does. -/
private def lowerReversedBytes32ByteAt (index : Nat) (value : ByteOperands) : LowerM String := do
  if index ≥ 32 then
    rejectLowering "byte index is out of range"
    return "0x00"
  lowerFixedByteAt 32 (31 - index) value

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

private theorem alignedBytes32Fields_preservesOutputCapacityFrame (values : List String) :
    PreservesOutputCapacityFrame (alignedBytes32Fields values) := by
  unfold alignedBytes32Fields
  split
  · apply bind_preservesOutputCapacityFrame _ _ (packBytes_preservesOutputCapacityFrame (values.take 31))
    intro low31
    exact pure_preservesOutputCapacityFrame (values[31]!, low31)
  · exact pure_preservesOutputCapacityFrame (values[1]!, values[0]!)
  · exact rejectThenPure_preservesOutputCapacityFrame
      "Bytes32 source has wrong aligned encoding" ("0x00", "0x00")

private theorem alignedBytes32Value_preservesOutputCapacityFrame
    (source : Expr (.bytes 32)) (values : List String) :
    PreservesOutputCapacityFrame (alignedBytes32Value source values) := by
  unfold alignedBytes32Value
  split
  · split
    · exact pure_preservesOutputCapacityFrame _
    · exact alignedBytes32Fields_preservesOutputCapacityFrame values
  · exact alignedBytes32Fields_preservesOutputCapacityFrame values

private def lowerInputReads (op : String) (raw : Bool)
    (identifiers : List String) : LowerM Unit := do
  for identifier in identifiers do
    lowerInputRead op raw identifier

private theorem lowerInputReads_preservesOutputCapacityFrame (op : String) (raw : Bool)
    (identifiers : List String) :
    PreservesOutputCapacityFrame (lowerInputReads op raw identifiers) := by
  unfold lowerInputReads
  apply forIn_preservesOutputCapacityFrame
  intro identifier accumulator
  apply bind_preservesOutputCapacityFrame _ _
    (lowerInputRead_preservesOutputCapacityFrame op raw identifier)
  intro ignored
  exact pure_preservesOutputCapacityFrame _

private def insertAlias (name value : String) : LowerM Unit := do
  modify fun state => {state with aliases := (name, value) :: state.aliases}
  pure ()

private theorem insertAlias_preservesOutputCapacityFrame (name value : String) :
    PreservesOutputCapacityFrame (insertAlias name value) := by
  intro state
  change OutputCapacityFrame state {state with aliases := (name, value) :: state.aliases}
  exact OutputCapacityFrame.of_sameInstructions rfl rfl

private def insertByteAlias (name : String) (value : ByteOperands) : LowerM Unit := do
  modify fun state => {state with byteAliases := (name, value) :: state.byteAliases}
  pure ()

private theorem insertByteAlias_preservesOutputCapacityFrame (name : String)
    (value : ByteOperands) : PreservesOutputCapacityFrame (insertByteAlias name value) := by
  intro state
  change OutputCapacityFrame state {state with byteAliases := (name, value) :: state.byteAliases}
  exact OutputCapacityFrame.of_sameInstructions rfl rfl

def lowerByteInput (input : Input) (raw : Bool := false) : LowerM Unit := do
  let op := if input.visibility == .«public» then "public_input" else "private_input"
  let read (identifier : String) (ty : Json := nativeType) :=
    lowerInputRead op raw identifier ty
  match raw, input.ty with
  | true, .bytes _ => do
      let requirements := Native.Input.callArgumentRequirements input
      lowerInputRequirements op true requirements
      insertByteAlias input.name
        {values := (requirements.map (·.identifier)).reverse, packed := true}
  | false, .bytes _ => do
    let requirements := Native.Input.requirements input
    lowerInputRequirements op false requirements
    let values := requirements.map (·.identifier)
    let packed := input.visibility == .«public»
    insertByteAlias input.name {values := if packed then values.reverse else values, packed}
  | _, .foreign kind => do
    let output := "%input_" ++ input.name
    read output (toJson kind.nativeName)
    insertAlias input.name output
  | _, .opaqueBytes | _, .opaqueString => do
    let output := "%input_" ++ input.name
    read output
    insertAlias input.name output
  | _, .jubjubScalar => do
    let native := input.nativeIdentifiers.head!
    read native
    let scalar ← lowerJubjubScalarFromNative native
    let encoded ← lowerJubjubScalarToNative scalar
    emit "constrain_eq" [("a", toJson native), ("b", toJson encoded)]
    insertAlias input.name scalar
  | _, .jubjubPoint => do
    let x := input.nativeIdentifiers[0]!
    let y := input.nativeIdentifiers[1]!
    lowerInputReads op raw [x, y]
    let point ← lowerPointFromCoordinates x y
    insertAlias input.name point
  | _, _ =>
    let output := input.nativeIdentifiers.head!
    read output
    constrainType input.ty output

theorem lowerByteInput_preservesOutputCapacityFrame (input : Input) (raw : Bool) :
    PreservesOutputCapacityFrame (lowerByteInput input raw) := by
  cases input with
  | mk name ty visibility span =>
    let source : Input := {name, ty, visibility, span}
    let op := if visibility == .«public» then "public_input" else "private_input"
    cases ty with
    | native =>
      let identifier := source.nativeIdentifiers.head!
      have h := bind_preservesOutputCapacityFrame
        (lowerInputRead op raw identifier)
        (fun _ => constrainType .native identifier)
        (lowerInputRead_preservesOutputCapacityFrame op raw identifier)
        (fun _ => constrainType_preservesOutputCapacityFrame .native identifier)
      simpa [lowerByteInput, source, op] using h
    | bool =>
      let identifier := source.nativeIdentifiers.head!
      have h := bind_preservesOutputCapacityFrame
        (lowerInputRead op raw identifier)
        (fun _ => constrainType .bool identifier)
        (lowerInputRead_preservesOutputCapacityFrame op raw identifier)
        (fun _ => constrainType_preservesOutputCapacityFrame .bool identifier)
      simpa [lowerByteInput, source, op] using h
    | uint maximum =>
      let identifier := source.nativeIdentifiers.head!
      have h := bind_preservesOutputCapacityFrame
        (lowerInputRead op raw identifier)
        (fun _ => constrainType (.uint maximum) identifier)
        (lowerInputRead_preservesOutputCapacityFrame op raw identifier)
        (fun _ => constrainType_preservesOutputCapacityFrame (.uint maximum) identifier)
      simpa [lowerByteInput, source, op] using h
    | bytes length =>
      cases raw with
      | false =>
        let requirements := Native.Input.requirements source
        let value : ByteOperands :=
          {values := if visibility == .«public» then
              (requirements.map (·.identifier)).reverse else requirements.map (·.identifier),
            packed := visibility == .«public»}
        have h := bind_preservesOutputCapacityFrame
          (lowerInputRequirements op false requirements)
          (fun _ => insertByteAlias name value)
          (lowerInputRequirements_preservesOutputCapacityFrame op false requirements)
          (fun _ => insertByteAlias_preservesOutputCapacityFrame name value)
        simpa [lowerByteInput, source, op, requirements, value] using h
      | true =>
        let requirements := Native.Input.callArgumentRequirements source
        let value : ByteOperands :=
          {values := (requirements.map (·.identifier)).reverse, packed := true}
        have h := bind_preservesOutputCapacityFrame
          (lowerInputRequirements op true requirements)
          (fun _ => insertByteAlias name value)
          (lowerInputRequirements_preservesOutputCapacityFrame op true requirements)
          (fun _ => insertByteAlias_preservesOutputCapacityFrame name value)
        simpa [lowerByteInput, source, op, requirements, value] using h
    | opaqueBytes | opaqueString =>
      let identifier := "%input_" ++ name
      have h := bind_preservesOutputCapacityFrame
        (lowerInputRead op raw identifier)
        (fun _ => insertAlias name identifier)
        (lowerInputRead_preservesOutputCapacityFrame op raw identifier)
        (fun _ => insertAlias_preservesOutputCapacityFrame name identifier)
      simpa [lowerByteInput, source, op] using h
    | foreign kind =>
      let identifier := "%input_" ++ name
      have h := bind_preservesOutputCapacityFrame
        (lowerInputRead op raw identifier (toJson kind.nativeName))
        (fun _ => insertAlias name identifier)
        (lowerInputRead_preservesOutputCapacityFrame op raw identifier (toJson kind.nativeName))
        (fun _ => insertAlias_preservesOutputCapacityFrame name identifier)
      simpa [lowerByteInput, source, op] using h
    | jubjubScalar =>
      let identifier := source.nativeIdentifiers.head!
      have bridge : PreservesOutputCapacityFrame (do
          let scalar ← lowerJubjubScalarFromNative identifier
          let encoded ← lowerJubjubScalarToNative scalar
          emit "constrain_eq" [("a", toJson identifier), ("b", toJson encoded)]
          insertAlias name scalar) := by
        apply bind_preservesOutputCapacityFrame _ _
          (lowerJubjubScalarFromNative_preservesOutputCapacityFrame identifier)
        intro scalar
        apply bind_preservesOutputCapacityFrame _ _
          (lowerJubjubScalarToNative_preservesOutputCapacityFrame scalar)
        intro encoded
        apply bind_preservesOutputCapacityFrame _ _ (emit_preservesOutputCapacityFrame _ _)
        intro ignored
        exact insertAlias_preservesOutputCapacityFrame name scalar
      have h := bind_preservesOutputCapacityFrame
        (lowerInputRead op raw identifier)
        (fun _ => do
          let scalar ← lowerJubjubScalarFromNative identifier
          let encoded ← lowerJubjubScalarToNative scalar
          emit "constrain_eq" [("a", toJson identifier), ("b", toJson encoded)]
          insertAlias name scalar)
        (lowerInputRead_preservesOutputCapacityFrame op raw identifier)
        (fun _ => bridge)
      simpa [lowerByteInput, source, op, Input.nativeIdentifiers, identifier] using h
    | jubjubPoint =>
      let identifiers := source.nativeIdentifiers
      have bridge : PreservesOutputCapacityFrame (do
          let point ← lowerPointFromCoordinates identifiers[0]! identifiers[1]!
          insertAlias name point) := by
        apply bind_preservesOutputCapacityFrame _ _
          (lowerPointFromCoordinates_preservesOutputCapacityFrame identifiers[0]! identifiers[1]!)
        intro point
        exact insertAlias_preservesOutputCapacityFrame name point
      have h := bind_preservesOutputCapacityFrame
        (lowerInputReads op raw identifiers)
        (fun _ => do
          let point ← lowerPointFromCoordinates identifiers[0]! identifiers[1]!
          insertAlias name point)
        (lowerInputReads_preservesOutputCapacityFrame op raw identifiers)
        (fun _ => bridge)
      simpa [lowerByteInput, source, op, Input.nativeIdentifiers, identifiers,
        List.head!] using h

theorem lowerByteInput_fixedBytes_preservesOutputCapacityFrame (name : String)
    (length : Nat) (visibility : Visibility) (raw : Bool) (span : SourceSpan := {}) :
    PreservesOutputCapacityFrame
      (lowerByteInput {name, ty := .bytes length, visibility, span} raw) :=
  lowerByteInput_preservesOutputCapacityFrame _ raw

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
  | .select condition yes no => do
    let bit ← lowerExpr condition
    let a ← lowerOpaqueBytes yes
    let b ← lowerOpaqueBytes no
    selectOperands bit a b
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
  | .select condition yes no => do
    let bit ← lowerExpr condition
    let a ← lowerOpaqueString yes
    let b ← lowerOpaqueString no
    selectOperands bit a b
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
    let values ← (yes.zip no).mapM fun (yes, no) => selectOperands condition yes no
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
  | .bytesAt (length := 32) (.toBytes32 value) index => do
    let input ← lowerExpr value
    if Native.isWidenedByte value then
      lowerFixedByteAt 32 index {values := input :: List.replicate 31 "0x00"}
    else do
      let bytes ← lowerToBytes32Bytes input
      lowerRawFixedByteAt 32 index bytes
  | .bytesAt (length := 32) (.reverseBytes32 value) index => do
    let bytes ← lowerBytes value
    lowerReversedBytes32ByteAt index bytes
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
  | .letE (source := source) name value body => do
    let value ← match source, value with
      | .opaqueBytes, value => lowerOpaqueBytes value
      | .opaqueString, value => lowerOpaqueString value
      | _, value => lowerExpr value
    let aliases := (← get).aliases
    modify fun s => {s with aliases := (name, value) :: aliases}
    let result ← lowerExpr body
    modify fun s => {s with aliases := aliases}
    pure result
  | .assertE condition body => do
    emit "assert" [("cond", toJson (← lowerExpr condition))]
    lowerExpr body
  | .disclose _ value => lowerExpr value
  | .eq (ty := .opaqueBytes) a b => do binary "test_eq" (← lowerOpaqueBytes a) (← lowerOpaqueBytes b)
  | .eq (ty := .opaqueString) a b => do binary "test_eq" (← lowerOpaqueString a) (← lowerOpaqueString b)
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

/-- SHA-512 allocates from the actual digest and packed outputs, for any
fixed-width preimage whose lowering has an output capacity frame. -/
theorem lowerBytes_sha512_preservesOutputCapacityFrame {length : Nat}
    (value : Expr (.bytes length))
    (valueFrame : PreservesOutputCapacityFrame (lowerBytes value)) :
    PreservesOutputCapacityFrame (lowerBytes (.sha512 value)) := by
  simp only [lowerBytes]
  apply bind_preservesOutputCapacityFrame _ _ valueFrame
  intro operand
  exact lowerFixedByteHash_preservesOutputCapacityFrame "sha512" length 64 operand
    ⟨by decide, by decide, by decide⟩

/-- Lowering a fixed-byte literal allocates no SSA names, including the
zero-width literal consumed by the circuit output preflight. -/
theorem lowerBytes_literal_preservesOutputCapacityFrame {length : Nat} (values : List Nat) :
    PreservesOutputCapacityFrame (lowerBytes (Expr.bytesLiteral length values)) := by
  intro state
  simp [lowerBytes, StateT.run_pure]
  exact OutputCapacityFrame.refl state

theorem lowerBytes_literal32_preservesOutputCapacityFrame (values : List Nat) :
    PreservesOutputCapacityFrame (lowerBytes (Expr.bytes32Literal values)) := by
  intro state
  simp [lowerBytes, StateT.run_pure]
  exact OutputCapacityFrame.refl state

theorem lowerBytes_ref_preservesOutputCapacityFrame {length : Nat} (name : String) :
    PreservesOutputCapacityFrame (lowerBytes (Expr.ref name : Expr (.bytes length))) := by
  simp only [lowerBytes]
  have getFrame : PreservesOutputCapacityFrame
      (get : StateM LowerState LowerState) := OutputCapacityFrame.refl
  apply bind_preservesOutputCapacityFrame _ _ getFrame
  intro snapshot
  cases hit : snapshot.byteAliases.lookup name with
  | some operands =>
    simpa only [hit] using pure_preservesOutputCapacityFrame operands
  | none =>
    simpa only [hit] using rejectThenPure_preservesOutputCapacityFrame
      s!"unbound Bytes32 source symbol '{name}'" ({values := []} : ByteOperands)

/-- Byte selection packs both arms, then allocates or reuses one native select
result for each aligned chunk. -/
theorem lowerBytes_select_preservesOutputCapacityFrame {length : Nat}
    (condition : Expr .bool) (yes no : Expr (.bytes length))
    (conditionFrame : PreservesOutputCapacityFrame (lowerExpr condition))
    (yesFrame : PreservesOutputCapacityFrame (lowerBytes yes))
    (noFrame : PreservesOutputCapacityFrame (lowerBytes no)) :
    PreservesOutputCapacityFrame (lowerBytes (.select condition yes no)) := by
  simp only [lowerBytes]
  apply bind_preservesOutputCapacityFrame _ _ conditionFrame
  intro bit
  apply bind_preservesOutputCapacityFrame _ _ yesFrame
  intro yesBytes
  apply bind_preservesOutputCapacityFrame _ _
    (byteChunks_preservesOutputCapacityFrame length yesBytes)
  intro yesChunks
  apply bind_preservesOutputCapacityFrame _ _ noFrame
  intro noBytes
  apply bind_preservesOutputCapacityFrame _ _
    (byteChunks_preservesOutputCapacityFrame length noBytes)
  intro noChunks
  exact listMapM_preservesOutputCapacityFrame (yesChunks.zip noChunks)
    (fun pair => selectOperands bit pair.1 pair.2)
    (by
      intro pair
      exact selectOperands_preservesOutputCapacityFrame bit pair.1 pair.2)

theorem lowerBytes_persistentHash32_preservesOutputCapacityFrame (value : Expr (.bytes 32))
    (valueFrame : PreservesOutputCapacityFrame (lowerBytes value)) :
    PreservesOutputCapacityFrame (lowerBytes (.persistentHash32 value)) := by
  simp only [lowerBytes]
  apply bind_preservesOutputCapacityFrame _ _ valueFrame
  intro operands
  apply bind_preservesOutputCapacityFrame _ _
    (alignedBytes32Value_preservesOutputCapacityFrame value operands.values)
  intro chunks
  obtain ⟨highByte, low31⟩ := chunks
  apply bind_preservesOutputCapacityFrame _ _
    (lowerPersistentHash_preservesOutputCapacityFrame "bytes32" bytes32Alignment [highByte, low31])
  intro result
  exact pure_preservesOutputCapacityFrame _

theorem lowerExpr_bytesField_preservesOutputCapacityFrame {length : Nat}
    (value : Expr (.bytes length)) (index : Nat)
    (valueFrame : PreservesOutputCapacityFrame (lowerBytes value)) :
    PreservesOutputCapacityFrame (lowerExpr (.bytesField value index)) := by
  simp only [lowerExpr]
  apply bind_preservesOutputCapacityFrame _ _ valueFrame
  intro operand
  split
  · exact rejectThenPure_preservesOutputCapacityFrame "byte field chunk index is out of range" "0x00"
  · split
    · split
      · exact rejectThenPure_preservesOutputCapacityFrame "byte chunk count mismatch" "0x00"
      · exact pure_preservesOutputCapacityFrame _
    · split
      · exact rejectThenPure_preservesOutputCapacityFrame "byte leaf count mismatch" "0x00"
      · exact packBytes_preservesOutputCapacityFrame _

theorem lowerExpr_select_preservesOutputCapacityFrame {ty : Ty}
    (condition : Expr .bool) (yes no : Expr ty)
    (conditionFrame : PreservesOutputCapacityFrame (lowerExpr condition))
    (yesFrame : PreservesOutputCapacityFrame (lowerExpr yes))
    (noFrame : PreservesOutputCapacityFrame (lowerExpr no)) :
    PreservesOutputCapacityFrame (lowerExpr (.select condition yes no)) := by
  simp only [lowerExpr]
  apply bind_preservesOutputCapacityFrame _ _ conditionFrame
  intro bit
  apply bind_preservesOutputCapacityFrame _ _ yesFrame
  intro yesValue
  apply bind_preservesOutputCapacityFrame _ _ noFrame
  intro noValue
  exact selectOperands_preservesOutputCapacityFrame bit yesValue noValue

theorem lowerExpr_poseidon2_preservesOutputCapacityFrame (domain : Nat)
    (left right : Expr .native)
    (leftFrame : PreservesOutputCapacityFrame (lowerExpr left))
    (rightFrame : PreservesOutputCapacityFrame (lowerExpr right)) :
    PreservesOutputCapacityFrame (lowerExpr (.poseidon2 domain left right)) := by
  simp only [lowerExpr]
  apply bind_preservesOutputCapacityFrame _ _ leftFrame
  intro leftValue
  apply bind_preservesOutputCapacityFrame _ _ rightFrame
  intro rightValue
  apply cachedScalarOutput_preservesOutputCapacityFrame
  intro output
  apply instruction_scalarOutputDefinitions _ _ _ ⟨by decide, by decide, by decide⟩ _
  all_goals
    simp [Native.stringField, instruction, Json.getObjVal?, Json.mkObj, Json.getStr?,
      Std.TreeMap.Raw.get?_eq_getElem?, Std.TreeMap.Raw.getElem?_ofList_of_mem, Lean.ToJson.toJson]
    rfl

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

private theorem bindPublicInputs_preservesOutputCapacityFrame (identifiers : List String) :
    PreservesOutputCapacityFrame (do
      for identifier in identifiers do bindPublic [identifier]) := by
  apply forIn_preservesOutputCapacityFrame
  intro identifier _
  apply bind_preservesOutputCapacityFrame _ _
    (emit_preservesOutputCapacityFrame "impact"
      [("guard", toJson ("0x01" : String)), ("inputs", toJson [identifier])])
  intro _
  exact pure_preservesOutputCapacityFrame _

def lowerPublicForeignInputPrefix (input : Input) (kind : Foreign.Kind) : LowerM Unit := do
  lowerByteInput input
  for output in (← encodeForeign kind ("%input_" ++ input.name)) do
    bindPublic [output]

/-- The actual public foreign input prefix accounts for every encoded field
through the output slots of `encode`, including a repeated encoding. -/
theorem lowerPublicForeignInputPrefix_preservesOutputCapacityFrame
    (name : String) (kind : Foreign.Kind) (span : SourceSpan := {}) :
    PreservesOutputCapacityFrame (lowerPublicForeignInputPrefix
      {name, ty := .foreign kind, visibility := .«public», span} kind) := by
  let output := "%input_" ++ name
  unfold lowerPublicForeignInputPrefix
  apply bind_preservesOutputCapacityFrame _ _
  · exact lowerByteInput_preservesOutputCapacityFrame _ false
  · intro _
    apply bind_preservesOutputCapacityFrame _ _
      (encodeForeign_preservesOutputCapacityFrame kind output)
    intro outputs
    exact bindPublicInputs_preservesOutputCapacityFrame outputs

def bindPublicGuarded (guard : Expr .bool) (values : List String) : LowerM Unit := do
  emit "impact" [("guard", toJson (← lowerExpr guard)), ("inputs", toJson values)]

def lowerCircuitInput (input : Input) : LowerM Unit := do
  if input.visibility == .«public» then
    match input.ty with
    | .bytes _ => lowerPublicFixedBytesInputPrefix input
    | .foreign kind => lowerPublicForeignInputPrefix input kind
    | _ => do
      lowerByteInput input
      for output in input.nativeIdentifiers do bindPublic [output]
  else
    lowerByteInput input

theorem lowerCircuitInput_preservesOutputCapacityFrame (input : Input) :
    PreservesOutputCapacityFrame (lowerCircuitInput input) := by
  cases input with
  | mk name ty visibility span =>
    by_cases publicInput : (visibility == .«public») = true
    · have visibilityIsPublic : visibility = .«public» := by
        cases visibility with
        | «public» => rfl
        | «private» => cases publicInput
      subst visibility
      cases ty with
      | bytes width =>
        simpa [lowerCircuitInput, publicInput] using
          lowerPublicFixedBytesInputPrefix_preservesOutputCapacityFrame name width span
      | foreign kind =>
        simpa [lowerCircuitInput, publicInput] using
          lowerPublicForeignInputPrefix_preservesOutputCapacityFrame name kind span
      | _ =>
        simp only [lowerCircuitInput, publicInput, ite_true]
        apply bind_preservesOutputCapacityFrame _ _
          (lowerByteInput_preservesOutputCapacityFrame _ false)
        intro _
        exact bindPublicInputs_preservesOutputCapacityFrame _
    · simpa [lowerCircuitInput, publicInput] using
        (lowerByteInput_preservesOutputCapacityFrame {name, ty, visibility, span} false)

def lowerCircuitInputs (inputs : List Input) : LowerM Unit := do
  for input in inputs do lowerCircuitInput input

/-- Sizes the entire input prefix of the ordinary circuit lowerer using the
output slots from its emitted instructions. -/
theorem lowerCircuitInputs_preservesOutputCapacityFrame (inputs : List Input) :
    PreservesOutputCapacityFrame (lowerCircuitInputs inputs) := by
  unfold lowerCircuitInputs
  apply forIn_preservesOutputCapacityFrame
  intro input _
  apply bind_preservesOutputCapacityFrame _ _
    (lowerCircuitInput_preservesOutputCapacityFrame input)
  intro _
  exact pure_preservesOutputCapacityFrame _

def lowerConstraints (constraints : List (Expr .bool)) : LowerM Unit := do
  for condition in constraints do
    let value ← lowerExpr condition
    emit "assert" [("cond", toJson value)]

theorem lowerConstraints_preservesOutputCapacityFrame
    (constraints : List (Expr .bool))
    (frames : ∀ condition ∈ constraints, PreservesOutputCapacityFrame (lowerExpr condition)) :
    PreservesOutputCapacityFrame (lowerConstraints constraints) := by
  unfold lowerConstraints
  apply forIn_preservesOutputCapacityFrame_of_mem
  intro condition member _
  apply bind_preservesOutputCapacityFrame _ _ (frames condition member)
  intro result
  apply bind_preservesOutputCapacityFrame _ _ (emit_preservesOutputCapacityFrame _ _)
  intro _
  exact pure_preservesOutputCapacityFrame _

def lowerReturnPreflight (output : Output) : LowerM Unit :=
  match output with
  | {ty := .bytes 0, value, ..} => discard (lowerBytes value)
  | _ => pure ()

def lowerReturnFieldStep (output : Output) (values : List String) :
    LowerM (ForInStep (List String)) := do
  lowerReturnPreflight output
  match output.nativeReturnFields with
  | .error message => do
    rejectLowering message
    pure (ForInStep.yield values)
  | .ok fields =>
    let values ← forIn fields values fun field accumulator => do
      let value ← lowerExpr field
      pure (ForInStep.yield (accumulator ++ [value]))
    pure (ForInStep.yield values)

def lowerReturnFieldsFrom (outputs : List Output) (values : List String) : LowerM (List String) :=
  forIn outputs values lowerReturnFieldStep

def lowerReturnFields (outputs : List Output) : LowerM (List String) :=
  lowerReturnFieldsFrom outputs []

theorem lowerReturnFields_preservesOutputCapacityFrame (outputs : List Output)
    (preflight : ∀ output ∈ outputs, PreservesOutputCapacityFrame (lowerReturnPreflight output))
    (fields : ∀ output ∈ outputs, ∀ projections,
      output.nativeReturnFields = .ok projections → ∀ field ∈ projections,
        PreservesOutputCapacityFrame (lowerExpr field)) :
    PreservesOutputCapacityFrame (lowerReturnFields outputs) := by
  unfold lowerReturnFields lowerReturnFieldsFrom
  apply forIn_preservesOutputCapacityFrame_of_mem
  intro output member values
  unfold lowerReturnFieldStep
  apply bind_preservesOutputCapacityFrame _ _ (preflight output member)
  intro _
  cases projections : output.nativeReturnFields with
  | error message =>
    simp only [projections]
    exact rejectThenPure_preservesOutputCapacityFrame message (ForInStep.yield values)
  | ok projectionsList =>
    simp only [projections]
    apply bind_preservesOutputCapacityFrame
    · apply forIn_preservesOutputCapacityFrame_of_mem
      intro field fieldMember accumulator
      apply bind_preservesOutputCapacityFrame _ _
        (fields output member projectionsList projections field fieldMember)
      intro value
      exact pure_preservesOutputCapacityFrame (ForInStep.yield (accumulator ++ [value]))
    · intro returned
      exact pure_preservesOutputCapacityFrame (ForInStep.yield returned)

def lowerBody (c : Circuit) : LowerM Unit := do
  lowerCircuitInputs c.inputs
  lowerConstraints c.constraints
  let outputs ← lowerReturnFields c.outputs
  if !outputs.isEmpty then bindPublic outputs
  emit "output" [("vals", toJson outputs)]

/-- Compose the actual standalone circuit stages. The expression premises
apply to the circuit's constraints and to its emitted return projections. -/
theorem lowerBody_preservesOutputCapacityFrame (c : Circuit)
    (constraints : ∀ condition ∈ c.constraints, PreservesOutputCapacityFrame (lowerExpr condition))
    (preflight : ∀ output ∈ c.outputs, PreservesOutputCapacityFrame (lowerReturnPreflight output))
    (fields : ∀ output ∈ c.outputs, ∀ projections,
      output.nativeReturnFields = .ok projections → ∀ field ∈ projections,
        PreservesOutputCapacityFrame (lowerExpr field)) :
    PreservesOutputCapacityFrame (lowerBody c) := by
  unfold lowerBody
  apply bind_preservesOutputCapacityFrame _ _ (lowerCircuitInputs_preservesOutputCapacityFrame _)
  intro _
  apply bind_preservesOutputCapacityFrame _ _ (lowerConstraints_preservesOutputCapacityFrame _ constraints)
  intro _
  apply bind_preservesOutputCapacityFrame _ _
    (lowerReturnFields_preservesOutputCapacityFrame _ preflight fields)
  intro outputs
  split
  · apply bind_preservesOutputCapacityFrame _ _
      (emit_preservesOutputCapacityFrame "impact"
        [("guard", toJson ("0x01" : String)), ("inputs", toJson outputs)])
    intro _
    exact emit_preservesOutputCapacityFrame _ _
  · exact emit_preservesOutputCapacityFrame _ _

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

/-- Link rewritten standalone-circuit JSON to the exact instruction vector
produced by the selected rewrite mode over the pruned source's LowerM output. -/
private theorem lowerCircuit_instructions_with_rewrites (circuit : Circuit) (rewrites : Rewrites)
    (program : Json) (accepted : lowerCircuit circuit rewrites = .ok program) :
    Native.arrayField program "instructions" = .ok
      (optimizedInstructions rewrites
        ((lowerBody (Passes.pruneCircuit circuit)).run {}).2.instructions) := by
  cases rewrites <;> simp only [lowerCircuit, bind, bind_ok] at accepted
  all_goals
    rcases accepted with ⟨_, disclosure, _, validation, _, constants, _, outputConstants, gate⟩
    cases produced : (lowerBody (Passes.pruneCircuit circuit)).run {} with
    | mk value state =>
      simp only [produced] at gate
      rw [bind_ok] at gate
      rcases gate with ⟨expected, expectedAccepted, producerAccepted⟩
      obtain ⟨equal, checked⟩ := (validateProduced_ok _ _ _ _).mp producerAccepted
      rw [equal]
      rfl

/-- Relate the accepted JSON instruction vector to the actual lowerBody run. -/
theorem lowerCircuit_instructions (circuit : Circuit) (program : Json)
    (accepted : lowerCircuit circuit = .ok program) :
    Native.arrayField program "instructions" =
      .ok ((lowerBody (Passes.pruneCircuit circuit)).run {}).2.instructions := by
  exact lowerCircuit_instructions_with_rewrites circuit .disabled program accepted

/-- Both accepted rewrite modes consume the same pruned lowerBody vector. The
comparison-enabled result adds comparison reuse after range deduplication. -/
theorem lowerCircuit_comparison_pipeline
    (circuit : Circuit) (rangeProgram comparisonProgram : Json)
    (rangeAccepted : lowerCircuit circuit .rangeAndAssertions = .ok rangeProgram)
    (comparisonAccepted : lowerCircuit circuit .includingComparisons = .ok comparisonProgram) :
    let raw := ((lowerBody (Passes.pruneCircuit circuit)).run {}).2.instructions
    Native.arrayField rangeProgram "instructions" =
        .ok (RangeDedup.removeDuplicateAssertions (RangeDedup.run raw)) ∧
      Native.arrayField comparisonProgram "instructions" =
        .ok (RangeDedup.removeDuplicateAssertions (RangeDedup.reuseComparisons
          (RangeDedup.run raw))) := by
  constructor
  · simpa [optimizedInstructions] using
      (lowerCircuit_instructions_with_rewrites circuit .rangeAndAssertions rangeProgram
        rangeAccepted)
  · simpa [optimizedInstructions] using
      (lowerCircuit_instructions_with_rewrites circuit .includingComparisons comparisonProgram
        comparisonAccepted)

set_option maxHeartbeats 600000 in
/-- The comparison-enabled accepted vector is the exact comparison rewrite of
the accepted range-and-assertion vector for the same source circuit. -/
theorem lowerCircuit_comparison_instructions_reuse_range_instructions
    (circuit : Circuit) (rangeProgram comparisonProgram : Json)
    (rangeAccepted : lowerCircuit circuit .rangeAndAssertions = .ok rangeProgram)
    (comparisonAccepted : lowerCircuit circuit .includingComparisons = .ok comparisonProgram) :
    ∃ rangeInstructions,
      Native.arrayField rangeProgram "instructions" = .ok rangeInstructions ∧
      Native.arrayField comparisonProgram "instructions" =
        .ok (RangeDedup.reuseComparisons rangeInstructions) := by
  obtain ⟨rangeInstructions, comparisonInstructions⟩ :=
    lowerCircuit_comparison_pipeline circuit rangeProgram comparisonProgram
      rangeAccepted comparisonAccepted
  refine ⟨RangeDedup.removeDuplicateAssertions
    (RangeDedup.run ((lowerBody (Passes.pruneCircuit circuit)).run {}).2.instructions),
    rangeInstructions, ?_⟩
  rw [comparisonInstructions]
  change Except.ok (RangeDedup.removeDuplicateAssertions (RangeDedup.reuseComparisons
    (RangeDedup.run ((lowerBody (Passes.pruneCircuit circuit)).run {}).2.instructions))) =
      Except.ok (RangeDedup.reuseComparisons (RangeDedup.removeDuplicateAssertions
        (RangeDedup.run ((lowerBody (Passes.pruneCircuit circuit)).run {}).2.instructions)))
  congr 1
  exact (RangeDedup.reuseComparisons_removeDuplicateAssertions
    (RangeDedup.run ((lowerBody (Passes.pruneCircuit circuit)).run {}).2.instructions)).symm

def lowerEntrypointInputs (entry : Entrypoint) : LowerM Unit := do
  for input in entry.circuit.inputs do
    lowerByteInput input (entry.callInputs.contains input.name)

/-- Ledger call arguments are already provided by the call transcript. The
input loop still counts every emitted definition in their typed bridges. -/
theorem lowerEntrypointInputs_preservesOutputCapacityFrame (entry : Entrypoint) :
    PreservesOutputCapacityFrame (lowerEntrypointInputs entry) := by
  unfold lowerEntrypointInputs
  apply forIn_preservesOutputCapacityFrame
  intro input _
  apply bind_preservesOutputCapacityFrame _ _
    (lowerByteInput_preservesOutputCapacityFrame input (entry.callInputs.contains input.name))
  intro _
  exact pure_preservesOutputCapacityFrame _

def lowerEntrypointAliases (entry : Entrypoint) : LowerM Unit := do
  for output in entry.circuit.outputs do
    match output with
    | {name, ty := .bytes _, value, ..} =>
      let value ← lowerBytes value
      modify fun s => {s with byteAliases := (name, value) :: s.byteAliases}
    | {name, ty := .opaqueBytes, value, ..} =>
      let value ← lowerOpaqueBytes value
      modify fun s => {s with aliases := (name, value) :: s.aliases}
    | {name, ty := .opaqueString, value, ..} =>
      let value ← lowerOpaqueString value
      modify fun s => {s with aliases := (name, value) :: s.aliases}
    | {name, value, ..} =>
      let value ← lowerExpr value
      modify fun s => {s with aliases := (name, value) :: s.aliases}

/-- Compose the output-capacity frame across every typed alias path in the
entrypoint output loop. The expression lowerers supply their own frame proofs. -/
theorem lowerEntrypointAliases_preservesOutputCapacityFrame (entry : Entrypoint)
    (frames : ∀ output ∈ entry.circuit.outputs, match output with
      | {ty := .bytes _, value, ..} => PreservesOutputCapacityFrame (lowerBytes value)
      | {ty := .opaqueBytes, value, ..} => PreservesOutputCapacityFrame (lowerOpaqueBytes value)
      | {ty := .opaqueString, value, ..} => PreservesOutputCapacityFrame (lowerOpaqueString value)
      | {value, ..} => PreservesOutputCapacityFrame (lowerExpr value)) :
    PreservesOutputCapacityFrame (lowerEntrypointAliases entry) := by
  unfold lowerEntrypointAliases
  apply forIn_preservesOutputCapacityFrame_of_mem
  intro output member _
  have frame := frames output member
  cases output with
  | mk name ty value span =>
    cases ty <;>
      apply bind_preservesOutputCapacityFrame _ _ frame <;>
      intro lowered <;>
      exact modify_preservesOutputCapacityFrame _ (fun _ => rfl) (fun _ => rfl)

def lowerLedgerRead (read : Impact.Read) : LowerM Unit := do
  for scalarRead in Impact.Read.scalarReads read do
    let activity ← (match scalarRead.guard with
      | none => pure none
      | some guard => do pure (some (← lowerExpr guard)) : LowerM (Option String))
    let activityJson := (activity.map toJson).getD Json.null
    for (name, ty) in scalarRead.bindings do
      let output := "%input_" ++ name
      let bindRead : LowerM Unit := match ty with
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
        | _ => do
          emit "public_input" [
            ("guard", activityJson),
            ("type", nativeType), ("output", toJson output)]
          constrainType ty output
      bindRead
    let maskBytes : LowerM Unit := match scalarRead.ty with
      | .bytes _ => do
          let values ← scalarRead.bindings.mapM fun (name, ty) => do
            match scalarRead.guard, ty with
            | some guard, .uint maximum =>
              lowerExpr (.select guard (.ref name : Expr (.uint maximum)) (.uint maximum 0))
            | _, _ => pure ("%input_" ++ name)
          modify fun state => {state with byteAliases :=
            (scalarRead.name, {values := values.reverse, packed := true}) :: state.byteAliases}
      | _ => pure ()
    maskBytes
    if scalarRead.ty == .jubjubPoint then do
      let xName := scalarRead.bindings[0]!.1
      let yName := scalarRead.bindings[1]!.1
      let x := "%input_" ++ xName
      let y := "%input_" ++ yName
      let x ← (match scalarRead.guard with
        | none => pure x
        | some guard => lowerExpr (.select guard (.ref xName : Expr .native) (.native 0)) : LowerM String)
      let y ← (match scalarRead.guard with
        | none => pure y
        | some guard => lowerExpr (.select guard (.ref yName : Expr .native) (.native 1)) : LowerM String)
      let point ← lowerPointFromCoordinates x y
      modify fun state => {state with aliases := (scalarRead.name, point) :: state.aliases}
  lowerConstraints read.inactiveDefaultConstraints

theorem lowerLedgerRead_preservesOutputCapacityFrame (read : Impact.Read)
    (guards : ∀ scalarRead ∈ read.scalarReads, ∀ guard,
      scalarRead.guard = some guard → PreservesOutputCapacityFrame (lowerExpr guard))
    (defaults : ∀ condition ∈ read.inactiveDefaultConstraints,
      PreservesOutputCapacityFrame (lowerExpr condition)) :
    PreservesOutputCapacityFrame (lowerLedgerRead read) := by
  unfold lowerLedgerRead
  apply bind_preservesOutputCapacityFrame
  · apply forIn_preservesOutputCapacityFrame_of_mem
    intro scalarRead member _
    apply bind_preservesOutputCapacityFrame
    · cases selected : scalarRead.guard with
      | none => exact pure_preservesOutputCapacityFrame _
      | some guard =>
        apply bind_preservesOutputCapacityFrame _ _ (guards scalarRead member guard selected)
        intro _
        exact pure_preservesOutputCapacityFrame _
    · intro activity
      apply bind_preservesOutputCapacityFrame
      · apply forIn_preservesOutputCapacityFrame
        intro binding _
        obtain ⟨name, ty⟩ := binding
        apply bind_preservesOutputCapacityFrame
        · split
          · apply bind_preservesOutputCapacityFrame _ _ (emit_preservesOutputCapacityFrame _ _)
            intro _
            apply bind_preservesOutputCapacityFrame _ _
              (lowerJubjubScalarFromNative_preservesOutputCapacityFrame _)
            intro scalar
            apply bind_preservesOutputCapacityFrame _ _
              (lowerJubjubScalarToNative_preservesOutputCapacityFrame _)
            intro encoded
            apply bind_preservesOutputCapacityFrame _ _ (emit_preservesOutputCapacityFrame _ _)
            intro _
            exact modify_preservesOutputCapacityFrame _ (fun _ => rfl) (fun _ => rfl)
          · exact emit_preservesOutputCapacityFrame _ _
          · apply bind_preservesOutputCapacityFrame _ _ (emit_preservesOutputCapacityFrame _ _)
            intro _
            exact constrainType_preservesOutputCapacityFrame _ _
        · intro _
          exact pure_preservesOutputCapacityFrame _
      · intro _
        apply bind_preservesOutputCapacityFrame
        · split
          · apply bind_preservesOutputCapacityFrame
            · apply listMapM_preservesOutputCapacityFrame
              intro binding
              obtain ⟨name, ty⟩ := binding
              cases selected : scalarRead.guard <;> cases ty <;>
                try exact pure_preservesOutputCapacityFrame _
              rename_i guard maximum
              apply lowerExpr_select_preservesOutputCapacityFrame
              · exact guards scalarRead member guard selected
              · simp only [lowerExpr]
                apply bind_preservesOutputCapacityFrame (get : LowerM LowerState) _
                  (fun state => OutputCapacityFrame.refl state)
                intro _
                exact pure_preservesOutputCapacityFrame _
              · simpa only [lowerExpr] using pure_preservesOutputCapacityFrame (fieldImmediate 0)
            · intro values
              exact modify_preservesOutputCapacityFrame _ (fun _ => rfl) (fun _ => rfl)
          · exact pure_preservesOutputCapacityFrame _
        · intro _
          split
          · apply bind_preservesOutputCapacityFrame
            · cases selected : scalarRead.guard with
              | none => exact pure_preservesOutputCapacityFrame _
              | some guard =>
                apply lowerExpr_select_preservesOutputCapacityFrame
                · exact guards scalarRead member guard selected
                · simp only [lowerExpr]
                  apply bind_preservesOutputCapacityFrame (get : LowerM LowerState) _
                    (fun state => OutputCapacityFrame.refl state)
                  intro _
                  exact pure_preservesOutputCapacityFrame _
                · simpa only [lowerExpr] using pure_preservesOutputCapacityFrame (fieldImmediate 0)
            · intro x
              apply bind_preservesOutputCapacityFrame
              · cases selected : scalarRead.guard with
                | none => exact pure_preservesOutputCapacityFrame _
                | some guard =>
                  apply lowerExpr_select_preservesOutputCapacityFrame
                  · exact guards scalarRead member guard selected
                  · simp only [lowerExpr]
                    apply bind_preservesOutputCapacityFrame (get : LowerM LowerState) _
                      (fun state => OutputCapacityFrame.refl state)
                    intro _
                    exact pure_preservesOutputCapacityFrame _
                  · simpa only [lowerExpr] using pure_preservesOutputCapacityFrame (fieldImmediate 1)
              · intro y
                apply bind_preservesOutputCapacityFrame _ _
                  (lowerPointFromCoordinates_preservesOutputCapacityFrame x y)
                intro point
                apply bind_preservesOutputCapacityFrame
                · exact modify_preservesOutputCapacityFrame _ (fun _ => rfl) (fun _ => rfl)
                · intro _
                  exact pure_preservesOutputCapacityFrame _
          · exact pure_preservesOutputCapacityFrame _
  · intro _
    exact lowerConstraints_preservesOutputCapacityFrame _ defaults

def lowerLedgerReads (entry : Entrypoint) (plan : Impact.Plan) : LowerM Unit := do
  -- Public call parameters have already been read in declaration order.
  let publicCount := Impact.publicInputReadCount entry.circuit.inputs
  for read in plan.reads.drop publicCount do
    lowerLedgerRead read

theorem lowerLedgerReads_preservesOutputCapacityFrame (entry : Entrypoint)
    (plan : Impact.Plan)
    (guards : ∀ read ∈ plan.reads.drop (Impact.publicInputReadCount entry.circuit.inputs),
      ∀ scalarRead ∈ read.scalarReads, ∀ guard, scalarRead.guard = some guard →
        PreservesOutputCapacityFrame (lowerExpr guard))
    (defaults : ∀ read ∈ plan.reads.drop (Impact.publicInputReadCount entry.circuit.inputs),
      ∀ condition ∈ read.inactiveDefaultConstraints, PreservesOutputCapacityFrame (lowerExpr condition)) :
    PreservesOutputCapacityFrame (lowerLedgerReads entry plan) := by
  unfold lowerLedgerReads
  apply forIn_preservesOutputCapacityFrame_of_mem
  intro read member _
  apply bind_preservesOutputCapacityFrame _ _
    (lowerLedgerRead_preservesOutputCapacityFrame read (guards read member) (defaults read member))
  intro _
  exact pure_preservesOutputCapacityFrame _

def lowerLedgerOperations (plan : Impact.Plan) : LowerM Unit := do
  -- The ledger consumes one activity entry per VM opcode. Compound Impact
  -- operations split their field vectors at each native opcode.
  for (operation, index) in plan.operations.zipIdx do
    let guard := ((plan.activityGuards[index]?).getD none).getD (.bool true)
    for fields in operation.fieldGroups do
      bindPublicGuarded guard (← fields.mapM lowerExpr)

theorem lowerLedgerOperations_preservesOutputCapacityFrame (plan : Impact.Plan)
    (fieldsFrame : ∀ item ∈ plan.operations.zipIdx, ∀ fields ∈ item.1.fieldGroups,
      ∀ field ∈ fields, PreservesOutputCapacityFrame (lowerExpr field))
    (guardsFrame : ∀ item ∈ plan.operations.zipIdx, PreservesOutputCapacityFrame
      (lowerExpr (((plan.activityGuards[item.2]?).getD none).getD (.bool true)))) :
    PreservesOutputCapacityFrame (lowerLedgerOperations plan) := by
  unfold lowerLedgerOperations
  apply forIn_preservesOutputCapacityFrame_of_mem
  intro operationIndex member _
  obtain ⟨operation, index⟩ := operationIndex
  apply bind_preservesOutputCapacityFrame
  · apply forIn_preservesOutputCapacityFrame_of_mem
    intro fields group _
    apply bind_preservesOutputCapacityFrame
    · exact listMapM_preservesOutputCapacityFrame_of_mem fields lowerExpr
        (fieldsFrame (operation, index) member fields group)
    · intro values
      apply bind_preservesOutputCapacityFrame
      · unfold bindPublicGuarded
        apply bind_preservesOutputCapacityFrame _ _ (guardsFrame (operation, index) member)
        intro _
        exact emit_preservesOutputCapacityFrame _ _
      · intro _
        exact pure_preservesOutputCapacityFrame _
  · intro _
    exact pure_preservesOutputCapacityFrame _

def lowerEntrypointBody (entry : Entrypoint) (plan : Impact.Plan) : LowerM Unit := do
  lowerEntrypointInputs entry
  lowerConstraints entry.circuit.constraints
  lowerEntrypointAliases entry
  lowerLedgerReads entry plan
  lowerConstraints plan.guards
  lowerLedgerOperations plan
  -- Entrypoint returns are public outputs committed with the call statement.
  let returned ← lowerReturnFields entry.returns
  emit "output" [("vals", toJson returned)]

/-- Compose allocation across the actual stages of an entrypoint, requiring
expression frames only at positions lowered by this source entry and plan. -/
theorem lowerEntrypointBody_preservesOutputCapacityFrame (entry : Entrypoint) (plan : Impact.Plan)
    (constraints : ∀ condition ∈ entry.circuit.constraints,
      PreservesOutputCapacityFrame (lowerExpr condition))
    (aliases : PreservesOutputCapacityFrame (lowerEntrypointAliases entry))
    (readGuards : ∀ read ∈ plan.reads.drop (Impact.publicInputReadCount entry.circuit.inputs),
      ∀ scalarRead ∈ read.scalarReads, ∀ guard, scalarRead.guard = some guard →
        PreservesOutputCapacityFrame (lowerExpr guard))
    (readDefaults : ∀ read ∈ plan.reads.drop (Impact.publicInputReadCount entry.circuit.inputs),
      ∀ condition ∈ read.inactiveDefaultConstraints, PreservesOutputCapacityFrame (lowerExpr condition))
    (planGuards : ∀ condition ∈ plan.guards, PreservesOutputCapacityFrame (lowerExpr condition))
    (operationFields : ∀ item ∈ plan.operations.zipIdx, ∀ group ∈ item.1.fieldGroups,
      ∀ field ∈ group, PreservesOutputCapacityFrame (lowerExpr field))
    (operationGuards : ∀ item ∈ plan.operations.zipIdx, PreservesOutputCapacityFrame
      (lowerExpr (((plan.activityGuards[item.2]?).getD none).getD (.bool true))))
    (preflight : ∀ output ∈ entry.returns, PreservesOutputCapacityFrame (lowerReturnPreflight output))
    (returns : ∀ output ∈ entry.returns, ∀ projections,
      output.nativeReturnFields = .ok projections → ∀ field ∈ projections,
        PreservesOutputCapacityFrame (lowerExpr field)) :
    PreservesOutputCapacityFrame (lowerEntrypointBody entry plan) := by
  unfold lowerEntrypointBody
  apply bind_preservesOutputCapacityFrame _ _ (lowerEntrypointInputs_preservesOutputCapacityFrame entry)
  intro _
  apply bind_preservesOutputCapacityFrame _ _
    (lowerConstraints_preservesOutputCapacityFrame _ constraints)
  intro _
  apply bind_preservesOutputCapacityFrame _ _ aliases
  intro _
  apply bind_preservesOutputCapacityFrame _ _
    (lowerLedgerReads_preservesOutputCapacityFrame entry plan readGuards readDefaults)
  intro _
  apply bind_preservesOutputCapacityFrame _ _
    (lowerConstraints_preservesOutputCapacityFrame _ planGuards)
  intro _
  apply bind_preservesOutputCapacityFrame _ _
    (lowerLedgerOperations_preservesOutputCapacityFrame plan operationFields operationGuards)
  intro _
  apply bind_preservesOutputCapacityFrame _ _
    (lowerReturnFields_preservesOutputCapacityFrame _ preflight returns)
  intro _
  exact emit_preservesOutputCapacityFrame _ _

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

theorem lowerEntrypoint_validation_and_instructions_with_rewrites
    (state : List StateDecl) (entry : Entrypoint) (rewrites : Rewrites)
    (program : Json) (accepted : lowerEntrypoint state entry rewrites = .ok program) :
    ∃ plan expected, Impact.lower state (Passes.pruneEntrypoint entry) = .ok plan ∧
      Native.expectedEntrypoint state (Passes.pruneEntrypoint entry) = .ok expected ∧
      Native.validate (optimizedExpected rewrites expected) program = .ok () ∧
      Native.arrayField program "instructions" = .ok (optimizedInstructions rewrites
        ((lowerEntrypointBody (Passes.pruneEntrypoint entry) plan).run {}).2.instructions) := by
  simp only [lowerEntrypoint, bind, bind_ok] at accepted
  obtain ⟨⟨resultPlan, relation⟩, lowered, result⟩ := accepted
  cases result
  simp only [lowerPrunedEntrypoint, bind, bind_ok] at lowered
  rcases lowered with ⟨plan, planAccepted, gate⟩
  cases produced : (lowerEntrypointBody (Passes.pruneEntrypoint entry) plan).run {} with
  | mk value result =>
    simp only [produced] at gate
    simp only [bind_ok] at gate
    rcases gate with ⟨expected, expectedAccepted, _, producerAccepted, output⟩
    cases output
    obtain ⟨equal, checked⟩ := (validateProduced_ok _ _ _ _).mp producerAccepted
    refine ⟨_, expected, planAccepted, expectedAccepted, ?_, ?_⟩
    · rw [equal]
      exact checked
    · rw [equal, produced]
      rfl

/-- Accepted ledger-call JSON passes producer validation for the pruned
entrypoint and retains the emitted instructions for the exact accepted plan. -/
theorem lowerEntrypoint_validation_and_instructions (state : List StateDecl) (entry : Entrypoint)
    (program : Json) (accepted : lowerEntrypoint state entry = .ok program) :
    ∃ plan expected, Impact.lower state (Passes.pruneEntrypoint entry) = .ok plan ∧
      Native.expectedEntrypoint state (Passes.pruneEntrypoint entry) = .ok expected ∧
      Native.validate expected program = .ok () ∧
      Native.arrayField program "instructions" =
        .ok ((lowerEntrypointBody (Passes.pruneEntrypoint entry) plan).run {}).2.instructions :=
  lowerEntrypoint_validation_and_instructions_with_rewrites state entry .disabled program accepted

/-- Both accepted ledger rewrite modes share the exact Impact plan and source
validation schedule. Comparison reuse acts on the accepted range-and-assertion
instruction vector. -/
theorem lowerEntrypoint_comparison_instructions_reuse_range_instructions
    (state : List StateDecl) (entry : Entrypoint) (rangeProgram comparisonProgram : Json)
    (rangeAccepted : lowerEntrypoint state entry .rangeAndAssertions = .ok rangeProgram)
    (comparisonAccepted : lowerEntrypoint state entry .includingComparisons = .ok comparisonProgram) :
    ∃ plan expected rangeInstructions,
      Impact.lower state (Passes.pruneEntrypoint entry) = .ok plan ∧
      Native.expectedEntrypoint state (Passes.pruneEntrypoint entry) = .ok expected ∧
      Native.validate {expected with assertions := expected.assertions.eraseDups} rangeProgram = .ok () ∧
      Native.validate {expected with assertions := expected.assertions.eraseDups} comparisonProgram = .ok () ∧
      Native.arrayField rangeProgram "instructions" = .ok rangeInstructions ∧
      Native.arrayField comparisonProgram "instructions" =
        .ok (RangeDedup.reuseComparisons rangeInstructions) := by
  obtain ⟨plan, expected, impact, schedule, rangeValid, rangeArray⟩ :=
    lowerEntrypoint_validation_and_instructions_with_rewrites state entry .rangeAndAssertions
      rangeProgram rangeAccepted
  obtain ⟨comparisonPlan, comparisonExpected, comparisonImpact, comparisonSchedule,
      comparisonValid, comparisonArray⟩ :=
    lowerEntrypoint_validation_and_instructions_with_rewrites state entry .includingComparisons
      comparisonProgram comparisonAccepted
  have samePlan := Except.ok.inj (comparisonImpact.symm.trans impact)
  have sameExpected := Except.ok.inj (comparisonSchedule.symm.trans schedule)
  subst comparisonPlan comparisonExpected
  refine ⟨plan, expected, _, impact, schedule, rangeValid, comparisonValid, rangeArray, ?_⟩
  rw [comparisonArray]
  simp only [optimizedInstructions, RangeDedup.reuseComparisons_removeDuplicateAssertions]

/-- Accepted ledger-call JSON retains the exact instruction vector emitted by
the production body over the actual accepted pruned plan. -/
theorem lowerEntrypoint_instructions (state : List StateDecl) (entry : Entrypoint)
    (program : Json) (accepted : lowerEntrypoint state entry = .ok program) :
    ∃ plan, Impact.lower state (Passes.pruneEntrypoint entry) = .ok plan ∧
      Native.arrayField program "instructions" =
        .ok ((lowerEntrypointBody (Passes.pruneEntrypoint entry) plan).run {}).2.instructions := by
  obtain ⟨plan, _, planAccepted, _, _, instructions⟩ :=
    lowerEntrypoint_validation_and_instructions state entry program accepted
  exact ⟨plan, planAccepted, instructions⟩

end Noctium.Backend.Zkir
