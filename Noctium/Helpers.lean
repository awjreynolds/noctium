import Noctium.Wire
import Noctium.NativeExpression
import Noctium.Semantics
import Noctium.Types.ValueExpressions
import Noctium.Types.ValueViews
import Noctium.Types.ValueSchema
import Noctium.GuardedExpression

namespace Noctium.Helpers

/-- Declaration identity is independent of spelling and overload signatures. -/
structure DeclarationId where
  scope : Nat
  ordinal : Nat
  deriving Repr, BEq, DecidableEq, Inhabited

inductive ResultType where
  | unit
  | scalar (ty : Ty)
  | composite (type : Types.CompositeType)
  deriving Repr, BEq, Inhabited

inductive EffectKind where
  | witness | privateState | ledgerRead | ledgerWrite
  | assertion | fallibleCast | event | crossCall
  deriving Repr, BEq, DecidableEq

abbrev Effects := List EffectKind

def EffectKind.impure : EffectKind → Bool
  | .assertion | .fallibleCast => false
  | _ => true

structure Scope where
  id : Nat
  parent : Option Nat := none
  /-- A value binding stops function lookup through this scope. -/
  values : List String := []
  deriving Repr, Inhabited

structure Parameter where
  name : String
  ty : Ty
  deriving Repr, Inhabited

def Parameter.resultType (parameter : Parameter) : ResultType :=
  .scalar parameter.ty

structure WitnessParameter where
  name : String
  type : ResultType
  deriving Repr

/-- Explicit host identity. Returning a value grants no circuit truth or release authority. -/
structure WitnessSignature where
  name : String
  operation : String
  capability : String
  privateKey : Option String := none
  parameters : List WitnessParameter := []
  result : ResultType
  span : SourceSpan := {}
  deriving Repr

/-- Closed set of curve operations admitted in readable helper/control bodies.
Argument and result types are fixed here so helper typing and native lowering
share one signature table. -/
inductive CurveOp where
  | scalarFromNative
  | scalarToNative
  | mulGenerator
  | mul
  | add
  | neg
  | x
  | y
  | fromCoordinates
  | hashToCurve (arity : Nat)
  | foreignUnary (operation : Foreign.UnaryOp)
  | foreignBinary (operation : Foreign.BinaryOp)
  | foreignEncodedField (kind : Foreign.Kind) (index : Nat)
  deriving Repr, BEq, DecidableEq, Inhabited

def CurveOp.operationName : CurveOp → String
  | .scalarFromNative => "jubjubScalarFromNative"
  | .scalarToNative => "jubjubScalarToNative"
  | .mulGenerator => "jubjubMulGenerator"
  | .mul => "jubjubMul"
  | .add => "jubjubAdd"
  | .neg => "jubjubNeg"
  | .x => "jubjubX"
  | .y => "jubjubY"
  | .fromCoordinates => "jubjubFromCoordinates"
  | .hashToCurve arity => s!"hashToCurve:{arity}"
  | .foreignUnary operation =>
    s!"foreignUnary:{operation.name}:{operation.inputKind.sourceName}"
  | .foreignBinary operation =>
    s!"foreignBinary:{operation.name}:{operation.leftKind.sourceName}:{operation.rightKind.sourceName}"
  | .foreignEncodedField kind index => s!"foreignEncodedField:{kind.sourceName}:{index}"

def CurveOp.signature : CurveOp → List Ty × Ty
  | .scalarFromNative => ([.native], .jubjubScalar)
  | .scalarToNative => ([.jubjubScalar], .native)
  | .mulGenerator => ([.jubjubScalar], .jubjubPoint)
  | .mul => ([.jubjubPoint, .jubjubScalar], .jubjubPoint)
  | .add => ([.jubjubPoint, .jubjubPoint], .jubjubPoint)
  | .neg => ([.jubjubPoint], .jubjubPoint)
  | .x | .y => ([.jubjubPoint], .native)
  | .fromCoordinates => ([.native, .native], .jubjubPoint)
  | .hashToCurve arity => (List.replicate arity .native, .jubjubPoint)
  | .foreignUnary operation =>
    ([.foreign operation.inputKind], .foreign operation.outputKind)
  | .foreignBinary operation =>
    ([.foreign operation.leftKind, .foreign operation.rightKind], .foreign operation.outputKind)
  | .foreignEncodedField kind _ => ([.foreign kind], .native)

/-- Closed readable byte/hash operations. Vector and fixed-byte lengths are
bounded at the typed source boundary, and point hashing follows FAB affine
coordinates. -/
inductive BytesOp where
  | bytesLiteral (length : Nat) (values : List Nat)
  | persistentHash32
  | persistentHashVector32
  | persistentHashNative
  | persistentHashNativeVector
  | transientHashNativeVector
  | persistentHashPoint
  | sha256 (length : Nat)
  | sha512 (length : Nat)
  | keccak256 (length : Nat)
  | keccak256Secp256k1Point
  | reverseBytes32
  | reverseBytes (length : Nat)
  | sliceBytes (length start stop : Nat)
  | concatBytes (leftLength rightLength : Nat)
  | foreignToBytes (kind : Foreign.Kind)
  | foreignFromBytes (kind : Foreign.Kind) (length : Nat)
  | degradeToNative
  | toBytes32 (source : Ty)
  | serialize (source : Ty) (length : Nat)
  | deserialize (target : Ty) (length : Nat)
  | fromBytesChecked (target : Ty) (length : Nat)
  deriving Repr, BEq, DecidableEq, Inhabited

def BytesOp.operationName : BytesOp → String
  | .bytesLiteral _ _ => "bytesLiteral"
  | .persistentHash32 => "persistentHash32"
  | .persistentHashVector32 => "persistentHashVector32"
  | .persistentHashNative => "persistentHashNative"
  | .persistentHashNativeVector => "persistentHashNativeVector"
  | .transientHashNativeVector => "transientHashNativeVector"
  | .persistentHashPoint => "persistentHashPoint"
  | .sha256 length => s!"sha256:{length}"
  | .sha512 length => s!"sha512:{length}"
  | .keccak256 length => s!"keccak256:{length}"
  | .keccak256Secp256k1Point => "keccak256:Secp256k1Point"
  | .reverseBytes32 => "reverseBytes32"
  | .reverseBytes length => s!"reverseBytes:{length}"
  | .sliceBytes length start stop => s!"sliceBytes:{length}:{start}:{stop}"
  | .concatBytes leftLength rightLength => s!"concatBytes:{leftLength}:{rightLength}"
  | .foreignToBytes kind => s!"foreignToBytes:{kind.sourceName}"
  | .foreignFromBytes kind length => s!"foreignFromBytes:{kind.sourceName}:{length}"
  | .degradeToNative => "degradeToNative"
  | .toBytes32 .native => "nativeToBytes32"
  | .toBytes32 .jubjubScalar => "jubjubScalarToBytes32"
  | .toBytes32 .jubjubPoint => "jubjubPointToBytes32"
  | .toBytes32 _ => "unsupportedToBytes32"
  | .serialize source length => s!"serialize:{NativeExpression.typeName source}:{length}"
  | .deserialize target length => s!"deserialize:{NativeExpression.typeName target}:{length}"
  | .fromBytesChecked target length =>
    s!"fromBytesChecked:{NativeExpression.typeName target}:{length}"

def BytesOp.signature (operation : BytesOp) (argumentCount : Nat) : Except String (List Ty × Ty) := do
  match operation with
  | .bytesLiteral length values =>
    unless argumentCount == 0 do throw "bytes literal does not accept arguments"
    unless length ≤ Types.defaultLimits.maxVectorLength do throw "byte literal length exceeds the source limit"
    unless values.length == length && values.all (· ≤ 255) do
      throw "byte literal must contain exactly its declared number of octets"
    pure ([], .bytes length)
  | .persistentHash32 =>
    unless argumentCount == 1 do throw "persistentHash32 requires one Bytes32 argument"
    pure ([.bytes 32], .bytes 32)
  | .persistentHashVector32 =>
    unless argumentCount ≥ 1 && argumentCount ≤ 32 do
      throw "persistentHashVector32 requires 1 to 32 Bytes32 arguments"
    pure (List.replicate argumentCount (.bytes 32), .bytes 32)
  | .persistentHashNative =>
    unless argumentCount == 1 do throw "persistentHashNative requires one Native argument"
    pure ([.native], .bytes 32)
  | .persistentHashNativeVector =>
    unless argumentCount ≥ 1 && argumentCount ≤ 32 do
      throw "persistentHashNativeVector requires 1 to 32 Native arguments"
    pure (List.replicate argumentCount .native, .bytes 32)
  | .transientHashNativeVector =>
    unless argumentCount ≤ Types.defaultLimits.maxVectorLength do
      throw "transientHashNativeVector field count is outside the source limit"
    pure (List.replicate argumentCount .native, .native)
  | .persistentHashPoint =>
    unless argumentCount == 1 do throw "persistentHashPoint requires one JubjubPoint argument"
    pure ([.jubjubPoint], .bytes 32)
  | .sha256 length =>
    unless argumentCount == 1 do throw "sha256 requires one byte-string argument"
    unless length ≤ Types.defaultLimits.maxVectorLength do throw "sha256 input length exceeds the source limit"
    pure ([.bytes length], .bytes 32)
  | .sha512 length =>
    unless argumentCount == 1 do throw "sha512 requires one byte-string argument"
    unless length ≤ Types.defaultLimits.maxVectorLength do throw "sha512 input length exceeds the source limit"
    pure ([.bytes length], .bytes 64)
  | .keccak256 length =>
    unless argumentCount == 1 do throw "keccak256 requires one byte-string argument"
    unless length ≤ Types.defaultLimits.maxVectorLength do throw "keccak256 input length exceeds the source limit"
    pure ([.bytes length], .bytes 32)
  | .keccak256Secp256k1Point =>
    unless argumentCount == 1 do throw "keccak256 Secp256k1Point requires one point argument"
    pure ([.foreign (.point .secp256k1)], .bytes 32)
  | .reverseBytes32 =>
    unless argumentCount == 1 do throw "reverseBytes32 requires one Bytes32 argument"
    pure ([.bytes 32], .bytes 32)
  | .reverseBytes length =>
    unless argumentCount == 1 do throw "reverseBytes requires one byte-string argument"
    unless length ≤ Types.defaultLimits.maxVectorLength do throw "reverseBytes length exceeds the source limit"
    pure ([.bytes length], .bytes length)
  | .sliceBytes length start stop =>
    unless argumentCount == 1 do throw "sliceBytes requires one byte-string argument"
    unless length ≤ Types.defaultLimits.maxVectorLength do throw "sliceBytes length exceeds the source limit"
    unless start ≤ stop && stop ≤ length do throw "sliceBytes bounds are outside the source byte string"
    pure ([.bytes length], .bytes (stop - start))
  | .concatBytes leftLength rightLength =>
    unless argumentCount == 2 do throw "concatBytes requires two byte-string arguments"
    unless leftLength ≤ Types.defaultLimits.maxVectorLength &&
        rightLength ≤ Types.defaultLimits.maxVectorLength &&
        leftLength + rightLength ≤ Types.defaultLimits.maxVectorLength do
      throw "concatBytes result exceeds the source byte limit"
    pure ([.bytes leftLength, .bytes rightLength], .bytes (leftLength + rightLength))
  | .foreignToBytes kind => do
    unless argumentCount == 1 do throw "foreignToBytes requires one foreign value"
    pure ([.foreign kind], .bytes kind.byteLength)
  | .foreignFromBytes kind length => do
    unless argumentCount == 1 do throw "foreignFromBytes requires one byte-string argument"
    unless length ≤ Types.defaultLimits.maxVectorLength do
      throw "foreignFromBytes input length exceeds the source limit"
    if let .point _ := kind then
      unless length == kind.byteLength do
        throw s!"foreign point decoding requires exactly {kind.byteLength} bytes"
    pure ([.bytes length], .foreign kind)
  | .degradeToNative =>
    unless argumentCount == 1 do throw "degradeToNative requires one Bytes32 argument"
    pure ([.bytes 32], .native)
  | .toBytes32 source =>
    unless argumentCount == 1 do throw "toBytes32 requires one argument"
    unless source == .native || source == .jubjubScalar || source == .jubjubPoint do
      throw "toBytes32 requires Native, JubjubScalar or JubjubPoint"
    pure ([source], .bytes 32)
  | .serialize type length | .deserialize type length =>
    unless argumentCount == 1 do throw "wire codec requires one argument"
    let some width := Wire.scalarWidth type | throw "wire codec requires a scalar or fixed bytes"
    unless width ≤ length && length ≤ maxBytesLength do
      throw s!"wire codec requires a byte length from {width} through {maxBytesLength}"
    match operation with
    | .serialize .. => pure ([type], .bytes length)
    | _ => pure ([.bytes length], type)
  | .fromBytesChecked target length => do
    unless argumentCount == 1 do throw "fromBytesChecked requires one argument"
    unless 0 < length && length ≤ maxBytesLength do
      throw s!"fromBytesChecked requires a byte length from 1 through {maxBytesLength}"
    match target with
    | .native => pure ([.bytes length], .native)
    | .uint maximum => do
      ScalarPolicy.validate (.uint maximum)
      pure ([.bytes length], .uint maximum)
    | _ => throw "fromBytesChecked supports only Native and UInt"

inductive Term where
  | unit
  | native (number : Nat)
  | bool (value : Bool)
  | uint (maximum number : Nat)
  | ref (name : String)
  | binary (op : ScalarPolicy.Binary) (left right : Term)
  | boolAnd (left right : Term)
  | boolOr (left right : Term)
  | boolXor (left right : Term)
  | eq (left right : Term)
  | cast (target : Ty) (value : Term)
  | disclose (span : SourceSpan) (value : Term)
  | select (condition yes no : Term)
  | ite (condition yes no : Term)
  | andThen (left right : Term)
  | orElse (left right : Term)
  | witness (name : String) (ty : Ty)
  | witnessCall (site name : String) (arguments : List Term)
  | poseidon2 (domain : Nat) (left right : Term)
  | curve (operation : CurveOp) (arguments : List Term)
  | bytes (operation : BytesOp) (arguments : List Term)
  | bytes32Literal (values : List Nat)
  /-- A canonical typed foreign value, stored in its native wire encoding. -/
  | foreignConstant (kind : Foreign.Kind) (encoding : List Nat)
  /-- Project one checked byte from a fixed-length source byte string. -/
  | bytesAt (value : Term) (index : Nat)
  | call (name : String) (arguments : List Term)
  /-- A checked aggregate assembled from scalar source terms in canonical leaf order. -/
  | composite (type : Types.CompositeType) (leaves : List Term)
  /-- A static tuple, struct, enum-payload, vector or byte projection. -/
  | project (value : Term) (projection : Types.Projection)
  /-- A checked dynamic selection from a fixed-length vector. -/
  | index (value index : Term)
  /-- An external-effect fixture has a typed result, but no native implementation.
  Its label is recorded by the reference trace evaluator. -/
  | effect (kind : EffectKind) (label : String) (result : Term)
  | at (span : SourceSpan) (value : Term)
  deriving Repr

inductive Statement where
  | bind (name : String) (ty : ResultType) (value : Term)
  | evaluate (value : Term)
  | assert (condition : Term)
  | «return» (value : Option Term := none)
  | branch (condition : Term) (yes no : List Statement)
  /-- A half-open source range. Preparation lowers each iteration to a
  constant-true branch with a fresh Native index binding. -/
  | forRange (index : String) (start stop : Nat) (body : List Statement)
  | stage (capability key : String) (ty : Ty) (value : Term)
  | readCell (state destination : String) (ty : Ty)
  | writeCell (state : String) (ty : Ty) (value : Term)
  | readMap (state destination : String) (keyTy valueTy : Ty) (key : Term)
  | readMember (state destination : String) (keyTy valueTy : Ty) (key : Term)
  | writeMap (state : String) (keyTy valueTy : Ty) (key value : Term)
  | emitEvent (kind : EventKind) (payload : Term)
  deriving Repr

structure Declaration where
  id : DeclarationId
  name : String
  parameters : List Parameter := []
  /-- Nominal aggregate types keyed by parameter name; scalar Parameter stays source-compatible. -/
  compositeParameters : List (String × Types.CompositeType) := []
  result : ResultType := .unit
  body : List Statement := []
  declaredPure : Bool := false
  span : SourceSpan := {}
  deriving Repr

def Declaration.parameterType (declaration : Declaration) (parameter : Parameter) : ResultType :=
  match declaration.compositeParameters.lookup parameter.name with
  | some .unit => .unit
  | some type => .composite type
  | none => .scalar parameter.ty

structure AggregateInput where
  name : String
  type : Types.CompositeType
  visibility : Visibility
  span : SourceSpan := {}
  deriving Repr

structure Export where
  name : String
  target : DeclarationId
  inputs : List Input := []
  compositeInputs : List AggregateInput := []
  span : SourceSpan := {}
  deriving Repr

structure Program where
  scopes : List Scope := [{id := 0}]
  declarations : List Declaration := []
  exports : List Export := []
  composites : Types.CompositeEnv := {}
  witnesses : List WitnessSignature := []
  ledger : List StateDecl := []
  deriving Repr

private def fail (span : SourceSpan) (message : String) : Except Diagnostic α :=
  .error {span, message}

private def liftError (span : SourceSpan) (value : Except String α) : Except Diagnostic α :=
  match value with
  | .ok result => .ok result
  | .error message => fail span message

/-- Local compiler resource policy, independent of Compact language limits.
Expanded nodes are a conservative preflight bound, not an emitted-node count. -/
structure Limits where
  maxDeclarations : Nat := 256
  maxScopes : Nat := 256
  maxExports : Nat := 256
  maxParameters : Nat := 64
  maxSourceNodes : Nat := 16384
  maxSourceDepth : Nat := 128
  maxCallDepth : Nat := 64
  maxAnalysisSteps : Nat := 65536
  maxExpandedNodes : Nat := 65536
  maxExpandedDepth : Nat := 256
  maxExecutionSteps : Nat := 131072
  deriving Repr

private def curveArgumentLimit (limits : Limits) : CurveOp → Nat
  | .hashToCurve _ => Types.defaultLimits.maxVectorLength
  | _ => limits.maxParameters

private def resource (span : SourceSpan) (kind : String) : Except Diagnostic α :=
  fail span s!"helper resource limit exceeded: {kind}"

private def maxForRangeEndpoint : Nat := 2 ^ 248 - 1

private def validateCurveArity (span : SourceSpan) (operation : CurveOp) (arguments : List Term) :
    Except Diagnostic Unit := do
  if let .hashToCurve arity := operation then
    if arity > Types.defaultLimits.maxVectorLength then resource span "hashToCurve field count"
    unless arity == arguments.length do fail span "hashToCurve argument count mismatch"
  if let .foreignEncodedField kind index := operation then
    unless index < kind.encodedFieldCount do
      fail span "foreign encoded field index is out of range"

private def validateLimits (limits : Limits) : Except Diagnostic Unit := do
  let hard : Limits := {}
  let fields := [
    ("declarations", limits.maxDeclarations, hard.maxDeclarations),
    ("scopes", limits.maxScopes, hard.maxScopes),
    ("exports", limits.maxExports, hard.maxExports),
    ("parameters", limits.maxParameters, hard.maxParameters),
    ("source nodes", limits.maxSourceNodes, hard.maxSourceNodes),
    ("source depth", limits.maxSourceDepth, hard.maxSourceDepth),
    ("call depth", limits.maxCallDepth, hard.maxCallDepth),
    ("call analysis steps", limits.maxAnalysisSteps, hard.maxAnalysisSteps),
    ("expanded nodes", limits.maxExpandedNodes, hard.maxExpandedNodes),
    ("expanded depth", limits.maxExpandedDepth, hard.maxExpandedDepth),
    ("execution steps", limits.maxExecutionSteps, hard.maxExecutionSteps)]
  for (name, actual, maximum) in fields do
    if actual > maximum then resource {} s!"requested {name} exceeds hard policy"

private def textMetadata (text : String) : Except Diagnostic Unit := do
  if text.utf8ByteSize > 1024 then resource {} "metadata text"

private def validateForRange (span : SourceSpan) (index : String) (start stop : Nat) :
    Except Diagnostic Nat := do
  textMetadata index
  if start > maxForRangeEndpoint || stop > maxForRangeEndpoint then
    resource span "finite range endpoint"
  if start > stop then fail span "finite range start exceeds its stop"
  let count := stop - start
  if count > Types.defaultLimits.maxVectorLength then
    resource span "finite range length"
  pure count

def validWitnessIdentifier (name : String) : Bool :=
  !name.isEmpty && name.utf8ByteSize ≤ 128 && name.toList.all (fun c =>
    ('a' ≤ c && c ≤ 'z') || ('A' ≤ c && c ≤ 'Z') || ('0' ≤ c && c ≤ '9') || "_-.:".contains c)

def witnessSignature (program : Program) (name : String) (span : SourceSpan := {}) :
    Except Diagnostic WitnessSignature :=
  match program.witnesses.find? (·.name == name) with
  | some signature => pure signature
  | none => fail span s!"unknown typed witness '{name}'"

private def spanMetadata (span : SourceSpan) : Except Diagnostic Unit := do
  if span.file.utf8ByteSize > 1024 || span.line > 1000000000 || span.column > 1000000000 then
    resource {} "source-span metadata"

private def termMetadata : Term → Except Diagnostic Unit
  | .ref name | .call name _ | .witness name _ | .effect _ name _ => textMetadata name
  | .witnessCall site name _ => do
    unless validWitnessIdentifier site && validWitnessIdentifier name do
      fail {} "invalid typed witness site or provider identity"
  | .at span _ | .disclose span _ => spanMetadata span
  | .project _ (.field name) => textMetadata name
  | .project _ (.enumField variant name) => do textMetadata variant; textMetadata name
  | _ => pure ()

private def statementMetadata : Statement → Except Diagnostic Unit
  | .bind name _ _ => textMetadata name
  | .forRange index _ _ _ => textMetadata index
  | .stage capability key _ _ => do textMetadata capability; textMetadata key
  | .readCell state destination _ => do textMetadata state; textMetadata destination
  | .writeCell state _ _ => textMetadata state
  | .readMap state destination _ _ _ | .readMember state destination _ _ _ =>
    do textMetadata state; textMetadata destination
  | .writeMap state _ _ _ _ => textMetadata state
  | _ => pure ()

private def statementTerms : Statement → List Term
  | .bind _ _ value | .evaluate value | .assert value | .stage _ _ _ value => [value]
  | .writeCell _ _ value => [value]
  | .readCell .. => []
  | .readMap _ _ _ _ key | .readMember _ _ _ _ key => [key]
  | .writeMap _ _ _ key value => [key, value]
  | .emitEvent _ payload => [payload]
  | .branch condition _ _ => [condition]
  | .return value => value.toList
  | .forRange .. => []

private def checkLedgerSchema (span : SourceSpan) (ledger : List StateDecl) : Except Diagnostic Unit := do
  unless uniqueNames (ledger.map (·.name)) do fail span "duplicate helper ledger declaration"
  for state in ledger do
    textMetadata state.name
    match state.kind with
    | .cell ty =>
      liftError state.span (ty.validate Capabilities.source)
    | .map keyTy valueTy => do
      liftError state.span (keyTy.validate Capabilities.source)
      liftError state.span (valueTy.validate Capabilities.source)
    | .tree schema => liftError state.span (schema.validate Capabilities.source)
    | .merkleTree depth | .historicMerkleTree depth =>
      unless 2 ≤ depth && depth ≤ 32 do
        fail state.span "MerkleTree depth must be between 2 and 32"
    | .opaqueString =>
      unless state.sealed do fail state.span "OpaqueString state must be sealed"

/-- Traverse syntax with a bounded work list before invoking recursive passes. -/
private def scanTerms (limits : Limits) (span : SourceSpan) (available : Nat)
    (terms : List Term) : Except Diagnostic (Nat × Nat) := go available 0 0 (terms.map (·, 1))
where
  go : Nat → Nat → Nat → List (Term × Nat) → Except Diagnostic (Nat × Nat)
    | _, used, deepest, [] => pure (used, deepest)
    | 0, _, _, _ :: _ => resource span "source nodes"
    | fuel + 1, used, deepest, (term, depth) :: rest => do
      if depth > limits.maxSourceDepth then resource span "source depth"
      termMetadata term
      let children ← match term with
        | .binary _ a b | .boolAnd a b | .boolOr a b | .boolXor a b
        | .eq a b | .poseidon2 _ a b
        | .andThen a b | .orElse a b => pure [a, b]
        | .cast _ value | .disclose _ value | .effect _ _ value | .at _ value
        | .project value _ | .bytesAt value _ => pure [value]
        | .composite _ leaves => pure leaves
        | .index value index => pure [value, index]
        | .select c a b | .ite c a b => pure [c, a, b]
        | .call _ arguments | .witnessCall _ _ arguments => do
          if arguments.length > limits.maxParameters then resource span "call arguments"
          pure arguments
        | .curve operation arguments => do
          validateCurveArity span operation arguments
          if arguments.length > curveArgumentLimit limits operation then resource span "curve arguments"
          pure arguments
        | .bytes _ arguments => do
          if arguments.length > limits.maxParameters then resource span "byte operation arguments"
          pure arguments
        | _ => pure []
      go fuel (used + 1) (max deepest depth) (children.map (·, depth + 1) ++ rest)

private inductive SourceNode where
  | term (value : Term)
  | statement (value : Statement)

/-- Branch bodies share the source budget, including inactive and post-return syntax. -/
private def scanBody (limits : Limits) (span : SourceSpan) (available : Nat)
    (body : List Statement) : Except Diagnostic (Nat × Nat × Nat) :=
  if body.length > available then resource span "source nodes"
  else go available 0 0 0 (body.map fun value => (SourceNode.statement value, 0))
where
  go : Nat → Nat → Nat → Nat → List (SourceNode × Nat) → Except Diagnostic (Nat × Nat × Nat)
    | _, used, statements, deepest, [] => pure (used, statements, deepest)
    | 0, _, _, _, _ :: _ => resource span "source nodes"
    | fuel + 1, used, statements, deepest, (node, depth) :: rest => do
      if depth > limits.maxSourceDepth then resource span "source depth"
      let (children, statements) ← match node with
        | .statement value => do
          statementMetadata value
          let terms := (statementTerms value).map SourceNode.term
          let arms ← match value with
            | .branch _ yes no => do
              if yes.length + no.length > fuel then resource span "source nodes"
              pure ((yes ++ no).map SourceNode.statement)
            | .forRange index start stop body => do
              discard (validateForRange span index start stop)
              if body.length > fuel then resource span "source nodes"
              pure (body.map SourceNode.statement)
            | _ => pure []
          pure (terms ++ arms, statements + 1)
        | .term value => do
          termMetadata value
          let terms ← match value with
            | .binary _ a b | .boolAnd a b | .boolOr a b | .boolXor a b
            | .eq a b | .poseidon2 _ a b
            | .andThen a b | .orElse a b => pure [a, b]
            | .cast _ value | .disclose _ value | .effect _ _ value | .at _ value
            | .project value _ | .bytesAt value _ => pure [value]
            | .composite _ leaves => pure leaves
            | .index value index => pure [value, index]
            | .select c a b | .ite c a b => pure [c, a, b]
            | .call _ arguments | .witnessCall _ _ arguments => do
              if arguments.length > limits.maxParameters then resource span "call arguments"
              pure arguments
            | .curve operation arguments => do
              validateCurveArity span operation arguments
              if arguments.length > curveArgumentLimit limits operation then resource span "curve arguments"
              pure arguments
            | .bytes _ arguments => do
              if arguments.length > limits.maxParameters then resource span "byte operation arguments"
              pure arguments
            | _ => pure []
          pure (terms.map SourceNode.term, statements)
      go fuel (used + 1) statements (max deepest depth)
        (children.map (·, depth + 1) ++ rest)

private structure SourceSize where
  nodes : Nat
  depth : Nat

private def witnessSites (body : List Statement) (fuel : Nat) : Except Diagnostic (List String) :=
  go fuel (body.map SourceNode.statement) []
where
  go : Nat → List SourceNode → List String → Except Diagnostic (List String)
    | _, [], sites => pure sites
    | 0, _ :: _, _ => resource {} "typed witness site traversal"
    | fuel + 1, node :: rest, sites => do
      match node with
      | .statement statement =>
        let children := (statementTerms statement).map SourceNode.term
        let arms := match statement with
          | .branch _ yes no => (yes ++ no).map SourceNode.statement
          | .forRange _ _ _ body => body.map SourceNode.statement
          | _ => []
        go fuel (children ++ arms ++ rest) sites
      | .term term =>
        if let .curve operation arguments := term then
          validateCurveArity {} operation arguments
          if arguments.length > curveArgumentLimit ({} : Limits) operation then
            resource {} "curve arguments"
        let (children, site) := match term with
          | .witnessCall site _ arguments => (arguments, some site)
          | .call _ arguments | .composite _ arguments => (arguments, none)
          | .curve _ arguments => (arguments, none)
          | .bytes _ arguments => (arguments, none)
          | .binary _ a b | .boolAnd a b | .boolOr a b | .boolXor a b
          | .eq a b | .poseidon2 _ a b | .andThen a b | .orElse a b
          | .index a b => ([a, b], none)
          | .cast _ value | .disclose _ value | .effect _ _ value | .at _ value
          | .project value _ | .bytesAt value _ => ([value], none)
          | .select c a b | .ite c a b => ([c, a, b], none)
          | _ => ([], none)
        let sites ← match site with
          | none => pure sites
          | some site => do
            if sites.contains site then fail {} "duplicate typed witness site in helper declaration"
            pure (site :: sites)
        go fuel (children.map SourceNode.term ++ rest) sites

private def checkedComposite (program : Program) (span : SourceSpan)
    (type : Types.CompositeType) : Except Diagnostic Types.CompiledType :=
  match Types.compileType program.composites type with
  | .ok compiled => pure compiled
  | .error diagnostic => fail (if diagnostic.span.file.isEmpty then span else diagnostic.span) diagnostic.message

/-- Select a child type using the same checked layout as projection lowering. -/
def projectedType (composites : Types.CompositeEnv) (span : SourceSpan)
    (parent : Types.CompositeType) (projection : Types.Projection) : Except Diagnostic Types.CompositeType := do
  discard (checkedComposite {composites} span parent)
  match parent, projection with
  | .tuple items, .tupleIndex index =>
    match items[index]? with
    | some type => pure type
    | none => fail span "aggregate tuple projection out of bounds"
  | .structure id, .field name =>
    match composites.structures.find? (·.id == id) with
    | none => fail span s!"unknown aggregate struct '{id}'"
    | some declaration =>
      match declaration.fields.find? (·.name == name) with
      | some field => pure field.type
      | none => fail span s!"unknown aggregate struct field '{name}'"
  | .vector length type, .vectorIndex index =>
    if index < length then pure type else fail span "aggregate vector projection out of bounds"
  | .bytes length, .byteIndex index =>
    if index < length then pure (.scalar (.uint 255)) else fail span "aggregate byte projection out of bounds"
  | .enumeration id, .enumField variant name =>
    match composites.enumerations.find? (·.id == id) with
    | none => fail span s!"unknown aggregate enum '{id}'"
    | some declaration =>
      match declaration.variants.find? (·.name == variant) with
      | none => fail span s!"unknown aggregate enum variant '{variant}'"
      | some selected =>
        match selected.fields.find? (·.name == name) with
        | some field => pure field.type
        | none => fail span s!"unknown aggregate enum field '{name}'"
  | .enumeration _, .enumTag => pure (.scalar .native)
  | _, _ => fail span "aggregate projection kind/type mismatch"

private def validateResultType (program : Program) (span : SourceSpan) : ResultType → Except Diagnostic Unit
  | .unit => pure ()
  | .scalar type => do
    liftError span (type.validate Capabilities.crypto)
  | .composite type => discard (checkedComposite program span type)

partial def sourceLeafTypes : Types.Layout → List Ty
  | .unit => []
  | .scalar .nativeField => [.native]
  | .scalar .booleanField => [.bool]
  | .scalar (.boundedUnsignedField maximum) => [.uint maximum]
  | .scalar (.enumTagField _) => [.native]
  | .scalar .byteField => [.native]
  | .curve type => [type]
  | .tuple items => items.flatMap sourceLeafTypes
  | .structure _ fields => fields.flatMap (sourceLeafTypes ∘ Prod.snd)
  | .vector length element => (List.range length).flatMap fun _ => sourceLeafTypes element
  | .bytes length _ => List.replicate length .native
  | .enumeration _ _ _ payloadLeaves _ _ => .native :: List.replicate payloadLeaves .native

/-- The common checked layout preserves both operands' canonical leaf order. -/
def checkedAggregateEquality (program : Program) (span : SourceSpan)
    (left right : Types.CompositeType) : Except Diagnostic Types.CompiledType := do
  let some common := left.leastUpperBound? right
    | fail span "helper equality requires compatible checked aggregate types"
  checkedComposite program span common

partial def sourceLeafPaths : Types.Layout → String → List String
  | .unit, _ => []
  | .scalar _, path => [path]
  | .curve type, path => (List.range type.nativeCallFieldCount).map fun index =>
      path ++ s!".$curve{index}"
  | .tuple items, path => items.zipIdx.flatMap fun (item, index) =>
      sourceLeafPaths item (path ++ s!".{index}")
  | .structure _ fields, path => fields.flatMap fun (name, item) =>
      sourceLeafPaths item (path ++ s!".{name}")
  | .vector length element, path => (List.range length).flatMap fun index =>
      sourceLeafPaths element (path ++ s!".{index}")
  | .bytes length _, path => (List.range length).map fun index => path ++ s!".{index}"
  | .enumeration _ _ _ payloadLeaves _ _, path =>
      (path ++ ".$tag") :: ((List.range payloadLeaves).map fun index => path ++ s!".$payload{index}")

private def aggregateInputName (root component : String) : String :=
  if component.isEmpty then root else root ++ component

private def aggregateInputs (program : Program) (entry : Export) : Except Diagnostic (List Input) := do
  let mut inputs := entry.inputs
  for input in entry.compositeInputs do
    let compiled ← checkedComposite program input.span input.type
    let names := sourceLeafPaths compiled.checked.value ""
    unless names.length == compiled.checked.expandedLeaves do
      fail input.span "aggregate source input path count mismatch"
    inputs := inputs ++ (names.map fun path => {
      name := aggregateInputName input.name path, ty := .native,
      visibility := input.visibility, span := input.span : Input})
  pure inputs

private def sourcePreflight (limits : Limits) (program : Program) :
    Except Diagnostic (List (DeclarationId × SourceSize)) := do
  validateLimits limits
  if program.ledger.length > limits.maxDeclarations then resource {} "ledger declarations"
  checkLedgerSchema {} program.ledger
  if program.declarations.length > limits.maxDeclarations then resource {} "declarations"
  if program.scopes.length > limits.maxScopes then resource {} "scopes"
  if program.exports.length > limits.maxExports then resource {} "exports"
  if program.witnesses.length > 32 then resource {} "typed witness declarations"
  unless uniqueNames (program.witnesses.map (·.name)) do fail {} "duplicate typed witness declaration"
  for signature in program.witnesses do
    spanMetadata signature.span
    unless validWitnessIdentifier signature.name && validWitnessIdentifier signature.operation &&
        signature.operation.endsWith ".v1" && validWitnessIdentifier signature.capability do
      fail signature.span "invalid typed witness operation or capability identity"
    if signature.operation == "private_state.stage.v1" || signature.operation == "private_state.compare_exchange.v1" then
      fail signature.span "private staging and commit operations require the controlled journal lifecycle"
    if signature.operation == "private_state.read.v1" then
      let some key := signature.privateKey | fail signature.span "private state reads require an explicit source key"
      unless !key.isEmpty && key.utf8ByteSize ≤ 128 && !key.startsWith "/" && !key.endsWith "/" &&
          (key.splitOn "/").all (fun part => validWitnessIdentifier part && part != "." && part != "..") &&
          signature.parameters.isEmpty do
        fail signature.span "invalid typed private-state read key or arguments"
    else if signature.privateKey.isSome then fail signature.span "only private-state reads accept a source key"
    if signature.parameters.length > limits.maxParameters then resource signature.span "typed witness arguments"
    unless uniqueNames (signature.parameters.map (·.name)) do fail signature.span "duplicate typed witness argument"
    for parameter in signature.parameters do
      unless validWitnessIdentifier parameter.name do fail signature.span "invalid typed witness argument name"
      if parameter.type == .unit then fail signature.span "typed witness arguments cannot have Unit type"
      validateResultType program signature.span parameter.type
    validateResultType program signature.span signature.result
  for scope in program.scopes do
    if scope.id > 18446744073709551615 then resource {} "declaration identity metadata"
    if scope.values.length > limits.maxParameters then resource {} "scope bindings"
    for name in scope.values do textMetadata name
  for entry in program.exports do
    textMetadata entry.name
    spanMetadata entry.span
    if entry.target.scope > 18446744073709551615 || entry.target.ordinal > 18446744073709551615 then
      resource {} "declaration identity metadata"
    if entry.inputs.length > limits.maxParameters then resource entry.span "entry inputs"
    if entry.inputs.length + entry.compositeInputs.length > limits.maxParameters then resource entry.span "entry inputs"
    for input in entry.inputs do
      textMetadata input.name
      spanMetadata input.span
    for input in entry.compositeInputs do
      textMetadata input.name
      spanMetadata input.span
      discard (checkedComposite program input.span input.type)
  let mut available := limits.maxSourceNodes
  let mut sizes := []
  for declaration in program.declarations do
    textMetadata declaration.name
    spanMetadata declaration.span
    if declaration.id.scope > 18446744073709551615 || declaration.id.ordinal > 18446744073709551615 then
      resource {} "declaration identity metadata"
    if declaration.parameters.length > limits.maxParameters then resource declaration.span "parameters"
    for parameter in declaration.parameters do textMetadata parameter.name
    unless uniqueNames (declaration.compositeParameters.map Prod.fst) do
      fail declaration.span "duplicate composite helper parameter type"
    for (name, type) in declaration.compositeParameters do
      textMetadata name
      unless declaration.parameters.any (·.name == name) do
        fail declaration.span s!"composite helper type for unknown parameter '{name}'"
      validateResultType program declaration.span (.composite type)
    for parameter in declaration.parameters do
      validateResultType program declaration.span (declaration.parameterType parameter)
    validateResultType program declaration.span declaration.result
    let (nodes, statements, depth) ← scanBody limits declaration.span available declaration.body
    discard (witnessSites declaration.body limits.maxSourceNodes)
    available := available - nodes
    sizes := (declaration.id, {
      nodes := 3 * (nodes + declaration.parameters.length + 2)
      depth := 3 * (statements + depth + declaration.parameters.length + 2)}) :: sizes
  pure sizes

private partial def bodyHasForRange : List Statement → Bool
  | [] => false
  | .forRange _ _ _ _ :: _ => true
  | .branch _ yes no :: rest =>
    bodyHasForRange yes || bodyHasForRange no || bodyHasForRange rest
  | _ :: rest => bodyHasForRange rest

private def traversalTermChildren : Term → List Term
  | .binary _ left right | .boolAnd left right | .boolOr left right | .boolXor left right
  | .eq left right | .poseidon2 _ left right | .andThen left right | .orElse left right => [left, right]
  | .cast _ value | .disclose _ value | .effect _ _ value | .at _ value
  | .project value _ | .bytesAt value _ => [value]
  | .select condition yes no | .ite condition yes no => [condition, yes, no]
  | .witnessCall _ _ arguments | .call _ arguments | .composite _ arguments
  | .curve _ arguments | .bytes _ arguments => arguments
  | .index value index => [value, index]
  | _ => []

private def saturatedMultiply (limit left right : Nat) : Nat :=
  min (limit + 1) (left * right)

private def saturatedSourceAdd (limit left right : Nat) : Nat :=
  min (limit + 1) (left + right)

/-- Count the compiler-owned expansion without constructing any copies. Every
generated iteration costs four source nodes for its branch, condition, index
binding and index value, plus the expanded body. -/
private def expandedSourceNodeCount (limits : Limits) (program : Program) :
    Except Diagnostic Nat :=
  go limits.maxSourceNodes 0
    (program.declarations.flatMap fun declaration =>
      declaration.body.map fun statement => (SourceNode.statement statement, 1))
where
  go : Nat → Nat → List (SourceNode × Nat) → Except Diagnostic Nat
    | _, count, [] => pure count
    | 0, _, _ :: _ => resource {} "expanded source traversal"
    | fuel + 1, count, (node, multiplier) :: rest => do
      let cap := limits.maxSourceNodes
      match node with
      | .statement statement =>
        match statement with
        | .forRange index start stop body => do
          let iterations ← validateForRange {} index start stop
          let copies := saturatedMultiply cap multiplier iterations
          let count := saturatedSourceAdd cap count (saturatedMultiply cap copies 4)
          let children := body.map fun child => (SourceNode.statement child, copies)
          go fuel count (children ++ rest)
        | _ =>
          let count := saturatedSourceAdd cap count multiplier
          let terms := (statementTerms statement).map fun term => (SourceNode.term term, multiplier)
          let arms := match statement with
            | .branch _ yes no => (yes ++ no).map fun child => (SourceNode.statement child, multiplier)
            | _ => []
          go fuel count (terms ++ arms ++ rest)
      | .term term =>
        let count := saturatedSourceAdd cap count multiplier
        let children := (traversalTermChildren term).map fun child => (SourceNode.term child, multiplier)
        go fuel count (children ++ rest)

private structure ExpansionState where
  reservedSites : List String
  nextSite : Nat := 0

private abbrev ExpansionM := StateM ExpansionState

private def freshLoopWitnessSite : ExpansionM String := do
  let mut selected : Option String := none
  while selected.isNone do
    let state ← get
    let candidate := "noctium.loop.call." ++ toString state.nextSite
    set {state with nextSite := state.nextSite + 1}
    if validWitnessIdentifier candidate && !state.reservedSites.contains candidate then
      modify fun current => {current with reservedSites := candidate :: current.reservedSites}
      selected := some candidate
  pure (selected.getD "noctium.loop.call.0")

private partial def freshenTermWitnessSites (term : Term) : ExpansionM Term := do
  match term with
  | .binary operation left right =>
    return .binary operation (← freshenTermWitnessSites left) (← freshenTermWitnessSites right)
  | .boolAnd left right => return .boolAnd (← freshenTermWitnessSites left) (← freshenTermWitnessSites right)
  | .boolOr left right => return .boolOr (← freshenTermWitnessSites left) (← freshenTermWitnessSites right)
  | .boolXor left right => return .boolXor (← freshenTermWitnessSites left) (← freshenTermWitnessSites right)
  | .eq left right => return .eq (← freshenTermWitnessSites left) (← freshenTermWitnessSites right)
  | .cast target value => return .cast target (← freshenTermWitnessSites value)
  | .disclose span value => return .disclose span (← freshenTermWitnessSites value)
  | .select condition yes no =>
    return .select (← freshenTermWitnessSites condition) (← freshenTermWitnessSites yes)
      (← freshenTermWitnessSites no)
  | .ite condition yes no =>
    return .ite (← freshenTermWitnessSites condition) (← freshenTermWitnessSites yes)
      (← freshenTermWitnessSites no)
  | .andThen left right => return .andThen (← freshenTermWitnessSites left) (← freshenTermWitnessSites right)
  | .orElse left right => return .orElse (← freshenTermWitnessSites left) (← freshenTermWitnessSites right)
  | .witnessCall _site name arguments => do
    let site ← freshLoopWitnessSite
    return .witnessCall site name (← arguments.mapM freshenTermWitnessSites)
  | .poseidon2 domain left right =>
    return .poseidon2 domain (← freshenTermWitnessSites left) (← freshenTermWitnessSites right)
  | .curve operation arguments => return .curve operation (← arguments.mapM freshenTermWitnessSites)
  | .bytes operation arguments => return .bytes operation (← arguments.mapM freshenTermWitnessSites)
  | .bytesAt value index => return .bytesAt (← freshenTermWitnessSites value) index
  | .call name arguments => return .call name (← arguments.mapM freshenTermWitnessSites)
  | .composite type leaves => return .composite type (← leaves.mapM freshenTermWitnessSites)
  | .project value projection => return .project (← freshenTermWitnessSites value) projection
  | .index value index => return .index (← freshenTermWitnessSites value) (← freshenTermWitnessSites index)
  | .effect kind label result => return .effect kind label (← freshenTermWitnessSites result)
  | .at span value => return .at span (← freshenTermWitnessSites value)
  | value => pure value

mutual
private partial def freshenStatementWitnessSites (statement : Statement) : ExpansionM Statement := do
  match statement with
  | .bind name type value => return .bind name type (← freshenTermWitnessSites value)
  | .evaluate value => return .evaluate (← freshenTermWitnessSites value)
  | .assert condition => return .assert (← freshenTermWitnessSites condition)
  | .return value => return .return (← value.mapM freshenTermWitnessSites)
  | .branch condition yes no =>
    return .branch (← freshenTermWitnessSites condition)
      (← freshenStatementsWitnessSites yes) (← freshenStatementsWitnessSites no)
  | .forRange index start stop body =>
    return .forRange index start stop (← freshenStatementsWitnessSites body)
  | .stage capability key type value =>
    return .stage capability key type (← freshenTermWitnessSites value)
  | .readCell .. => pure statement
  | .readMap state destination keyType valueType key =>
    return .readMap state destination keyType valueType (← freshenTermWitnessSites key)
  | .readMember state destination keyType valueType key =>
    return .readMember state destination keyType valueType (← freshenTermWitnessSites key)
  | .writeCell state type value => return .writeCell state type (← freshenTermWitnessSites value)
  | .writeMap state keyType valueType key value =>
    return .writeMap state keyType valueType (← freshenTermWitnessSites key)
      (← freshenTermWitnessSites value)
  | .emitEvent kind payload => return .emitEvent kind (← freshenTermWitnessSites payload)

private partial def freshenStatementsWitnessSites (body : List Statement) : ExpansionM (List Statement) :=
  body.mapM freshenStatementWitnessSites
end

mutual
private partial def expandRangeStatement (statement : Statement) : ExpansionM (List Statement) := do
  match statement with
  | .branch condition yes no =>
    return [.branch condition (← expandRangeBody yes) (← expandRangeBody no)]
  | .forRange index start stop body => do
    let mut expanded := []
    for offset in List.range (stop - start) do
      let body ← expandRangeBody body
      let body ← freshenStatementsWitnessSites body
      let indexValue := Statement.bind index (.scalar .native) (.native (start + offset))
      expanded := expanded ++ [.branch (.bool true) (indexValue :: body) []]
    return expanded
  | statement => return [statement]

private partial def expandRangeBody (body : List Statement) : ExpansionM (List Statement) := do
  let mut expanded := []
  for statement in body do
    expanded := expanded ++ (← expandRangeStatement statement)
  pure expanded
end

private partial def rejectLoopReturns (span : SourceSpan) (fuel : Nat)
    (body : List Statement) : Except Diagnostic Unit := go fuel body
where
  go : Nat → List Statement → Except Diagnostic Unit
    | _, [] => pure ()
    | 0, _ :: _ => resource span "finite range return scan"
    | fuel + 1, statement :: rest => match statement with
      | .return _ => fail span "return cannot escape a finite range body"
      | .branch _ yes no => go fuel (yes ++ no ++ rest)
      | .forRange _ _ _ nested => go fuel (nested ++ rest)
      | _ => go fuel rest

/-- Change declaration bodies while preserving program metadata and declaration
identity. This bridge lets source transformations reuse the checked resolver. -/
private def mapDeclarationBody (transform : List Statement → List Statement)
    (declaration : Declaration) : Declaration :=
  {declaration with body := transform declaration.body}

def mapDeclarationBodies (transform : List Statement → List Statement)
    (program : Program) : Program :=
  {program with declarations := program.declarations.map (mapDeclarationBody transform)}

private theorem mapDeclarationBodies_scopes (transform : List Statement → List Statement)
    (program : Program) : (mapDeclarationBodies transform program).scopes = program.scopes := rfl

private theorem mapDeclarationBodies_declarations (transform : List Statement → List Statement)
    (program : Program) :
    (mapDeclarationBodies transform program).declarations =
      program.declarations.map (mapDeclarationBody transform) := rfl

/-- Finding a declaration by its stable id commutes with mapping its body.
This keeps entrypoint lookup aligned with the checked helper resolver after a
source transformation. -/
theorem mapDeclarationBodies_findDeclarationById
    (transform : List Statement → List Statement) (program : Program) (id : DeclarationId) :
    ((mapDeclarationBodies transform program).declarations.find?
        (fun declaration => declaration.id == id)) =
      (program.declarations.find? (fun declaration => declaration.id == id)).map
        (fun declaration => {declaration with body := transform declaration.body}) := by
  rw [mapDeclarationBodies_declarations]
  induction program.declarations with
  | nil => simp
  | cons declaration rest ih =>
      by_cases h : declaration.id == id
      · simp [h, mapDeclarationBody]
      · simp [h, mapDeclarationBody, ih]

/-- Public admission result for source syntax and resource limits. -/
def syntacticPreflight (limits : Limits) (program : Program) : Except Diagnostic Unit := do
  (sourcePreflight limits program).map fun _ => ()

def commonType : ResultType → ResultType → Option ResultType
  | .unit, .unit => some .unit
  | .scalar left, .scalar right => (.scalar ·) <$> Types.scalarLeastUpperBound? left right
  | .composite left, .composite right =>
    (.composite ·) <$> Types.CompositeType.leastUpperBound? left right
  | _, _ => none

def subtype (source target : ResultType) : Bool := commonType source target == some target

private def compatible (arguments : List ResultType) (declaration : Declaration) : Bool :=
  arguments.length == declaration.parameters.length &&
    (arguments.zip declaration.parameters).all fun (actual, parameter) =>
      subtype actual (declaration.parameterType parameter)

private def helperCandidate (scope : Nat) (name : String)
    (arguments : List (Option ResultType)) (declaration : Declaration) : Bool :=
  declaration.id.scope == scope && declaration.name == name &&
    arguments.length == declaration.parameters.length &&
    (arguments.zip declaration.parameters).all fun (actual, parameter) =>
      match actual with
      | none => true
      | some actual => subtype actual (declaration.parameterType parameter)

private def selectCandidates (span : SourceSpan) (name : String) :
    List Declaration → Except Diagnostic (Option Declaration)
  | [declaration] => pure (some declaration)
  | _ :: _ :: _ => fail span s!"ambiguous helper overload '{name}'"
  | [] => pure none

/-- Search one lexical group at a time. An ambiguous inner group never falls back. -/
private def resolveUncheckedPartial (program : Program) (scope : Nat) (name : String)
    (arguments : List (Option ResultType))
    (span : SourceSpan := {}) : Except Diagnostic Declaration := go (program.scopes.length + 1) scope
where
  go : Nat → Nat → Except Diagnostic Declaration
    | 0, _ => fail span "helper lexical scope cycle"
    | fuel + 1, scope => do
      let some group := program.scopes.find? (·.id == scope)
        | fail span "unknown helper lexical scope"
      if group.values.contains name then fail span s!"helper '{name}' is hidden by a value binding"
      else
        let candidates := program.declarations.filter (helperCandidate scope name arguments)
        match selectCandidates span name candidates with
        | .error diagnostic => .error diagnostic
        | .ok (some declaration) => .ok declaration
        | .ok none => match group.parent with
          | some parent => go fuel parent
          | none => fail span s!"no compatible helper overload '{name}'"

private def resolveUnchecked (program : Program) (scope : Nat) (name : String)
    (arguments : List ResultType) (span : SourceSpan := {}) : Except Diagnostic Declaration :=
  resolveUncheckedPartial program scope name (arguments.map some) span

def resolveWithLimits (limits : Limits) (program : Program) (scope : Nat) (name : String)
    (arguments : List ResultType) (span : SourceSpan := {}) : Except Diagnostic Declaration := do
  discard (sourcePreflight limits program)
  spanMetadata span
  textMetadata name
  if arguments.length > limits.maxParameters then resource span "call arguments"
  resolveUnchecked program scope name arguments span

/-- Resolve a helper when some argument types are not known yet. An omitted
type matches any parameter, while known arguments keep ordinary subtype checks. -/
def resolveWithPartialTypes (limits : Limits) (program : Program) (scope : Nat) (name : String)
    (arguments : List (Option ResultType)) (span : SourceSpan := {}) :
    Except Diagnostic Declaration := do
  discard (sourcePreflight limits program)
  spanMetadata span
  textMetadata name
  if arguments.length > limits.maxParameters then resource span "call arguments"
  resolveUncheckedPartial program scope name arguments span

def resolve (program : Program) (scope : Nat) (name : String) (arguments : List ResultType)
    (span : SourceSpan := {}) : Except Diagnostic Declaration :=
  resolveWithLimits {} program scope name arguments span

private theorem helperCandidate_mapDeclarationBody (transform : List Statement → List Statement)
    (scope : Nat) (name : String) (arguments : List (Option ResultType)) (declaration : Declaration) :
    helperCandidate scope name arguments (mapDeclarationBody transform declaration) =
      helperCandidate scope name arguments declaration := by
  cases declaration
  rfl

private theorem filterHelperCandidates_mapDeclarationBody
    (transform : List Statement → List Statement) (scope : Nat) (name : String)
    (arguments : List (Option ResultType)) (declarations : List Declaration) :
    (declarations.map (mapDeclarationBody transform)).filter
        (helperCandidate scope name arguments) =
      (declarations.filter (helperCandidate scope name arguments)).map
        (mapDeclarationBody transform) := by
  induction declarations with
  | nil => rfl
  | cons declaration rest ih =>
      simp only [List.map_cons, List.filter_cons, helperCandidate_mapDeclarationBody, ih]
      split <;> rfl

private theorem selectCandidates_mapDeclarationBody
    (transform : List Statement → List Statement) (span : SourceSpan) (name : String)
    (declarations : List Declaration) :
    selectCandidates span name (declarations.map (mapDeclarationBody transform)) =
      (selectCandidates span name declarations).map (Option.map (mapDeclarationBody transform)) := by
  cases declarations with
  | nil => rfl
  | cons first rest => cases rest with
    | nil => rfl
    | cons second tail => rfl

private theorem resolveUncheckedPartial_go_mapDeclarationBodies
    (transform : List Statement → List Statement) (program : Program)
    (name : String) (arguments : List (Option ResultType)) (span : SourceSpan) :
    ∀ fuel scope,
      resolveUncheckedPartial.go (mapDeclarationBodies transform program) name arguments span fuel scope =
        (resolveUncheckedPartial.go program name arguments span fuel scope).map
          (mapDeclarationBody transform) := by
  intro fuel
  induction fuel with
  | zero => intro scope; simp [resolveUncheckedPartial.go, fail, Except.map]
  | succ fuel ih =>
      intro scope
      unfold resolveUncheckedPartial.go
      rw [mapDeclarationBodies_scopes]
      cases hgroup : program.scopes.find? (fun x => x.id == scope) with
      | none => simp [hgroup, fail, Except.map, Except.bind]
      | some group =>
          cases hhidden : group.values.contains name with
          | true =>
              have hmem : name ∈ group.values := List.contains_iff_mem.mp hhidden
              simp [hgroup, hhidden, hmem, fail, Except.map, Except.bind]
          | false =>
              have hmem : name ∉ group.values := by
                intro h
                have htrue := List.contains_iff_mem.mpr h
                rw [hhidden] at htrue
                cases htrue
              have hcandidates := filterHelperCandidates_mapDeclarationBody
                transform scope name arguments program.declarations
              simp [hgroup, hhidden, hmem]
              rw [mapDeclarationBodies_declarations]
              rw [hcandidates]
              rw [selectCandidates_mapDeclarationBody]
              let candidates := program.declarations.filter (helperCandidate scope name arguments)
              cases hselection : selectCandidates span name candidates with
              | error error => simp [hselection, candidates, fail, Except.map]
              | ok selected =>
                  cases selected with
                  | some declaration => simp [hselection, candidates, mapDeclarationBody, Except.map]
                  | none =>
                      cases hparent : group.parent with
                      | none => simp [hselection, candidates, hparent, fail, Except.map]
                      | some parent => simp [hselection, candidates, hparent, ih, fail, Except.map]

private theorem resolveUnchecked_mapDeclarationBodies
    (transform : List Statement → List Statement) (program : Program)
    (scope : Nat) (name : String) (arguments : List ResultType) (span : SourceSpan) :
    resolveUnchecked (mapDeclarationBodies transform program) scope name arguments span =
      (resolveUnchecked program scope name arguments span).map (mapDeclarationBody transform) := by
  unfold resolveUnchecked resolveUncheckedPartial
  rw [mapDeclarationBodies_scopes]
  exact resolveUncheckedPartial_go_mapDeclarationBodies transform program name
    (arguments.map some) span _ _

private theorem sourcePreflight_result_of_admitted (limits : Limits) (program : Program)
    (admitted : syntacticPreflight limits program = .ok ()) :
    ∃ sizes, sourcePreflight limits program = .ok sizes := by
  unfold syntacticPreflight at admitted
  cases result : sourcePreflight limits program with
  | error diagnostic =>
      simp only [result, Except.map] at admitted
      cases admitted
  | ok sizes => exact ⟨sizes, rfl⟩

theorem resolveWithLimits_mapDeclarationBodies
    (limits : Limits) (transform : List Statement → List Statement)
    (program : Program) (scope : Nat) (name : String)
    (arguments : List ResultType) (span : SourceSpan := {})
    (sourceAdmitted : syntacticPreflight limits program = .ok ())
    (mappedAdmitted : syntacticPreflight limits (mapDeclarationBodies transform program) = .ok ()) :
    resolveWithLimits limits (mapDeclarationBodies transform program) scope name arguments span =
      (resolveWithLimits limits program scope name arguments span).map fun declaration =>
        {declaration with body := transform declaration.body} := by
  rcases sourcePreflight_result_of_admitted limits program sourceAdmitted with
    ⟨sourceSizes, sourceResult⟩
  rcases sourcePreflight_result_of_admitted limits (mapDeclarationBodies transform program) mappedAdmitted with
    ⟨mappedSizes, mappedResult⟩
  have hresolve := resolveUnchecked_mapDeclarationBodies transform program scope name arguments span
  change resolveWithLimits limits (mapDeclarationBodies transform program) scope name arguments span =
    (resolveWithLimits limits program scope name arguments span).map (mapDeclarationBody transform)
  unfold resolveWithLimits
  rw [sourceResult, mappedResult]
  cases hspan : spanMetadata span with
  | error diagnostic =>
      simp [hspan, Except.map, Except.bind, Except.instMonad, Monad.toBind,
        Bind.bind, Functor.discard, Functor.mapConst, Applicative.toFunctor]
  | ok spanValue =>
      cases hname : textMetadata name with
      | error diagnostic =>
          simp [hspan, hname, Except.map, Except.bind, Except.instMonad, Monad.toBind,
            Bind.bind, Functor.discard, Functor.mapConst, Applicative.toFunctor]
      | ok nameValue =>
          by_cases harguments : limits.maxParameters < arguments.length
          · cases hresource : resource span "call arguments" with
            | error diagnostic =>
                simp [harguments, hresource, Except.map, Except.bind, Except.instMonad, Monad.toBind,
                  Bind.bind, Functor.discard, Functor.mapConst, Applicative.toFunctor]
            | ok unit =>
                simp [harguments, hresource, hresolve, mapDeclarationBody, Except.map, Except.bind,
                  Except.instMonad, Monad.toBind, Bind.bind, Functor.discard,
                  Functor.mapConst, Applicative.toFunctor]
          · simp [hspan, hname, harguments, hresolve, mapDeclarationBody,
              Except.map, Except.bind, Except.instMonad, Monad.toBind, Bind.bind,
              Functor.discard, Functor.mapConst, Applicative.toFunctor]

abbrev Environment := List (String × ResultType)
abbrev PartialEnvironment := List (String × Option ResultType)

private def scalar (span : SourceSpan) : ResultType → Except Diagnostic Ty
  | .scalar ty => pure ty
  | .unit => fail span "unit is not a scalar helper argument"
  | .composite _ => fail span "aggregate helper value is not a scalar"

def resultTypeOfComposite : Types.CompositeType → ResultType
  | .unit => .unit
  | .scalar type => .scalar type
  | type => .composite type

def indexResultType (span : SourceSpan) (parent index : ResultType) : Except Diagnostic ResultType := do
  let .composite (.vector length element) := parent
    | fail span "dynamic aggregate index requires a vector value"
  unless length > 0 do fail span "cannot dynamically index an empty aggregate vector"
  let indexType ← scalar span index
  unless indexType == .native || (match indexType with | .uint _ => true | _ => false) do
    fail span "aggregate index requires Native or UInt"
  pure (resultTypeOfComposite element)

private def common (span : SourceSpan) (left right : Ty) : Except Diagnostic Ty := do
  if subtype (.scalar left) (.scalar right) then pure right
  else if subtype (.scalar right) (.scalar left) then pure left
  else fail span "incompatible helper scalar types"

private def lookup (program : Program) (id : DeclarationId) (span : SourceSpan) : Except Diagnostic Declaration :=
  match program.declarations.find? (·.id == id) with
  | some declaration => pure declaration
  | none => fail span "unknown helper declaration identity"

structure TermInfo (Ty := ResultType) where
  ty : Ty
  calls : List DeclarationId := []
  effects : Effects := []
  guarded : Bool := false
  deriving Repr, Inhabited

private abbrev PartialTermInfo := TermInfo (Option ResultType)

private def combine {Ty : Type} (ty : Ty) (children : List (TermInfo Ty)) (effects : Effects := []) : TermInfo Ty :=
  {ty, calls := children.flatMap (·.calls), effects := (children.flatMap (·.effects) ++ effects).eraseDups, guarded := children.any (·.guarded)}

private def partialSubtype (source : Option ResultType) (target : ResultType) : Bool :=
  match source with
  | none => true
  | some source => subtype source target

private def knownType (span : SourceSpan) : Option ResultType → Except Diagnostic ResultType
  | some ty => pure ty
  | none => fail span "unknown helper type cannot be used here"

private def partialCommonType (left right : Option ResultType) : Option (Option ResultType) :=
  match left, right with
  | none, right => some right
  | left, none => some left
  | some left, some right => (some ·) <$> commonType left right

private def inferPartialTerm (fuel : Nat) (program : Program) (scope : Nat)
    (env : PartialEnvironment) (span : SourceSpan) (value : Term) : Except Diagnostic PartialTermInfo :=
  match fuel with
  | 0 => resource span "type-analysis depth"
  | fuel + 1 => do
    match value with
    | .unit => pure {ty := some .unit}
    | .native number =>
      unless number < Field.modulus do fail span "noncanonical helper native constant"
      pure {ty := some (.scalar .native)}
    | .bool _ => pure {ty := some (.scalar .bool)}
    | .uint maximum number =>
      liftError span (ScalarPolicy.validate (.uint maximum))
      unless number ≤ maximum do fail span "helper unsigned constant exceeds declared bound"
      pure {ty := some (.scalar (.uint maximum))}
    | .ref name =>
      let some ty := env.lookup name | fail span s!"unknown helper value '{name}'"
      pure {ty}
    | .binary op left right =>
      let left ← inferPartialTerm fuel program scope env span left
      let right ← inferPartialTerm fuel program scope env span right
      let lt ← scalar span (← knownType span left.ty)
      let rt ← scalar span (← knownType span right.ty)
      let result ← liftError span (ScalarPolicy.infer op lt.scalarKind rt.scalarKind)
      let ty ← match result with
        | .native => pure Ty.native
        | .bool => pure Ty.bool
        | .uint maximum => pure (Ty.uint maximum)
        | .bytes _ => fail span "byte strings do not support scalar arithmetic"
        | .opaqueBytes => fail span "OpaqueBytes do not support scalar arithmetic"
        | .jubjubScalar | .jubjubPoint =>
          fail span "Jubjub values require a qualified curve operation"
        | .foreign _ => fail span "foreign values require a qualified curve operation"
      pure (combine (some (.scalar ty)) [left, right]
        (if op == .sub && lt != .native && rt != .native then [.fallibleCast] else []))
    | .boolAnd left right | .boolOr left right | .boolXor left right =>
      let left ← inferPartialTerm fuel program scope env span left
      let right ← inferPartialTerm fuel program scope env span right
      unless left.ty == some (.scalar .bool) && right.ty == some (.scalar .bool) do
        fail span "eager Boolean operands require Bool"
      pure (combine (some (.scalar .bool)) [left, right])
    | .eq left right =>
      let left ← inferPartialTerm fuel program scope env span left
      let right ← inferPartialTerm fuel program scope env span right
      match left.ty, right.ty with
      | some (.composite left), some (.composite right) =>
        discard (checkedAggregateEquality program span left right)
      | _, _ =>
        discard (common span (← scalar span (← knownType span left.ty))
          (← scalar span (← knownType span right.ty)))
      pure (combine (some (.scalar .bool)) [left, right])
    | .cast target value =>
      if target.isBytes then fail span "byte strings do not support scalar casts"
      liftError span (target.validate {poseidon2 := true})
      let value ← inferPartialTerm fuel program scope env span value
      let source ← scalar span (← knownType span value.ty)
      if source.isBytes then fail span "byte strings do not support scalar casts"
      pure (combine (some (.scalar target)) [value] [.fallibleCast])
    | .disclose _ value => inferPartialTerm fuel program scope env span value
    | .select condition yes no =>
      let condition ← inferPartialTerm fuel program scope env span condition
      unless condition.ty == some (.scalar .bool) do fail span "helper selector requires Bool"
      let yes ← inferPartialTerm fuel program scope env span yes
      let no ← inferPartialTerm fuel program scope env span no
      let ty ← common span (← scalar span (← knownType span yes.ty)) (← scalar span (← knownType span no.ty))
      pure (combine (some (.scalar ty)) [condition, yes, no])
    | .ite condition yes no =>
      let condition ← inferPartialTerm fuel program scope env span condition
      unless condition.ty == some (.scalar .bool) do fail span "helper condition requires Bool"
      let yes ← inferPartialTerm fuel program scope env span yes
      let no ← inferPartialTerm fuel program scope env span no
      let some ty := partialCommonType yes.ty no.ty
        | fail span "conditional branches require a common type"
      pure {combine ty [condition, yes, no] with guarded := true}
    | .andThen left right | .orElse left right =>
      let left ← inferPartialTerm fuel program scope env span left
      let right ← inferPartialTerm fuel program scope env span right
      unless left.ty == some (.scalar .bool) && right.ty == some (.scalar .bool) do
        fail span "short-circuit operands require Bool"
      pure {combine (some (.scalar .bool)) [left, right] with guarded := true}
    | .witness _ ty =>
      liftError span (ty.validate Capabilities.crypto)
      pure {ty := some (.scalar ty), effects := [.witness]}
    | .witnessCall _ name arguments =>
      let signature ← witnessSignature program name span
      let arguments ← arguments.mapM (inferPartialTerm fuel program scope env span)
      unless arguments.length == signature.parameters.length do fail span "typed witness argument arity mismatch"
      for (argument, parameter) in arguments.zip signature.parameters do
        unless partialSubtype argument.ty parameter.type do fail span "typed witness argument type mismatch"
      pure (combine (some signature.result) arguments [.witness])
    | .poseidon2 domain left right =>
      unless domain < Field.modulus do fail span "noncanonical helper hash domain"
      let left ← inferPartialTerm fuel program scope env span left
      let right ← inferPartialTerm fuel program scope env span right
      unless partialSubtype left.ty (.scalar .native) && partialSubtype right.ty (.scalar .native) do
        fail span "helper hash arguments require Native"
      pure (combine (some (.scalar .native)) [left, right])
    | .curve operation arguments => do
      validateCurveArity span operation arguments
      if arguments.length > curveArgumentLimit ({} : Limits) operation then
        resource span "curve arguments"
      let (expected, result) := operation.signature
      unless arguments.length == expected.length do
        fail span s!"{operation.operationName} argument count mismatch"
      let values ← arguments.mapM (inferPartialTerm fuel program scope env span)
      for (value, expectedType) in values.zip expected do
        unless partialSubtype value.ty (.scalar expectedType) do
          fail span s!"{operation.operationName} argument type mismatch"
      pure (combine (some (.scalar result)) values
        (match operation with
          | .fromCoordinates | .foreignUnary (.inv _) | .foreignUnary (.x _) |
            .foreignUnary (.y _) | .foreignBinary (.fromCoordinates _) => [.fallibleCast]
          | _ => []))
    | .bytes32Literal bytes => do
      unless bytes.length == 32 && bytes.all (· ≤ 255) do
        fail span "Bytes32 literal must contain exactly 32 byte values"
      pure {ty := some (.scalar (.bytes 32))}
    | .foreignConstant kind encoding => do
      liftError span ((Ty.foreign kind).validate Capabilities.crypto)
      discard (Foreign.decodeValue kind encoding |>.mapError fun message => {span, message})
      pure {ty := some (.scalar (.foreign kind))}
    | .bytes operation arguments => do
      let (expected, result) ← (operation.signature arguments.length).mapError fun message =>
        {span, message}
      let values ← arguments.mapM (inferPartialTerm fuel program scope env span)
      for (value, expectedType) in values.zip expected do
        unless partialSubtype value.ty (.scalar expectedType) do
          fail span s!"{operation.operationName} argument type mismatch"
      pure (combine (some (.scalar result)) values
        (match operation with
          | .foreignFromBytes (.point _) _ | .deserialize .. => [.fallibleCast]
          | _ => []))
    | .bytesAt value index => do
      let value ← inferPartialTerm fuel program scope env span value
      let .scalar (.bytes length) := (← knownType span value.ty)
        | fail span "byteAt requires a fixed byte-string value"
      unless index < length do
        fail span "byteAt index is outside the byte string"
      pure (combine (some (.scalar (.uint 255))) [value])
    | .call name arguments =>
      if (env.lookup name).isSome then fail span s!"helper '{name}' is hidden by a value binding"
      let arguments ← arguments.mapM (inferPartialTerm fuel program scope env span)
      let declaration ← resolveUncheckedPartial program scope name (arguments.map (·.ty)) span
      let info := combine (some declaration.result) arguments
      pure {info with calls := declaration.id :: info.calls}
    | .composite type leaves => do
      let compiled ← checkedComposite program span type
      let values ← leaves.mapM (inferPartialTerm fuel program scope env span)
      let expected := sourceLeafTypes compiled.checked.value
      unless values.length == expected.length do fail span "aggregate source leaf count mismatch"
      for (value, expectedType) in values.zip expected do
        unless partialSubtype value.ty (.scalar expectedType) do
          fail span "aggregate source leaf type mismatch"
      pure (combine (some (resultTypeOfComposite type)) values)
    | .project value projection => do
      let parent ← inferPartialTerm fuel program scope env span value
      let .composite type := (← knownType span parent.ty) | fail span "aggregate projection requires a composite value"
      let selected ← projectedType program.composites span type projection
      pure (combine (some (resultTypeOfComposite selected)) [parent])
    | .index value index => do
      let parent ← inferPartialTerm fuel program scope env span value
      let index ← inferPartialTerm fuel program scope env span index
      pure (combine (some (← indexResultType span (← knownType span parent.ty) (← knownType span index.ty))) [parent, index])
    | .effect kind _ result =>
      unless kind.impure do fail span "external helper effects require an external effect category"
      let result ← inferPartialTerm fuel program scope env span result
      pure (combine result.ty [result] [kind])
    | .at span value => inferPartialTerm fuel program scope env span value

private def inferTerm (fuel : Nat) (program : Program) (scope : Nat) (env : Environment)
    (span : SourceSpan) (value : Term) : Except Diagnostic TermInfo := do
  let info ← inferPartialTerm fuel program scope (env.map fun (name, ty) => (name, some ty)) span value
  let some ty := info.ty | fail span "unknown helper type in typed environment"
  pure {ty, calls := info.calls, effects := info.effects, guarded := info.guarded}

structure Summary where
  id : DeclarationId
  calls : List DeclarationId
  direct : Effects
  effects : Effects := []
  guarded : Bool := false
  expandedNodes : Nat := 0
  expandedDepth : Nat := 0
  callDepth : Nat := 0
  deriving Repr, Inhabited

/-- Check all body syntax, including statements after a return. Execution still
stops at the first return. Branch syntax will use the same syntax-wide walk. -/
private structure BodyInfo where
  calls : List DeclarationId := []
  effects : Effects := []
  guarded : Bool := false
  returned : Bool := false
  deriving Inhabited

private def checkedCell (program : Program) (span : SourceSpan) (name : String) (ty : Ty)
    (write : Bool) : Except Diagnostic Unit := do
  liftError span (ty.validate Capabilities.source)
  let some state := program.ledger.find? (·.name == name)
    | fail span s!"unknown helper ledger cell '{name}'"
  match state.kind with
  | .cell actual =>
    unless actual == ty do fail span s!"ledger cell '{name}' type mismatch"
    if write && state.sealed then fail span s!"sealed state '{name}' cannot be written"
  | _ => fail span s!"state '{name}' is not a scalar cell"

private def inputNames (program : Program) (target : DeclarationId) : List String :=
  program.exports.filter (·.target == target) |>.flatMap fun entry =>
    entry.inputs.map (·.name) ++ entry.compositeInputs.flatMap fun input =>
      match Types.compileType program.composites input.type with
      | .ok compiled => sourceLeafPaths compiled.checked.value input.name
      | .error _ => [input.name]

private def checkedMap (program : Program) (span : SourceSpan) (name : String)
    (keyTy valueTy : Ty) (write : Bool := false) : Except Diagnostic Unit := do
  liftError span ((LedgerValueType.map keyTy (.scalar valueTy)).validate Capabilities.source)
  let some state := program.ledger.find? (·.name == name)
    | fail span s!"unknown helper ledger map '{name}'"
  unless state.kind == .map keyTy valueTy do
    fail span s!"ledger map '{name}' type mismatch"
  if write && state.sealed then fail span s!"sealed state '{name}' cannot be written"

private def checkBody (limits : Limits) (program : Program) (declaration : Declaration)
    (fuel : Nat) (env : PartialEnvironment) (body : List Statement)
    (locals : List String) : Except Diagnostic BodyInfo :=
  match fuel with
  | 0 => resource declaration.span "statement-analysis depth"
  | fuel + 1 => do
    let span := declaration.span
    let mut env := env
    let mut locals := locals
    let mut result : BodyInfo := {}
    for statement in body do
      let info ← match statement with
        | .bind name ty value => do
          validateResultType program span ty
          if locals.contains name then fail span s!"duplicate helper value '{name}'"
          let info ← inferPartialTerm limits.maxSourceDepth program declaration.id.scope env span value
          unless partialSubtype info.ty ty do fail span "helper binding type mismatch"
          env := (name, some ty) :: env
          locals := name :: locals
          pure info
        | .evaluate value => inferPartialTerm limits.maxSourceDepth program declaration.id.scope env span value
        | .assert condition => do
          let info ← inferPartialTerm limits.maxSourceDepth program declaration.id.scope env span condition
          unless info.ty == some (.scalar .bool) do fail span "helper assertion requires Bool"
          pure {info with effects := (.assertion :: info.effects).eraseDups}
        | .return value => do
          let info ← match value with
            | some value => inferPartialTerm limits.maxSourceDepth program declaration.id.scope env span value
            | none => pure {ty := some .unit}
          unless partialSubtype info.ty declaration.result do fail span "helper return type mismatch"
          result := {result with returned := true}
          pure info
        | .branch condition yes no => do
          let condition ← inferPartialTerm limits.maxSourceDepth program declaration.id.scope env span condition
          unless condition.ty == some (.scalar .bool) do fail span "helper condition requires Bool"
          let yes ← checkBody limits program declaration fuel env yes []
          let no ← checkBody limits program declaration fuel env no []
          result := {result with returned := result.returned || (yes.returned && no.returned)}
          pure {ty := some .unit, calls := condition.calls ++ yes.calls ++ no.calls, effects := (condition.effects ++ yes.effects ++ no.effects).eraseDups, guarded := true}
        | .forRange index start stop loopBody => do
          discard (validateForRange span index start stop)
          rejectLoopReturns span limits.maxSourceNodes loopBody
          let bodyInfo ← checkBody limits program declaration fuel
            ((index, some (.scalar .native)) :: env) loopBody [index]
          pure {ty := some .unit, calls := bodyInfo.calls, effects := bodyInfo.effects, guarded := bodyInfo.guarded}
        | .stage _ _ ty value => do
          liftError span (ty.validate Capabilities.crypto)
          let info ← inferPartialTerm limits.maxSourceDepth program declaration.id.scope env span value
          unless partialSubtype info.ty (.scalar ty) do fail span "private stage type mismatch"
          pure {info with effects := (.privateState :: info.effects).eraseDups}
        | .readCell state destination ty => do
          checkedCell program span state ty false
          if locals.contains destination || (inputNames program declaration.id).contains destination then
            fail span s!"ledger read destination '{destination}' shadows an existing binding"
          env := (destination, some (.scalar ty)) :: env
          locals := destination :: locals
          pure {ty := some .unit, effects := [.ledgerRead]}
        | .writeCell state ty value => do
          checkedCell program span state ty true
          let info ← inferPartialTerm limits.maxSourceDepth program declaration.id.scope env span value
          unless partialSubtype info.ty (.scalar ty) do fail span "ledger cell write type mismatch"
          pure {info with effects := (.ledgerWrite :: info.effects).eraseDups}
        | .readMap state destination keyTy valueTy key
        | .readMember state destination keyTy valueTy key => do
          checkedMap program span state keyTy valueTy
          let info ← inferPartialTerm limits.maxSourceDepth program declaration.id.scope env span key
          unless partialSubtype info.ty (.scalar keyTy) do fail span "ledger map key type mismatch"
          if locals.contains destination || (inputNames program declaration.id).contains destination then
            fail span s!"ledger read destination '{destination}' shadows an existing binding"
          let resultTy := match statement with
            | .readMember .. => Ty.bool
            | _ => valueTy
          env := (destination, some (.scalar resultTy)) :: env
          locals := destination :: locals
          pure {info with ty := some .unit, effects := (.ledgerRead :: info.effects).eraseDups}
        | .writeMap state keyTy valueTy key value => do
          checkedMap program span state keyTy valueTy true
          let key ← inferPartialTerm limits.maxSourceDepth program declaration.id.scope env span key
          unless partialSubtype key.ty (.scalar keyTy) do fail span "ledger map key type mismatch"
          let value ← inferPartialTerm limits.maxSourceDepth program declaration.id.scope env span value
          unless partialSubtype value.ty (.scalar valueTy) do fail span "ledger map value type mismatch"
          pure (combine (some .unit) [key, value] [.ledgerWrite])
        | .emitEvent kind payload => do
          let info ← inferPartialTerm limits.maxSourceDepth program declaration.id.scope env span payload
          unless partialSubtype info.ty (.scalar (.bytes kind.payloadSize)) do
            fail span "helper ledger event payload type mismatch"
          pure {info with ty := some .unit, effects := (.event :: info.effects).eraseDups}
      result := {result with
        calls := result.calls ++ info.calls
        effects := (result.effects ++ info.effects).eraseDups
        guarded := result.guarded || info.guarded}
    pure result

private def checkDeclarationWithEnvironmentUnchecked (limits : Limits) (program : Program)
    (declaration : Declaration) (env : PartialEnvironment) : Except Diagnostic Summary := do
  let span := declaration.span
  unless uniqueNames (declaration.parameters.map (·.name)) do fail span "duplicate helper parameter"
  unless env.map (·.1) == declaration.parameters.map (·.name) do
    fail span "partial helper parameter names do not match declaration"
  for (_, ty) in env do
    if let some ty := ty then validateResultType program span ty
  validateResultType program span declaration.result
  let info ← checkBody limits program declaration limits.maxSourceDepth env declaration.body
    (env.map (·.1))
  unless info.returned || declaration.result == .unit do fail span "helper fall-through returns unit, incompatible with declared result"
  pure {id := declaration.id, calls := info.calls, direct := info.effects, guarded := info.guarded}

private def checkDeclarationUnchecked (limits : Limits) (program : Program) (declaration : Declaration) :
    Except Diagnostic Summary :=
  checkDeclarationWithEnvironmentUnchecked limits program declaration
    (declaration.parameters.map fun parameter => (parameter.name, some (declaration.parameterType parameter)))

private def prepareProgramAndSizes (limits : Limits) (program : Program) :
    Except Diagnostic (Program × List (DeclarationId × SourceSize)) := do
  let sizes ← sourcePreflight limits program
  let expandedNodes ← expandedSourceNodeCount limits program
  if expandedNodes > limits.maxSourceNodes then resource {} "expanded source nodes"
  if program.declarations.any (fun declaration => bodyHasForRange declaration.body) then
    for declaration in program.declarations do
      if bodyHasForRange declaration.body then
        discard (checkDeclarationUnchecked limits program declaration)
    let originalSites ← program.declarations.mapM fun declaration =>
      witnessSites declaration.body limits.maxSourceNodes
    let initial : ExpansionState := {reservedSites := originalSites.flatten}
    let expandDeclarations : ExpansionM (List Declaration) := do
      program.declarations.mapM fun (declaration : Declaration) => do
        let body ← expandRangeBody declaration.body
        pure {declaration with body}
    let (declarations, _) := expandDeclarations.run initial
    let prepared := {program with declarations}
    pure (prepared, ← sourcePreflight limits prepared)
  else pure (program, sizes)

/-- Validate and lower finite ranges into ordinary checked helper syntax.
Expansion happens only after the weighted source budget and original body
typing checks pass. -/
def prepareProgramWithLimits (limits : Limits) (program : Program) :
    Except Diagnostic Program :=
  (prepareProgramAndSizes limits program).map Prod.fst

def inferWithLimits (limits : Limits) (program : Program) (scope : Nat) (env : Environment)
    (span : SourceSpan) (value : Term) : Except Diagnostic TermInfo := do
  let program ← prepareProgramWithLimits limits program
  spanMetadata span
  discard (scanTerms limits span limits.maxSourceNodes [value])
  if env.length > limits.maxSourceNodes then resource span "type environment"
  for (name, _) in env do textMetadata name
  inferTerm limits.maxSourceDepth program scope env span value

def inferPartialWithLimits (limits : Limits) (program : Program) (scope : Nat)
    (env : PartialEnvironment) (span : SourceSpan) (value : Term) :
    Except Diagnostic (TermInfo (Option ResultType)) := do
  let program ← prepareProgramWithLimits limits program
  spanMetadata span
  discard (scanTerms limits span limits.maxSourceNodes [value])
  if env.length > limits.maxSourceNodes then resource span "type environment"
  for (name, _) in env do textMetadata name
  inferPartialTerm limits.maxSourceDepth program scope env span value

def infer (program : Program) (scope : Nat) (env : Environment) (span : SourceSpan)
    (value : Term) : Except Diagnostic TermInfo :=
  inferWithLimits {} program scope env span value

def checkDeclarationWithLimits (limits : Limits) (program : Program) (declaration : Declaration) :
    Except Diagnostic Summary := do
  let program ← prepareProgramWithLimits limits program
  discard (sourcePreflight limits {program with declarations := [declaration]})
  let declaration := (program.declarations.find? (·.id == declaration.id)).getD declaration
  checkDeclarationUnchecked limits program declaration

def checkPartialDeclarationWithLimits (limits : Limits) (program : Program)
    (declaration : Declaration) (env : PartialEnvironment) : Except Diagnostic Summary := do
  let candidate := {program with declarations := program.declarations ++ [declaration]}
  discard (sourcePreflight limits candidate)
  let expandedNodes ← expandedSourceNodeCount limits candidate
  if expandedNodes > limits.maxSourceNodes then resource declaration.span "expanded source nodes"
  let program ← prepareProgramWithLimits limits program
  if env.length > limits.maxSourceNodes then resource declaration.span "type environment"
  for (name, _) in env do textMetadata name
  checkDeclarationWithEnvironmentUnchecked limits program declaration env

def checkDeclaration (program : Program) (declaration : Declaration) : Except Diagnostic Summary :=
  checkDeclarationWithLimits {} program declaration

private structure AnalysisState where
  remaining : Nat
  cache : List Summary := []
  deriving Inhabited

private def saturatedAdd (limit left right : Nat) : Nat := min (limit + 1) (left + right)

/-- Cache summaries before another call site traverses the same callee. Keep
call-site multiplicity when adding expansion bounds, including duplicate edges. -/
private def summarize (limits : Limits) (summaries : List Summary)
    (sizes : List (DeclarationId × SourceSize)) (span : SourceSpan) (id : DeclarationId) :
    StateT AnalysisState (Except Diagnostic) Summary := go limits.maxCallDepth [] id
where
  go : Nat → List DeclarationId → DeclarationId → StateT AnalysisState (Except Diagnostic) Summary
    | fuel, stack, id => do
      let state ← get
      if state.remaining == 0 then liftM (resource span "call analysis steps")
      set {state with remaining := state.remaining - 1}
      if stack.contains id then liftM (fail span "reachable recursive helper call cycle")
      if let some cached := state.cache.find? (·.id == id) then
        if cached.callDepth > fuel then liftM (resource span "call depth")
        return cached
      match fuel with
      | 0 => liftM (resource span "call depth")
      | fuel + 1 =>
        let some summary := summaries.find? (·.id == id)
          | liftM (fail span "unknown helper call graph identity")
        let children ← summary.calls.mapM (go fuel (id :: stack))
        let direct := sizes.lookup id |>.getD {nodes := 0, depth := 0}
        let expandedNodes := children.foldl
          (fun count child => saturatedAdd limits.maxExpandedNodes count child.expandedNodes)
          direct.nodes
        if expandedNodes > limits.maxExpandedNodes then liftM (resource span "expanded nodes")
        let expandedDepth := saturatedAdd limits.maxExpandedDepth direct.depth
          ((children.map (·.expandedDepth)).foldl max 0)
        if expandedDepth > limits.maxExpandedDepth then liftM (resource span "expanded depth")
        let result := {summary with
          effects := (summary.direct ++ children.flatMap (·.effects)).eraseDups
          guarded := summary.guarded || children.any (·.guarded)
          expandedNodes
          expandedDepth
          callDepth := 1 + (children.map (·.callDepth)).foldl max 0}
        modify fun state => {state with cache := result :: state.cache}
        pure result

/-- Unreachable recursion is pruned before cycle/purity analysis. Every declared
signature and statement is still statically checked. -/
def analyzeWithLimits (limits : Limits) (program : Program) : Except Diagnostic (List Summary) := do
  let (program, sizes) ← prepareProgramAndSizes limits program
  unless uniqueNames (program.scopes.map (toString ∘ Scope.id)) do fail {} "duplicate helper scope identity"
  unless (program.declarations.map (·.id)).eraseDups.length == program.declarations.length do
    fail {} "duplicate helper declaration identity"
  unless uniqueNames (program.exports.map (·.name)) do fail {} "duplicate monomorphic helper entrypoint name"
  for scope in program.scopes do
    let mut next := scope.parent
    let mut seen := [scope.id]
    for _ in List.range (program.scopes.length + 1) do
      if let some id := next then
        if seen.contains id then fail {} "helper lexical scope cycle"
        let some parent := program.scopes.find? (·.id == id) | fail {} "unknown parent helper scope"
        seen := id :: seen
        next := parent.parent
  for declaration in program.declarations do
    unless program.scopes.any (·.id == declaration.id.scope) do fail declaration.span "unknown declaration scope"
  let summaries ← program.declarations.mapM (checkDeclarationUnchecked limits program)
  let mut state : AnalysisState := {remaining := limits.maxAnalysisSteps}
  for entry in program.exports do
    let declaration ← lookup program entry.target entry.span
    unless uniqueNames (entry.inputs.map (·.name)) do fail entry.span "duplicate helper entrypoint input"
    unless uniqueNames (entry.compositeInputs.map (·.name)) do fail entry.span "duplicate aggregate helper entrypoint input"
    let scalarNames := entry.inputs.map (·.name)
    if entry.compositeInputs.any (fun input => scalarNames.contains input.name) then
      fail entry.span "duplicate helper entrypoint input"
    for input in entry.inputs do liftError input.span (input.ty.validate Capabilities.crypto)
    for input in entry.compositeInputs do discard (checkedComposite program input.span input.type)
    let mut scalarInputs := entry.inputs
    let mut aggregateInputs := entry.compositeInputs
    let mut arguments := []
    for parameter in declaration.parameters do
      match declaration.parameterType parameter with
      | .scalar _ =>
        let some input := scalarInputs.head?
          | fail entry.span "helper entrypoint input signature mismatch"
        scalarInputs := scalarInputs.drop 1
        arguments := arguments ++ [.scalar input.ty]
      | .composite _ =>
        let some input := aggregateInputs.head?
          | fail entry.span "helper entrypoint input signature mismatch"
        aggregateInputs := aggregateInputs.drop 1
        arguments := arguments ++ [.composite input.type]
      | .unit =>
        let some input := aggregateInputs.head?
          | fail entry.span "helper entrypoint input signature mismatch"
        aggregateInputs := aggregateInputs.drop 1
        unless input.type == .unit do fail input.span "helper Unit input type mismatch"
        arguments := arguments ++ [.unit]
    unless compatible arguments declaration do
      fail entry.span "helper entrypoint input signature mismatch"
    unless scalarInputs.isEmpty && aggregateInputs.isEmpty do
      fail entry.span "helper entrypoint input signature mismatch"
    let (_, next) ← (summarize limits summaries sizes entry.span entry.target).run state
    state := next
  let mut results := []
  for summary in summaries do
    if let some result := state.cache.find? (·.id == summary.id) then
      let declaration ← lookup program summary.id {}
      if declaration.declaredPure && result.effects.any EffectKind.impure then
        fail declaration.span s!"declared-pure helper '{declaration.name}' has transitive effects"
      results := results ++ [result]
  pure results

def analyze (program : Program) : Except Diagnostic (List Summary) :=
  analyzeWithLimits {} program

/-- Resource-checked query closures avoid rescanning a whole program for each
node in another checked pass. Each standalone query retains local input caps. -/
structure Prepared where
  program : Program
  summaries : List Summary
  infer : Nat → Environment → SourceSpan → Term → Except Diagnostic TermInfo
  resolve : Nat → String → List ResultType → SourceSpan → Except Diagnostic Declaration

def prepareWithLimits (limits : Limits) (program : Program) : Except Diagnostic Prepared := do
  let program ← prepareProgramWithLimits limits program
  let summaries ← analyzeWithLimits limits program
  pure {
    program, summaries
    infer := fun scope env span value => do
      spanMetadata span
      discard (scanTerms limits span limits.maxSourceNodes [value])
      if env.length > limits.maxSourceNodes then resource span "type environment"
      for (name, _) in env do textMetadata name
      inferTerm limits.maxSourceDepth program scope env span value
    resolve := fun scope name arguments span => do
      spanMetadata span
      textMetadata name
      if arguments.length > limits.maxParameters then resource span "call arguments"
      resolveUnchecked program scope name arguments span
  }

structure Scalar where
  ty : Ty
  value : Expr ty
  deriving Repr

instance : Inhabited Scalar := ⟨⟨.bool, .bool true⟩⟩

/-- Unit uses an unobservable internal Bool token, so scalar sequencing still
retains unused arguments, assertions and fallible casts. -/
structure Lowered where
  ty : ResultType
  scalar : Scalar
  components : List Scalar := []
  constraints : List (Expr .bool) := []
  deriving Inhabited

private def scalarValue {ty : Ty} (value : Expr ty) : Lowered :=
  { ty := .scalar ty, scalar := ⟨ty, value⟩ }

private def foreignConstantExpr : (kind : Foreign.Kind) → kind.Denote → Expr (.foreign kind)
  | .base curve, value => .foreignBase curve value
  | .scalar curve, value => .foreignScalar curve value
  | .point curve, value => .foreignPoint curve value

private def unitValue : Lowered := {ty := .unit, scalar := ⟨.bool, .bool true⟩}

private def components (value : Lowered) : List Scalar :=
  match value.ty with
  | .unit => []
  | .scalar _ => [value.scalar]
  | .composite _ => value.components

private def aggregateValue (type : Types.CompositeType) (values : List Scalar)
    (constraints : List (Expr .bool) := []) : Lowered :=
  { ty := .composite type, scalar := values.headD ⟨.bool, .bool true⟩,
    components := values, constraints }

private def nativeOfScalar (span : SourceSpan) (value : Scalar) : Except Diagnostic (Expr .native) :=
  match value with
  | ⟨.native, value⟩ => pure value
  | ⟨.bool, value⟩ => pure (.cast .native value)
  | ⟨.uint _, value⟩ => pure (.cast .native value)
  | ⟨.bytes _, _⟩ => fail span "byte strings require separate native byte leaves"
  | ⟨.opaqueBytes, _⟩ => fail span "OpaqueBytes require a Compress projection"
  | ⟨.opaqueString, _⟩ => fail span "OpaqueString requires a Compress projection"
  | ⟨.jubjubScalar, _⟩ | ⟨.jubjubPoint, _⟩ =>
    fail span "Jubjub values require a qualified curve operation"
  | ⟨.foreign _, _⟩ => fail span "foreign values require a qualified curve operation"

private def lowerSourceLeaves (span : SourceSpan) (expected : List Ty)
    (values : List Scalar) : Except Diagnostic (List (Expr .native)) := do
  unless expected.length == values.length do fail span "aggregate source leaf count mismatch"
  let mut fields := []
  for (expectedType, value) in expected.zip values do
    if expectedType.isJubjub || expectedType.isForeign then
      unless expectedType.nativeCallFieldCount > 0 do
        fail span "invalid qualified curve layout leaf"
      let encoded ← match value with
        | ⟨actual, expression⟩ =>
          if h : actual = expectedType then
            let encoded := (h ▸ expression).nativeCallFields
            if encoded.length == expectedType.nativeCallFieldCount then pure encoded
            else fail span "qualified curve ABI field count mismatch"
          else fail span "aggregate source leaf type mismatch"
      fields := fields ++ encoded
    else
      fields := fields ++ [← nativeOfScalar span value]
  pure fields

private def decodeCurveFields (span : SourceSpan) (type : Ty)
    (fields : List Scalar) : Except Diagnostic (Expr type) := do
  unless type.isJubjub || type.isForeign do
    fail span "invalid qualified curve layout leaf"
  unless fields.length == type.nativeCallFieldCount do
    fail span "qualified curve ABI field count mismatch"
  let nativeFields ← fields.mapM (nativeOfScalar span)
  let expression ← (Wire.decodeCurveFields type nativeFields).mapError fun message => {span, message}
  pure expression

private def restoreLayoutScalar (span : SourceSpan) (type : Ty)
    (fields : List Scalar) : Except Diagnostic (Expr type) := do
  if type.isJubjub || type.isForeign then
    decodeCurveFields span type fields
  else
    unless fields.length == 1 do fail span "aggregate scalar projection field count mismatch"
    let some field := fields.head? | fail span "aggregate scalar projection has no field"
    pure (.cast type (← nativeOfScalar span field))

private def coerce (span : SourceSpan) (value : Lowered) (target : ResultType) : Except Diagnostic Lowered := do
  unless subtype value.ty target do fail span "helper lowering type mismatch"
  match target with
  | .unit => pure value
  | .scalar ty =>
    if h : value.scalar.ty = ty then pure {value with ty := target, scalar := ⟨ty, h ▸ value.scalar.value⟩}
    else pure {value with ty := target, scalar := ⟨ty, .cast ty value.scalar.value⟩}
  | .composite type => do
    let leaves ← (components value).mapM (nativeOfScalar span)
    let normalized := leaves.map fun leaf => ⟨.native, leaf⟩
    pure {value with
      ty := .composite type
      scalar := normalized.headD value.scalar
      components := normalized}

private def boolExpr (span : SourceSpan) (value : Lowered) : Except Diagnostic (Expr .bool) :=
  if h : value.scalar.ty = .bool then pure (h ▸ value.scalar.value)
  else fail span "helper lowering expected Bool"

private def nativeExpr (span : SourceSpan) (value : Lowered) : Except Diagnostic (Expr .native) := do
  let value ← coerce span value (.scalar .native)
  if h : value.scalar.ty = .native then pure (h ▸ value.scalar.value)
  else fail span "helper lowering expected Native"

private def typedExpr (span : SourceSpan) (target : Ty) (value : Lowered) : Except Diagnostic (Expr target) := do
  let value ← coerce span value (.scalar target)
  if h : value.scalar.ty = target then pure (h ▸ value.scalar.value)
  else fail span "helper lowering expected declared scalar type"

private partial def expressionUsesName (name : String) : Expr ty → Bool
  | .native _ | .bool _ | .uint _ _ | .opaqueBytesEmpty | .opaqueStringEmpty
  | .bytesLiteral _ _ | .bytes32Literal _
  | .foreignBase _ _ | .foreignScalar _ _ | .foreignPoint _ _ => false
  | .bytesField value _ | .bytesAt value _ | .reverseBytes value | .sliceBytes value _ _
  | .sha256 value | .sha512 value | .keccak256 value | .keccak256Secp256k1Point value
  | .persistentHash32 value | .reverseBytes32 value
  | .persistentHashNative value | .toBytes32 value | .fromBytes32 value | .fromBytes value
  | .jubjubScalarFromNative value | .jubjubScalarToNative value | .jubjubMulGenerator value
  | .jubjubNeg value | .jubjubCoordinate value _ | .foreignEncodedField value _
  | .foreignUnary _ value | .foreignToBytes value | .foreignFromBytes _ value
  | .inv value | .cast _ value | .disclose _ value => expressionUsesName name value
  | .persistentHashVector32 values | .hashToCurve values
  | .persistentHashNativeVector values | .transientHash values => values.any (expressionUsesName name)
  | .persistentCommitFab _ _ opening values | .transientCommitFab _ _ opening values =>
    expressionUsesName name opening ||
      values.any (fun ⟨_, value⟩ => expressionUsesName name value)
  | .sha512Fab _ _ values | .transientHashFab _ _ values =>
    values.any (fun ⟨_, value⟩ => expressionUsesName name value)
  | .concatBytes left right | .foreignBinary _ left right | .jubjubMul left right
  | .jubjubAdd left right | .add left right | .mul left right | .sub left right
  | .uadd left right | .usub left right | .umul left right | .eq left right
  | .poseidon2 _ left right => expressionUsesName name left || expressionUsesName name right
  | .jubjubFromCoordinates left right => expressionUsesName name left || expressionUsesName name right
  | .boolAnd left right | .boolOr left right | .boolXor left right =>
    expressionUsesName name left || expressionUsesName name right
  | .select condition yes no =>
    expressionUsesName name condition || expressionUsesName name yes || expressionUsesName name no
  | .letE localName value body => expressionUsesName name value ||
      (localName != name && expressionUsesName name body)
  | .assertE condition body => expressionUsesName name condition || expressionUsesName name body
  | .ref candidate => candidate == name
  | _ => true

private partial def expressionIsTotal (env : TypeEnv) : Expr ty → Bool
  | .native _ | .bool _ | .uint _ _ | .opaqueBytesEmpty | .opaqueStringEmpty => true
  | .foreignPoint curve point => Foreign.pointValid curve point
  | .bytesLiteral length values =>
    length ≤ maxBytesLength && values.length == length && values.all (· ≤ 255)
  | .bytes32Literal values => values.length == 32 && values.all (· ≤ 255)
  | .bytesAt (length := length) value index => index < length && expressionIsTotal env value
  | .ref name => env.lookup name == some ty
  | .add left right | .mul left right | .sub left right
  | .boolAnd left right | .boolOr left right | .boolXor left right
  | .eq left right => expressionIsTotal env left && expressionIsTotal env right
  | .select condition yes no => expressionIsTotal env condition &&
      expressionIsTotal env yes && expressionIsTotal env no
  | .letE (source := source) name value body => expressionIsTotal env value &&
      expressionIsTotal ((name, source) :: env) body
  | .disclose _ value => expressionIsTotal env value
  | .cast .native (source := source) value =>
    match source with
    | .native | .bool | .uint _ => expressionIsTotal env value
    | _ => false
  | _ => false

private def sequence (types : TypeEnv) (name : String) (value body : Lowered) : Lowered :=
  let bind {ty : Ty} (expression : Expr ty) : Expr ty :=
    if !expressionUsesName name expression && expressionIsTotal types value.scalar.value then
      expression
    else .letE name value.scalar.value expression
  {body with
    scalar := ⟨body.scalar.ty, bind body.scalar.value⟩
    components := body.components.map fun component =>
      ⟨component.ty, bind component.value⟩
    constraints := body.constraints.map fun condition => bind condition}

private def selectExpr {ty : Ty} (condition : Expr .bool) (yes no : Expr ty) : Expr ty :=
  match ty with
  | .jubjubScalar => .jubjubScalarFromNative (.select condition
      (.jubjubScalarToNative yes) (.jubjubScalarToNative no))
  | .jubjubPoint => .jubjubFromCoordinates
      (.select condition (.jubjubCoordinate yes 0) (.jubjubCoordinate no 0))
      (.select condition (.jubjubCoordinate yes 1) (.jubjubCoordinate no 1))
  | _ => .select condition yes no

private def selectScalar (span : SourceSpan) (condition : Expr .bool)
    (yes no : Scalar) : Except Diagnostic Scalar := do
  if h : yes.ty = no.ty then
    pure ⟨yes.ty, selectExpr condition yes.value (h.symm ▸ no.value)⟩
  else
    fail span "native helper branch scalar type mismatch"

private def guardConstraint (condition : Expr .bool) (active : Bool)
    (constraint : Expr .bool) : Expr .bool :=
  let guard := if active then condition else .eq condition (.bool false)
  .select guard (GuardedExpression.totalize guard constraint) (.bool true)

private def selectLowered (span : SourceSpan) (condition : Expr .bool)
    (yes no : Lowered) : Except Diagnostic Lowered := do
  unless yes.ty == no.ty do fail span "native helper branch result type mismatch"
  unless (components yes).length == (components no).length do
    fail span "native helper branch component count mismatch"
  let inactive := Expr.eq condition (.bool false)
  let components ← (components yes).zip (components no) |>.mapM fun (left, right) => do
    selectScalar span condition
      ⟨left.ty, GuardedExpression.totalize condition left.value⟩
      ⟨right.ty, GuardedExpression.totalize inactive right.value⟩
  let scalar ← selectScalar span condition
    ⟨yes.scalar.ty, GuardedExpression.totalize condition yes.scalar.value⟩
    ⟨no.scalar.ty, GuardedExpression.totalize inactive no.scalar.value⟩
  let value : Lowered := {yes with
    scalar := scalar
    components := components
    constraints := yes.constraints.map (guardConstraint condition true) ++
      no.constraints.map (guardConstraint condition false)}
  pure value

private def bindCondition (name : String) (condition : Expr .bool)
    (value : Lowered) : Lowered :=
  let bind {ty : Ty} (expression : Expr ty) : Expr ty := .letE name condition expression
  {value with
    scalar := ⟨value.scalar.ty, bind value.scalar.value⟩
    components := value.components.map fun component => ⟨component.ty, bind component.value⟩
    constraints := value.constraints.map bind}

private abbrev LowerEnv := List (String × Lowered)
private structure LocalBinding where
  name : String
  value : Scalar
  creationGuard : Expr .bool
  deriving Repr

structure WitnessCallBinding where
  ordinal : Nat
  site : String
  name : String
  path : List DeclarationId
  result : ResultType
  inputs : List String
  effectCount : Nat := 0
  guard : Expr .bool := .bool true
  guarded : Bool := false
  deriving Repr

structure HostedCircuit where
  circuit : Circuit
  calls : List WitnessCallBinding
  deriving Repr

private structure LowerState where
  next : Nat := 0
  reserved : List String := []
  types : TypeEnv := []
  witnessInputs : List Input := []
  privateOrigins : List (String × PrivateOriginKind) := []
  witnessCalls : List WitnessCallBinding := []
  witnessConstraints : List (Expr .bool) := []
  ledgerMode : Bool := false
  ledgerEffects : List Effect := []
  ledgerGuards : List (Option (Expr .bool)) := []
  ledgerSpans : List SourceSpan := []
  allowGuardedWitnesses : Bool := false
  guard : Expr .bool := .bool true
  guardActive : Bool := false
  localBindings : List LocalBinding := []
  callPath : List DeclarationId := []
  remaining : Nat
  deriving Inhabited

private abbrev LowerM := StateT LowerState (Except Diagnostic)

private def spendLower (span : SourceSpan) : LowerM Unit := do
  let state ← get
  if state.remaining == 0 then liftM (resource span "lowering steps")
  set {state with remaining := state.remaining - 1}

private def fresh : LowerM String := do
  let state ← get
  let start := state.next
  let reserved := state.reserved
  let some n := (List.range (reserved.length + 1)).map (· + start) |>.find?
    (fun n => !reserved.contains s!"$helper{n}")
    | liftM (fail {} "helper fresh binding exhaustion")
  set {state with next := n + 1}
  pure s!"$helper{n}"

private def freshTyped (type : Ty) : LowerM String := do
  let name ← fresh
  modify fun state => {state with types := (name, type) :: state.types}
  pure name

private def recordLocal (name : String) (value : Scalar) : LowerM Unit := do
  modify fun state => {state with localBindings := {
    name, value, creationGuard := state.guard} :: state.localBindings}

private def closeBindings (types : TypeEnv) (bindings : List LocalBinding)
    (value : Expr ty) : Expr ty :=
  bindings.foldl (fun body binding =>
    match binding.value with
    | ⟨_, source⟩ =>
      let unused := !expressionUsesName binding.name body
      if unused && expressionIsTotal types source &&
          expressionIsTotal types binding.creationGuard then body
      else Expr.letE binding.name
        (GuardedExpression.totalize binding.creationGuard source) body) value

private def closeGuard (types : TypeEnv) (guard : Expr .bool)
    (bindings : List LocalBinding) : Expr .bool := closeBindings types bindings guard

private def closeExpression (types : TypeEnv) (bindings : List LocalBinding)
    (value : Expr ty) : Expr ty := closeBindings types bindings value

private def closeLedgerEffect (types : TypeEnv) (bindings : List LocalBinding) : Effect → Effect
  | .require condition => .require (closeExpression types bindings condition)
  | .writeCell state ty value => .writeCell state ty (closeExpression types bindings value)
  | .emitEvent kind payload => .emitEvent kind (closeExpression types bindings payload)
  | .readMap state destination keyTy valueTy key =>
      .readMap state destination keyTy valueTy (closeExpression types bindings key)
  | .readMember state destination keyTy valueTy key =>
      .readMember state destination keyTy valueTy (closeExpression types bindings key)
  | .writeMap state keyTy valueTy key value =>
      .writeMap state keyTy valueTy (closeExpression types bindings key) (closeExpression types bindings value)
  | effect => effect

private def appendLedgerEffect (span : SourceSpan) (effect : Effect) : LowerM Unit := do
  let state ← get
  let guard := if state.guardActive then
    some (closeGuard state.types state.guard state.localBindings) else none
  modify fun state => {state with
    ledgerEffects := state.ledgerEffects ++ [closeLedgerEffect state.types state.localBindings effect]
    ledgerGuards := state.ledgerGuards ++ [guard]
    ledgerSpans := state.ledgerSpans ++ [span]}

private def appendLedgerConstraints (span : SourceSpan) (conditions : List (Expr .bool)) : LowerM Unit := do
  for condition in conditions do
    appendLedgerEffect span (.require condition)

/-- Retain strict term evaluation even when a Unit result discards its value. -/
private def evaluateLedgerTerm (span : SourceSpan) (value : Lowered) : LowerM Unit := do
  appendLedgerConstraints span value.constraints
  let types := (← get).types
  let values := if (components value).isEmpty then [value.scalar] else components value
  for component in values do
    unless expressionIsTotal types component.value do
      let name ← fresh
      appendLedgerEffect span (.require (.letE name component.value (.bool true)))

private def andGuard (left right : Expr .bool) : Expr .bool := .boolAnd left right

private def guardedBranch (guard condition : Expr .bool) (active : Bool) : Expr .bool :=
  andGuard guard (if active then condition else .eq condition (.bool false))

private structure ProjectionLowering where
  selectedType : Types.CompositeType
  values : List Scalar
  parentConstraints : List (Expr .bool)
  projectionConstraints : List (Expr .bool)

private instance : Nonempty ProjectionLowering := ⟨{
  selectedType := .scalar .bool,
  values := [],
  parentConstraints := [],
  projectionConstraints := []
}⟩

def projectionSlice (layout : Types.Layout) (projection : Types.Projection) :
    Except String (Nat × Nat) := do
  match layout, projection with
  | .tuple items, .tupleIndex index =>
    let some selected := items[index]? | throw "aggregate tuple projection out of bounds"
    pure ((items.take index).map Types.Layout.leafCount |>.sum, selected.leafCount)
  | .structure _ fields, .field name =>
    let some index := fields.findIdx? (·.1 == name) | throw "unknown aggregate field"
    let some selected := fields[index]? | throw "aggregate field layout mismatch"
    pure ((fields.take index).map (fun field => field.2.leafCount) |>.sum, selected.2.leafCount)
  | .vector length element, .vectorIndex index =>
    unless index < length do throw "aggregate vector projection out of bounds"
    pure (index * element.leafCount, element.leafCount)
  | .bytes length _, .byteIndex index =>
    unless index < length do throw "aggregate byte projection out of bounds"
    pure (index, 1)
  | .enumeration _ _ _ _ _ variants, .enumField variant name =>
    let some selected := variants.find? (·.1 == variant) | throw "unknown aggregate enum variant"
    let some index := selected.2.1.findIdx? (·.1 == name) | throw "unknown aggregate enum field"
    let some field := selected.2.1[index]? | throw "aggregate enum layout mismatch"
    pure (1 + ((selected.2.1.take index).map (fun item => item.2.leafCount)).sum,
      field.2.leafCount)
  | .enumeration .., .enumTag => pure (0, 1)
  | _, _ => throw "aggregate projection kind/type mismatch"

private def liftD (value : Except Diagnostic α) : LowerM α := liftM value

private def scalarEquality : {ty : Ty} → Expr ty → Expr ty → LowerM (Expr .bool)
  | .bytes length, left, right => do
    let equalities := (List.range ((length + 30) / 31)).map fun chunk =>
      Expr.eq (Expr.bytesField left chunk) (Expr.bytesField right chunk)
    match equalities with
    | [] => do
      let leftName ← fresh
      let rightName ← fresh
      pure (Expr.letE leftName left (Expr.letE rightName right (.bool true)))
    | first :: rest =>
      pure (rest.foldl (fun accumulated next =>
        Expr.select accumulated next (.bool false)) first)
  | _, left, right => pure (.eq left right)

mutual
  private partial def lowerProjectionData (program : Program) (scope : Nat)
      (env : LowerEnv) (span : SourceSpan) (value : Term)
      (projection : Types.Projection) : LowerM ProjectionLowering := do
    let parent ← lowerTerm program scope env span value
    let .composite parentType := parent.ty
      | liftD (fail span "aggregate projection requires a composite value")
    let selectedType ← liftD (projectedType program.composites span parentType projection)
    let parentLayout := (← liftD (checkedComposite program span parentType)).checked.value
    let childType ← liftD (checkedComposite program span selectedType)
    let (offset, count) ← liftD
      ((projectionSlice parentLayout projection).mapError fun message => {span, message})
    let values := (components parent).drop offset |>.take count
    unless values.length == childType.checked.expandedLeaves do
      liftD (fail span "aggregate projection leaf count mismatch")
    let projectionConstraints ← if let .enumField variant _ := projection then
      match parentLayout with
      | .enumeration _ _ _ _ _ variants => do
        let some variantIndex := variants.findIdx? (·.1 == variant)
          | liftD (fail span "unknown aggregate enum variant")
        let some tag := (components parent).head?
          | liftD (fail span "aggregate enum projection has no tag")
        pure [Expr.eq (← liftD (nativeOfScalar span tag)) (.native variantIndex)]
      | _ => liftD (fail span "enum projection requires an enum layout")
    else pure []
    pure {
      selectedType,
      values,
      parentConstraints := parent.constraints,
      projectionConstraints
    }

  /-- Reuse the already-checked physical fields when a curve projection flows
  directly into composite construction. General projections still decode the
  logical curve and retain Wire's exact round-trip assertion. -/
  private partial def lowerCurveProjectionFields (program : Program) (scope : Nat)
      (env : LowerEnv) (span : SourceSpan) (expectedType : Ty) (term : Term) :
      LowerM (Option (List (Expr .native) × List (Expr .bool))) := do
    unless expectedType.isJubjub || expectedType.isForeign do return none
    if (← get).ledgerMode then return none
    let .project parentTerm projection := term | return none
    spendLower span
    let projected ← lowerProjectionData program scope env span parentTerm projection
    unless projected.selectedType == .scalar expectedType do
      liftD (fail span "aggregate source leaf type mismatch")
    unless projected.values.length == expectedType.nativeCallFieldCount do
      liftD (fail span "qualified curve ABI field count mismatch")
    let nativeFields ← projected.values.mapM fun field => liftD (nativeOfScalar span field)
    pure (some (nativeFields,
      projected.parentConstraints ++ projected.projectionConstraints))

  private partial def lowerTerm (program : Program) (scope : Nat) (env : LowerEnv)
      (span : SourceSpan) (term : Term) : LowerM Lowered := do
    let value ← lowerTermCore program scope env span term
    if (← get).ledgerMode then
      evaluateLedgerTerm span value
      pure {value with constraints := []}
    else
      pure value

  private partial def lowerTermCore (program : Program) (scope : Nat) (env : LowerEnv)
      (span : SourceSpan) (term : Term) : LowerM Lowered := do
    spendLower span
    match term with
    | .unit => pure unitValue
    | .native n => pure (scalarValue (.native n))
    | .bool b => pure (scalarValue (.bool b))
    | .uint m n => pure (scalarValue (.uint m n))
    | .ref name =>
      let some value := env.lookup name | liftD (fail span s!"unbound helper value '{name}'")
      pure value
    | .binary op left right =>
      let left ← lowerTerm program scope env span left
      let right ← lowerTerm program scope env span right
      let result ← match left.scalar, right.scalar with
      | ⟨.uint _, a⟩, ⟨.uint _, b⟩ =>
        match op with
        | .add => pure (scalarValue (.uadd a b))
        | .sub => pure (scalarValue (.usub a b))
        | .mul => pure (scalarValue (.umul a b))
      | _, _ =>
        let left ← liftD (nativeExpr span left)
        let right ← liftD (nativeExpr span right)
        let value := match op with | .add => Expr.add left right | .sub => .sub left right | .mul => .mul left right
        pure (scalarValue value)
      pure {result with constraints := left.constraints ++ right.constraints ++ result.constraints}
    | .boolAnd left right | .boolOr left right | .boolXor left right => do
      let leftValue ← lowerTerm program scope env span left
      let rightValue ← lowerTerm program scope env span right
      let constraints := leftValue.constraints ++ rightValue.constraints
      let leftExpr ← liftD (typedExpr span .bool leftValue)
      let rightExpr ← liftD (typedExpr span .bool rightValue)
      let result ← match term with
        | .boolAnd .. => pure (Expr.boolAnd leftExpr rightExpr)
        | .boolOr .. => pure (Expr.boolOr leftExpr rightExpr)
        | .boolXor .. => pure (Expr.boolXor leftExpr rightExpr)
        | _ => liftD (fail span "invalid eager Boolean term")
      pure {scalarValue result with constraints}
    | .eq left right =>
      let left ← lowerTerm program scope env span left
      let right ← lowerTerm program scope env span right
      let constraints := left.constraints ++ right.constraints
      match left.ty, right.ty with
      | .composite leftType, .composite rightType => do
        let compiled ← liftD (checkedAggregateEquality program span leftType rightType)
        let leftValues := components left
        let rightValues := components right
        let leaves := compiled.checked.expandedLeaves
        unless leftValues.length == leaves && rightValues.length == leaves do
          liftD (fail span "aggregate equality leaf count mismatch")
        let equalities ← leftValues.zip rightValues |>.mapM fun (left, right) => do
          let left ← liftD (nativeOfScalar span left)
          let right ← liftD (nativeOfScalar span right)
          scalarEquality left right
        let value := match equalities with
          | [] => .bool true
          | first :: rest => rest.foldl Expr.boolAnd first
        pure {scalarValue value with constraints}
      | .scalar _, .scalar _ => do
        let ty ← liftD (common span left.scalar.ty right.scalar.ty)
        let left ← liftD (typedExpr span ty left)
        let right ← liftD (typedExpr span ty right)
        let value ← scalarEquality left right
        pure {scalarValue value with constraints}
      | _, _ => liftD (fail span "helper equality requires scalar operands or matching aggregates")
    | .cast target value =>
      let value ← lowerTerm program scope env span value
      pure {scalarValue (.cast target value.scalar.value) with constraints := value.constraints}
    | .disclose release value =>
      let value ← lowerTerm program scope env span value
      match value.ty with
      | .unit => pure value
      | .scalar _ => pure {value with scalar := ⟨value.scalar.ty, .disclose release value.scalar.value⟩}
      | .composite _ => pure {value with components := value.components.map fun item =>
          ⟨item.ty, .disclose release item.value⟩}
    | .select condition yes no =>
      let condition ← lowerTerm program scope env span condition
      let yes ← lowerTerm program scope env span yes
      let no ← lowerTerm program scope env span no
      let constraints := condition.constraints ++ yes.constraints ++ no.constraints
      let ty ← liftD (common span yes.scalar.ty no.scalar.ty)
      let result := scalarValue (.select (← liftD (boolExpr span condition))
        (← liftD (typedExpr span ty yes)) (← liftD (typedExpr span ty no)))
      pure {result with constraints}
    | .ite condition yes no => do
      let condition ← lowerTerm program scope env span condition
      let conditionExpr ← liftD (boolExpr span condition)
      let entryState ← get
      let safeCondition := GuardedExpression.totalize entryState.guard conditionExpr
      modify fun state => {state with
        guard := guardedBranch entryState.guard safeCondition true, guardActive := true}
      let yes ← lowerTerm program scope env span yes
      modify fun state => {state with
        guard := guardedBranch entryState.guard safeCondition false, guardActive := true,
        localBindings := entryState.localBindings}
      let no ← lowerTerm program scope env span no
      let noState ← get
      modify fun state => {noState with
        guard := entryState.guard, guardActive := entryState.guardActive,
        localBindings := entryState.localBindings}
      let some ty := commonType yes.ty no.ty
        | liftD (fail span "conditional branches require a common type")
      let yes ← liftD (coerce span yes ty)
      let no ← liftD (coerce span no ty)
      let name ← freshTyped .bool
      let conditionRef : Expr .bool := .ref name
      let selected ← liftD (selectLowered span conditionRef yes no)
      let selected := bindCondition name conditionExpr selected
      pure {selected with constraints := condition.constraints ++ selected.constraints}
    | .andThen left right | .orElse left right => do
      let left ← lowerTerm program scope env span left
      let leftExpr ← liftD (boolExpr span left)
      let entryState ← get
      let safeLeft := GuardedExpression.totalize entryState.guard leftExpr
      modify fun state => {state with
        guard := guardedBranch entryState.guard safeLeft
          (match term with | .andThen .. => true | _ => false), guardActive := true}
      let right ← lowerTerm program scope env span right
      let rightExpr ← liftD (boolExpr span right)
      let rightState ← get
      modify fun state => {rightState with
        guard := entryState.guard, guardActive := entryState.guardActive,
        localBindings := entryState.localBindings}
      let name ← freshTyped .bool
      let leftRef : Expr .bool := .ref name
      let active := match term with
        | .andThen .. => leftRef
        | .orElse .. => .eq leftRef (.bool false)
        | _ => .bool false
      let result := match term with
        | .andThen .. => Expr.select leftRef (GuardedExpression.totalize leftRef rightExpr) (.bool false)
        | .orElse .. => Expr.select leftRef (.bool true)
            (GuardedExpression.totalize active rightExpr)
        | _ => Expr.bool false
      let result : Lowered := {
        scalarValue result with
        constraints := left.constraints ++ right.constraints.map (guardConstraint leftRef
          (match term with | .andThen .. => true | _ => false))}
      let result := bindCondition name leftExpr result
      pure result
    | .witness _ ty => do
      let state ← get
      if state.allowGuardedWitnesses && state.guardActive then
        liftD (fail span "guarded native witnesses require a typed provider binding")
      let inputName ← freshTyped ty
      modify fun state => {state with
        witnessInputs := state.witnessInputs ++ [{name := inputName, ty, visibility := .private, span}]
        privateOrigins := state.privateOrigins ++ [(inputName, .provider)]}
      pure (scalarValue (ty := ty) (Expr.ref inputName))
    | .witnessCall site name arguments => do
      let signature ← liftD (witnessSignature program name span)
      let entryState ← get
      let callGuard := closeGuard entryState.types entryState.guard entryState.localBindings
      let arguments ← arguments.mapM (lowerTerm program scope env span)
      let mut bindings := []
      let mut constraints := arguments.flatMap (·.constraints)
      for (argument, parameter) in arguments.zip signature.parameters do
        let argument ← liftD (coerce span argument parameter.type)
        let argumentComponents := components argument
        if argumentComponents.isEmpty then
          let binding ← freshTyped argument.scalar.ty
          recordLocal binding argument.scalar
          bindings := bindings ++ [(binding, argument.scalar)]
        else
          for component in argumentComponents do
            let binding ← freshTyped component.ty
            recordLocal binding component
            bindings := bindings ++ [(binding, component)]
      let leafTypes ← match signature.result with
        | .unit => pure []
        | .scalar type => pure [type]
        | .composite type => do
          let compiled ← liftD (checkedComposite program span type)
          pure (List.replicate compiled.checked.expandedLeaves Ty.native)
      let mut inputs := []
      let mut leaves := []
      for type in leafTypes do
        let inputName ← freshTyped type
        inputs := inputs ++ [inputName]
        leaves := leaves ++ [⟨type, Expr.ref inputName⟩]
        modify fun state => {state with
          witnessInputs := state.witnessInputs ++ [{name := inputName, ty := type, visibility := .private, span}]
          privateOrigins := state.privateOrigins ++ [(inputName,
            if signature.operation == "private_state.read.v1" then .privateState else .provider)]}
      if let .composite type := signature.result then
        let compiled ← liftD (checkedComposite program span type)
        let state ← get
        let nativeLeaves ← liftD (leaves.mapM (nativeOfScalar span))
        let checked ← liftD ((Types.checkNativeExpression compiled state.types
          nativeLeaves).mapError fun message => {span, message})
        -- Canonical input bounds apply even when the witness call is inactive.
        modify fun state => {state with witnessConstraints := state.witnessConstraints ++ checked.constraints}
      let state ← get
      if state.guardActive then
        for (inputName, type) in inputs.zip leafTypes do
          let zero := GuardedExpression.zeroValue type
          let equal ← scalarEquality (.ref inputName) zero
          modify fun state => {state with witnessConstraints := state.witnessConstraints ++
            [Expr.select callGuard (.bool true) equal]}
      let value ← match signature.result with
        | .unit => pure unitValue
        | .scalar _ => pure {ty := signature.result, scalar := leaves.headD ⟨.bool, .bool true⟩}
        | .composite type => pure (aggregateValue type leaves)
      modify fun state => {state with witnessCalls := state.witnessCalls ++ [{
        ordinal := state.witnessCalls.length, site, name, path := state.callPath,
        result := signature.result, inputs, effectCount := state.ledgerEffects.length,
        guard := callGuard, guarded := state.guardActive}]}
      let types := (← get).types
      pure (bindings.foldr (fun (binding, component) body =>
        sequence types binding {ty := .scalar component.ty, scalar := component} body)
          {value with constraints})
    | .poseidon2 domain left right =>
      let left ← lowerTerm program scope env span left
      let right ← lowerTerm program scope env span right
      let result := scalarValue (.poseidon2 domain
        (← liftD (nativeExpr span left)) (← liftD (nativeExpr span right)))
      pure {result with constraints := left.constraints ++ right.constraints}
    | .curve operation arguments => do
      liftD (validateCurveArity span operation arguments)
      if arguments.length > curveArgumentLimit ({} : Limits) operation then
        liftD (resource span "curve arguments")
      let (expectedTypes, _) := operation.signature
      unless arguments.length == expectedTypes.length do
        liftD (fail span s!"{operation.operationName} argument count mismatch")
      let values ← arguments.mapM (lowerTerm program scope env span)
      for (value, expectedType) in values.zip expectedTypes do
        unless value.ty == .scalar expectedType do
          liftD (fail span s!"{operation.operationName} argument type mismatch")
      let result ← match operation, values with
        | .scalarFromNative, [value] => do
          let value ← liftD (typedExpr span .native value)
          pure (scalarValue (.jubjubScalarFromNative value))
        | .scalarToNative, [value] => do
          let value ← liftD (typedExpr span .jubjubScalar value)
          pure (scalarValue (.jubjubScalarToNative value))
        | .mulGenerator, [value] => do
          let value ← liftD (typedExpr span .jubjubScalar value)
          pure (scalarValue (.jubjubMulGenerator value))
        | .mul, [point, scalar] => do
          let point ← liftD (typedExpr span .jubjubPoint point)
          let scalar ← liftD (typedExpr span .jubjubScalar scalar)
          pure (scalarValue (.jubjubMul point scalar))
        | .add, [left, right] => do
          let left ← liftD (typedExpr span .jubjubPoint left)
          let right ← liftD (typedExpr span .jubjubPoint right)
          pure (scalarValue (.jubjubAdd left right))
        | .neg, [point] => do
          let point ← liftD (typedExpr span .jubjubPoint point)
          pure (scalarValue (.jubjubNeg point))
        | .x, [point] => do
          let point ← liftD (typedExpr span .jubjubPoint point)
          pure (scalarValue (.jubjubCoordinate point 0))
        | .y, [point] => do
          let point ← liftD (typedExpr span .jubjubPoint point)
          pure (scalarValue (.jubjubCoordinate point 1))
        | .fromCoordinates, [x, y] => do
          let x ← liftD (typedExpr span .native x)
          let y ← liftD (typedExpr span .native y)
          pure (scalarValue (.jubjubFromCoordinates x y))
        | .hashToCurve _, values => do
          let values ← values.mapM fun value => liftD (typedExpr span .native value)
          pure (scalarValue (.hashToCurve values))
        | .foreignUnary foreignOp, [value] => do
          let value ← liftD (typedExpr span (.foreign foreignOp.inputKind) value)
          pure (scalarValue (Expr.foreignUnary foreignOp value))
        | .foreignBinary foreignOp, [left, right] => do
          let left ← liftD (typedExpr span (.foreign foreignOp.leftKind) left)
          let right ← liftD (typedExpr span (.foreign foreignOp.rightKind) right)
          pure (scalarValue (Expr.foreignBinary foreignOp left right))
        | .foreignEncodedField kind index, [value] => do
          let value ← liftD (typedExpr span (.foreign kind) value)
          pure (scalarValue (Expr.foreignEncodedField value index))
        | _, _ => liftD (fail span "invalid checked curve operation shape")
      pure {result with constraints := values.flatMap (·.constraints) ++ result.constraints}
    | .bytes32Literal bytes => pure (scalarValue (Expr.bytes32Literal bytes))
    | .foreignConstant kind encoding => do
      let decoded ← liftD (Foreign.decodeValue kind encoding |>.mapError fun message => {span, message})
      pure (scalarValue (foreignConstantExpr kind decoded))
    | .bytesAt value index => do
      let value ← lowerTerm program scope env span value
      let .scalar (.bytes length) := value.ty
        | liftD (fail span "byteAt requires a fixed byte-string value")
      unless index < length do
        liftD (fail span "byteAt index is outside the byte string")
      let bytes ← liftD (typedExpr span (.bytes length) value)
      pure {scalarValue (Expr.bytesAt bytes index) with constraints := value.constraints}
    | .bytes operation arguments => do
      let (expectedTypes, _) ← liftD ((operation.signature arguments.length).mapError fun message =>
        {span, message})
      let values ← arguments.mapM (lowerTerm program scope env span)
      for (value, expectedType) in values.zip expectedTypes do
        unless value.ty == .scalar expectedType do
          liftD (fail span s!"{operation.operationName} argument type mismatch")
      let result ← match operation, values with
        | .bytesLiteral length bytes, [] => do
          pure (scalarValue (Expr.bytesLiteral length bytes))
        | .persistentHash32, [value] => do
          let value ← liftD (typedExpr span (.bytes 32) value)
          pure (scalarValue (Expr.persistentHash32 value))
        | .persistentHashVector32, values => do
          let values ← values.mapM fun value => liftD (typedExpr span (.bytes 32) value)
          pure (scalarValue (Expr.persistentHashVector32 values))
        | .persistentHashNative, [value] => do
          let value ← liftD (typedExpr span .native value)
          pure (scalarValue (Expr.persistentHashNative value))
        | .persistentHashNativeVector, values => do
          let values ← values.mapM fun value => liftD (typedExpr span .native value)
          pure (scalarValue (Expr.persistentHashNativeVector values))
        | .transientHashNativeVector, values => do
          let values ← values.mapM fun value => liftD (typedExpr span .native value)
          pure (scalarValue (Expr.transientHash values))
        | .persistentHashPoint, [value] => do
          let point ← liftD (typedExpr span .jubjubPoint value)
          pure (scalarValue (Expr.persistentHashNativeVector [
            Expr.jubjubCoordinate point 0, Expr.jubjubCoordinate point 1]))
        | .sha256 length, [value] => do
          let value ← liftD (typedExpr span (.bytes length) value)
          pure (scalarValue (Expr.sha256 value))
        | .sha512 length, [value] => do
          let value ← liftD (typedExpr span (.bytes length) value)
          pure (scalarValue (Expr.sha512 value))
        | .keccak256 length, [value] => do
          let value ← liftD (typedExpr span (.bytes length) value)
          pure (scalarValue (Expr.keccak256 value))
        | .keccak256Secp256k1Point, [value] => do
          let value ← liftD (typedExpr span (.foreign (.point .secp256k1)) value)
          pure (scalarValue (Expr.keccak256Secp256k1Point value))
        | .reverseBytes32, [value] => do
          let value ← liftD (typedExpr span (.bytes 32) value)
          pure (scalarValue (Expr.reverseBytes32 value))
        | .reverseBytes length, [value] => do
          let value ← liftD (typedExpr span (.bytes length) value)
          pure (scalarValue (Expr.reverseBytes value))
        | .sliceBytes length start stop, [value] => do
          let value ← liftD (typedExpr span (.bytes length) value)
          pure (scalarValue (Expr.sliceBytes value start stop))
        | .concatBytes leftLength rightLength, [left, right] => do
          let left ← liftD (typedExpr span (.bytes leftLength) left)
          let right ← liftD (typedExpr span (.bytes rightLength) right)
          pure (scalarValue (Expr.concatBytes left right))
        | .toBytes32 source, [value] => do
          let value ← liftD (typedExpr span source value)
          pure (scalarValue (Expr.toBytes32 value))
        | .foreignToBytes kind, [value] => do
          let value ← liftD (typedExpr span (.foreign kind) value)
          pure (scalarValue (Expr.foreignToBytes value))
        | .foreignFromBytes kind length, [value] => do
          let value ← liftD (typedExpr span (.bytes length) value)
          pure (scalarValue (Expr.foreignFromBytes kind value))
        | .serialize type length, [value] => do
          let some codec := Wire.scalarCodec type | liftD (fail span "unsupported serialization type")
          let value ← liftD (typedExpr span type value)
          if fits : codec.width ≤ length then
            pure (scalarValue (codec.serialize value length fits))
          else liftD (fail span "serialization result is too short")
        | .deserialize type length, [value] => do
          let some codec := Wire.scalarCodec type | liftD (fail span "unsupported deserialization type")
          let value ← liftD (typedExpr span (.bytes length) value)
          pure (scalarValue (codec.deserialize value))
        | .fromBytesChecked target length, [value] => do
          let value ← liftD (typedExpr span (.bytes length) value)
          match target with
          | .native => pure (scalarValue (Wire.checkedNativeFromBytes value))
          | .uint maximum =>
            pure (scalarValue (Wire.checkedUIntFromBytes maximum value))
          | _ => liftD (fail span "fromBytesChecked supports only Native and UInt")
        | .degradeToNative, [value] => do
          let value ← liftD (typedExpr span (.bytes 32) value)
          pure (scalarValue (Expr.bytesField value 1))
        | _, _ => liftD (fail span "invalid checked byte operation shape")
      pure {result with constraints := values.flatMap (·.constraints) ++ result.constraints}
    | .call name arguments =>
      let values ← arguments.mapM (lowerTerm program scope env span)
      let declaration ← liftD (resolveUnchecked program scope name (values.map (·.ty)) span)
      lowerCall program declaration values span
    | .composite type leaves => do
      let compiled ← liftD (checkedComposite program span type)
      let expected := sourceLeafTypes compiled.checked.value
      unless leaves.length == expected.length do liftD (fail span "aggregate source leaf count mismatch")
      let mut nativeLeaves := []
      let mut sourceConstraints := []
      for (expectedType, leaf) in expected.zip leaves do
        if let some (projectedFields, constraints) ←
            lowerCurveProjectionFields program scope env span expectedType leaf then
          nativeLeaves := nativeLeaves ++ projectedFields
          sourceConstraints := sourceConstraints ++ constraints
        else
          let value ← lowerTerm program scope env span leaf
          let fields ← liftD (lowerSourceLeaves span [expectedType] [value.scalar])
          nativeLeaves := nativeLeaves ++ fields
          sourceConstraints := sourceConstraints ++ value.constraints
      let state ← get
      let checked ← liftD ((Types.checkNativeExpression compiled state.types nativeLeaves).mapError
        fun message => {span, message})
      pure (aggregateValue type (nativeLeaves.map fun leaf => ⟨.native, leaf⟩)
        (sourceConstraints ++ checked.constraints))
    | .project value projection => do
      let projected ← lowerProjectionData program scope env span value projection
      let constraints := projected.parentConstraints ++ projected.projectionConstraints
      match resultTypeOfComposite projected.selectedType with
      | .unit => pure {unitValue with constraints}
      | .scalar ty =>
        let scalar ← liftD (restoreLayoutScalar span ty projected.values)
        pure {scalarValue scalar with constraints}
      | .composite type => pure (aggregateValue type projected.values constraints)
    | .index value index => do
      let parent ← lowerTerm program scope env span value
      let indexValue ← lowerTerm program scope env span index
      let .composite (.vector length element) := parent.ty
        | liftD (fail span "dynamic aggregate index requires a vector value")
      unless length > 0 do liftD (fail span "cannot dynamically index an empty aggregate vector")
      let _ ← liftD (checkedComposite program span (.vector length element))
      let childType ← liftD (checkedComposite program span element)
      let indexExpr ← liftD (nativeExpr span indexValue)
      let bounded := Expr.cast (.uint (length - 1)) indexExpr
      let boundCheck := Expr.eq bounded bounded
      let width := childType.checked.expandedLeaves
      let parentLeaves := (← liftD ((components parent).mapM (nativeOfScalar span))).toArray
      let last := length - 1
      -- The range constraint makes the last element the only valid fallback.
      let selected := (List.range width).map fun leafOffset =>
        ((List.range last).foldr (fun position rest =>
          .select (.eq indexExpr (.native position))
            ((parentLeaves[position * width + leafOffset]?).getD (.native 0)) rest)
          ((parentLeaves[last * width + leafOffset]?).getD (.native 0)))
      let constraints := parent.constraints ++ indexValue.constraints ++ [boundCheck]
      match resultTypeOfComposite element with
      | .unit => pure {unitValue with constraints}
      | .scalar ty =>
        let selected := selected.map fun field => ⟨.native, field⟩
        pure {scalarValue (← liftD (restoreLayoutScalar span ty selected)) with constraints}
      | .composite type => pure (aggregateValue type (selected.map fun leaf => ⟨.native, leaf⟩) constraints)
    | .effect kind label _ => liftD (fail span s!"native helper capability unavailable: {repr kind} ({label})")
    | .at span value => lowerTerm program scope env span value

  private partial def lowerCall (program : Program) (declaration : Declaration)
      (values : List Lowered) (span : SourceSpan) : LowerM Lowered := do
    spendLower span
    let initial ← get
    let callerPath := initial.callPath
    modify fun state => {state with callPath := callerPath ++ [declaration.id]}
    let mut env := []
    let mut bindings := []
    for (parameter, actual) in declaration.parameters.zip values do
      spendLower span
      let parameterType := declaration.parameterType parameter
      let actual ← liftD (coerce span actual parameterType)
      let mut references : List Scalar := []
      let actualComponents := components actual
      if actualComponents.isEmpty then
        let name ← freshTyped actual.scalar.ty
        recordLocal name actual.scalar
        bindings := bindings ++ [(name, actual.scalar)]
      else
        for component in actualComponents do
          let name ← freshTyped component.ty
          recordLocal name component
          bindings := bindings ++ [(name, component)]
          references := references ++ [⟨component.ty, .ref name⟩]
      let reference := match parameterType with
        | .composite type => aggregateValue type references
        | .scalar _ => {actual with scalar := references.headD actual.scalar}
        | .unit => unitValue
      env := (parameter.name, reference) :: env
    let argumentConstraints := values.flatMap (·.constraints)
    if (← get).ledgerMode then appendLedgerConstraints span argumentConstraints
    let body ← lowerBody program declaration env declaration.body
    modify fun state => {state with
      callPath := callerPath
      guard := initial.guard
      guardActive := initial.guardActive
      localBindings := initial.localBindings}
    let body := {body with constraints :=
      (if initial.ledgerMode then [] else argumentConstraints ++ body.constraints)}
    let types := (← get).types
    pure (bindings.foldr (fun (name, value) body =>
      sequence types name {ty := .scalar value.ty, scalar := value} body) body)

  private partial def lowerBody (program : Program) (declaration : Declaration)
      (env : LowerEnv) (body : List Statement) : LowerM Lowered :=
    lowerBodyWith program declaration env body (fun _ => pure unitValue)

  private partial def lowerBodyWith (program : Program) (declaration : Declaration)
      (env : LowerEnv) (body : List Statement)
      (continuation : LowerEnv → LowerM Lowered) : LowerM Lowered := do
    spendLower declaration.span
    match body with
    | [] => continuation env
    | .return value :: _ =>
      let value ← match value with
        | none => pure unitValue
        | some value => lowerTerm program declaration.id.scope env declaration.span value
      let value ← liftD (coerce declaration.span value declaration.result)
      if (← get).ledgerMode then appendLedgerConstraints declaration.span value.constraints
      pure {value with constraints := if (← get).ledgerMode then [] else value.constraints}
    | statement :: rest =>
      match statement with
      | .bind name ty value =>
        let value ← lowerTerm program declaration.id.scope env declaration.span value
        let value ← liftD (coerce declaration.span value ty)
        if (← get).ledgerMode then appendLedgerConstraints declaration.span value.constraints
        let mut references : List Scalar := []
        let mut bindings := []
        for component in components value do
          let localName ← freshTyped component.ty
          recordLocal localName component
          bindings := bindings ++ [(localName, component)]
          references := references ++ [⟨component.ty, .ref localName⟩]
        if bindings.isEmpty then
          let localName ← freshTyped value.scalar.ty
          recordLocal localName value.scalar
          bindings := [(localName, value.scalar)]
        let reference : Lowered := match ty with
          | .unit => unitValue
          | .scalar _ => {value with scalar := references.headD value.scalar}
          | .composite type => aggregateValue type references
        let body ← lowerBodyWith program declaration ((name, reference) :: env) rest continuation
        let body := {body with constraints := if (← get).ledgerMode then [] else value.constraints ++ body.constraints}
        let types := (← get).types
        pure (bindings.foldr (fun (localName, component) body =>
          sequence types localName {ty := .scalar component.ty, scalar := component} body) body)
      | .evaluate value =>
        let value ← lowerTerm program declaration.id.scope env declaration.span value
        if (← get).ledgerMode then appendLedgerConstraints declaration.span value.constraints
        let mut bindings := []
        for component in components value do
          let name ← freshTyped component.ty
          bindings := bindings ++ [(name, component)]
        if bindings.isEmpty then
          let name ← freshTyped value.scalar.ty
          bindings := [(name, value.scalar)]
        let body ← lowerBodyWith program declaration env rest continuation
        let body := {body with constraints := if (← get).ledgerMode then [] else value.constraints ++ body.constraints}
        let types := (← get).types
        pure (bindings.foldr (fun (name, component) body =>
          sequence types name {ty := .scalar component.ty, scalar := component} body) body)
      | .assert condition =>
        let condition ← lowerTerm program declaration.id.scope env declaration.span condition
        if (← get).ledgerMode then appendLedgerConstraints declaration.span condition.constraints
        let conditionExpr ← liftD (boolExpr declaration.span condition)
        if (← get).ledgerMode then do
          appendLedgerEffect declaration.span (.require conditionExpr)
          let body ← lowerBodyWith program declaration env rest continuation
          pure {body with constraints := []}
        else do
          let body ← lowerBodyWith program declaration env rest continuation
          if let .composite _ := body.ty then
            pure {body with constraints := condition.constraints ++
              [Expr.eq conditionExpr (.bool true)] ++ body.constraints}
          else
            pure {body with
              scalar := ⟨body.scalar.ty, .assertE conditionExpr body.scalar.value⟩
              constraints := condition.constraints ++ body.constraints}
      | .branch (.bool conditionValue) yes no => do
        let entryState ← get
        let resume : LowerEnv → LowerM Lowered := fun _ => do
          let branchState ← get
          modify fun state => {state with
            guard := entryState.guard, guardActive := entryState.guardActive,
            localBindings := entryState.localBindings}
          let body ← lowerBodyWith program declaration env rest continuation
          let finalState ← get
          modify fun _state => {finalState with localBindings := branchState.localBindings}
          pure body
        let selected ← lowerBodyWith program declaration env
          (if conditionValue then yes else no) resume
        let finalState ← get
        modify fun _state => {finalState with
          guard := entryState.guard, guardActive := entryState.guardActive,
          localBindings := entryState.localBindings}
        pure selected
      | .branch condition yes no => do
        let condition ← lowerTerm program declaration.id.scope env declaration.span condition
        if (← get).ledgerMode then appendLedgerConstraints declaration.span condition.constraints
        let conditionExpr ← liftD (boolExpr declaration.span condition)
        let entryState ← get
        let name ← freshTyped .bool
        let conditionRef : Expr .bool := .ref name
        recordLocal name ⟨.bool, conditionExpr⟩
        let branchState ← get
        let resume : LowerEnv → LowerM Lowered := fun _ =>
          lowerBodyWith program declaration env rest continuation
        modify fun state => {state with
          guard := guardedBranch branchState.guard conditionRef true, guardActive := true}
        let yes ← lowerBodyWith program declaration env yes resume
        modify fun state => {state with
          guard := guardedBranch branchState.guard conditionRef false, guardActive := true,
          localBindings := branchState.localBindings}
        let no ← lowerBodyWith program declaration env no resume
        modify fun state => {state with
          guard := entryState.guard, guardActive := entryState.guardActive,
          localBindings := entryState.localBindings}
        let selected ← liftD (selectLowered declaration.span conditionRef yes no)
        let selected := bindCondition name conditionExpr selected
        pure {selected with constraints :=
          if (← get).ledgerMode then [] else condition.constraints ++ selected.constraints}
      | .readCell stateName destination ty => do
        unless (← get).ledgerMode do
          liftD (fail declaration.span "native helper capability unavailable: ledger read")
        let readName ← freshTyped ty
        appendLedgerEffect declaration.span (.readCell stateName readName ty)
        let reference : Lowered := scalarValue (ty := ty) (Expr.ref readName)
        lowerBodyWith program declaration ((destination, reference) :: env) rest continuation
      | .writeCell stateName ty value => do
        unless (← get).ledgerMode do
          liftD (fail declaration.span "native helper capability unavailable: ledger write")
        let value ← lowerTerm program declaration.id.scope env declaration.span value
        appendLedgerConstraints declaration.span value.constraints
        let value ← liftD (typedExpr declaration.span ty value)
        appendLedgerEffect declaration.span (.writeCell stateName ty value)
        lowerBodyWith program declaration env rest continuation
      | .readMap stateName destination keyTy valueTy key
      | .readMember stateName destination keyTy valueTy key => do
        unless (← get).ledgerMode do
          liftD (fail declaration.span "native helper capability unavailable: ledger read")
        let key ← lowerTerm program declaration.id.scope env declaration.span key
        let key ← liftD (typedExpr declaration.span keyTy key)
        let resultTy := match statement with
          | .readMember .. => Ty.bool
          | _ => valueTy
        let readName ← freshTyped resultTy
        let effect := match statement with
          | .readMember .. => Effect.readMember stateName readName keyTy valueTy key
          | _ => Effect.readMap stateName readName keyTy valueTy key
        appendLedgerEffect declaration.span effect
        let reference := scalarValue (ty := resultTy) (Expr.ref readName)
        lowerBodyWith program declaration ((destination, reference) :: env) rest continuation
      | .writeMap stateName keyTy valueTy key value => do
        unless (← get).ledgerMode do
          liftD (fail declaration.span "native helper capability unavailable: ledger write")
        let key ← lowerTerm program declaration.id.scope env declaration.span key
        let key ← liftD (typedExpr declaration.span keyTy key)
        let value ← lowerTerm program declaration.id.scope env declaration.span value
        let value ← liftD (typedExpr declaration.span valueTy value)
        appendLedgerEffect declaration.span (.writeMap stateName keyTy valueTy key value)
        lowerBodyWith program declaration env rest continuation
      | .emitEvent kind payload => do
        unless (← get).ledgerMode do
          liftD (fail declaration.span "native helper capability unavailable: ledger event")
        let payload ← lowerTerm program declaration.id.scope env declaration.span payload
        appendLedgerConstraints declaration.span payload.constraints
        let payload ← liftD (typedExpr declaration.span (.bytes kind.payloadSize) payload)
        appendLedgerEffect declaration.span (.emitEvent kind payload)
        lowerBodyWith program declaration env rest continuation
      | .forRange .. => liftD (fail declaration.span "unprepared finite range reached helper lowering")
      | .stage .. => liftD (fail declaration.span "native helper capability unavailable: private state")
      | .return _ => liftD (fail declaration.span "invalid helper statement sequence")
end

/-- Compilation always performs typing, call-graph/purity analysis and DF-00.
No caller-supplied summary or disclosure exemption is accepted. -/
private def compileHostedMode (limits : Limits) (program : Program) (entryName : String)
    (allowGuardedWitnesses : Bool) : Except Diagnostic HostedCircuit := do
  let program ← prepareProgramWithLimits limits program
  let summaries ← analyzeWithLimits limits program
  for summary in summaries do
    if summary.guarded && summary.effects.contains .witness && !allowGuardedWitnesses then
      fail {} "native helper capability unavailable: witness-dependent guarded control (CF-02)"
    if let some effect := summary.effects.find? fun effect => effect.impure && effect != .witness then
      let declaration ← lookup program summary.id {}
      fail declaration.span s!"native helper capability unavailable: {repr effect}"
  let some entry := program.exports.find? (·.name == entryName) | fail {} "unknown helper entrypoint"
  let declaration ← lookup program entry.target entry.span
  let inputs ← aggregateInputs program entry
  unless uniqueNames (inputs.map (·.name)) do fail entry.span "aggregate input component names collide"
  let inputTypes : TypeEnv := inputs.map fun input => (input.name, input.ty)
  let mut inputConstraints := []
  for input in entry.compositeInputs do
    let compiled ← checkedComposite program input.span input.type
    let leaves := (sourceLeafPaths compiled.checked.value "").map fun path =>
      Expr.ref (aggregateInputName input.name path)
    let checked ← liftError input.span ((Types.checkNativeExpression compiled inputTypes leaves).mapError id)
    inputConstraints := inputConstraints ++ checked.constraints
  let mut values := []
  let mut scalarInputs := entry.inputs
  let mut aggregateInputs := entry.compositeInputs
  for parameter in declaration.parameters do
    match declaration.parameterType parameter with
    | .composite type =>
      let some input := aggregateInputs.head?
        | fail entry.span s!"missing composite helper input '{parameter.name}'"
      aggregateInputs := aggregateInputs.drop 1
      unless input.type == type do fail input.span "helper composite input identity mismatch"
      let compiled ← checkedComposite program input.span type
      let leaves := (sourceLeafPaths compiled.checked.value "").map fun path =>
        ⟨.native, Expr.ref (aggregateInputName input.name path)⟩
      values := values ++ [aggregateValue type leaves]
    | .unit =>
      let some input := aggregateInputs.head?
        | fail entry.span s!"missing Unit helper input '{parameter.name}'"
      aggregateInputs := aggregateInputs.drop 1
      unless input.type == .unit do fail input.span "helper Unit input type mismatch"
      values := values ++ [unitValue]
    | .scalar _ =>
      let some input := scalarInputs.head?
        | fail entry.span s!"missing scalar helper input '{parameter.name}'"
      scalarInputs := scalarInputs.drop 1
      values := values ++ [scalarValue (ty := input.ty) (Expr.ref input.name)]
  unless scalarInputs.isEmpty && aggregateInputs.isEmpty do
    fail entry.span "helper entrypoint input signature mismatch"
  let (body, lowering) ← (lowerCall program declaration values entry.span).run
    {reserved := inputs.map (·.name), types := inputTypes,
      allowGuardedWitnesses, remaining := limits.maxExecutionSteps}
  let inputs := inputs ++ lowering.witnessInputs
  let outputName := ((List.range (inputs.length + 1)).map fun n =>
    if n == 0 then "result" else s!"result{n}").find?
      (fun name => !(inputs.map (·.name)).contains name) |>.getD "result"
  let outputValues ← match declaration.result with
    | .unit => pure []
    | .scalar _ => pure [(outputName, body.scalar)]
    | .composite type => do
      let compiled ← checkedComposite program entry.span type
      unless body.components.length == compiled.checked.expandedLeaves do
        fail entry.span "aggregate helper result leaf count mismatch"
      let paths := sourceLeafPaths compiled.checked.value ""
      pure ((paths.zip body.components).map fun (path, component) =>
        (aggregateInputName outputName path, component))
  let outputs := outputValues.map fun (name, component) => {
    name, ty := component.ty, value := component.value, span := entry.span : Output}
  let mut outputConstraints := []
  if let .composite type := declaration.result then
    let compiled ← checkedComposite program entry.span type
    unless body.components.length == compiled.checked.expandedLeaves do
      fail entry.span "aggregate helper result leaf count mismatch"
    let leaves ← body.components.mapM (nativeOfScalar entry.span)
    let checked ← liftError entry.span ((Types.checkNativeExpression compiled lowering.types leaves).mapError id)
    outputConstraints := checked.constraints
  let circuit : Circuit := {
    name := entry.name, inputs, outputs, span := entry.span
    privateOrigins := lowering.privateOrigins
    constraints := inputConstraints ++ lowering.witnessConstraints ++ body.constraints ++ outputConstraints ++
      (if outputValues.isEmpty then [.letE "$unit" body.scalar.value (.bool true)] else [])
  }
  circuit.validate Capabilities.crypto
  Disclosure.circuit circuit
  pure {circuit, calls := lowering.witnessCalls}

def compileHostedWithLimits (limits : Limits) (program : Program) (entryName : String) :
    Except Diagnostic HostedCircuit := compileHostedMode limits program entryName false

/-- Witness artifacts opt in to guarded typed provider calls. Ordinary helper
compilation keeps rejecting witness-dependent control. -/
def compileHostedWitnessWithLimits (limits : Limits) (program : Program) (entryName : String) :
    Except Diagnostic HostedCircuit := compileHostedMode limits program entryName true

def compileWithLimits (limits : Limits) (program : Program) (entryName : String) : Except Diagnostic Circuit :=
  (compileHostedWithLimits limits program entryName).map (·.circuit)

def compile (program : Program) (entryName : String) : Except Diagnostic Circuit :=
  compileWithLimits {} program entryName

structure HostedEntrypoint where
  entrypoint : Entrypoint
  calls : List WitnessCallBinding
  deriving Repr

private def compileEntrypointForState (allowWitnesses : Bool) (limits : Limits) (program : Program)
    (entryName : String) (ledger : List StateDecl) : Except Diagnostic HostedEntrypoint := do
  let program ← prepareProgramWithLimits limits program
  let summaries ← analyzeWithLimits limits program
  for summary in summaries do
    for effect in summary.effects do
      unless effect == .assertion || effect == .fallibleCast ||
          effect == .ledgerRead || effect == .ledgerWrite || effect == .event ||
          (allowWitnesses && effect == .witness) do
        let declaration ← lookup program summary.id {}
        fail declaration.span s!"native ledger helper capability unavailable: {repr effect}"
  let some exported := program.exports.find? (·.name == entryName)
    | fail {} "unknown helper entrypoint"
  let declaration ← lookup program exported.target exported.span
  let inputs ← aggregateInputs program exported
  unless uniqueNames (inputs.map (·.name)) do fail exported.span "aggregate input component names collide"
  let inputTypes : TypeEnv := inputs.map fun input => (input.name, input.ty)
  let mut inputConstraints := []
  for input in exported.compositeInputs do
    let compiled ← checkedComposite program input.span input.type
    let leaves := (sourceLeafPaths compiled.checked.value "").map fun path =>
      Expr.ref (aggregateInputName input.name path)
    let checked ← liftError input.span ((Types.checkNativeExpression compiled inputTypes leaves).mapError id)
    inputConstraints := inputConstraints ++ checked.constraints
  let mut values := []
  let mut scalarInputs := exported.inputs
  let mut aggregateInputs := exported.compositeInputs
  for parameter in declaration.parameters do
    match declaration.parameterType parameter with
    | .composite type => do
      let some input := aggregateInputs.head?
        | fail exported.span s!"missing composite helper input '{parameter.name}'"
      aggregateInputs := aggregateInputs.drop 1
      unless input.type == type do fail input.span "helper composite input identity mismatch"
      let compiled ← checkedComposite program input.span type
      let leaves := (sourceLeafPaths compiled.checked.value "").map fun path =>
        ⟨.native, Expr.ref (aggregateInputName input.name path)⟩
      values := values ++ [aggregateValue type leaves]
    | .unit => do
      let some input := aggregateInputs.head?
        | fail exported.span s!"missing Unit helper input '{parameter.name}'"
      aggregateInputs := aggregateInputs.drop 1
      unless input.type == .unit do fail input.span "helper Unit input type mismatch"
      values := values ++ [unitValue]
    | .scalar _ => do
      let some input := scalarInputs.head?
        | fail exported.span s!"missing scalar helper input '{parameter.name}'"
      scalarInputs := scalarInputs.drop 1
      values := values ++ [scalarValue (ty := input.ty) (Expr.ref input.name)]
  unless scalarInputs.isEmpty && aggregateInputs.isEmpty do
    fail exported.span "helper entrypoint input signature mismatch"
  let initial : LowerState := {
    reserved := inputs.map (·.name), types := inputTypes, ledgerMode := true,
    allowGuardedWitnesses := allowWitnesses,
    remaining := limits.maxExecutionSteps}
  let action : LowerM Lowered := do
    appendLedgerConstraints exported.span inputConstraints
    lowerCall program declaration values exported.span
  let (body, lowering) ← action.run initial
  unless allowWitnesses || (lowering.witnessInputs.isEmpty && lowering.witnessCalls.isEmpty) do
    fail exported.span "native ledger helper witness scheduling is unavailable"
  let readNames := lowering.ledgerEffects.filterMap fun
    | .readCell _ destination _ => some destination
    | .readMap _ destination _ _ _ | .readMember _ destination _ _ _ => some destination
    | _ => none
  let compositeReturnInfo ← match declaration.result with
    | .composite type => do
      let compiled ← checkedComposite program exported.span type
      if compiled.checked.expandedLeaves > maxEntrypointReturnFields then
        fail exported.span "entrypoint return field limit exceeded"
      discard (Types.schemaJson compiled |>.mapError fun message =>
        {span := exported.span, message})
      pure (some (type, compiled.checked.expandedLeaves))
    | _ => pure none
  let reservedOutputNames := (inputs ++ lowering.witnessInputs).map (·.name) ++ readNames
  let physicalNames (base : String) := match compositeReturnInfo with
    | some (_, count) => (List.range count).map fun index => s!"{base}_{index}"
    | none => [base]
  let outputName := ((List.range (reservedOutputNames.length + 1)).map fun index =>
    if index == 0 then "result" else s!"result{index}").find?
      (fun name => !reservedOutputNames.contains name &&
        (physicalNames name).all (!reservedOutputNames.contains ·)) |>.getD "result_fresh"
  let returnData ← match declaration.result with
    | .unit => pure (([] : List Output), ([] : List ReturnView))
    | .scalar ty => do
      let value ← typedExpr exported.span ty body
      pure ([{name := outputName, ty := ty, value := value, span := exported.span}],
        ([] : List ReturnView))
    | .composite type => do
      let some (_, expectedCount) := compositeReturnInfo
        | fail exported.span "composite return layout was not checked"
      let returnComponents := components body
      unless returnComponents.length == expectedCount do
        fail exported.span "composite return leaf count mismatch"
      let mut outputs : List Output := []
      let mut fields : List String := []
      for (component, index) in returnComponents.zipIdx do
        let name := s!"{outputName}_{index}"
        let value ← nativeOfScalar exported.span component
        outputs := outputs ++ [{name, ty := .native, value, span := exported.span}]
        fields := fields ++ [name]
      let view : ReturnView := {
        name := outputName
        environment := program.composites
        type := type
        fields := fields}
      pure (outputs, [view])
  let returns := returnData.1
  let returnViews := returnData.2
  let circuit : Circuit := {
    name := exported.name, inputs := inputs ++ lowering.witnessInputs, outputs := [],
    constraints := if allowWitnesses then lowering.witnessConstraints else [], span := exported.span,
    privateOrigins := lowering.privateOrigins}
  let result : Entrypoint := {
    name := exported.name, circuit, effects := lowering.ledgerEffects, returns, returnViews,
    span := exported.span, effectSpans := lowering.ledgerSpans,
    effectGuards := lowering.ledgerGuards}
  let capabilities := {Capabilities.crypto with stateCells := true, stateMaps := true}
  match result.validate capabilities ledger with
  | .error diagnostic => .error diagnostic
  | .ok _ => pure ()
  match Disclosure.entrypoint result with
  | .error diagnostic => .error diagnostic
  | .ok _ => pure ()
  pure {entrypoint := result, calls := lowering.witnessCalls}

def compileEntrypointWithLimits (limits : Limits) (program : Program) (entryName : String) :
    Except Diagnostic Entrypoint :=
  (compileEntrypointForState false limits program entryName program.ledger).map (·.entrypoint)

def compileEntrypoint (program : Program) (entryName : String) : Except Diagnostic Entrypoint :=
  compileEntrypointWithLimits {} program entryName

private def compileBoundEntrypointForWithLimits (allowWitnesses : Bool) (limits : Limits)
    (program : Program) (entryName : String) (ledger : List StateDecl) :
    Except Diagnostic HostedEntrypoint := do
  checkLedgerSchema {} ledger
  for declared in program.ledger do
    let some actual := ledger.find? (·.name == declared.name)
      | fail declared.span s!"source ledger state '{declared.name}' is absent from its contract"
    unless actual.kind == declared.kind && actual.sealed == declared.sealed do
      fail declared.span s!"source ledger state '{declared.name}' does not match its contract declaration"
  let program := {program with ledger}
  compileEntrypointForState allowWitnesses limits program entryName ledger

/-- Compile source ledger effects with their ordered typed provider calls. -/
def compileHostedEntrypointForWithLimits (limits : Limits) (program : Program)
    (entryName : String) (ledger : List StateDecl) : Except Diagnostic HostedEntrypoint :=
  compileBoundEntrypointForWithLimits true limits program entryName ledger

/-- Compile source cell declarations against the owning contract's schema. -/
def compileEntrypointForWithLimits (limits : Limits) (program : Program)
    (entryName : String) (ledger : List StateDecl) : Except Diagnostic Entrypoint :=
  (compileBoundEntrypointForWithLimits false limits program entryName ledger).map (·.entrypoint)

/-- Bind source cell declarations to the owning contract's authoritative state
schema before compiling source reads and writes. -/
def compileEntrypointFor (program : Program) (entryName : String) (ledger : List StateDecl) :
    Except Diagnostic Entrypoint :=
  compileEntrypointForWithLimits {} program entryName ledger

private abbrev TraceValue := Option ScalarPolicy.Value
private abbrev TraceEnv := List (String × TraceValue)
private structure TraceState where
  events : List String := []
  remaining : Nat
  deriving Inhabited

private abbrev TraceM := StateT TraceState (Except Diagnostic)

private def spendTrace (span : SourceSpan) : TraceM Unit := do
  let state ← get
  if state.remaining == 0 then liftM (resource span "evaluation steps")
  set {state with remaining := state.remaining - 1}

private def traceScalar (span : SourceSpan) (value : TraceValue) : TraceM ScalarPolicy.Value :=
  match value with
  | some value => pure value
  | none => liftM (fail span "unit used as scalar in helper trace")

private def traceType : TraceValue → ResultType
  | none => .unit
  | some value => .scalar (match value.kind with
    | .native => .native | .bool => .bool | .uint m => .uint m | .bytes length => .bytes length
    | .opaqueBytes => .opaqueBytes
    | .jubjubScalar => .jubjubScalar | .jubjubPoint => .jubjubPoint
    | .foreign kind => .foreign kind)

private def traceCast (span : SourceSpan) (value : TraceValue) (ty : ResultType) : TraceM TraceValue := do
  match ty with
  | .unit => pure none
  | .scalar ty =>
    if ty.isForeign then liftM (fail span "foreign helper evaluation requires the native control runtime")
    let value ← traceScalar span value
    some <$> liftM (liftError span (ScalarPolicy.cast value ty.scalarKind))
  | .composite _ => liftM (fail span "aggregate helper trace is unavailable")

mutual
  private partial def traceTerm (program : Program) (ctx : EvalContext) (scope : Nat)
      (env : TraceEnv) (span : SourceSpan) (term : Term) : TraceM TraceValue := do
    spendTrace span
    match term with
    | .unit => pure none
    | .native n => pure (some ⟨.native, n⟩)
    | .bool b => pure (some ⟨.bool, if b then 1 else 0⟩)
    | .uint m n => pure (some ⟨.uint m, n⟩)
    | .foreignConstant .. => liftM (fail span "foreign helper evaluation requires the native control runtime")
    | .ref name =>
      let some value := env.lookup name | liftM (fail span "unbound helper trace value")
      pure value
    | .binary op left right =>
      let left ← traceTerm program ctx scope env span left >>= traceScalar span
      let right ← traceTerm program ctx scope env span right >>= traceScalar span
      some <$> liftM (liftError span (ScalarPolicy.evaluate op left right))
    | .boolAnd left right | .boolOr left right | .boolXor left right => do
      let left ← traceTerm program ctx scope env span left >>= traceScalar span
      let right ← traceTerm program ctx scope env span right >>= traceScalar span
      let leftBool := left.number != 0
      let rightBool := right.number != 0
      let result ← match term with
        | .boolAnd .. => pure (leftBool && rightBool)
        | .boolOr .. => pure (leftBool || rightBool)
        | .boolXor .. => pure (leftBool != rightBool)
        | _ => liftM (fail span "invalid eager Boolean trace term")
      pure (some ⟨.bool, if result then 1 else 0⟩)
    | .cast target value =>
      let value ← traceTerm program ctx scope env span value
      traceCast span value (.scalar target)
    | .eq left right =>
      let left ← traceTerm program ctx scope env span left
      let right ← traceTerm program ctx scope env span right
      let ty ← liftM (common span (← liftM (scalar span (traceType left)))
        (← liftM (scalar span (traceType right))))
      let left ← traceCast span left (.scalar ty)
      let right ← traceCast span right (.scalar ty)
      pure (some ⟨.bool, if left == right then 1 else 0⟩)
    | .select condition yes no =>
      let condition ← traceTerm program ctx scope env span condition >>= traceScalar span
      let yes ← traceTerm program ctx scope env span yes
      let no ← traceTerm program ctx scope env span no
      let ty ← liftM (common span (← liftM (scalar span (traceType yes)))
        (← liftM (scalar span (traceType no))))
      traceCast span (if condition.number == 0 then no else yes) (.scalar ty)
    | .ite condition yes no =>
      let condition ← traceTerm program ctx scope env span condition >>= traceScalar span
      let result ← traceTerm program ctx scope env span (if condition.number == 0 then no else yes)
      let info ← liftM (inferTerm 128 program scope (env.map fun (name, value) => (name, traceType value)) span term)
      traceCast span result info.ty
    | .andThen left right =>
      let left ← traceTerm program ctx scope env span left >>= traceScalar span
      if left.number == 0 then pure (some left) else traceTerm program ctx scope env span right
    | .orElse left right =>
      let left ← traceTerm program ctx scope env span left >>= traceScalar span
      if left.number != 0 then pure (some left) else traceTerm program ctx scope env span right
    | .witness .. | .witnessCall .. => liftM (fail span "registered witness execution requires the portable control runtime")
    | .disclose _ value => traceTerm program ctx scope env span value
    | .poseidon2 domain left right =>
      let left ← traceTerm program ctx scope env span left >>= traceScalar span
      let right ← traceTerm program ctx scope env span right >>= traceScalar span
      let result ← liftM (liftError span (ctx.poseidon2 domain left.number right.number))
      let value : ScalarPolicy.Value := ⟨.native, result⟩
      liftM (liftError span value.validate)
      pure (some value)
    -- Curve terms still need the portable control runtime to produce a point,
    -- but trace every ordered field argument before reporting that boundary.
    | .curve operation arguments => do
      liftM (validateCurveArity span operation arguments)
      if arguments.length > curveArgumentLimit ({} : Limits) operation then
        liftM (resource span "curve arguments")
      let (expected, _) := operation.signature
      unless arguments.length == expected.length do
        liftM (fail span s!"{operation.operationName} argument count mismatch")
      let values ← arguments.mapM (traceTerm program ctx scope env span)
      for (value, expectedType) in values.zip expected do
        unless traceType value == .scalar expectedType do
          liftM (fail span s!"{operation.operationName} argument type mismatch")
      liftM (fail span s!"{operation.operationName} helper evaluation requires the native control runtime")
    -- shortcut: byte traces need ordered byte values; extend the trace model before enabling them.
    | .bytes32Literal _ | .bytes .. | .bytesAt .. =>
      liftM (fail span "byte-string helper evaluation requires the qualified native control runtime")
    | .call name arguments =>
      let values ← arguments.mapM (traceTerm program ctx scope env span)
      let declaration ← liftM (resolveUnchecked program scope name (values.map traceType) span)
      traceCall program ctx declaration values
    | .composite .. | .project .. | .index .. => liftM (fail span "aggregate helper trace is unavailable")
    | .effect _ label result =>
      let result ← traceTerm program ctx scope env span result
      modify fun state => {state with events := label :: state.events}
      pure result
    | .at span value => traceTerm program ctx scope env span value

  private partial def traceCall (program : Program) (ctx : EvalContext) (declaration : Declaration)
      (values : List TraceValue) : TraceM TraceValue := do
    spendTrace declaration.span
    let env ← (declaration.parameters.zip values).mapM fun (parameter, value) => do
      spendTrace declaration.span
      pure (parameter.name, ← traceCast declaration.span value (.scalar parameter.ty))
    traceBody program ctx declaration env declaration.body

  private partial def traceBody (program : Program) (ctx : EvalContext) (declaration : Declaration)
      (env : TraceEnv) (body : List Statement) : TraceM TraceValue := do
    pure (← traceBlock program ctx declaration env body).2

  private partial def traceBlock (program : Program) (ctx : EvalContext) (declaration : Declaration)
      (env : TraceEnv) (body : List Statement) : TraceM (Bool × TraceValue) := do
    spendTrace declaration.span
    match body with
    | [] => pure (false, none)
    | .return none :: _ => pure (true, none)
    | .return (some value) :: _ =>
      let value ← traceTerm program ctx declaration.id.scope env declaration.span value
      pure (true, ← traceCast declaration.span value declaration.result)
    | .bind name ty value :: rest =>
      let value ← traceTerm program ctx declaration.id.scope env declaration.span value
      let value ← traceCast declaration.span value ty
      traceBlock program ctx declaration ((name, value) :: env) rest
    | .evaluate value :: rest =>
      discard (traceTerm program ctx declaration.id.scope env declaration.span value)
      traceBlock program ctx declaration env rest
    | .assert condition :: rest =>
      let condition ← traceTerm program ctx declaration.id.scope env declaration.span condition >>= traceScalar declaration.span
      unless condition.number == 1 do liftM (fail declaration.span "helper assertion failed")
      traceBlock program ctx declaration env rest
    | .branch condition yes no :: rest =>
      let condition ← traceTerm program ctx declaration.id.scope env declaration.span condition >>= traceScalar declaration.span
      let result ← traceBlock program ctx declaration env (if condition.number == 0 then no else yes)
      if result.1 then pure result else traceBlock program ctx declaration env rest
    | .forRange .. :: _ =>
      liftM (fail declaration.span "unprepared finite range reached helper trace")
    | .readCell .. :: _ =>
      liftM (fail declaration.span "ledger reads require the native contract runtime")
    | .writeCell .. :: _ =>
      liftM (fail declaration.span "ledger writes require the native contract runtime")
    | .readMap .. :: _ | .readMember .. :: _ =>
      liftM (fail declaration.span "ledger reads require the native contract runtime")
    | .writeMap .. :: _ =>
      liftM (fail declaration.span "ledger writes require the native contract runtime")
    | .emitEvent .. :: _ =>
      liftM (fail declaration.span "ledger events require the native contract runtime")
    | .stage _ _ _ _ :: _ => liftM (fail declaration.span "private staging requires the portable control runtime")
end

/-- Deterministic effect fixtures validate source evaluation order separately
from native capability support. No witness callback or external side effect runs. -/
def traceWithLimits (limits : Limits) (program : Program) (ctx : EvalContext) (entryName : String)
    (inputs : List ScalarPolicy.Value) : Except Diagnostic (TraceValue × List String) := do
  let program ← prepareProgramWithLimits limits program
  discard (analyzeWithLimits limits program)
  let some entry := program.exports.find? (·.name == entryName) | fail {} "unknown helper trace entrypoint"
  let declaration ← lookup program entry.target entry.span
  unless inputs.length == entry.inputs.length do fail entry.span "helper trace input count mismatch"
  for (input, value) in entry.inputs.zip inputs do
    liftError input.span value.validate
    unless traceType (some value) == .scalar input.ty do fail input.span "helper trace input type mismatch"
  let (result, state) ← (traceCall program ctx declaration (inputs.map some)).run
    {remaining := limits.maxExecutionSteps}
  pure (result, state.events.reverse)

def trace (program : Program) (ctx : EvalContext) (entryName : String)
    (inputs : List ScalarPolicy.Value) : Except Diagnostic (TraceValue × List String) :=
  traceWithLimits {} program ctx entryName inputs

/-- Discarding a parameter cannot discard a failing actual argument. -/
theorem argument_failure_preserved (ctx : EvalContext) (env : EvalEnv)
    (name : String) (argument : Expr source) (body : Expr result) (message : String)
    (h : argument.eval ctx env = .error message) :
    (Expr.letE name argument body).eval ctx env = .error message := by
  rw [Expr.eval, h]
  rfl

/-- The binding introduced for a helper parameter transfers actual origins
without releasing them, even when parameter and caller spellings coincide. -/
theorem parameter_origins_preserved (env : Disclosure.Environment) (name : String)
    (argument : Expr source) :
    Disclosure.origins env (Expr.letE name argument (Expr.ref name : Expr source)) =
      Disclosure.origins env argument := by
  simp only [Disclosure.origins]
  cases Disclosure.origins env argument <;> simp [List.lookup]

end Noctium.Helpers
