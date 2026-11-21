import Noctium.Core
import Noctium.Types.Composite

namespace Noctium

def maxBytesLength : Nat := Types.defaultLimits.maxVectorLength

def balanceMaximum : Nat := 2 ^ 128 - 1

inductive Visibility where
  | «public» | «private»
  deriving Repr, BEq, DecidableEq, Inhabited

inductive PrivateOriginKind where
  | parameter | provider | privateState
  deriving Repr, BEq, DecidableEq

/-- Every expression carries its result type, independently of a backend. -/
inductive Expr : Ty → Type where
  | native (value : Nat) : Expr .native
  | bool (value : Bool) : Expr .bool
  /-- Eager Boolean conjunction. Both operands evaluate before the result. -/
  | boolAnd (left right : Expr .bool) : Expr .bool
  /-- Eager Boolean disjunction. Both operands evaluate before the result. -/
  | boolOr (left right : Expr .bool) : Expr .bool
  /-- Eager Boolean exclusive-or. Both operands evaluate before the result. -/
  | boolXor (left right : Expr .bool) : Expr .bool
  | uint (maximum value : Nat) : Expr (.uint maximum)
  /-- Pack one field-sized chunk of a typed byte string using the pinned
  little-endian chunk encoding. This constructor is for backend transcript
  lowering. Source expressions cannot cast or do arithmetic on byte strings. -/
  | bytesField (value : Expr (.bytes length)) (chunkIndex : Nat) : Expr .native
  | bytesAt (value : Expr (.bytes length)) (index : Nat) : Expr (.uint 255)
  /-- The one Native projection used for FAB `Compress` alignment. The raw byte
  sequence stays in the host plan and is never reconstructed from this field. -/
  | opaqueBytesProjection (value : Expr .opaqueBytes) : Expr .native
  /-- A fixed-length, right-zero-padded source byte string. -/
  | bytesLiteral (length : Nat) (values : List Nat) : Expr (.bytes length)
  /-- Reverse a fixed-length source byte string without changing its type. -/
  | reverseBytes {length : Nat} (value : Expr (.bytes length)) : Expr (.bytes length)
  /-- Take the half-open byte range [start, end) from a fixed-length string. -/
  | sliceBytes {length : Nat} (value : Expr (.bytes length)) (start stop : Nat) :
      Expr (.bytes (stop - start))
  /-- Concatenate two fixed-length byte strings. -/
  | concatBytes {leftLength rightLength : Nat} (left : Expr (.bytes leftLength))
      (right : Expr (.bytes rightLength)) : Expr (.bytes (leftLength + rightLength))
  /-- Internal SHA-256 expression lowered through the pinned persistent-hash path. -/
  | sha256 {length : Nat} (value : Expr (.bytes length)) : Expr (.bytes 32)
  /-- SHA-512 over a source byte string, returning its full fixed-width digest. -/
  | sha512 {length : Nat} (value : Expr (.bytes length)) : Expr (.bytes 64)
  /-- Keccak-256 over a source byte string, returning its full fixed-width digest. -/
  | keccak256 {length : Nat} (value : Expr (.bytes length)) : Expr (.bytes 32)
  /-- Compact-compatible Keccak over the canonical FAB encoding of a
  Secp256k1Point. This is distinct from the point's compressed byte form. -/
  | keccak256Secp256k1Point
      (value : Expr (.foreign (.point .secp256k1))) : Expr (.bytes 32)
  /-- SHA-256 over the pinned FAB Bytes32 alignment, using native ZKIR
  persistent_hash and returning a typed Bytes32 digest. -/
  | persistentHash32 (value : Expr (.bytes 32)) : Expr (.bytes 32)
  /-- A canonical source-time Bytes32 value. The frontend pads UTF-8 bytes on
  the right and validation checks the resulting 32 byte values. -/
  | bytes32Literal (values : List Nat) : Expr (.bytes 32)
  /-- Reverse the source-order bytes of a typed Bytes32 value. -/
  | reverseBytes32 (value : Expr (.bytes 32)) : Expr (.bytes 32)
  /-- SHA-256 over an ordered, bounded vector of FAB-aligned Bytes32 values. -/
  | persistentHashVector32 (values : List (Expr (.bytes 32))) : Expr (.bytes 32)
  /-- SHA-256 over the canonical 32-byte little-endian Native field encoding. -/
  | persistentHashNative (value : Expr .native) : Expr (.bytes 32)
  /-- SHA-256 over an ordered vector of canonical Native field encodings. -/
  | persistentHashNativeVector (values : List (Expr .native)) : Expr (.bytes 32)
  /-- Serialize a typed field or Jubjub value using the pinned ZKIR byte codec. -/
  | toBytes32 (value : Expr source) : Expr (.bytes 32)
  /-- Decode a Bytes32 value into one of the explicitly supported typed values. -/
  | fromBytes32 (value : Expr (.bytes 32)) : Expr target
  /-- Decode little-endian bytes directly into Native or JubjubScalar. -/
  | fromBytes {length : Nat} (value : Expr (.bytes length)) : Expr target
  /-- Explicitly reduce a Native field into the Jubjub scalar field. -/
  | jubjubScalarFromNative (value : Expr .native) : Expr .jubjubScalar
  /-- Losslessly expose a canonical Jubjub scalar as its Native limb. -/
  | jubjubScalarToNative (value : Expr .jubjubScalar) : Expr .native
  | jubjubMulGenerator (scalar : Expr .jubjubScalar) : Expr .jubjubPoint
  | jubjubMul (point : Expr .jubjubPoint) (scalar : Expr .jubjubScalar) : Expr .jubjubPoint
  | jubjubAdd (left right : Expr .jubjubPoint) : Expr .jubjubPoint
  | jubjubNeg (point : Expr .jubjubPoint) : Expr .jubjubPoint
  | jubjubCoordinate (point : Expr .jubjubPoint) (index : Nat) : Expr .native
  | jubjubFromCoordinates (x y : Expr .native) : Expr .jubjubPoint
  /-- Hash an ordered, bounded list of Native values to a Jubjub subgroup point. -/
  | hashToCurve (values : List (Expr .native)) : Expr .jubjubPoint
  /-- Canonical literals for the pinned foreign field families. -/
  | foreignBase (curve : Foreign.Curve) (value : Nat) : Expr (.foreign (.base curve))
  | foreignScalar (curve : Foreign.Curve) (value : Nat) : Expr (.foreign (.scalar curve))
  | foreignPoint (curve : Foreign.Curve) (value : Foreign.Point) : Expr (.foreign (.point curve))
  /-- One canonical native Encode projection from a typed foreign value. -/
  | foreignEncodedField {kind : Foreign.Kind} (value : Expr (.foreign kind))
      (index : Nat) : Expr .native
  | foreignUnary (operation : Foreign.UnaryOp)
      (value : Expr (.foreign operation.inputKind)) : Expr (.foreign operation.outputKind)
  | foreignBinary (operation : Foreign.BinaryOp)
      (left : Expr (.foreign operation.leftKind))
      (right : Expr (.foreign operation.rightKind)) : Expr (.foreign operation.outputKind)
  | foreignToBytes {kind : Foreign.Kind} (value : Expr (.foreign kind)) :
      Expr (.bytes kind.byteLength)
  | foreignFromBytes (kind : Foreign.Kind) {length : Nat}
      (value : Expr (.bytes length)) : Expr (.foreign kind)
  | copyValue (value : Expr ty) : Expr ty
  | ref (name : String) : Expr ty
  | add (a b : Expr .native) : Expr .native
  | mul (a b : Expr .native) : Expr .native
  | sub (a b : Expr .native) : Expr .native
  | uadd (a : Expr (.uint m)) (b : Expr (.uint n)) : Expr (.uint (m + n))
  | usub (a : Expr (.uint m)) (b : Expr (.uint n)) : Expr (.uint m)
  | umul (a : Expr (.uint m)) (b : Expr (.uint n)) : Expr (.uint (m * n))
  /-- Multiplicative inverse in the source type's pinned prime field. -/
  | inv (value : Expr ty) : Expr ty
  | cast (target : Ty) (value : Expr source) : Expr target
  | letE (name : String) (value : Expr source) (body : Expr ty) : Expr ty
  | assertE (condition : Expr .bool) (body : Expr ty) : Expr ty
  | disclose (span : SourceSpan) (value : Expr ty) : Expr ty
  | eq (a b : Expr ty) : Expr .bool
  | select (condition : Expr .bool) (yes no : Expr ty) : Expr ty
  | poseidon2 (domain : Nat) (a b : Expr .native) : Expr .native
  /-- Hash the exact ordered Native operands with the pinned transient_hash. -/
  | transientHash (values : List (Expr .native)) : Expr .native
  deriving Repr

def Expr.foreignIdentity (curve : Foreign.Curve) : Expr (.foreign (.point curve)) :=
  .foreignPoint curve .identity

structure Input where
  name : String
  ty : Ty
  visibility : Visibility
  span : SourceSpan := {}
  deriving Repr

/-- Public bytes use FAB chunks in high-to-low order. -/
def Input.byteProjectionIdentifiers (name : String) (length : Nat) : List String :=
  if length == 32 then
    [s!"_noctium_bytes32_{name}_high", s!"_noctium_bytes32_{name}_low31"]
  else
    (List.range ((length + 30) / 31)).map fun index => s!"_noctium_bytes_{name}_{index}"

def Input.nativeIdentifiers (input : Input) : List String :=
  match input.ty with
  | .bytes length =>
    if input.visibility == .«public» then
      (Input.byteProjectionIdentifiers input.name length).map fun name => "%input_" ++ name
    else (List.range length).map fun index =>
      s!"%input_{input.name}_byte_{index}"
  | .jubjubPoint => [s!"%input_{input.name}_x", s!"%input_{input.name}_y"]
  | .foreign _ => ["%input_" ++ input.name]
  | .opaqueBytes => ["%input_" ++ input.name]
  | _ => ["%input_" ++ input.name]

/-- Committed byte arguments use FAB high-to-low chunks, as returns do. -/
def Input.callArgumentIdentifiers (input : Input) : List String :=
  match input.ty with
  | .bytes length => (List.range ((length + 30) / 31)).map fun index =>
      s!"%input_{input.name}_call_chunk_{index}"
  | _ => input.nativeIdentifiers

/-- Reserved Native projections used by the public transcript prologue.
These names never replace the typed source alias. -/
def Input.publicProjectionIdentifiers (input : Input) : List String :=
  if input.visibility != .«public» then [] else
  match input.ty with
  | .bytes length => Input.byteProjectionIdentifiers input.name length
  | .jubjubScalar => [s!"_noctium_jubjub_scalar_{input.name}"]
  | .jubjubPoint => [s!"_noctium_jubjub_point_{input.name}_0",
      s!"_noctium_jubjub_point_{input.name}_1"]
  | .foreign kind => (List.range kind.encodedFieldCount).map fun index =>
      s!"_noctium_foreign_{input.name}_{index}"
  | _ => []

structure Output where
  name : String
  ty : Ty
  value : Expr ty
  span : SourceSpan := {}
  deriving Repr

/-- The scalar and fixed-byte layouts committed by the call ABI. -/
def Expr.nativeCallFields : Expr ty → List (Expr .native) :=
  match ty with
  | .native => fun value => [value]
  | .bool => fun value => [.cast .native value]
  | .uint _ => fun value => [.cast .native value]
  | .bytes length => fun value =>
    (List.range ((length + 30) / 31)).map fun index => .bytesField value index
  | .jubjubScalar => fun value => [.jubjubScalarToNative value]
  | .jubjubPoint => fun value => [.jubjubCoordinate value 0, .jubjubCoordinate value 1]
  | .foreign kind => fun value =>
    (List.range kind.encodedFieldCount).map fun index => .foreignEncodedField value index
  | .opaqueBytes => fun value => [.opaqueBytesProjection value]

def Output.nativeReturnFields (output : Output) : Except String (List (Expr .native)) :=
  pure (output.value.nativeCallFields)

def Ty.nativeCallFieldCount (ty : Ty) : Nat :=
  match ty with
  | .bytes length => (length + 30) / 31
  | .jubjubPoint => 2
  | .foreign kind => kind.encodedFieldCount
  | _ => 1

def Output.nativeReturnFieldCount (output : Output) : Nat := output.ty.nativeCallFieldCount

def maxEntrypointReturnFields : Nat := 256

structure ReturnView where
  name : String
  environment : Types.CompositeEnv
  type : Types.CompositeType
  fields : List String
  deriving Repr

structure CallInputView where
  name : String
  fields : List (String × Ty)
  deriving Repr

/-- Recursive ledger value descriptions. Scalar leaves use the existing typed
scalar surface. Maps retain their key type and recursively describe values. -/
inductive LedgerValueType where
  | scalar (ty : Ty)
  | map (keyTy : Ty) (value : LedgerValueType)
  | set (keyTy : Ty)
  /-- The fixed QualifiedShieldedCoinInfo Set key supported by the native
  `insertShieldedCoinSet` operation. General record-keyed Sets stay unsupported. -/
  | shieldedCoinSet (environment : Types.CompositeEnv) (type : Types.CompositeType)
  | composite (environment : Types.CompositeEnv) (type : Types.CompositeType)
  | list (environment : Types.CompositeEnv) (type : Types.CompositeType)
  | counter
  | merkleTree (depth : Nat) (historic : Bool)
  deriving Repr, BEq, DecidableEq

def LedgerValueType.merkleTreeConfig? : LedgerValueType → Option (Nat × Bool)
  | .merkleTree depth historic => some (depth, historic)
  | _ => none

/-- A typed dynamic key in a nested ledger path. -/
inductive PathKey where
  | mk (ty : Ty) (value : Expr ty)
  deriving Repr

def PathKey.ty : PathKey → Ty
  | .mk ty _ => ty

/-- Resolve a complete source key path against a recursive map schema. -/
def LedgerValueType.resolvePath (schema : LedgerValueType) : List PathKey →
    Except String LedgerValueType
  | [] => pure schema
  | .mk keyTy _ :: rest => do
    match schema with
    | .scalar _ => throw "nested map path continues through a scalar value"
    | .counter => throw "nested map path continues through a Counter value"
    | .map expected value =>
      unless keyTy == expected do throw "nested map key type mismatch"
      value.resolvePath rest
    | .set _ => throw "set members have no readable value"
    | .shieldedCoinSet .. => throw "qualified shielded coin Set members have no readable value"
    | .composite .. => throw "nested map path continues through a composite value"
    | .list .. => throw "nested map path continues through a list value"
    | .merkleTree .. => throw "nested map path continues through a MerkleTree value"

def LedgerValueType.merkleTreePathConfig (schema : LedgerValueType)
    (keys : List PathKey) : Except String (Nat × Bool) := do
  if keys.isEmpty then throw "nested MerkleTree path requires at least one map key"
  if keys.length > 12 then throw "nested MerkleTree path supports at most 12 map keys"
  let selected ← schema.resolvePath keys
  let some config := selected.merkleTreeConfig?
    | throw "nested path does not select a MerkleTree"
  let (depth, _) := config
  unless 2 ≤ depth && depth ≤ 32 do throw "MerkleTree depth must be between 2 and 32"
  pure config

def LedgerValueType.counterPath (schema : LedgerValueType) (keys : List PathKey) :
    Except String Unit := do
  if keys.length > 14 then throw "counter path exceeds the native insertion depth"
  if keys.isEmpty then
    unless schema == .counter do throw "counter operation requires a Counter value"
  else
    let .counter ← schema.resolvePath keys
      | throw "counter path must select a Counter value"

def LedgerValueType.collectionKey? : LedgerValueType → Option Ty
  | .map ty _ | .set ty => some ty
  | _ => none

/-- The final key addresses an entry in the selected parent map or set. -/
def LedgerValueType.entryParent (schema : LedgerValueType) (keys : List PathKey) :
    Except String LedgerValueType := do
  let some key := keys.getLast? | throw "map or set operation requires a key"
  if keys.length > 14 then throw "map or set path exceeds the native insertion depth"
  let parent ← schema.resolvePath (keys.take (keys.length - 1))
  let some expected := parent.collectionKey? | throw "entry path must select a map or set"
  unless key.ty == expected do throw "map or set key type mismatch"
  pure parent

/-- A removal path names the complete entry path in a map or set. -/
def LedgerValueType.removalPath (schema : LedgerValueType) (keys : List PathKey) :
    Except String Unit := do
  discard (schema.entryParent keys)

private def checkedNativeRecord (environment : Types.CompositeEnv)
    (type : Types.CompositeType) : Except String (Types.CheckedLayout Types.defaultLimits) := do
  let checked ← (Types.checkedLayout Types.defaultLimits environment type).mapError (·.message)
  unless checked.expandedLeaves > 0 && checked.value.nativeFieldOnly do
    throw "ledger composite values must contain one or more Native fields only"
  pure checked

def LedgerValueType.recordFields (environment : Types.CompositeEnv)
    (type : Types.CompositeType) : Except String (List (String × Ty)) := do
  match checkedNativeRecord environment type with
  | .ok checked => do
    let rec names : Nat → Types.Layout → Except String (List String)
      | 0, _ => throw "composite leaf name traversal exhausted checked fuel"
      | fuel + 1, layout => do
        match layout with
        | .scalar .nativeField => pure ["value"]
        | .tuple items =>
          pure (← items.zipIdx.mapM fun (item, index) => do
            pure ((← names fuel item).map fun name => s!"{index}_{name}")).flatten
        | .structure _ fields =>
          pure (← fields.mapM fun (field, item) => do
            pure ((← names fuel item).map fun name =>
              if name == "value" then field else s!"{field}_{name}")).flatten
        | .vector length element =>
          pure (← (List.range length).mapM fun index => do
            pure ((← names fuel element).map fun name => s!"{index}_{name}")).flatten
        | _ => throw "ledger composite values must contain Native fields only"
    let result ← names (checked.layoutNodes + 1) checked.value
    unless result.length == checked.expandedLeaves do throw "composite leaf name count mismatch"
    unless result.eraseDups.length == result.length do throw "duplicate composite leaf name"
    pure (result.map fun name => (name, .native))
  | .error nativeError => do
    let .structure id := type | throw nativeError
    let some declaration := environment.structures.find? (·.id == id)
      | throw nativeError
    unless !declaration.fields.isEmpty do throw "ledger records must contain at least one field"
    let fields ← declaration.fields.mapM fun field => do
      match field.type with
      | .scalar .native => pure (field.name, Ty.native)
      | .scalar (.bytes 32) => pure (field.name, Ty.bytes 32)
      | .scalar .jubjubPoint => pure (field.name, Ty.jubjubPoint)
      | _ => throw "mixed ledger records must be flat Native, Bytes32, or JubjubPoint fields"
    let referencedByOtherStruct := environment.structures.any fun existing =>
      existing.id != id && existing.fields.any fun field =>
        field.type.referencedIds.contains id
    let referencedByEnum := environment.enumerations.any fun enumeration =>
      enumeration.variants.any fun variant => variant.fields.any fun field =>
        field.type.referencedIds.contains id
    unless !referencedByOtherStruct && !referencedByEnum do
      throw "mixed ledger records cannot be nested in other composite declarations"
    -- Normalize only the requested leaf record for the existing bounded layout checker.
    let structures := environment.structures.map fun existing =>
      if existing.id == id then
        {existing with fields := existing.fields.map fun field =>
          match field.type with
          | .scalar (.bytes 32) | .scalar .jubjubPoint =>
            {field with type := .scalar .native}
          | _ => field}
      else existing
    let normalized : Types.CompositeEnv := {environment with structures}
    let checked ← (Types.checkedLayout Types.defaultLimits normalized type).mapError (·.message)
    unless checked.value.nativeFieldOnly && checked.expandedLeaves == fields.length do
      throw "mixed ledger record layout does not match its flat field declaration"
    pure fields

def LedgerValueType.shieldedCoinRecordFields (environment : Types.CompositeEnv)
    (type : Types.CompositeType) : Except String (List (String × Ty)) := do
  let .structure id := type | throw "shielded coin map value must be a named flat record"
  let some declaration := environment.structures.find? (·.id == id)
    | throw "shielded coin map record declaration is missing"
  let shape := declaration.fields.map fun field => (field.name, field.type)
  unless shape == [
      ("nonce", .scalar (.bytes 32)), ("color", .scalar (.bytes 32)),
      ("value", .scalar (.uint (2 ^ 128 - 1))),
      ("mtIndex", .scalar (.uint (2 ^ 64 - 1)))] do
    throw "shielded coin map record must be flat nonce: Bytes32, color: Bytes32, value: UInt128, mtIndex: UInt64"
  pure [("nonce", .bytes 32), ("color", .bytes 32),
    ("value", .uint (2 ^ 128 - 1)), ("mtIndex", .uint (2 ^ 64 - 1))]

/-- Describe a List element as its typed scalar value or as the fields of its
existing checked record representation. -/
def LedgerValueType.listElementFields (environment : Types.CompositeEnv)
    (type : Types.CompositeType) : Except String (List (String × Ty)) :=
  match type with
  | .scalar ty => pure [("value", ty)]
  | _ => LedgerValueType.recordFields environment type

def LedgerValueType.listPath (schema : LedgerValueType) (keys : List PathKey) :
    Except String (Types.CompositeEnv × Types.CompositeType × List (String × Ty)) := do
  if keys.length > 13 then throw "list path exceeds the native insertion depth"
  let .list environment type ← schema.resolvePath keys
    | throw "list operation path must select a List value"
  let fields ← LedgerValueType.listElementFields environment type
  pure (environment, type, fields)

def LedgerValueType.compositeSchema (schema : LedgerValueType) :
    Except String (Types.CompositeEnv × Types.CompositeType × List (String × Ty)) :=
  match schema with
  | .composite environment type => do
    let fields ← LedgerValueType.recordFields environment type
    pure (environment, type, fields)
  | _ => .error "nested map value is not a composite record"

structure Circuit where
  name : String
  inputs : List Input := []
  outputs : List Output := []
  constraints : List (Expr .bool) := []
  span : SourceSpan := {}
  /-- Private provenance labels for declared provider/private-state input fixtures.
  These strengthen visibility and never authorize disclosure. -/
  privateOrigins : List (String × PrivateOriginKind) := []
  deriving Repr

inductive StateKind where
  | cell (valueTy : Ty)
  | map (keyTy valueTy : Ty)
  | tree (value : LedgerValueType)
  | merkleTree (depth : Nat)
  | historicMerkleTree (depth : Nat)
  /-- UTF-8 FAB state metadata. This value is host/deployment-only and never a circuit Ty. -/
  | opaqueString
  deriving Repr, BEq, DecidableEq

def StateKind.pathSchema : StateKind → Option LedgerValueType
  | .map keyTy valueTy => some (.map keyTy (.scalar valueTy))
  | .tree schema => some schema
  | _ => none

def StateKind.validateCollectionPath (kind : StateKind) (keys : List PathKey) :
    Except String Unit := do
  if keys.length >= 16 then throw "collection path exceeds the native index limit"
  let some schema := kind.pathSchema | throw "path must select a Map or Set"
  unless (← schema.resolvePath keys).collectionKey?.isSome do
    throw "path must select a Map or Set"

def StateKind.merkleTreeDepth? : StateKind → Option Nat
  | .merkleTree depth | .historicMerkleTree depth => some depth
  | _ => none

def StateKind.isHistoricMerkleTree : StateKind → Bool
  | .historicMerkleTree _ => true
  | _ => false

structure StateDecl where
  name : String
  kind : StateKind
  sealed : Bool := false
  span : SourceSpan := {}
  deriving Repr

inductive ConstructorType where
  | scalar (ty : Ty)
  | opaqueString
  deriving Repr, BEq, DecidableEq

structure ConstructorParameter where
  name : String
  type : ConstructorType
  deriving Repr

inductive ConstructorValue where
  | scalar {ty : Ty} (value : Expr ty)
  | opaqueStringParameter (name : String)
  | opaqueStringLiteral (value : String)
  deriving Repr

structure ConstructorInitializer where
  state : String
  type : ConstructorType
  value : ConstructorValue
  deriving Repr

/-- Fresh-deployment inputs and cell values. This metadata never enters a circuit. -/
structure Constructor where
  parameters : List ConstructorParameter := []
  initializers : List ConstructorInitializer := []
  deriving Repr

inductive EventFieldType where
  | bytes (length : Nat)
  | flag
  | amount

def EventFieldType.width : EventFieldType → Nat
  | .bytes length => length
  | .flag => 1
  | .amount => 16

/-- Standard log layouts for the pinned Ledger 9 event schema. -/
inductive EventKind where
  | shieldedSpend
  | shieldedReceive
  | shieldedMint
  | shieldedBurn
  | unshieldedSpend
  | unshieldedReceive
  | unshieldedMint
  | unshieldedBurn
  | paused
  | unpaused
  | misc
  deriving Repr, BEq

def EventKind.tag : EventKind → Nat
  | .shieldedSpend => 0
  | .shieldedReceive => 1
  | .shieldedMint => 2
  | .shieldedBurn => 3
  | .unshieldedSpend => 4
  | .unshieldedReceive => 5
  | .unshieldedMint => 6
  | .unshieldedBurn => 7
  | .paused => 8
  | .unpaused => 9
  | .misc => 10

private def eventAddressFields : List (String × EventFieldType) :=
  [("isUser", .flag), ("userKey", .bytes 32), ("contractAddress", .bytes 32)]

private def eventTokenFields : List (String × EventFieldType) :=
  [("domainSep", .bytes 32), ("tokenType", .bytes 32), ("amount", .amount)]

def EventKind.fields : EventKind → List (String × EventFieldType)
  | .shieldedSpend => [("nullifier", .bytes 32)]
  | .shieldedReceive =>
    [("commitment", .bytes 32), ("hasCiphertext", .flag), ("ciphertext", .bytes 512),
      ("hasContractAddress", .flag), ("contractAddress", .bytes 32)]
  | .shieldedMint =>
    [("commitment", .bytes 32), ("domainSep", .bytes 32), ("hasAmount", .flag), ("amount", .amount)]
  | .shieldedBurn => [("nullifier", .bytes 32), ("hasAmount", .flag), ("amount", .amount)]
  | .unshieldedSpend | .unshieldedReceive => eventAddressFields ++ eventTokenFields
  | .unshieldedMint => eventTokenFields
  | .unshieldedBurn => eventAddressFields ++ [("tokenType", .bytes 32), ("amount", .amount)]
  | .paused | .unpaused => []
  | .misc => [("name", .bytes 32), ("payload", .bytes 256)]

def EventKind.payloadSize (kind : EventKind) : Nat :=
  kind.fields.foldl (fun size field => size + field.2.width) 0

structure CallerBindings where
  present : String
  isContract : String
  contractAddress : String
  userAddress : String
  deriving Repr

def CallerBindings.types (names : CallerBindings) : List (String × Ty) :=
  [(names.present, .bool), (names.isContract, .bool),
    (names.contractAddress, .bytes 32), (names.userAddress, .bytes 32)]
/-- Query the starting ledger balance of either native token namespace. -/
inductive BalanceQuery where
  | exact
  | compare (less : Bool) (limit : Expr (.uint balanceMaximum))
  deriving Repr

def BalanceQuery.resultType : BalanceQuery → Ty
  | .exact => .uint balanceMaximum
  | .compare .. => .bool

inductive LedgerFieldExpr where
  | mk (ty : Ty) (value : Expr ty)
  deriving Repr

def LedgerFieldExpr.ty : LedgerFieldExpr → Ty
  | .mk ty _ => ty

/-- State effects are ordered transaction instructions, not circuit nodes.
A read binds a typed name for later guards/writes. Outputs are bound explicitly
by an entrypoint. The backend must bind these values into the accepted transcript. -/
inductive Effect where
  | readCell (state destination : String) (ty : Ty)
  | readMap (state destination : String) (keyTy valueTy : Ty) (key : Expr keyTy)
  | readMember (state destination : String) (keyTy valueTy : Ty) (key : Expr keyTy)
  | readContractAddress (destination : String)
  | require (condition : Expr .bool)
  | writeCell (state : String) (ty : Ty) (value : Expr ty)
  | writeMap (state : String) (keyTy valueTy : Ty) (key : Expr keyTy) (value : Expr valueTy)
  | requireAbsent (state : String) (keyTy : Ty) (key : Expr keyTy)
  /-- Direct-IR/direct-contract-DSL claim using the ledger's fixed contract-call
  transcript slot. The commitment is the native transient input/output hash.
  Helper and witness-statement authoring APIs do not expose this effect yet. -/
  | claimContractCall (address entryPointHash : Expr (.bytes 32)) (commitment : Expr .native)
  | mintShielded (domain : Expr (.bytes 32)) (amount : Expr (.uint (2 ^ 64 - 1)))
  /-- Receive an already-funded shielded coin into a typed Bytes32-keyed tree map.
  The backend computes its commitment from the disclosed coin data and the
  contract address read from ledger context. -/
  | receiveShieldedToMap (state : String) (nonce color : Expr (.bytes 32))
      (amount : Expr (.uint (2 ^ 128 - 1))) (selfAddress : Expr (.bytes 32))
  /-- Insert a coin whose self-recipient commitment is already booked in the
  current transaction into a qualified-record Set. The runtime gets its index
  from the transaction context. -/
  | insertShieldedCoinSet (state : String) (nonce color : Expr (.bytes 32))
      (amount : Expr (.uint (2 ^ 128 - 1))) (selfAddress : Expr (.bytes 32))
  /-- Store a coin whose self-recipient commitment is already booked in the
  current transaction. The runtime obtains its Ledger index from context. -/
  | writeShieldedCoinCell (state : String) (nonce color : Expr (.bytes 32))
      (amount : Expr (.uint (2 ^ 128 - 1))) (selfAddress : Expr (.bytes 32))
  /-- Spend the exact coin record read from a Bytes32-keyed tree Map entry.
  The backend derives native nullifier and output-commitment claims. -/
  | spendShieldedFromMap (state : String) (nonce color : Expr (.bytes 32))
      (amount : Expr (.uint (2 ^ 128 - 1))) (recipient selfAddress : Expr (.bytes 32))
  /-- Split a recorded shielded coin between one recipient output and one
  contract-owned change output. The frontend removes the old map key and then
  reuses receiveShieldedToMap to qualify and insert the change coin. -/
  | sendShieldedFromMap (state : String) (nonce color : Expr (.bytes 32))
      (inputAmount sendAmount : Expr (.uint (2 ^ 128 - 1)))
      (recipient selfAddress : Expr (.bytes 32))
  /-- Receive an exact shielded coin transiently at this contract and forward
  its full value to another contract. The backend derives receive, nullifier
  and contract-recipient spend commitments. This operation does not store a
  relay coin or create change. -/
  | relayShieldedImmediate (nonce color : Expr (.bytes 32))
      (amount : Expr (.uint (2 ^ 128 - 1))) (recipient selfAddress : Expr (.bytes 32))
  | mintUnshielded (domain : Expr (.bytes 32)) (amount : Expr (.uint (2 ^ 64 - 1)))
  | incUnshieldedInputs (color : Expr (.bytes 32)) (amount : Expr (.uint balanceMaximum))
      (isUnshielded : Expr .bool)
  | incUnshieldedOutputs (color : Expr (.bytes 32)) (amount : Expr (.uint balanceMaximum))
      (isUnshielded : Expr .bool)
  | claimUnshieldedCoinSpend (color : Expr (.bytes 32)) (amount : Expr (.uint balanceMaximum))
      (isUnshielded isContract : Expr .bool) (recipient : Expr (.bytes 32))
  | requireContractCaller (address : Expr (.bytes 32))
  /-- Candidate boundary for the native guaranteed and fallible transcripts. -/
  | checkpoint
  | readCaller (destinations : CallerBindings)
  | readTokenBalance (destination : String) (color : Expr (.bytes 32))
      (isUnshielded : Expr .bool) (query : BalanceQuery)
  /-- Compare the native ledger transcript's block time, in seconds, with a
  public cutoff. `before` selects the strict `<` direction; false selects `>`. -/
  | blockTimeCompare (destination : String) (before : Bool)
      (deadline : Expr (.uint (2 ^ 64 - 1)))
  | emitEvent (kind : EventKind) (payload : Expr (.bytes kind.payloadSize))
  | readPath (state destination : String) (keys : List PathKey) (valueTy : Ty)
  | memberPath (state destination : String) (keys : List PathKey)
  | mapIsEmpty (state destination : String) (keys : List PathKey)
  | mapSize (state destination : String) (keys : List PathKey)
  | counterRead (state destination : String) (keys : List PathKey)
  | counterLessThan (state destination : String) (keys : List PathKey)
      (threshold : Expr (.uint (2 ^ 64 - 1)))
  | counterAdjust (state : String) (keys : List PathKey) (subtract : Bool)
      (amount : Expr (.uint (2 ^ 32 - 1)))
  | counterReset (state : String) (keys : List PathKey)
  | insertPath (state : String) (keys : List PathKey) (valueTy : Ty) (value : Expr valueTy)
  | writePath (state : String) (keys : List PathKey) (valueTy : Ty) (value : Expr valueTy)
  | readCompositePath (state destination : String) (keys : List PathKey)
      (type : Types.CompositeType) (destinations : List (String × Ty))
  | writeCompositePath (state : String) (keys : List PathKey)
      (type : Types.CompositeType) (values : List LedgerFieldExpr)
  | listLength (state destination : String) (keys : List PathKey)
  | listHead (state destination : String) (keys : List PathKey)
      (type : Types.CompositeType) (destinations : List (String × Ty))
  | listPushFront (state : String) (keys : List PathKey)
      (type : Types.CompositeType) (values : List LedgerFieldExpr)
  | listPopFront (state : String) (keys : List PathKey)
  | listReset (state : String) (keys : List PathKey)
  | merkleTreeIsFull (state destination : String)
  | merkleTreeCheckRoot (state : String) (expected : Expr .native) (destination : String)
  | merkleTreeInsertHash (state : String) (hash : Expr (.bytes 32))
  | merkleTreeInsertHashIndex (state : String) (hash : Expr (.bytes 32))
      (index : Expr (.uint (2 ^ 64 - 1)))
  | merkleTreeReset (state : String)
  | merkleTreeResetHistory (state : String)
  | merkleTreeIsFullAt (state : String) (keys : List PathKey) (destination : String)
  | merkleTreeCheckRootAt (state : String) (keys : List PathKey)
      (expected : Expr .native) (destination : String)
  | merkleTreeInsertHashAt (state : String) (keys : List PathKey) (hash : Expr (.bytes 32))
  | merkleTreeInsertHashIndexAt (state : String) (keys : List PathKey)
      (hash : Expr (.bytes 32)) (index : Expr (.uint (2 ^ 64 - 1)))
  | merkleTreeResetAt (state : String) (keys : List PathKey) (depth : Nat) (historic : Bool)
      (emptyHistory : Bool := false)
  | merkleTreeResetHistoryAt (state : String) (keys : List PathKey)
  | emptyMapPath (state : String) (keys : List PathKey)
  | setInsert (state : String) (keys : List PathKey)
  | removePath (state : String) (keys : List PathKey)
  deriving Repr

structure Entrypoint where
  name : String
  circuit : Circuit
  /-- Private Native circuit inputs promoted to the ledger call argument ABI.
  Names retain their order in the call's aligned input value. -/
  callInputs : List String := []
  /-- Logical arguments expanded to Native slots in the call header. -/
  callInputViews : List CallInputView := []
  effects : List Effect := []
  /-- Proof-bound public values returned with the entrypoint call. -/
  returns : List Output := []
  /-- Logical composite returns grouped from their canonical Native fields. -/
  returnViews : List ReturnView := []
  span : SourceSpan := {}
  effectSpans : List SourceSpan := []
  /-- Optional activity guards aligned with `effects`. An empty list preserves
  legacy behavior. -/
  effectGuards : List (Option (Expr .bool)) := []
  deriving Repr

/-- Selected in the explicit call order, independently of transcript declaration order. -/
def Entrypoint.callArguments (entry : Entrypoint) : List Input :=
  entry.callInputs.filterMap fun name => entry.circuit.inputs.find? (·.name == name)

def Entrypoint.effectGuardAt (entry : Entrypoint) (index : Nat) : Option (Expr .bool) :=
  (entry.effectGuards[index]?).getD none

structure Contract where
  name : String
  state : List StateDecl := []
  constructor : Option Constructor := none
  entrypoints : List Entrypoint := []
  span : SourceSpan := {}
  deriving Repr

private def constructorTypeOfValue : ConstructorValue → ConstructorType
  | .scalar (ty := ty) _ => .scalar ty
  | .opaqueStringParameter _ | .opaqueStringLiteral _ => .opaqueString


structure Capabilities where
  nativeModulus : Nat := Field.modulus
  nativeArithmetic : Bool := true
  equality : Bool := true
  select : Bool := true
  typedBoolean : Bool := false
  poseidon2 : Bool := false
  persistentHash32 : Bool := false
  persistentHashVector32 : Bool := false
  persistentHashNative : Bool := false
  sha512 : Bool := false
  keccak256 : Bool := false
  bytes32Conversions : Bool := false
  hashToCurve : Bool := false
  jubjub : Bool := false
  foreignValues : Bool := false
  foreignArithmetic : Bool := false
  foreignByteConversions : Bool := false
  stateCells : Bool := false
  stateMaps : Bool := false
  deriving Repr

/-- Pure expression capabilities implemented by the pinned native crypto path. -/
def Capabilities.crypto : Capabilities := {
  typedBoolean := true, poseidon2 := true, persistentHash32 := true, persistentHashVector32 := true,
  persistentHashNative := true, sha512 := true, keccak256 := true,
  bytes32Conversions := true, hashToCurve := true, jubjub := true, foreignValues := true,
  foreignArithmetic := true, foreignByteConversions := true
}

/-- Source checking includes the currently implemented ledger state features. -/
def Capabilities.source : Capabilities := {
  typedBoolean := true, poseidon2 := true, persistentHash32 := true, persistentHashVector32 := true,
  persistentHashNative := true, sha512 := true, keccak256 := true,
  bytes32Conversions := true, hashToCurve := true, jubjub := true, foreignValues := true,
  foreignArithmetic := true, foreignByteConversions := true,
  stateCells := true, stateMaps := true
}

structure Diagnostic where
  span : SourceSpan
  message : String
  deriving Repr

abbrev TypeEnv := List (String × Ty)

def Ty.validate (caps : Capabilities) (ty : Ty) : Except String Unit := do
  match ty with
  | .bytes length =>
    unless length ≤ maxBytesLength do
      throw s!"byte string length exceeds the maximum of {maxBytesLength}"
  | .opaqueBytes => pure ()
  | .jubjubScalar | .jubjubPoint =>
    unless caps.jubjub do throw "target lacks qualified Jubjub support"
  | .foreign _ =>
    unless caps.foreignValues do throw "target lacks typed foreign-curve value support"
  | .native | .bool => ScalarPolicy.validate ty.scalarKind
  | .uint maximum =>
    ScalarPolicy.validate ty.scalarKind
    unless maximum < caps.nativeModulus do throw "unsigned type exceeds native representation"

def Expr.validate (caps : Capabilities) (env : TypeEnv) : Expr ty → Except String Unit
  | .native value =>
    if value < caps.nativeModulus then pure () else .error "noncanonical native constant"
  | .boolAnd left right | .boolOr left right | .boolXor left right => do
    unless caps.typedBoolean do throw "target lacks typed Boolean support"
    left.validate caps env
    right.validate caps env
  | .uint maximum value => do
    (Ty.uint maximum).validate caps
    if value ≤ maximum then pure () else .error "unsigned constant exceeds its type"
  | .bool _ => .ok ()
  | .bytesField (length := length) value chunkIndex => do
    value.validate caps env
    unless chunkIndex < (length + 30) / 31 do
      if length == 32 then throw "Bytes32 field chunk index is out of range"
      else throw "byte field chunk index is out of range"
  | .bytesAt (length := length) value index => do
    value.validate caps env
    unless index < length do
      if length == 32 then throw "Bytes32 byte index is out of range"
      else throw "byte index is out of range"
  | .opaqueBytesProjection value => value.validate caps env
  | .bytesLiteral length values => do
    unless length ≤ maxBytesLength do
      throw s!"byte string length exceeds the maximum of {maxBytesLength}"
    unless values.length == length && values.all (· ≤ 255) do
      throw "byte literal must contain exactly its declared number of byte values"
  | .reverseBytes (length := length) value => do
    unless caps.bytes32Conversions do throw "target lacks qualified fixed-byte support"
    unless length ≤ maxBytesLength do
      throw s!"byte string length exceeds the maximum of {maxBytesLength}"
    value.validate caps env
  | .sliceBytes (length := length) value start stop => do
    unless caps.bytes32Conversions do throw "target lacks qualified fixed-byte support"
    unless length ≤ maxBytesLength do
      throw s!"byte string length exceeds the maximum of {maxBytesLength}"
    unless start ≤ stop && stop ≤ length do throw "byte slice bounds are out of range"
    value.validate caps env
  | .concatBytes (leftLength := leftLength) (rightLength := rightLength) left right => do
    unless caps.bytes32Conversions do throw "target lacks qualified fixed-byte support"
    unless leftLength + rightLength ≤ maxBytesLength do
      throw s!"byte string length exceeds the maximum of {maxBytesLength}"
    left.validate caps env
    right.validate caps env
  | .sha256 (length := length) value => do
    unless caps.persistentHash32 do throw "target lacks qualified SHA-256 support"
    (Ty.bytes length).validate caps
    value.validate caps env
  | .sha512 (length := length) value => do
    unless caps.sha512 do throw "target lacks qualified SHA-512 support"
    unless length ≤ maxBytesLength do
      throw s!"byte string length exceeds the maximum of {maxBytesLength}"
    value.validate caps env
  | .keccak256 (length := length) value => do
    unless caps.keccak256 do throw "target lacks qualified Keccak-256 support"
    unless length ≤ maxBytesLength do
      throw s!"byte string length exceeds the maximum of {maxBytesLength}"
    value.validate caps env
  | .keccak256Secp256k1Point value => do
    unless caps.keccak256 do throw "target lacks qualified Keccak-256 support"
    value.validate caps env
  | .reverseBytes32 value => do
    unless caps.bytes32Conversions do throw "target lacks qualified Bytes32 conversion support"
    value.validate caps env
  | .persistentHash32 value => do
    unless caps.persistentHash32 do throw "target lacks qualified Bytes32 persistent-hash support"
    value.validate caps env
  | .bytes32Literal values => do
    unless values.length == 32 && values.all (· ≤ 255) do
      throw "Bytes32 literal must contain exactly 32 byte values"
  | .persistentHashVector32 values => do
    unless caps.persistentHashVector32 do throw "target lacks qualified Bytes32-vector persistent-hash support"
    unless values.length ≥ 1 && values.length ≤ 32 do
      throw "persistent hash vector must contain 1 to 32 Bytes32 values"
    for value in values do value.validate caps env
  | .persistentHashNative value => do
    unless caps.persistentHashNative do throw "target lacks qualified Native persistent-hash support"
    value.validate caps env
  | .persistentHashNativeVector values => do
    unless caps.persistentHashNative do throw "target lacks qualified Native persistent-hash support"
    unless values.length ≥ 1 && values.length ≤ 32 do
      throw "Native persistent-hash vector must contain 1 to 32 fields"
    for value in values do value.validate caps env
  | .toBytes32 (source := source) value => do
    unless caps.bytes32Conversions do throw "target lacks qualified Bytes32 conversion support"
    unless source == .native || source == .jubjubScalar || source == .jubjubPoint do
      throw "toBytes32 supports only Native, JubjubScalar and JubjubPoint"
    value.validate caps env
  | .fromBytes32 (target := target) value => do
    unless caps.bytes32Conversions do throw "target lacks qualified Bytes32 conversion support"
    unless target == .native || target == .jubjubScalar || target == .jubjubPoint do
      throw "fromBytes32 supports only Native, JubjubScalar and JubjubPoint"
    value.validate caps env
  | .fromBytes (target := target) (length := length) value => do
    unless target == .native || target == .jubjubScalar do
      throw "fromBytes supports only Native and JubjubScalar"
    unless length ≤ maxBytesLength do
      throw s!"byte string length exceeds the maximum of {maxBytesLength}"
    target.validate caps
    value.validate caps env
  | .jubjubScalarFromNative value => do
    unless caps.jubjub do throw "target lacks qualified Jubjub support"
    value.validate caps env
  | .jubjubScalarToNative value => do
    unless caps.jubjub do throw "target lacks qualified Jubjub support"
    value.validate caps env
  | .jubjubMulGenerator scalar => do
    unless caps.jubjub do throw "target lacks qualified Jubjub support"
    scalar.validate caps env
  | .jubjubMul point scalar => do
    unless caps.jubjub do throw "target lacks qualified Jubjub support"
    point.validate caps env
    scalar.validate caps env
  | .jubjubAdd left right => do
    unless caps.jubjub do throw "target lacks qualified Jubjub support"
    left.validate caps env
    right.validate caps env
  | .jubjubNeg point => do
    unless caps.jubjub do throw "target lacks qualified Jubjub support"
    point.validate caps env
  | .jubjubCoordinate point index => do
    unless caps.jubjub do throw "target lacks qualified Jubjub support"
    point.validate caps env
    unless index < 2 do throw "Jubjub coordinate index must be 0 or 1"
  | .jubjubFromCoordinates x y => do
    unless caps.jubjub do throw "target lacks qualified Jubjub support"
    x.validate caps env
    y.validate caps env
  | .hashToCurve values => do
    unless caps.hashToCurve do throw "target lacks qualified hash_to_curve support"
    unless caps.jubjub do throw "target lacks qualified Jubjub support"
    unless values.length ≤ Types.defaultLimits.maxVectorLength do
      throw s!"hash_to_curve input count exceeds the maximum of {Types.defaultLimits.maxVectorLength}"
    for value in values do value.validate caps env
  | .foreignBase curve value => do
    unless caps.foreignValues do throw "target lacks typed foreign-curve value support"
    unless value < curve.baseModulus do throw "foreign base-field constant is not canonical"
  | .foreignScalar curve value => do
    unless caps.foreignValues do throw "target lacks typed foreign-curve value support"
    unless value < curve.scalarModulus do throw "foreign scalar constant is not canonical"
  | .foreignPoint curve value => do
    unless caps.foreignValues do throw "target lacks typed foreign-curve value support"
    discard (Foreign.encodePoint curve value)
  | .foreignEncodedField (kind := kind) value index => do
    unless caps.foreignValues do throw "target lacks typed foreign-curve value support"
    value.validate caps env
    unless index < kind.encodedFieldCount do throw "foreign encoded-field index is out of range"
  | .foreignUnary operation value => do
    unless caps.foreignArithmetic do throw "target lacks foreign-curve arithmetic support"
    (Ty.foreign operation.inputKind).validate caps
    (Ty.foreign operation.outputKind).validate caps
    value.validate caps env
  | .foreignBinary operation left right => do
    unless caps.foreignArithmetic do throw "target lacks foreign-curve arithmetic support"
    (Ty.foreign operation.leftKind).validate caps
    (Ty.foreign operation.rightKind).validate caps
    (Ty.foreign operation.outputKind).validate caps
    left.validate caps env
    right.validate caps env
  | .foreignToBytes value => do
    unless caps.foreignByteConversions do throw "target lacks foreign-curve byte conversion support"
    value.validate caps env
  | .foreignFromBytes (kind := kind) (length := length) value => do
    unless caps.foreignByteConversions do throw "target lacks foreign-curve byte conversion support"
    (Ty.foreign kind).validate caps
    unless length ≤ maxBytesLength do
      throw s!"byte string length exceeds the maximum of {maxBytesLength}"
    if kind.byteLength == 33 then
      unless length == 33 do throw "foreign point decoding requires 33 bytes"
    value.validate caps env
  | .ref name => do
    ty.validate caps
    match env.lookup name with
    | none => .error s!"unknown reference '{name}'"
    | some found => if found == ty then pure () else .error s!"type mismatch for '{name}'"
  | .add a b | .mul a b | .sub a b => do
    if !caps.nativeArithmetic then throw "target lacks native arithmetic"
    a.validate caps env
    b.validate caps env
  | .uadd a b | .usub a b | .umul a b => do
    ty.validate caps
    if !caps.nativeArithmetic then throw "target lacks native arithmetic"
    a.validate caps env
    b.validate caps env
  | .inv value => do
    match ty with
    | .native =>
      unless caps.nativeArithmetic do throw "target lacks Native inverse support"
    | .jubjubScalar =>
      unless caps.jubjub do throw "target lacks Jubjub scalar inverse support"
    | _ => throw "inverse supports only Native and JubjubScalar"
    value.validate caps env
  | .cast target (source := source) value => do
    if target.isBytes || source.isBytes || target.isOpaqueBytes || source.isOpaqueBytes then
      throw "byte strings do not support scalar casts"
    if target.isJubjub || source.isJubjub || target.isForeign || source.isForeign then
      throw "curve values do not support scalar casts"
    target.validate caps
    value.validate caps env
  | .letE (source := source) name value body => do
    value.validate caps env
    body.validate caps ((name, source) :: env)
  | .assertE condition body => do
    condition.validate caps env
    body.validate caps env
  | .copyValue value | .disclose _ value => value.validate caps env
  | .eq (ty := operandTy) a b => do
    if operandTy.isBytes || operandTy.isOpaqueBytes then
      throw "byte string equality is not supported by this source surface"
    if !caps.equality then throw "target lacks equality"
    a.validate caps env
    b.validate caps env
  | .select c a b => do
    if ty.isJubjub || ty.isOpaqueBytes || (ty.isBytes && !caps.bytes32Conversions) then
      throw "byte string and Jubjub selection is not supported by this source surface"
    if ty.isForeign && !caps.foreignValues then
      throw "target lacks typed foreign-curve value support"
    if !caps.select then throw "target lacks conditional selection"
    c.validate caps env
    a.validate caps env
    b.validate caps env
  | .poseidon2 domain a b => do
    if domain >= caps.nativeModulus then throw "noncanonical Poseidon domain"
    if !caps.poseidon2 then throw "target lacks qualified Poseidon support"
    a.validate caps env
    b.validate caps env
  | .transientHash values => do
    unless caps.poseidon2 do throw "target lacks qualified Poseidon support"
    unless values.length ≤ Types.defaultLimits.maxVectorLength do
      throw s!"transient_hash input count exceeds the maximum of {Types.defaultLimits.maxVectorLength}"
    for value in values do value.validate caps env

def PathKey.validate (caps : Capabilities) (env : TypeEnv) : PathKey → Except String Unit
  | .mk _ value => value.validate caps env

private def validateLedgerMapKeyType (keyTy : Ty) : Except String Unit := do
  match keyTy with
  | .bytes length => unless length == 32 do throw "only Bytes32 is supported as a ledger map key"
  | _ => pure ()

def LedgerValueType.validate (caps : Capabilities) : LedgerValueType → Except String Unit
  | .counter => pure ()
  | .merkleTree depth _ => do
    unless 2 ≤ depth && depth ≤ 32 do
      throw "MerkleTree depth must be between 2 and 32"
  | .scalar ty => ty.validate caps
  | .map keyTy value => do
    validateLedgerMapKeyType keyTy
    keyTy.validate caps
    value.validate caps
  | .set keyTy => do
    validateLedgerMapKeyType keyTy
    keyTy.validate caps
  | .shieldedCoinSet environment type => do
    let fields ← LedgerValueType.shieldedCoinRecordFields environment type
    for (_, ty) in fields do
      ty.validate caps
  | .composite environment type => do
    let fields ← match LedgerValueType.recordFields environment type with
      | .ok fields => pure fields
      | .error _ => LedgerValueType.shieldedCoinRecordFields environment type
    for (_, ty) in fields do
      ty.validate caps
    pure ()
  | .list environment type => do
    let fields ← LedgerValueType.listElementFields environment type
    for (_, ty) in fields do
      ty.validate caps
    pure ()

private def resolveTreeState (decls : List StateDecl) (state : String)
    (keys : List PathKey) : Except String LedgerValueType := do
  let some decl := decls.find? (·.name == state) | throw s!"unknown tree state '{state}'"
  let .tree schema := decl.kind | throw s!"state '{state}' is not a recursive map"
  if keys.isEmpty then throw "nested map path must contain at least one key"
  if keys.length > 14 then throw "nested map path exceeds the native insertion depth"
  schema.resolvePath keys

private def resolveMerkleTreePath (decls : List StateDecl) (state : String)
    (keys : List PathKey) : Except String (Nat × Bool) := do
  let some decl := decls.find? (·.name == state) | throw s!"unknown MerkleTree state '{state}'"
  let .tree schema := decl.kind | throw s!"state '{state}' is not a recursive tree"
  schema.merkleTreePathConfig keys

private def resolveListState (decls : List StateDecl) (state : String)
    (keys : List PathKey) :
    Except String (Types.CompositeEnv × Types.CompositeType × List (String × Ty)) := do
  let some decl := decls.find? (·.name == state) | throw s!"unknown list state '{state}'"
  let .tree schema := decl.kind | throw s!"state '{state}' is not a recursive tree"
  schema.listPath keys

private def validateCounterEffect (decls : List StateDecl) (state : String)
    (keys : List PathKey) : Except String Unit := do
  let some decl := decls.find? (·.name == state) | throw s!"unknown tree state '{state}'"
  let .tree schema := decl.kind | throw s!"state '{state}' is not a recursive tree"
  schema.counterPath keys

def uniqueNames (names : List String) : Bool := names.eraseDups.length == names.length

private def Constructor.validate (caps : Capabilities) (states : List StateDecl)
    (constructor : Constructor) (span : SourceSpan) : Except Diagnostic Unit := do
  let parameterNames := constructor.parameters.map (·.name)
  unless uniqueNames parameterNames do
    throw {span, message := "duplicate constructor parameter"}
  for parameter in constructor.parameters do
    unless Types.validFieldName parameter.name do
      throw {span, message := s!"invalid constructor parameter '{parameter.name}'"}
    match parameter.type with
    | .scalar ty =>
      match ty.validate caps with
      | .error message => throw {span, message}
      | .ok _ => pure ()
    | .opaqueString => pure ()
  let scalarEnvironment := constructor.parameters.filterMap fun parameter =>
    match parameter.type with
    | .scalar ty => some (parameter.name, ty)
    | .opaqueString => none
  let initializerNames := constructor.initializers.map (·.state)
  unless uniqueNames initializerNames do
    throw {span, message := "duplicate constructor state initializer"}
  for initializer in constructor.initializers do
    unless Types.validFieldName initializer.state do
      throw {span, message := s!"invalid constructor state name '{initializer.state}'"}
    let some state := states.find? (·.name == initializer.state)
      | throw {span, message := s!"constructor initializes unknown state '{initializer.state}'"}
    unless constructorTypeOfValue initializer.value == initializer.type do
      throw {span, message := s!"constructor initializer type mismatch for '{initializer.state}'"}
    match state.kind, initializer.type, initializer.value with
    | .cell stateTy, .scalar initializerTy, .scalar (ty := expressionTy) value => do
      unless stateTy == initializerTy && stateTy == expressionTy do
        throw {span := state.span, message := s!"constructor scalar type mismatch for '{initializer.state}'"}
      match value.validate caps scalarEnvironment with
      | .error message => throw {span, message}
      | .ok _ => pure ()
    | .opaqueString, .opaqueString, .opaqueStringLiteral _ => pure ()
    | .opaqueString, .opaqueString, .opaqueStringParameter parameterName =>
      unless constructor.parameters.any (fun parameter =>
        parameter.name == parameterName && parameter.type == .opaqueString) do
        throw {span, message := s!"unknown OpaqueString constructor parameter '{parameterName}'"}
    | _, _, _ =>
      throw {span := state.span, message := s!"constructor initializer does not match cell '{initializer.state}'"}
  for state in states do
    if state.sealed && !(initializerNames.contains state.name) then
      throw {span := state.span, message := s!"sealed state '{state.name}' must be initialized by the constructor"}

private def Effect.writeTarget : Effect → Option String
  | .writeCell state _ _ | .writeMap state .. | .insertPath state .. | .writePath state .. |
    .receiveShieldedToMap state .. | .insertShieldedCoinSet state .. |
    .sendShieldedFromMap state .. |
    .writeShieldedCoinCell state .. |
    .writeCompositePath state .. | .counterAdjust state .. | .counterReset state .. |
    .listPushFront state .. | .listPopFront state .. | .listReset state .. |
    .emptyMapPath state .. | .setInsert state .. | .removePath state .. |
    .merkleTreeInsertHash state .. | .merkleTreeInsertHashIndex state .. |
    .merkleTreeReset state | .merkleTreeResetHistory state |
    .merkleTreeInsertHashAt state .. | .merkleTreeInsertHashIndexAt state .. |
    .merkleTreeResetAt state .. | .merkleTreeResetHistoryAt state .. => some state
  | _ => none

/-- Preserve first constraint diagnostic and source span in list order. -/
def validateConstraints (caps : Capabilities) (env : TypeEnv) (span : SourceSpan) :
    List (Expr .bool) → Except Diagnostic Unit
  | [] => .ok ()
  | condition :: rest =>
    match condition.validate caps env with
    | .error message => .error {span, message}
    | .ok _ => validateConstraints caps env span rest

def Circuit.validate (caps : Capabilities) (c : Circuit) : Except Diagnostic Unit := do
  if !uniqueNames (c.inputs.map (·.name)) then
    throw {span := c.span, message := "duplicate circuit input"}
  let env := c.inputs.map fun i => (i.name, i.ty)
  for input in c.inputs do
    match input.ty.validate caps with
    | .error message => throw {span := input.span, message}
    | .ok _ => pure ()
  if !uniqueNames (c.inputs.flatMap Input.nativeIdentifiers) then
    throw {span := c.span, message := "input names collide after native byte expansion"}
  let projections := c.inputs.flatMap Input.publicProjectionIdentifiers
  if !uniqueNames projections || projections.any (fun name =>
      c.inputs.any (fun input => input.name == name)) then
    throw {span := c.span, message := "input names collide with generated typed curve public projections"}
  if !uniqueNames (c.outputs.map (·.name)) then
    throw {span := c.span, message := "duplicate circuit output"}
  validateConstraints caps env c.span c.constraints
  for output in c.outputs do
    match output.ty.validate caps with
    | .error message => throw {span := output.span, message}
    | .ok _ => pure ()
    if (env.lookup output.name).isSome then
      throw {span := output.span, message := s!"output '{output.name}' shadows a circuit input"}
    match output.value.validate caps env with
    | .error message => throw {span := output.span, message}
    | .ok _ => pure ()

private def requireState (decls : List StateDecl) (name : String) (kind : StateKind) : Except String Unit :=
  match decls.find? (·.name == name) with
  | none => .error s!"unknown state '{name}'"
  | some {kind := .opaqueString, ..} =>
    .error "OpaqueString constructor metadata cannot be read or written by entrypoints"
  | some decl => if decl.kind == kind then pure () else .error s!"state type mismatch for '{name}'"

private def validateCallArguments (inputs : List Input) (names : List String)
    (span : SourceSpan) : Except Diagnostic Unit := do
  unless uniqueNames names do
    throw {span := span, message := "duplicate native call argument"}
  if names.length > 256 then
    throw {span := span, message := "too many native call arguments"}
  let mut fieldCount := 0
  for name in names do
    let some input := inputs.find? (·.name == name)
      | throw {span := span, message := s!"unknown circuit call argument '{name}'"}
    unless input.visibility == .private do
      throw {span := input.span, message := s!"call argument '{name}' must be a private circuit input"}
    fieldCount := fieldCount + input.ty.nativeCallFieldCount
  if fieldCount > 256 then
    throw {span := span, message := "too many native call argument fields"}

/-- Validate state names, typed reads, guards and writes in execution order. -/
def Entrypoint.validate (caps : Capabilities) (decls : List StateDecl) (e : Entrypoint) : Except Diagnostic Unit := do
  for decl in decls do
    if let .map keyTy _ := decl.kind then
      match validateLedgerMapKeyType keyTy with
      | .error message => throw {span := decl.span, message}
      | .ok _ => pure ()
    match decl.kind with
    | .tree schema =>
      match schema.validate caps with
      | .error message => throw {span := decl.span, message}
      | .ok _ => pure ()
    | _ => pure ()
    let types := match decl.kind with
      | .cell ty => [ty]
      | .map keyTy valueTy => [keyTy, valueTy]
      | .tree _ => []
      | .merkleTree _ | .historicMerkleTree _ => []
      | .opaqueString => []
    for ty in types do
      match ty.validate caps with
      | .error message => throw {span := decl.span, message}
      | .ok _ => pure ()
  e.circuit.validate caps
  validateCallArguments e.circuit.inputs e.callInputs e.span
  unless e.callInputViews.length ≤ 256 && uniqueNames (e.callInputViews.map (·.name)) do
    throw {span := e.span, message := "invalid logical call argument list"}
  let mut groupedInputs := []
  for view in e.callInputViews do
    let fields := view.fields.map Prod.fst
    unless !view.name.isEmpty && uniqueNames fields && !fields.any groupedInputs.contains do
      throw {span := e.span, message := "invalid aggregate call argument fields"}
    if let some first := fields.head? then
      unless ((e.callInputs.dropWhile (· != first)).take fields.length) == fields do
        throw {span := e.span, message := "aggregate call argument fields must remain adjacent in layout order"}
    unless fields.all (fun name => e.circuit.inputs.any (fun input => input.name == name && input.ty == .native)) do
      throw {span := e.span, message := "aggregate call argument fields must use Native"}
    groupedInputs := groupedInputs ++ fields
  unless e.effectGuards.isEmpty || e.effectGuards.length == e.effects.length do
    throw {span := e.span, message := "effect guard metadata length mismatch"}
  -- Typing permits private operands. Mandatory disclosure analysis decides
  -- whether their value/control dependence is authorized at a public sink.
  let mut env := e.circuit.inputs.map fun i => (i.name, i.ty)
  for output in e.circuit.outputs do
    if (e.circuit.inputs.find? (·.name == output.name)).isSome then
      throw {span := output.span, message := s!"output '{output.name}' shadows a circuit input"}
    env := env ++ [(output.name, output.ty)]
  for (effect, index) in e.effects.zipIdx do
    let span := e.effectSpans[index]?.getD e.span
    if let some stateName := effect.writeTarget then
      if let some state := decls.find? (·.name == stateName) then
        if state.sealed then
          throw {span, message := s!"sealed state '{stateName}' cannot be written by an entrypoint"}
    if let some condition := e.effectGuardAt index then
      match condition.validate caps env with
      | .error message => throw {span, message}
      | .ok _ => pure ()
      match effect with
      | .readCell .. | .readMap .. | .readMember .. | .writeCell .. | .writeMap .. |
          .claimContractCall .. | .requireContractCaller .. | .checkpoint | .emitEvent .. |
          .readContractAddress .. | .readTokenBalance .. | .mintShielded .. | .mintUnshielded .. |
          .incUnshieldedInputs .. | .incUnshieldedOutputs .. | .claimUnshieldedCoinSpend .. |
          .readPath .. | .memberPath .. | .mapIsEmpty .. | .mapSize .. |
          .insertPath .. | .writePath .. | .emptyMapPath .. | .setInsert .. |
          .readCompositePath .. | .writeCompositePath .. | .counterRead .. | .counterLessThan .. |
          .counterAdjust .. | .counterReset .. | .listLength .. | .listHead .. |
          .listPushFront .. | .listPopFront .. | .listReset .. | .removePath .. |
          .readCaller .. | .blockTimeCompare .. | .merkleTreeIsFull .. | .merkleTreeCheckRoot .. |
          .merkleTreeInsertHash .. | .merkleTreeInsertHashIndex .. | .merkleTreeReset .. |
          .merkleTreeResetHistory .. | .merkleTreeIsFullAt .. |
          .merkleTreeCheckRootAt .. | .merkleTreeInsertHashAt .. |
          .merkleTreeInsertHashIndexAt .. | .merkleTreeResetAt .. |
          .merkleTreeResetHistoryAt .. => pure ()
      | .require _ => pure ()
      | _ =>
        throw {span := span, message := "native guards are supported only on ledger reads, writes, and require effects"}
    let result : Except String (List (String × Ty)) := do
      match effect with
      | .readCell state destination ty =>
        if !caps.stateCells then throw "target lacks state cells"
        requireState decls state (.cell ty)
        pure [(destination, ty)]
      | .readMap state destination keyTy valueTy key =>
        if !caps.stateMaps then throw "target lacks state maps"
        requireState decls state (.map keyTy valueTy)
        key.validate caps env
        pure [(destination, valueTy)]
      | .readMember state destination keyTy valueTy key =>
        if !caps.stateMaps then throw "target lacks state maps"
        requireState decls state (.map keyTy valueTy)
        key.validate caps env
        pure [(destination, .bool)]
      | .readContractAddress destination => do
        (.bytes 32 : Ty).validate caps
        pure [(destination, .bytes 32)]
      | .require condition =>
        condition.validate caps env
        pure []
      | .claimContractCall address entryPointHash commitment => do
        address.validate caps env
        entryPointHash.validate caps env
        commitment.validate caps env
        pure []
      | .mintShielded domain amount | .mintUnshielded domain amount => do
        domain.validate caps env
        amount.validate caps env
        pure []
      | .receiveShieldedToMap state nonce color amount selfAddress => do
        if !caps.stateMaps then throw "target lacks state maps"
        let some declaration := decls.find? (·.name == state)
          | throw s!"unknown shielded coin map '{state}'"
        let .tree (.map keyTy (.composite compositeEnv recordType)) := declaration.kind
          | throw s!"shielded coin receive requires a root Bytes32-keyed tree Map '{state}'"
        unless keyTy == .bytes 32 do
          throw "shielded coin map key must be Bytes32"
        discard (LedgerValueType.shieldedCoinRecordFields compositeEnv recordType)
        nonce.validate caps env
        color.validate caps env
        amount.validate caps env
        selfAddress.validate caps env
        pure []
      | .writeShieldedCoinCell state nonce color amount selfAddress => do
        if !caps.stateCells then throw "target lacks state cells"
        let some declaration := decls.find? (·.name == state)
          | throw s!"unknown qualified shielded coin Cell '{state}'"
        let .tree (.composite compositeEnv recordType) := declaration.kind
          | throw s!"qualified shielded coin write requires a root composite Cell '{state}'"
        discard (LedgerValueType.shieldedCoinRecordFields compositeEnv recordType)
        nonce.validate caps env
        color.validate caps env
        amount.validate caps env
        selfAddress.validate caps env
        pure []
      | .insertShieldedCoinSet state nonce color amount selfAddress => do
        if !caps.stateMaps then throw "target lacks state maps"
        let some declaration := decls.find? (·.name == state)
          | throw s!"unknown qualified shielded coin Set '{state}'"
        let .tree (.shieldedCoinSet compositeEnv recordType) := declaration.kind
          | throw s!"qualified shielded coin insertion requires a root record Set '{state}'"
        discard (LedgerValueType.shieldedCoinRecordFields compositeEnv recordType)
        nonce.validate caps env
        color.validate caps env
        amount.validate caps env
        selfAddress.validate caps env
        pure []
      | .spendShieldedFromMap state nonce color amount recipient selfAddress => do
        if !caps.stateMaps then throw "target lacks state maps"
        let some declaration := decls.find? (·.name == state)
          | throw s!"unknown shielded coin map '{state}'"
        let .tree (.map keyTy (.composite compositeEnv recordType)) := declaration.kind
          | throw s!"shielded coin spend requires a root Bytes32-keyed tree Map '{state}'"
        unless keyTy == .bytes 32 do
          throw "shielded coin map key must be Bytes32"
        discard (LedgerValueType.shieldedCoinRecordFields compositeEnv recordType)
        nonce.validate caps env
        color.validate caps env
        amount.validate caps env
        recipient.validate caps env
        selfAddress.validate caps env
        pure []
      | .sendShieldedFromMap state nonce color inputAmount sendAmount recipient selfAddress => do
        if !caps.stateMaps then throw "target lacks state maps"
        let some declaration := decls.find? (·.name == state)
          | throw s!"unknown shielded coin map '{state}'"
        let .tree (.map keyTy (.composite compositeEnv recordType)) := declaration.kind
          | throw s!"shielded coin send requires a root Bytes32-keyed tree Map '{state}'"
        unless keyTy == .bytes 32 do
          throw "shielded coin map key must be Bytes32"
        discard (LedgerValueType.shieldedCoinRecordFields compositeEnv recordType)
        nonce.validate caps env
        color.validate caps env
        inputAmount.validate caps env
        sendAmount.validate caps env
        recipient.validate caps env
        selfAddress.validate caps env
        pure []
      | .relayShieldedImmediate nonce color amount recipient selfAddress => do
        nonce.validate caps env
        color.validate caps env
        amount.validate caps env
        recipient.validate caps env
        selfAddress.validate caps env
        pure []
      | .incUnshieldedInputs color amount isUnshielded
      | .incUnshieldedOutputs color amount isUnshielded => do
        color.validate caps env
        amount.validate caps env
        isUnshielded.validate caps env
        pure []
      | .claimUnshieldedCoinSpend color amount isUnshielded isContract recipient => do
        color.validate caps env
        amount.validate caps env
        isUnshielded.validate caps env
        isContract.validate caps env
        recipient.validate caps env
        pure []
      | .requireContractCaller address => do
        address.validate caps env
        pure []
      | .checkpoint => pure []
      | .readCaller destinations => do
        (.bytes 32 : Ty).validate caps
        pure destinations.types
      | .readTokenBalance destination color isUnshielded query => do
        color.validate caps env
        isUnshielded.validate caps env
        match query with
        | .exact => pure ()
        | .compare _ limit => limit.validate caps env
        pure [(destination, query.resultType)]
      | .blockTimeCompare destination _ deadline => do
        deadline.validate caps env
        pure [(destination, .bool)]
      | .emitEvent _ payload =>
        payload.validate caps env
        pure []
      | .writeCell state ty value =>
        if !caps.stateCells then throw "target lacks state cells"
        requireState decls state (.cell ty)
        value.validate caps env
        pure []
      | .writeMap state keyTy valueTy key value =>
        if !caps.stateMaps then throw "target lacks state maps"
        requireState decls state (.map keyTy valueTy)
        key.validate caps env
        value.validate caps env
        pure []
      | .requireAbsent state keyTy key =>
        if !caps.stateMaps then throw "target lacks state maps"
        match decls.find? (·.name == state) with
        | some {kind := .map found _, ..} =>
          if found != keyTy then throw s!"state key type mismatch for '{state}'"
        | _ => throw s!"unknown map state '{state}'"
        key.validate caps env
        pure []
      | .readPath state destination keys valueTy => do
        if !caps.stateMaps then throw "target lacks state maps"
        for key in keys do key.validate caps env
        let .scalar found ← resolveTreeState decls state keys
          | throw "nested map read must select a scalar value"
        unless found == valueTy do throw "nested map read value type mismatch"
        valueTy.validate caps
        pure [(destination, valueTy)]
      | .memberPath state destination keys => do
        if !caps.stateMaps then throw "target lacks state maps"
        for key in keys do key.validate caps env
        let some decl := decls.find? (·.name == state)
          | throw s!"unknown map or set state '{state}'"
        let some schema := decl.kind.pathSchema
          | throw s!"state '{state}' is not a map or set"
        discard (schema.entryParent keys)
        pure [(destination, .bool)]
      | .mapIsEmpty state destination keys => do
        if !caps.stateMaps then throw "target lacks state maps"
        for key in keys do key.validate caps env
        let some decl := decls.find? (·.name == state)
          | throw s!"unknown map or set state '{state}'"
        decl.kind.validateCollectionPath keys
        pure [(destination, .bool)]
      | .mapSize state destination keys => do
        if !caps.stateMaps then throw "target lacks state maps"
        for key in keys do key.validate caps env
        let some decl := decls.find? (·.name == state)
          | throw s!"unknown map or set state '{state}'"
        decl.kind.validateCollectionPath keys
        pure [(destination, .uint (2 ^ 64 - 1))]
      | .counterRead state destination keys => do
        if !caps.stateMaps then throw "target lacks state maps"
        for key in keys do key.validate caps env
        validateCounterEffect decls state keys
        pure [(destination, .uint (2 ^ 64 - 1))]
      | .counterLessThan state destination keys threshold => do
        if !caps.stateMaps then throw "target lacks state maps"
        for key in keys do key.validate caps env
        validateCounterEffect decls state keys
        threshold.validate caps env
        pure [(destination, .bool)]
      | .counterAdjust state keys _ amount => do
        if !caps.stateMaps then throw "target lacks state maps"
        for key in keys do key.validate caps env
        validateCounterEffect decls state keys
        amount.validate caps env
        pure []
      | .counterReset state keys => do
        if !caps.stateMaps then throw "target lacks state maps"
        for key in keys do key.validate caps env
        validateCounterEffect decls state keys
        pure []
      | .listLength state destination keys => do
        if !caps.stateMaps then throw "target lacks state maps"
        for key in keys do key.validate caps env
        discard (resolveListState decls state keys)
        pure [(destination, .uint (2 ^ 64 - 1))]
      | .listHead state _ keys type destinations => do
        if !caps.stateMaps then throw "target lacks state maps"
        for key in keys do key.validate caps env
        let (_, foundType, fields) ← resolveListState decls state keys
        unless foundType == type do throw "list head record type mismatch"
        unless fields.map Prod.snd == destinations.map Prod.snd do
          throw "list head destination count mismatch"
        unless uniqueNames (destinations.map Prod.fst) do throw "duplicate list head destination"
        for (_, ty) in fields do ty.validate caps
        pure destinations
      | .listPushFront state keys type values => do
        if !caps.stateMaps then throw "target lacks state maps"
        for key in keys do key.validate caps env
        let (_, foundType, fields) ← resolveListState decls state keys
        unless foundType == type do throw "list push record type mismatch"
        unless fields.map Prod.snd == values.map LedgerFieldExpr.ty do
          throw "list push record field type mismatch"
        for (_, ty) in fields do ty.validate caps
        for value in values do
          match value with
          | .mk ty expression => do
            ty.validate caps
            expression.validate caps env
        pure []
      | .listPopFront state keys | .listReset state keys => do
        if !caps.stateMaps then throw "target lacks state maps"
        for key in keys do key.validate caps env
        discard (resolveListState decls state keys)
        pure []
      | .merkleTreeIsFull state destination => do
        let some declaration := decls.find? (·.name == state)
          | throw s!"unknown MerkleTree state '{state}'"
        let some depth := declaration.kind.merkleTreeDepth?
          | throw s!"unknown MerkleTree state '{state}'"
        unless 2 ≤ depth && depth ≤ 32 do
          throw "MerkleTree depth must be between 2 and 32"
        pure [(destination, .bool)]
      | .merkleTreeCheckRoot state expected destination => do
        let some declaration := decls.find? (·.name == state)
          | throw s!"unknown MerkleTree state '{state}'"
        let some depth := declaration.kind.merkleTreeDepth?
          | throw s!"unknown MerkleTree state '{state}'"
        unless 2 ≤ depth && depth ≤ 32 do
          throw "MerkleTree depth must be between 2 and 32"
        expected.validate caps env
        pure [(destination, .bool)]
      | .merkleTreeInsertHash state hash => do
        let some declaration := decls.find? (·.name == state)
          | throw s!"unknown MerkleTree state '{state}'"
        let some depth := declaration.kind.merkleTreeDepth?
          | throw s!"unknown MerkleTree state '{state}'"
        unless 2 ≤ depth && depth ≤ 32 do
          throw "MerkleTree depth must be between 2 and 32"
        hash.validate caps env
        pure []
      | .merkleTreeInsertHashIndex state hash index => do
        let some declaration := decls.find? (·.name == state)
          | throw s!"unknown MerkleTree state '{state}'"
        let some depth := declaration.kind.merkleTreeDepth?
          | throw s!"unknown MerkleTree state '{state}'"
        unless 2 ≤ depth && depth ≤ 32 do
          throw "MerkleTree depth must be between 2 and 32"
        hash.validate caps env
        index.validate caps env
        pure []
      | .merkleTreeReset state => do
        let some declaration := decls.find? (·.name == state)
          | throw s!"unknown MerkleTree state '{state}'"
        let some depth := declaration.kind.merkleTreeDepth?
          | throw s!"unknown MerkleTree state '{state}'"
        unless 2 ≤ depth && depth ≤ 32 do
          throw "MerkleTree depth must be between 2 and 32"
        pure []
      | .merkleTreeResetHistory state => do
        let some declaration := decls.find? (·.name == state)
          | throw s!"unknown MerkleTree state '{state}'"
        let .historicMerkleTree depth := declaration.kind
          | throw "resetHistory requires a HistoricMerkleTree"
        unless 2 ≤ depth && depth ≤ 32 do
          throw "HistoricMerkleTree depth must be between 2 and 32"
        pure []
      | .merkleTreeIsFullAt state keys destination => do
        if !caps.stateMaps then throw "target lacks state maps"
        for key in keys do key.validate caps env
        discard (resolveMerkleTreePath decls state keys)
        pure [(destination, .bool)]
      | .merkleTreeCheckRootAt state keys expected destination => do
        if !caps.stateMaps then throw "target lacks state maps"
        for key in keys do key.validate caps env
        discard (resolveMerkleTreePath decls state keys)
        expected.validate caps env
        pure [(destination, .bool)]
      | .merkleTreeInsertHashAt state keys hash => do
        if !caps.stateMaps then throw "target lacks state maps"
        for key in keys do key.validate caps env
        discard (resolveMerkleTreePath decls state keys)
        hash.validate caps env
        pure []
      | .merkleTreeInsertHashIndexAt state keys hash index => do
        if !caps.stateMaps then throw "target lacks state maps"
        for key in keys do key.validate caps env
        discard (resolveMerkleTreePath decls state keys)
        hash.validate caps env
        index.validate caps env
        pure []
      | .merkleTreeResetAt state keys depth historic emptyHistory => do
        if !caps.stateMaps then throw "target lacks state maps"
        if emptyHistory && keys.isEmpty then
          throw "empty-history reset requires a nested HistoricMerkleTree"
        for key in keys do key.validate caps env
        let (foundDepth, foundHistoric) ← resolveMerkleTreePath decls state keys
        unless depth == foundDepth && historic == foundHistoric do
          throw "nested MerkleTree reset schema mismatch"
        if emptyHistory && !historic then
          throw "empty-history reset requires a HistoricMerkleTree"
        pure []
      | .merkleTreeResetHistoryAt state keys => do
        if !caps.stateMaps then throw "target lacks state maps"
        for key in keys do key.validate caps env
        let (_, historic) ← resolveMerkleTreePath decls state keys
        unless historic do throw "resetHistory requires a HistoricMerkleTree"
        pure []
      | .insertPath state keys valueTy value
      | .writePath state keys valueTy value => do
        if !caps.stateMaps then throw "target lacks state maps"
        for key in keys do key.validate caps env
        let .scalar found ← resolveTreeState decls state keys
          | throw "nested scalar write must select a scalar value"
        unless found == valueTy do throw "nested scalar write value type mismatch"
        value.validate caps env
        pure []
      | .readCompositePath state _ keys type destinations => do
        if !caps.stateMaps then throw "target lacks state maps"
        for key in keys do key.validate caps env
        let .composite compositeEnv foundType ← resolveTreeState decls state keys
          | throw "nested composite read must select a composite value"
        unless foundType == type do throw "nested composite read type mismatch"
        let fields ← match LedgerValueType.recordFields compositeEnv type with
          | .ok fields => pure fields
          | .error _ => LedgerValueType.shieldedCoinRecordFields compositeEnv type
        unless fields.map Prod.snd == destinations.map Prod.snd do
          throw "nested composite read destination count mismatch"
        unless uniqueNames (destinations.map Prod.fst) do throw "duplicate nested composite read destination"
        for (_, ty) in fields do ty.validate caps
        pure destinations
      | .writeCompositePath state keys type values => do
        if !caps.stateMaps then throw "target lacks state maps"
        for key in keys do key.validate caps env
        let .composite compositeEnv foundType ← resolveTreeState decls state keys
          | throw "nested composite write must select a composite value"
        unless foundType == type do throw "nested composite write type mismatch"
        let fields ← LedgerValueType.recordFields compositeEnv type
        unless fields.map Prod.snd == values.map LedgerFieldExpr.ty do
          throw "nested composite write field type mismatch"
        for (_, ty) in fields do ty.validate caps
        for value in values do
          match value with
          | .mk ty expression => do
            ty.validate caps
            expression.validate caps env
        pure []
      | .emptyMapPath state keys => do
        if !caps.stateMaps then throw "target lacks state maps"
        for key in keys do key.validate caps env
        let some decl := decls.find? (·.name == state)
          | throw s!"unknown map or set state '{state}'"
        decl.kind.validateCollectionPath keys
        pure []
      | .setInsert state keys => do
        if !caps.stateMaps then throw "target lacks state maps"
        for key in keys do key.validate caps env
        let some decl := decls.find? (·.name == state)
          | throw s!"unknown set state '{state}'"
        let some schema := decl.kind.pathSchema
          | throw s!"state '{state}' is not a set"
        let .set _ ← schema.entryParent keys
          | throw "set insertion path must select a Set"
        pure []
      | .removePath state keys => do
        if !caps.stateMaps then throw "target lacks state maps"
        for key in keys do key.validate caps env
        let some decl := decls.find? (·.name == state)
          | throw s!"unknown map or set state '{state}'"
        let some schema := decl.kind.pathSchema
          | throw s!"state '{state}' is not a map or set"
        schema.removalPath keys
        pure []
    match result with
    | .error message => throw {span := e.span, message}
    | .ok bindings =>
      for (name, ty) in bindings do
        if (env.lookup name).isSome then
          throw {span := e.span, message := s!"state read shadows '{name}'"}
        env := env ++ [(name, ty)]
  unless uniqueNames (e.returns.map (·.name)) do
    throw {span := e.span, message := "duplicate entrypoint return label"}
  unless (e.returns.map Output.nativeReturnFieldCount).sum ≤ maxEntrypointReturnFields do
    throw {span := e.span, message := "entrypoint return field limit exceeded"}
  for output in e.returns do
    if (env.lookup output.name).isSome then
      throw {span := output.span, message := s!"entrypoint return '{output.name}' shadows a source binding"}
    match output.ty.validate caps with
    | .error message => throw {span := output.span, message}
    | .ok _ => pure ()
    match output.value.validate caps env with
    | .error message => throw {span := output.span, message}
    | .ok _ => pure ()
  unless uniqueNames (e.returnViews.map (·.name)) do
    throw {span := e.span, message := "duplicate logical entrypoint return name"}
  unless e.returnViews.length ≤ maxEntrypointReturnFields do
    throw {span := e.span, message := "entrypoint logical return view limit exceeded"}
  let mut groupedFields : List String := []
  for view in e.returnViews do
    unless !view.name.isEmpty do
      throw {span := e.span, message := "logical entrypoint return name must not be empty"}
    if (e.returns.any (·.name == view.name)) then
      throw {span := e.span, message := s!"logical return '{view.name}' conflicts with a physical return field"}
    unless uniqueNames view.fields do
      throw {span := e.span, message := s!"duplicate physical field in logical return '{view.name}'"}
    let checked ← match Types.checkedLayout {} view.environment view.type e.span with
      | .ok checked => pure checked
      | .error diagnostic => throw {span := e.span, message := diagnostic.message}
    unless checked.expandedLeaves ≤ maxEntrypointReturnFields do
      throw {span := e.span, message := "entrypoint return field limit exceeded"}
    unless view.fields.length == checked.expandedLeaves do
      throw {span := e.span, message := s!"logical return '{view.name}' field count does not match its type"}
    let fieldsInEntryOrder := e.returns.filterMap fun output =>
      if view.fields.contains output.name then some output.name else none
    unless fieldsInEntryOrder == view.fields do
      throw {span := e.span, message := s!"logical return '{view.name}' fields do not follow physical return order"}
    for fieldName in view.fields do
      if groupedFields.contains fieldName then
        throw {span := e.span, message := s!"physical return field '{fieldName}' belongs to multiple logical returns"}
      let some output := e.returns.find? (·.name == fieldName)
        | throw {span := e.span, message := s!"logical return '{view.name}' references missing physical field '{fieldName}'"}
      unless output.ty == .native do
        throw {span := output.span, message := s!"logical return field '{fieldName}' must use Native"}
      groupedFields := groupedFields ++ [fieldName]

def Contract.validate (caps : Capabilities) (c : Contract) : Except Diagnostic Unit := do
  if !uniqueNames (c.state.map (·.name)) then
    throw {span := c.span, message := "duplicate state declaration"}
  if !uniqueNames (c.entrypoints.map (·.name)) then
    throw {span := c.span, message := "duplicate contract entrypoint"}
  for decl in c.state do
    if decl.sealed && !(match decl.kind with | .cell _ | .opaqueString => true | _ => false) then
      throw {span := decl.span, message := "only cells can be sealed"}
    if decl.kind == .opaqueString && !decl.sealed then
      throw {span := decl.span, message := "OpaqueString state must be sealed"}
    if let .map keyTy _ := decl.kind then
      match validateLedgerMapKeyType keyTy with
      | .error message => throw {span := decl.span, message}
      | .ok _ => pure ()
    let types := match decl.kind with
      | .cell ty => [ty]
      | .map keyTy valueTy => [keyTy, valueTy]
      | .tree _ => []
      | .merkleTree _ | .historicMerkleTree _ => []
      | .opaqueString => []
    for ty in types do
      match ty.validate caps with
      | .error message => throw {span := decl.span, message}
      | .ok _ => pure ()
    if let .tree schema := decl.kind then
      match schema.validate caps with
      | .error message => throw {span := decl.span, message}
      | .ok _ => pure ()
    if let some depth := decl.kind.merkleTreeDepth? then
      unless 2 ≤ depth && depth ≤ 32 do
        throw {span := decl.span, message := "MerkleTree depth must be between 2 and 32"}
  match c.constructor with
  | some constructor => Constructor.validate caps c.state constructor c.span
  | none =>
    if c.state.any (·.sealed) then
      throw {span := c.span, message := "sealed states require a constructor"}
  for entry in c.entrypoints do entry.validate caps c.state

end Noctium
