import Noctium.Types.Composite
import Noctium.Disclosure

namespace Noctium.Types

def aggregateWireLimit : Nat := 1048576
def aggregateWireMagic : String := "noctium:aggregate:value:v1:"

private def encodedNatSize (value : Nat) : Nat := (toString value).utf8ByteSize + 1
private def encodedTextSize (value : String) : Nat :=
  (toString value.length).utf8ByteSize + 1 + value.utf8ByteSize

private def typeEncodingSize : CompositeType → Nat
  | .unit => 1
  | .scalar .native | .scalar .bool => 2
  | .scalar .jubjubScalar | .scalar .jubjubPoint => 3
  | .scalar (.foreign kind) => 2 + (toString kind.sourceName.length).utf8ByteSize +
      1 + kind.sourceName.utf8ByteSize
  | .scalar (.uint maximum) => 2 + encodedNatSize maximum
  | .scalar (.bytes length) => 2 + encodedNatSize length
  | .scalar .opaqueBytes => 2
  | .scalar .opaqueString => 2
  | .tuple items => 3 + encodedNatSize items.length + (items.map typeEncodingSize).sum
  | .structure id | .enumeration id => 1 + encodedTextSize id
  | .vector length element => 1 + encodedNatSize length + typeEncodingSize element
  | .bytes length => 1 + encodedNatSize length

private def fieldEncodingSize (field : Field) : Nat :=
  1 + encodedTextSize field.name + typeEncodingSize field.type

private def references (environment : CompositeEnv) (id : DeclId) : List DeclId :=
  match environment.structures.find? (·.id == id), environment.enumerations.find? (·.id == id) with
  | some declaration, _ => declaration.fields.flatMap (fun field => field.type.referencedIds)
  | none, some declaration => declaration.variants.flatMap fun variant =>
      variant.fields.flatMap (fun field => field.type.referencedIds)
  | _, _ => []

private def closure (environment : CompositeEnv) : Nat → List DeclId → List DeclId → List DeclId
  | 0, _, seen => seen
  | _, [], seen => seen
  | fuel + 1, id :: rest, seen =>
    let next := (references environment id).eraseDups.filter fun reference =>
      !seen.contains reference && reference != id && !rest.contains reference
    closure environment fuel (rest ++ next) (id :: seen)

/-- Size preflight avoids allocating a large canonical fingerprint first. -/
def fingerprintSize (environment : CompositeEnv) (type : CompositeType) : Nat := Id.run do
  let reachable := closure environment (environment.structures.length + environment.enumerations.length + 1)
    type.referencedIds.eraseDups []
  let structures := environment.structures.filter (fun declaration => reachable.contains declaration.id)
  let enumerations := environment.enumerations.filter (fun declaration => reachable.contains declaration.id)
  let structureSize := (structures.map fun declaration =>
    1 + encodedTextSize declaration.id + encodedNatSize declaration.fields.length +
      (declaration.fields.map fieldEncodingSize).sum).sum
  let enumSize := (enumerations.map fun declaration =>
    1 + encodedTextSize declaration.id + encodedNatSize declaration.variants.length +
      (declaration.variants.map fun variant =>
        1 + encodedTextSize variant.name + encodedNatSize variant.fields.length +
          (variant.fields.map fieldEncodingSize).sum).sum).sum
  return "NoctiumCompositeTypeV1;".utf8ByteSize + typeEncodingSize type +
    "NoctiumCompositeLayoutV1;".utf8ByteSize + encodedNatSize structures.length + structureSize +
    encodedNatSize enumerations.length + enumSize

/-- A layout count certificate alone is not a proof of logical type identity.
This carrier also records that the layout came from the checked type compiler. -/
structure CompiledType where
  environment : CompositeEnv
  type : CompositeType
  limits : Limits
  checked : CheckedLayout limits
  checkedByCompiler : checkedLayout limits environment type = .ok checked
  fingerprint : String
  fingerprintMatches : fingerprint = type.fingerprint environment

def compileType (environment : CompositeEnv) (type : CompositeType)
    (limits : Limits := defaultLimits) : Except LayoutDiagnostic CompiledType := do
  match result : checkedLayout limits environment type with
  | .error diagnostic => throw diagnostic
  | .ok checked =>
    let size := fingerprintSize environment type
    if size > aggregateWireLimit || aggregateWireMagic.utf8ByteSize + 8 + size + 32 * checked.expandedLeaves > aggregateWireLimit then
      throw {span := {}, message := "aggregate canonical transport exceeds byte limit"}
    let fingerprint := type.fingerprint environment
    unless fingerprint.utf8ByteSize == size do
      throw {span := {}, message := "aggregate fingerprint size preflight mismatch"}
    pure {
      environment := environment
      type := type
      limits := limits
      checked := checked
      checkedByCompiler := result
      fingerprint := fingerprint
      fingerprintMatches := rfl
    }

inductive AggregateValue where
  | unit
  | scalar (type : Ty) (number : Nat)
  | jubjubPoint (x y : Nat)
  | foreignPoint (curve : Foreign.Curve) (point : Foreign.Point)
  | tuple (items : List AggregateValue)
  | structure (id : DeclId) (fields : List (String × AggregateValue))
  | enumeration (id variant : String) (fields : List (String × AggregateValue))
  | vector (items : List AggregateValue)
  | bytes (values : List Nat)
  deriving Repr, BEq

private def leafType : ScalarLeaf → Except String Ty
  | .nativeField => pure .native
  | .booleanField => pure .bool
  | .boundedUnsignedField maximum => pure (.uint maximum)
  | _ => throw "invalid standalone aggregate scalar layout"

private def scalarValid (type : Ty) (number : Nat) : Except String Unit := do
  if type.isBytes then throw "byte strings require an aggregate bytes value"
  match type with
  | .jubjubScalar =>
    unless number < Jubjub.scalarOrder do throw "aggregate Jubjub scalar is outside its type"
  | .foreign (.base curve) =>
    unless number < curve.baseModulus do throw "aggregate foreign base value is outside its type"
  | .foreign (.scalar curve) =>
    unless number < curve.scalarModulus do throw "aggregate foreign scalar is outside its type"
  | .jubjubPoint => throw "Jubjub points require a point aggregate value"
  | .foreign (.point _) => throw "foreign points require a point aggregate value"
  | _ =>
    ScalarPolicy.validate type.scalarKind
    unless ScalarPolicy.accepts type.scalarKind number do throw "aggregate scalar is outside its type"

private def flattenCurve (type : Ty) (value : AggregateValue) : Except String (List Nat) := do
  let fields ← match type, value with
    | .jubjubScalar, .scalar .jubjubScalar number => do
      scalarValid .jubjubScalar number
      pure [number]
    | .jubjubPoint, .jubjubPoint x y => do
      unless Jubjub.pointValid x y do throw "aggregate Jubjub point is not canonical or on curve"
      pure [x, y]
    | .foreign (.base curve), .scalar (.foreign (.base actual)) number => do
      unless curve == actual do throw "aggregate foreign curve type mismatch"
      scalarValid (.foreign (.base curve)) number
      Foreign.encodeValue (.base curve) number
    | .foreign (.scalar curve), .scalar (.foreign (.scalar actual)) number => do
      unless curve == actual do throw "aggregate foreign curve type mismatch"
      scalarValid (.foreign (.scalar curve)) number
      Foreign.encodeValue (.scalar curve) number
    | .foreign (.point curve), .foreignPoint actual point => do
      unless curve == actual do throw "aggregate foreign curve type mismatch"
      Foreign.encodeValue (.point curve) point
    | _, _ => throw "aggregate curve value/layout mismatch"
  unless fields.length == type.nativeCallFieldCount do throw "aggregate curve encoding width mismatch"
  pure fields

private def flattenAux : Nat → Layout → AggregateValue → Except String (List Nat)
  | 0, _, _ => throw "aggregate layout traversal exhausted checked fuel"
  | fuel + 1, layout, value => do
    match layout, value with
    | .unit, .unit => pure []
    | .scalar leaf, .scalar type number =>
      unless type == (← leafType leaf) do throw "aggregate scalar type mismatch"
      scalarValid type number
      pure [number]
    | .curve type, value => flattenCurve type value
    | .tuple layouts, .tuple values =>
      unless layouts.length == values.length do throw "aggregate tuple arity mismatch"
      let parts ← (layouts.zip values).mapM fun (layout, value) => flattenAux fuel layout value
      pure parts.flatten
    | .structure id fields, .structure actual values =>
      unless id == actual do throw "aggregate nominal struct identity mismatch"
      unless fields.map Prod.fst == values.map Prod.fst do throw "aggregate struct field order mismatch"
      let parts ← (fields.zip values).mapM fun (field, value) => flattenAux fuel field.2 value.2
      pure parts.flatten
    | .vector length element, .vector values =>
      unless length == values.length do throw "aggregate vector length mismatch"
      pure (← values.mapM (flattenAux fuel element)).flatten
    | .bytes length .byteField, .bytes values =>
      unless values.length == length do throw "aggregate byte length mismatch"
      unless values.all (· ≤ 255) do throw "aggregate byte out of range"
      pure values
    | .enumeration id _ _ payloadLeaves .zeroPadToMaximum variants, .enumeration actual variant values =>
      unless id == actual do throw "aggregate nominal enum identity mismatch"
      let some tag := variants.findIdx? (·.1 == variant) | throw "unknown aggregate enum variant"
      let some selected := variants[tag]? | throw "aggregate enum variant index mismatch"
      let fields := selected.2.1
      unless fields.map Prod.fst == values.map Prod.fst do throw "aggregate enum field order mismatch"
      let parts ← (fields.zip values).mapM fun (field, value) => flattenAux fuel field.2 value.2
      let payload := parts.flatten
      unless payload.length == selected.2.2 && payload.length ≤ payloadLeaves do throw "aggregate enum payload size mismatch"
      pure (tag :: payload ++ List.replicate (payloadLeaves - payload.length) 0)
    | _, _ => throw "aggregate logical value/layout mismatch"

def flatten (type : CompiledType) (value : AggregateValue) : Except String (List Nat) := do
  let leaves ← flattenAux (type.checked.layoutNodes + 1) type.checked.value value
  unless leaves.length == type.checked.expandedLeaves do throw "aggregate checked leaf count mismatch"
  pure leaves

private def unflattenAux : Nat → Layout → List Nat → Except String (AggregateValue × List Nat)
  | 0, _, _ => throw "aggregate layout traversal exhausted checked fuel"
  | fuel + 1, layout, leaves => do
    match layout with
    | .unit => pure (.unit, leaves)
    | .scalar leaf =>
      let number :: rest := leaves | throw "short aggregate scalar input"
      let type ← leafType leaf
      scalarValid type number
      pure (.scalar type number, rest)
    | .curve type => do
      let width := type.nativeCallFieldCount
      let (fields, rest) := leaves.splitAt width
      unless fields.length == width do throw "short aggregate curve input"
      let value ← match type with
        | .jubjubScalar => do
          let [number] := fields | throw "Jubjub scalar encoding requires one field"
          scalarValid .jubjubScalar number
          pure (.scalar .jubjubScalar number)
        | .jubjubPoint => do
          let [x, y] := fields | throw "Jubjub point encoding requires two fields"
          unless Jubjub.pointValid x y do throw "aggregate Jubjub point is not canonical or on curve"
          pure (.jubjubPoint x y)
        | .foreign (.base curve) => do
          let number ← Foreign.decodeValue (.base curve) fields
          scalarValid (.foreign (.base curve)) number
          pure (.scalar (.foreign (.base curve)) number)
        | .foreign (.scalar curve) => do
          let number ← Foreign.decodeValue (.scalar curve) fields
          scalarValid (.foreign (.scalar curve)) number
          pure (.scalar (.foreign (.scalar curve)) number)
        | .foreign (.point curve) => do
          let point ← Foreign.decodeValue (.point curve) fields
          pure (.foreignPoint curve point)
        | _ => throw "invalid aggregate curve layout type"
      pure (value, rest)
    | .tuple layouts =>
      let mut rest := leaves
      let mut values := []
      for layout in layouts do
        let (value, remaining) ← unflattenAux fuel layout rest
        values := values ++ [value]
        rest := remaining
      pure (.tuple values, rest)
    | .structure id fields =>
      let mut rest := leaves
      let mut values := []
      for (name, layout) in fields do
        let (value, remaining) ← unflattenAux fuel layout rest
        values := values ++ [(name, value)]
        rest := remaining
      pure (.structure id values, rest)
    | .vector length element =>
      let mut rest := leaves
      let mut values := []
      for _ in [:length] do
        let (value, remaining) ← unflattenAux fuel element rest
        values := values ++ [value]
        rest := remaining
      pure (.vector values, rest)
    | .bytes length .byteField =>
      let (values, rest) := leaves.splitAt length
      unless values.length == length && values.all (· ≤ 255) do throw "invalid aggregate byte input"
      pure (.bytes values, rest)
    | .enumeration id _ _ payloadLeaves .zeroPadToMaximum variants =>
      let tag :: rest := leaves | throw "short aggregate enum input"
      let some selected := variants[tag]? | throw "aggregate enum tag out of range"
      let (payload, rest) := rest.splitAt payloadLeaves
      unless payload.length == payloadLeaves do throw "short aggregate enum payload"
      let mut remaining := payload
      let mut values := []
      for (name, layout) in selected.2.1 do
        let (value, tail) ← unflattenAux fuel layout remaining
        values := values ++ [(name, value)]
        remaining := tail
      unless remaining.all (· == 0) do throw "nonzero aggregate enum padding"
      pure (.enumeration id selected.1 values, rest)
    | _ => throw "invalid aggregate byte layout"

def unflatten (type : CompiledType) (leaves : List Nat) : Except String AggregateValue := do
  unless leaves.length == type.checked.expandedLeaves do throw "aggregate leaf count mismatch"
  let (value, remaining) ← unflattenAux (type.checked.layoutNodes + 1) type.checked.value leaves
  unless remaining.isEmpty do throw "trailing aggregate leaves"
  pure value

structure TypedValue (type : CompiledType) where
  value : AggregateValue
  leaves : List Nat
  checked : flatten type value = .ok leaves

def checkValue (type : CompiledType) (value : AggregateValue) : Except String (TypedValue type) :=
  match result : flatten type value with
  | .error message => .error message
  | .ok leaves => .ok {value, leaves, checked := result}

/-- Successful reconstruction carries the exact input-leaf equality. -/
def unflattenChecked (type : CompiledType) (leaves : List Nat) :
    Except String (TypedValue type) := do
  let value ← unflatten type leaves
  match checked : flatten type value with
  | .error message => throw message
  | .ok canonical =>
    if equality : canonical = leaves then
      pure {value, leaves, checked := equality ▸ checked}
    else throw "aggregate reconstruction changed canonical leaves"

theorem unflattenChecked_flatten (type : CompiledType) (value : TypedValue type) :
    flatten type value.value = .ok value.leaves := value.checked

private def fieldFromNat (value : Nat) : ByteArray := Id.run do
  let mut bytes := ByteArray.empty
  let mut remaining := value
  for _ in [:32] do
    bytes := bytes.push (remaining % 256).toUInt8
    remaining := remaining / 256
  return bytes

private def appendU32 (bytes : ByteArray) (value : Nat) : ByteArray := Id.run do
  let mut result := bytes
  let mut remaining := value
  for _ in [:4] do
    result := result.push (remaining % 256).toUInt8
    remaining := remaining / 256
  return result

def encode (type : CompiledType) (value : AggregateValue) : Except String ByteArray := do
  let leaves ← flatten type value
  let fingerprint := type.fingerprint.toUTF8
  let mut bytes := appendU32 aggregateWireMagic.toUTF8 fingerprint.size
  bytes := bytes ++ fingerprint
  bytes := appendU32 bytes type.checked.expandedLeaves
  for leaf in leaves do bytes := bytes ++ fieldFromNat leaf
  unless bytes.size ≤ aggregateWireLimit do throw "aggregate wire byte limit exceeded"
  pure bytes

private def readU32 (bytes : ByteArray) (offset : Nat) : Except String Nat := do
  unless offset + 4 ≤ bytes.size do throw "short aggregate wire header"
  pure (bytes[offset]!.toNat + 256 * bytes[offset + 1]!.toNat +
    65536 * bytes[offset + 2]!.toNat + 16777216 * bytes[offset + 3]!.toNat)

def decode (type : CompiledType) (bytes : ByteArray) : Except String AggregateValue := do
  unless bytes.size ≤ aggregateWireLimit do throw "aggregate wire byte limit exceeded"
  let magic := aggregateWireMagic.toUTF8
  unless bytes.extract 0 magic.size == magic do throw "aggregate wire magic/version mismatch"
  let length ← readU32 bytes magic.size
  unless length ≤ aggregateWireLimit && length == type.fingerprint.utf8ByteSize do throw "aggregate wire fingerprint length mismatch"
  let endFingerprint := magic.size + 4 + length
  unless endFingerprint + 4 ≤ bytes.size do throw "short aggregate wire fingerprint"
  unless bytes.extract (magic.size + 4) endFingerprint == type.fingerprint.toUTF8 do throw "aggregate nominal/type fingerprint mismatch"
  let count ← readU32 bytes endFingerprint
  unless count == type.checked.expandedLeaves do throw "aggregate wire leaf count mismatch"
  let start := endFingerprint + 4
  unless start + count * 32 == bytes.size do throw "short or trailing aggregate wire fields"
  let mut leaves := []
  for index in [:count] do
    let value ← Field.decode (bytes.extract (start + index * 32) (start + (index + 1) * 32))
    leaves := leaves ++ [value]
  unflatten type leaves

/-- Decoding also offers the same checked-value carrier as construction. -/
def decodeChecked (type : CompiledType) (bytes : ByteArray) : Except String (TypedValue type) := do
  checkValue type (← decode type bytes)

theorem checked_value_flatten (type : CompiledType) (value : TypedValue type) :
    flatten type value.value = .ok value.leaves := value.checked

theorem compiled_layout_leaf_bound (type : CompiledType) :
    type.checked.value.leafCount ≤ type.limits.maxExpandedLeaves := by
  rw [type.checked.leafCountMatches]
  exact type.checked.leafCountBound

end Noctium.Types
