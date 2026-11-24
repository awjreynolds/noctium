import Noctium.Helpers

namespace Noctium.Helpers.Wire

/-- A fixed frame and the Lean type environment defining its payload. -/
structure Codec where
  payload : Types.CompositeType
  frameBytes : Nat
  composites : Types.CompositeEnv := {}

def codecName (index : Nat) : String := s!"__noctium_wire_{index}"

private structure Leaf where
  path : List Types.Projection := []
  type : Ty
  -- Aggregates store byte leaves and enum ordinals as Native fields.
  nativeLeaf : Bool := false

private def atPath (projection : Types.Projection) (leaves : List Leaf) : List Leaf :=
  leaves.map fun leaf => {leaf with path := projection :: leaf.path}

private partial def wireLeaves : Types.Layout → Except String (List Leaf)
  | .unit => pure []
  | .scalar .nativeField => pure [{type := .native}]
  | .scalar .booleanField => pure [{type := .bool}]
  | .scalar (.boundedUnsignedField maximum) => pure [{type := .uint maximum}]
  | .opaque _ => throw "opaque Compress leaves are not supported by reversible wire codecs"
  | .curve type => pure [{type}]
  | .tuple items => do
    pure (← items.zipIdx.mapM fun (item, index) =>
      atPath (.tupleIndex index) <$> wireLeaves item).flatten
  | .structure _ fields => do
    pure (← fields.mapM fun (name, field) => atPath (.field name) <$> wireLeaves field).flatten
  | .vector length element => do
    let leaves ← wireLeaves element
    pure ((List.range length).flatMap fun index => atPath (.vectorIndex index) leaves)
  | .bytes length _ =>
    pure ((List.range length).map fun index =>
      {path := [.byteIndex index], type := .uint 255, nativeLeaf := true})
  | .enumeration _ _ maximum 0 _ variants => do
    unless variants.all (·.2.1.isEmpty) do
      throw "wire enum requires fieldless variants"
    pure [{path := [.enumTag], type := .uint maximum, nativeLeaf := true}]
  | _ => throw "unsupported aggregate wire layout"

/-- Project the layout's ordered, typed FAB leaves without serializing a host frame. -/
def fabDigestOperands (compiled : Types.CompiledType) (value : Term) :
    Except String (List (Ty × Term)) := do
  let layout := compiled.checked.value
  let fields ← fabHashLayoutFields layout
  if fields.any fun field => match field.2 with | .opaque _ => true | _ => false then
    throw "opaque Compress leaves are not supported by generic FAB digest operands"
  let atoms ← fields.mapM fun field => fabHashLayoutAtoms field.2
  let emptyRootVector := match layout with
    | .vector 0 _ => true
    | _ => false
  unless ( !fields.isEmpty || emptyRootVector) &&
      atoms.flatten.length ≤ compiled.checked.expandedNodes do
    throw "FAB digest alignment exceeds the checked layout-node budget"
  unless fabHashEncodedFieldCount fields ≤ fabHashNativeOperandLimit do
    throw "FAB digest encoded operand count exceeds the native vector budget"
  visit (layout.nodeCount + 1) value layout
where
  visit : Nat → Term → Types.Layout → Except String (List (Ty × Term))
    | 0, _, _ => throw "FAB digest projection exhausted checked layout fuel"
    | fuel + 1, value, layout => do
      match layout with
      | .unit => pure []
      | .structure _ fields =>
        pure (← fields.mapM fun (name, field) =>
          visit fuel (.project value (.field name)) field).flatten
      | .tuple items =>
        pure (← items.zipIdx.mapM fun (item, index) =>
          visit fuel (.project value (.tupleIndex index)) item).flatten
      | .vector length element =>
        pure (← (List.range length).mapM fun index =>
          visit fuel (.project value (.vectorIndex index)) element).flatten
      | .scalar .nativeField => pure [(.native, value)]
      | .scalar .booleanField => pure [(.bool, value)]
      | .scalar (.boundedUnsignedField maximum) => pure [(.uint maximum, value)]
      | .bytes length .byteField => pure [(.bytes length, value)]
      | .curve ty => pure [(ty, value)]
      | .enumeration _ (.enumTagField maximum) _ 0 _ _ =>
        pure [(.uint maximum, .cast (.uint maximum) (.project value .enumTag))]
      | .opaque _ => throw "opaque Compress leaves are not supported by generic FAB digest operands"
      | _ => throw "unsupported FAB digest leaf type"

/-- Pack checked byte projections in the pinned little-endian FAB field order. -/
private def packHashBytes : List Term → Term
  | [] => .native 0
  | [byte] => byte
  | byte :: rest => .binary .add byte (.binary .mul (.native 256) (packHashBytes rest))

/-- Project a bound aggregate into the Native operands of transient_hash. -/
def transientHashOperands (compiled : Types.CompiledType) (value : Term) :
    Except String (List Term) := do
  let layout := compiled.checked.value
  let fields ← transientFabHashLayoutFields layout
  if fields.any fun field => match field.2 with | .opaque _ => true | _ => false then
    throw "opaque Compress leaves are not supported by numeric transient hashing"
  unless fabHashEncodedFieldCount fields ≤ Types.defaultLimits.maxVectorLength do
    throw "transientHashValue exceeds the native transient hash field limit"
  visit (compiled.checked.layoutNodes + 1) value layout
where
  visit : Nat → Term → Types.Layout → Except String (List Term)
    | 0, _, _ => throw "transientHashValue exhausted checked layout fuel"
    | fuel + 1, value, layout => do
      match layout with
      | .unit => pure []
      | .tuple items =>
        pure (← items.zipIdx.mapM fun (item, index) =>
          visit fuel (.project value (.tupleIndex index)) item).flatten
      | .structure _ fields =>
        pure (← fields.mapM fun (name, field) =>
          visit fuel (.project value (.field name)) field).flatten
      | .vector length element =>
        pure (← (List.range length).mapM fun index =>
          visit fuel (.project value (.vectorIndex index)) element).flatten
      | .scalar .nativeField => pure [value]
      | .scalar .booleanField => pure [.cast .native value]
      | .scalar (.boundedUnsignedField maximum) =>
        -- Keep the declared maximum on the checked layout and source input.
        -- The cast here only produces the field operand Compact hashes.
        discard (ScalarPolicy.validate (.uint maximum))
        pure [.cast .native value]
      | .bytes length .byteField =>
        unless length ≤ maxBytesLength do
          throw s!"transientHashValue byte length exceeds the maximum of {maxBytesLength}"
        if length == 0 then pure [] else do
          let byte := fun index => Term.cast .native (.project value (.byteIndex index))
          let count := bytesChunkCount length
          pure ((List.range count).map fun index =>
            let lowIndex := count - 1 - index
            let start := lowIndex * 31
            packHashBytes ((List.range (bytesChunkWidth length lowIndex)).map fun offset =>
              byte (start + offset)))
      | .enumeration _ (.enumTagField maximum) _ 0 _ variants =>
        unless maximum < 256 && !variants.isEmpty && variants.all (·.2.1.isEmpty) do
          throw "transientHashValue requires a one-byte fieldless enum"
        pure [.project value .enumTag]
      | .curve .jubjubScalar =>
        pure [.curve .scalarToNative [value]]
      | .curve .jubjubPoint =>
        pure [.curve .x [value], .curve .y [value]]
      | .curve (.foreign kind) =>
        pure ((List.range kind.encodedFieldCount).map fun index =>
          .curve (.foreignEncodedField kind index) [value])
      | .opaque _ => throw "opaque Compress leaves are not supported by numeric transient hashing"
      | _ => throw "unsupported transientHashValue leaf type"

private instance : Inhabited Term := ⟨.unit⟩


private partial def concatenate : List (Nat × Term) → Nat × Term
  | [] => (0, .bytes (.bytesLiteral 0 []) [])
  | [field] => field
  | fields =>
    let middle := (fields.length + 1) / 2
    let (leftWidth, left) := concatenate (fields.take middle)
    let (rightWidth, right) := concatenate (fields.drop middle)
    (leftWidth + rightWidth, .bytes (.concatBytes leftWidth rightWidth) [left, right])

/-- Build one encoder and one decoder for a checked nominal or structural layout.
A helper argument is evaluated once, and each projected field uses its declared width. -/
def declarations (compiled : Types.CompiledType) (name : String) (width : Nat)
    (encoder decoder : DeclarationId) : Except String (List Declaration) := do
  unless width ≤ maxBytesLength do throw "aggregate wire width exceeds the source limit"
  let leaves ← wireLeaves compiled.checked.value
  let mut offset := 0
  let mut encoded := []
  let mut decoded := []
  for leaf in leaves do
    let some leafWidth := Noctium.Wire.scalarWidth leaf.type
      | throw "unsupported scalar in aggregate wire layout"
    let projected := leaf.path.foldl Term.project (.ref "value")
    let projected := if leaf.path.getLast? == some .enumTag then
        .cast leaf.type projected else projected
    encoded := (leafWidth, .bytes (.serialize leaf.type leafWidth) [projected]) :: encoded
    let value := if leaf.type == .uint 255 then
        Term.bytesAt (.ref "frame") offset
      else
        let bytes := Term.bytes (.sliceBytes width offset (offset + leafWidth)) [.ref "frame"]
        Term.bytes (.deserialize leaf.type leafWidth) [bytes]
    decoded := (if leaf.nativeLeaf then Term.cast .native value else value) :: decoded
    offset := offset + leafWidth
  unless offset ≤ width do throw s!"aggregate wire layout requires at least {offset} bytes"
  let fields := encoded.reverse
  let padding := width - offset
  let fields := if padding == 0 then fields else
    fields ++ [(padding, .bytes (.bytesLiteral padding (List.replicate padding 0)) [])]
  let (_, result) := concatenate fields
  pure [
    {id := encoder, name := name ++ "Encode", parameters := [⟨"value", .native⟩],
      compositeParameters := [("value", compiled.type)], result := .scalar (.bytes width),
      body := [.return (some result)]},
    {id := decoder, name := name ++ "Decode", parameters := [⟨"frame", .bytes width⟩],
      result := .composite compiled.type,
      body := [.return (some (.composite compiled.type decoded.reverse))]}]

/-- Build a fixed-frame codec for a nominal `Maybe<T>` record. The tag leads
the record and the payload retains the exact type and declarations from its
codec. The caller owns the nominal identity. Normal codec admission checks the
combined environment and frame width. -/
def maybe (id : Types.DeclId) (payload : Codec) : Codec :=
  let maybeType : Types.CompositeType := .structure id
  let declaration : Types.StructDecl := {
    id
    fields := [
      {name := "is_some", type := .scalar .bool},
      {name := "value", type := payload.payload}
    ]
  }
  -- Keep duplicates in this environment so the shared layout validator rejects
  -- a caller ID that collides with a declaration inside the payload codec.
  let composites : Types.CompositeEnv := {
    structures := payload.composites.structures ++ [declaration]
    enumerations := payload.composites.enumerations
  }
  {payload := maybeType, frameBytes := payload.frameBytes + 1, composites}

def compositeEnv (base : Types.CompositeEnv) (codecs : List Codec) : Types.CompositeEnv :=
  {
    structures := (base.structures ++ codecs.flatMap (·.composites.structures)).eraseDups
    enumerations := (base.enumerations ++ codecs.flatMap (·.composites.enumerations)).eraseDups
  }

/-- Build a fixed-frame codec for a nominal `Either<L, R>` record. The caller
owns the nominal identity. The tag precedes both complete arm payloads, and
normal codec admission checks their combined layout and frame width. -/
def either (id : Types.DeclId) (left right : Codec) : Codec :=
  let eitherType : Types.CompositeType := .structure id
  let declaration : Types.StructDecl := {
    id
    fields := [
      {name := "is_left", type := .scalar .bool},
      {name := "left", type := left.payload},
      {name := "right", type := right.payload}
    ]
  }
  let arms := compositeEnv {} [left, right]
  -- Keep the generated declaration after arm declarations so checked type
  -- admission sees and rejects a conflicting caller-supplied identity.
  let composites : Types.CompositeEnv := {
    structures := arms.structures ++ [declaration]
    enumerations := arms.enumerations
  }
  {payload := eitherType, frameBytes := 1 + left.frameBytes + right.frameBytes, composites}

private def pairOrdinals : List Nat → List (Nat × Nat)
  | encoder :: decoder :: rest => (encoder, decoder) :: pairOrdinals rest
  | _ => []

/-- Allocate deterministic root-scope IDs for the generated codec helpers.
The candidate window is bounded by the existing root declaration count plus
the number of IDs required, so sparse large ordinals never force a large scan. -/
private def codecDeclarationIds (program : Program) (codecCount : Nat) : Except String
    (List (DeclarationId × DeclarationId)) := do
  if codecCount == 0 then pure [] else do
    let occupied := (program.declarations.filter (·.id.scope == 0)).map (·.id.ordinal)
    let bound := occupied.length + 2 * codecCount
    let available := ((List.range bound).map (· + 1)).filter fun ordinal =>
      !occupied.contains ordinal
    let pairs := pairOrdinals (available.take (2 * codecCount))
    unless pairs.length == codecCount do
      throw "unable to allocate root declaration IDs for wire codecs"
    pure (pairs.map fun (encoder, decoder) => (⟨0, encoder⟩, ⟨0, decoder⟩))

/-- Add the checked codec helpers to a readable circuit's root scope. -/
def attach (program : Program) (codecs : List Codec) : Except String Program := do
  let composites := compositeEnv program.composites codecs
  let ids ← codecDeclarationIds program codecs.length
  let helpers ← (codecs.zipIdx.zip ids).mapM fun ((codec, index), (encoder, decoder)) => do
    let compiled ← (Types.compileType composites codec.payload).mapError (·.message)
    declarations compiled (codecName index) codec.frameBytes encoder decoder
  pure {program with composites, declarations := program.declarations ++ helpers.flatten}

end Noctium.Helpers.Wire
