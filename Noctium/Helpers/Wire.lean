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

/-- Add the checked codec helpers to a readable circuit's root scope. -/
def attach (program : Program) (codecs : List Codec) : Except String Program := do
  let composites := compositeEnv program.composites codecs
  let helpers ← codecs.zipIdx.mapM fun (codec, index) => do
    let compiled ← (Types.compileType composites codec.payload).mapError (·.message)
    declarations compiled (codecName index) codec.frameBytes ⟨0, 2 * index + 1⟩ ⟨0, 2 * index + 2⟩
  pure {program with composites, declarations := program.declarations ++ helpers.flatten}

end Noctium.Helpers.Wire
