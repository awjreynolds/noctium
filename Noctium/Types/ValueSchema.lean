import Noctium.Types.Values
import Lean

namespace Noctium.Types
open Lean

private def commaCount (length : Nat) : Nat := length - 1

private def curveTypeName : Ty → String
  | .jubjubScalar => "JubjubScalar"
  | .jubjubPoint => "JubjubPoint"
  | .foreign kind => kind.sourceName
  | _ => ""

private def layoutJsonSize : Nat → Layout → Except String Nat
  | 0, _ => throw "aggregate schema traversal exhausted checked fuel"
  | fuel + 1, layout => do
    match layout with
    | .unit => pure "{\"kind\":\"unit\"}".utf8ByteSize
    | .scalar .nativeField => pure "{\"kind\":\"scalar\",\"leaf\":{\"kind\":\"native\"}}".utf8ByteSize
    | .scalar .booleanField => pure "{\"kind\":\"scalar\",\"leaf\":{\"kind\":\"bool\"}}".utf8ByteSize
    | .scalar (.boundedUnsignedField maximum) =>
      pure ("{\"kind\":\"scalar\",\"leaf\":{\"kind\":\"uint\",\"maximum\":\"\"}}".utf8ByteSize + (toString maximum).utf8ByteSize)
    | .tuple items =>
      pure ("{\"kind\":\"tuple\",\"items\":[]}".utf8ByteSize + commaCount items.length +
        (← items.mapM (layoutJsonSize fuel)).sum)
    | .structure id fields =>
      let sizes ← fields.mapM fun (name, layout) => do
        pure ("{\"name\":\"\",\"layout\":}".utf8ByteSize + name.utf8ByteSize + (← layoutJsonSize fuel layout))
      pure ("{\"kind\":\"struct\",\"id\":\"\",\"fields\":[]}".utf8ByteSize + id.utf8ByteSize + commaCount fields.length + sizes.sum)
    | .vector length element =>
      pure ("{\"kind\":\"vector\",\"length\":0,\"element\":}".utf8ByteSize - 1 +
        (toString length).utf8ByteSize + (← layoutJsonSize fuel element))
    | .bytes length .byteField =>
      pure ("{\"kind\":\"bytes\",\"length\":0}".utf8ByteSize - 1 + (toString length).utf8ByteSize)
    | .curve type =>
      pure ("{\"kind\":\"curve\",\"type\":\"\"}".utf8ByteSize +
        (curveTypeName type).utf8ByteSize)
    | .enumeration id _ _ _ _ variants =>
      let sizes ← variants.mapM fun (name, fields, _) => do
        let fields ← fields.mapM fun (name, layout) => do
          pure ("{\"name\":\"\",\"layout\":}".utf8ByteSize + name.utf8ByteSize + (← layoutJsonSize fuel layout))
        pure ("{\"name\":\"\",\"fields\":[]}".utf8ByteSize + name.utf8ByteSize + commaCount fields.length + fields.sum)
      pure ("{\"kind\":\"enum\",\"id\":\"\",\"variants\":[]}".utf8ByteSize + id.utf8ByteSize + commaCount variants.length + sizes.sum)
    | _ => throw "unsupported aggregate schema leaf"

private def layoutJson : Nat → Layout → Except String Json
  | 0, _ => throw "aggregate schema traversal exhausted checked fuel"
  | fuel + 1, layout => do
    match layout with
    | .unit => pure (Json.mkObj [("kind", toJson ("unit" : String))])
    | .scalar leaf =>
      let fields ← match leaf with
        | .nativeField => pure [("kind", toJson ("native" : String))]
        | .booleanField => pure [("kind", toJson ("bool" : String))]
        | .boundedUnsignedField maximum => pure [("kind", toJson ("uint" : String)), ("maximum", toJson (toString maximum))]
        | _ => throw "unsupported aggregate schema scalar"
      pure (Json.mkObj [("kind", toJson ("scalar" : String)), ("leaf", Json.mkObj fields)])
    | .tuple items => pure (Json.mkObj [("kind", toJson ("tuple" : String)),
        ("items", toJson (← items.mapM (layoutJson fuel)))])
    | .structure id fields =>
      let fields ← fields.mapM fun (name, layout) => do
        pure (Json.mkObj [("name", toJson name), ("layout", ← layoutJson fuel layout)])
      pure (Json.mkObj [("kind", toJson ("struct" : String)), ("id", toJson id), ("fields", toJson fields)])
    | .vector length element => pure (Json.mkObj [("kind", toJson ("vector" : String)),
        ("length", toJson length), ("element", ← layoutJson fuel element)])
    | .bytes length .byteField => pure (Json.mkObj [("kind", toJson ("bytes" : String)), ("length", toJson length)])
    | .curve type => pure (Json.mkObj [("kind", toJson ("curve" : String)),
        ("type", toJson (curveTypeName type))])
    | .enumeration id _ _ _ _ variants =>
      let variants ← variants.mapM fun (name, fields, _) => do
        let fields ← fields.mapM fun (name, layout) => do
          pure (Json.mkObj [("name", toJson name), ("layout", ← layoutJson fuel layout)])
        pure (Json.mkObj [("name", toJson name), ("fields", toJson fields)])
      pure (Json.mkObj [("kind", toJson ("enum" : String)), ("id", toJson id), ("variants", toJson variants)])
    | _ => throw "unsupported aggregate schema leaf"

def schemaJson (type : CompiledType) : Except String Json := do
  let size ← layoutJsonSize (type.checked.layoutNodes + 1) type.checked.value
  let overhead := "{\"schemaVersion\":1,\"typeFingerprint\":\"\",\"layout\":,\"counts\":{\"leaves\":0,\"expandedNodes\":0,\"layoutNodes\":0}}".utf8ByteSize - 3 +
    (toString type.checked.expandedLeaves).utf8ByteSize + (toString type.checked.expandedNodes).utf8ByteSize +
    (toString type.checked.layoutNodes).utf8ByteSize
  let expectedSize := overhead + type.fingerprint.utf8ByteSize + size
  unless expectedSize ≤ aggregateWireLimit do throw "aggregate public schema exceeds transport byte limit"
  let json := Json.mkObj [
    ("schemaVersion", toJson (1 : Nat)), ("typeFingerprint", toJson type.fingerprint),
    ("layout", ← layoutJson (type.checked.layoutNodes + 1) type.checked.value),
    ("counts", Json.mkObj [("leaves", toJson type.checked.expandedLeaves),
      ("expandedNodes", toJson type.checked.expandedNodes), ("layoutNodes", toJson type.checked.layoutNodes)])]
  unless json.compress.utf8ByteSize == expectedSize do throw "aggregate public schema size preflight mismatch"
  pure json

private def valueJsonAux : Nat → AggregateValue → Except String Json
  | 0, _ => throw "aggregate logical value traversal exhausted checked fuel"
  | fuel + 1, value => do
    match value with
    | .unit => pure (Json.mkObj [("kind", toJson ("unit" : String))])
    | .scalar .native value => pure (Json.mkObj [("kind", toJson ("native" : String)), ("value", toJson (toString value))])
    | .scalar .bool value => pure (Json.mkObj [("kind", toJson ("bool" : String)), ("value", toJson (value == 1))])
    | .scalar (.uint maximum) value => pure (Json.mkObj [("kind", toJson ("uint" : String)),
        ("maximum", toJson (toString maximum)), ("value", toJson (toString value))])
    | .scalar (.bytes _) _ => throw "byte strings require an aggregate bytes value"
    | .scalar .opaqueBytes _ => throw "OpaqueBytes require a qualified ledger scalar schema"
    | .scalar .opaqueString _ => throw "OpaqueString requires a qualified ledger scalar schema"
    | .scalar .jubjubScalar value => pure (Json.mkObj [
        ("kind", toJson ("jubjubScalar" : String)), ("value", toJson (toString value))])
    | .scalar (.foreign (.base curve)) value => do
      let bytes ← Foreign.canonicalBytes (.base curve) value
      pure (Json.mkObj [("kind", toJson ("foreign" : String)),
        ("type", toJson (Foreign.Kind.sourceName (.base curve))), ("bytes", toJson bytes)])
    | .scalar (.foreign (.scalar curve)) value => do
      let bytes ← Foreign.canonicalBytes (.scalar curve) value
      pure (Json.mkObj [("kind", toJson ("foreign" : String)),
        ("type", toJson (Foreign.Kind.sourceName (.scalar curve))), ("bytes", toJson bytes)])
    | .scalar (.foreign (.point _)) _ => throw "foreign points require a point aggregate value"
    | .scalar .jubjubPoint _ => throw "Jubjub points require a point aggregate value"
    | .jubjubPoint x y => pure (Json.mkObj [
        ("kind", toJson ("jubjubPoint" : String)),
        ("x", toJson (toString x)), ("y", toJson (toString y))])
    | .foreignPoint curve point => do
      let bytes ← Foreign.canonicalBytes (.point curve) point
      pure (Json.mkObj [("kind", toJson ("foreign" : String)),
        ("type", toJson (Foreign.Kind.sourceName (.point curve))),
        ("bytes", toJson bytes)])
    | .tuple items => pure (Json.mkObj [("kind", toJson ("tuple" : String)), ("items", toJson (← items.mapM (valueJsonAux fuel)))])
    | .structure id fields =>
      let fields ← fields.mapM fun (name, value) => do
        pure (Json.mkObj [("name", toJson name), ("value", ← valueJsonAux fuel value)])
      pure (Json.mkObj [("kind", toJson ("struct" : String)), ("id", toJson id), ("fields", toJson fields)])
    | .enumeration id variant fields =>
      let fields ← fields.mapM fun (name, value) => do
        pure (Json.mkObj [("name", toJson name), ("value", ← valueJsonAux fuel value)])
      pure (Json.mkObj [("kind", toJson ("enum" : String)), ("id", toJson id), ("variant", toJson variant), ("fields", toJson fields)])
    | .vector items => pure (Json.mkObj [("kind", toJson ("vector" : String)), ("items", toJson (← items.mapM (valueJsonAux fuel)))])
    | .bytes values => pure (Json.mkObj [("kind", toJson ("bytes" : String)), ("values", toJson values)])

def valueJson (type : CompiledType) (value : TypedValue type) : Except String Json := do
  let json ← valueJsonAux (type.checked.layoutNodes + 1) value.value
  unless json.compress.utf8ByteSize ≤ aggregateWireLimit do throw "aggregate logical JSON exceeds transport byte limit"
  pure json

end Noctium.Types
