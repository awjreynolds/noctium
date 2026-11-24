import Noctium.Types.ValueSchema

namespace Noctium.Types.Maybe

open Noctium

/-- A stable scalar `Maybe<T>` specialization name for logical output schemas. -/
def scalarTypeId (contractName : String) (payloadType : Ty)
    (nominalUInt? : Option NominalUIntType := none) : Except String DeclId := do
  let suffix ← match payloadType with
    | .native => pure "Native"
    | .bool => pure "Bool"
    | .uint maximum => do
      ScalarPolicy.validate (.uint maximum)
      let bits := maximum.log2 + 1
      if maximum + 1 == 2 ^ bits then
        pure s!"UInt{bits}"
      else
        pure s!"UIntRange{maximum + 1}"
    | _ => throw "Maybe payload must be a Native, Bool, or UInt scalar"
  let suffix := match nominalUInt? with
    | none => suffix
    | some nominalUInt => s!"{suffix}Of{nominalUInt.name}"
  if let some nominalUInt := nominalUInt? then
    unless payloadType == .uint nominalUInt.maximum do
      throw "nominal UInt Maybe payload bound does not match its declaration"
  let id := s!"{contractName}.Maybe{suffix}"
  unless validDeclId id do throw "invalid scalar Maybe type id"
  pure id

/-- Source-only nominal UInt identities carried by the scalar `Maybe` payload.
The wire schema still stores the ordinary bounded UInt field. -/
def scalarNominalUIntFields (payloadType : Ty)
    (nominalUInt? : Option NominalUIntType) : Except String (List (List String × NominalUIntType)) := do
  match nominalUInt? with
  | none => pure []
  | some nominalUInt => do
    unless payloadType == .uint nominalUInt.maximum do
      throw "nominal UInt Maybe payload bound does not match its declaration"
    ScalarPolicy.validate payloadType.scalarKind
    pure [(["value"], nominalUInt)]

/-- The one ordered field source shared by scalar Maybe schemas and frontend
return views. -/
def scalarFieldTypes (payloadType : Ty) : Except String (List (String × Ty)) := do
  match payloadType with
  | .native | .bool => pure ()
  | .uint _ => ScalarPolicy.validate payloadType.scalarKind
  | _ => throw "Maybe payload must be a Native, Bool, or UInt scalar"
  pure [("is_some", .bool), ("value", payloadType)]

/-- Compact's scalar Maybe result is a typed record ordered as `is_some`, `value`.
The stored payload remains present and canonical when the tag is false. -/
def scalarEnvironment (id : DeclId) (payloadType : Ty) : Except String CompositeEnv := do
  unless validDeclId id do throw "invalid scalar Maybe type id"
  let fieldTypes ← scalarFieldTypes payloadType
  let environment : CompositeEnv := {
    structures := [{
      id
      fields := fieldTypes.map fun (name, ty) => {name, type := .scalar ty}
    }]
  }
  discard ((compileType environment (.structure id)).mapError (·.message))
  pure environment

def scalarType (id : DeclId) : CompositeType := .structure id

/-- Make a canonical scalar Maybe value. `None` always carries the typed zero. -/
def scalarValue (id : DeclId) (payloadType : Ty) (present : Bool) (payload : Nat) : AggregateValue :=
  .structure id [
    ("is_some", .scalar .bool (if present then 1 else 0)),
    ("value", .scalar payloadType (if present then payload else 0))
  ]

end Noctium.Types.Maybe
