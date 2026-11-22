import Noctium.Frontend.Core
import Noctium.Helpers.Wire
import Noctium.Helpers.Iteration
import Noctium.Types.Maybe

namespace Noctium.Authoring

open Lean Elab Command
open Noctium
open Noctium.Helpers

structure PrivateStateField where
  name : String
  key : String
  capability : String
  signature : WitnessSignature
  codec : Option Name := none
  deriving Repr

structure PrivateStateSchema where
  name : String
  fields : List PrivateStateField
  deriving Repr

/-- The wire codec that fixes a typed witness callback's aggregate result ABI. -/
structure WitnessResultCodec where
  signatureName : String
  codec : Name
  deriving Repr, BEq

/-- The checked wire codec that fixes one typed witness callback's aggregate
parameter ABI. Parameter types alone carry nominal layout identity, while this
registry also pins the declared frame and field environment. -/
structure WitnessParameterCodec where
  signatureName : String
  parameterName : String
  codec : Name
  deriving Repr, BEq

structure ObservationInput where
  name : String
  type : String
  visibility : Noctium.Visibility
  deriving Repr, Inhabited

/-- Source policy observations emitted with a readable witness program.
This describes declared flows and claims, not every possible failure channel. -/
structure ObservationMetadata where
  entryName : String
  inputs : List ObservationInput := []
  privateReads : List String := []
  privateStages : List String := []
  witnessNames : List String := []
  authoredProves : List String := []
  explicitReleases : List String := []
  generatedValidity : List String := []
  deriving Repr, Inhabited

private def typeName : Ty → String
  | .native => "Native"
  | .bool => "Bool"
  | .uint maximum => s!"UIntRange {maximum + 1}"
  | .bytes 32 => "Bytes32"
  | .bytes length => s!"Bytes {length}"
  | .opaqueBytes => "OpaqueBytes"
  | .opaqueString => "OpaqueString"
  | .jubjubScalar => "JubjubScalar"
  | .jubjubPoint => "JubjubPoint"
  | .foreign kind => kind.sourceName

private def inputJson (input : ObservationInput) : Json := Json.mkObj [
  ("name", Lean.toJson input.name), ("type", Lean.toJson input.type),
  ("visibility", Lean.toJson (if input.visibility == .public then "public" else "private"))]

def ObservationMetadata.toJson (metadata : ObservationMetadata) : Json := Json.mkObj [
  ("schemaVersion", Lean.toJson (1 : Nat)), ("kind", Lean.toJson ("noctium-authoring-observations" : String)),
  ("entryName", Lean.toJson metadata.entryName), ("inputs", Lean.toJson (metadata.inputs.map inputJson)),
  ("privateReads", Lean.toJson metadata.privateReads), ("privateStages", Lean.toJson metadata.privateStages),
  ("witnessNames", Lean.toJson metadata.witnessNames), ("authoredProves", Lean.toJson metadata.authoredProves),
  ("explicitReleases", Lean.toJson metadata.explicitReleases),
  ("generatedValidity", Lean.toJson metadata.generatedValidity)]

initialize noctiumPrivateStateRegistry : SimplePersistentEnvExtension
    Noctium.Authoring.PrivateStateSchema (Array Noctium.Authoring.PrivateStateSchema) ←
  registerSimplePersistentEnvExtension {
    addImportedFn := fun entries => entries.foldl (init := #[]) (· ++ ·)
    addEntryFn := Array.push
  }

initialize noctiumWitnessSignatureRegistry : SimplePersistentEnvExtension
    Noctium.Helpers.WitnessSignature (Array Noctium.Helpers.WitnessSignature) ←
  registerSimplePersistentEnvExtension {
    addImportedFn := fun entries => entries.foldl (init := #[]) (· ++ ·)
    addEntryFn := Array.push
  }

initialize noctiumWitnessResultCodecRegistry : SimplePersistentEnvExtension
    Noctium.Authoring.WitnessResultCodec (Array Noctium.Authoring.WitnessResultCodec) ←
  registerSimplePersistentEnvExtension {
    addImportedFn := fun entries => entries.foldl (init := #[]) (· ++ ·)
    addEntryFn := Array.push
  }

initialize noctiumWitnessParameterCodecRegistry : SimplePersistentEnvExtension
    Noctium.Authoring.WitnessParameterCodec (Array Noctium.Authoring.WitnessParameterCodec) ←
  registerSimplePersistentEnvExtension {
    addImportedFn := fun entries => entries.foldl (init := #[]) (· ++ ·)
    addEntryFn := Array.push
  }

end Noctium.Authoring

namespace Noctium

open Lean Elab Command
open Noctium
open Noctium.Helpers
open Noctium.Authoring
open scoped Noctium

declare_syntax_cat noctium_witness_input_type
scoped syntax nltype : noctium_witness_input_type
scoped syntax "Payload" ident : noctium_witness_input_type

declare_syntax_cat noctium_private_field
scoped syntax "cell" ident ":" noctium_witness_input_type : noctium_private_field
scoped syntax (name := noctiumPrivateStateCommand) "noctium_private_state" ident
  "where" noctium_private_field* "end" : command

declare_syntax_cat noctium_witness_parameter
scoped syntax ident ":" nltype : noctium_witness_parameter
scoped syntax ident ":" "Payload" ident : noctium_witness_parameter
declare_syntax_cat noctium_witness_result
scoped syntax "Payload" ident : noctium_witness_result
scoped syntax nltype : noctium_witness_result
scoped syntax ident : noctium_witness_result
scoped syntax (name := noctiumWitnessDeclarationCommand) "noctium_witness" ident
  "(" noctium_witness_parameter,* ")" ":" noctium_witness_result : command

scoped syntax "witness" ident "(" nlexpr,* ")" : nlexpr
scoped syntax "if" nlexpr "then" nlexpr "else" nlexpr : nlexpr
declare_syntax_cat noctium_callback_step
scoped syntax "let" ident ":=" nlexpr : noctium_callback_step
scoped syntax "prove" nlexpr : noctium_callback_step
scoped syntax "do" noctium_callback_step* "return" nlexpr "end" : nlexpr
scoped syntax "map(" "[" nlexpr,* "]" "," "fun" ident* "=>" nlexpr ")" : nlexpr
scoped syntax "fold(" nlexpr "," "[" nlexpr,* "]" "," "fun" ident* "=>" nlexpr ")" : nlexpr
scoped syntax "encode(" ident "," nlexpr ")" : nlexpr
scoped syntax "decode(" ident "," nlexpr ")" : nlexpr
scoped syntax "default(" "Payload" ident ")" : nlexpr
declare_syntax_cat noctium_record_field
scoped syntax ident ":=" nlexpr : noctium_record_field
scoped syntax ".." nlexpr : noctium_record_field
scoped syntax "record(" "Payload" ident "," "{" noctium_record_field,* "}" ")" : nlexpr
declare_syntax_cat noctium_tuple_item
scoped syntax nlexpr : noctium_tuple_item
scoped syntax ".." nlexpr : noctium_tuple_item
scoped syntax "tuple(" noctium_tuple_item,* ")" : nlexpr
scoped syntax (name := readablePackBytes) "packBytes(" noctium_tuple_item,* ")" : nlexpr
scoped syntax (name := readableVector) "vector(" noctium_tuple_item,* ")" : nlexpr
scoped syntax "vector(" "Payload" ident "," "[" noctium_tuple_item,* "]" ")" : nlexpr
scoped syntax "some(" nlexpr ")" : nlexpr
scoped syntax "none(" "Payload" ident ")" : nlexpr
scoped syntax "none(" nltype ")" : nlexpr
scoped syntax "either(" nlexpr "," nlexpr "," nlexpr ")" : nlexpr
scoped syntax "field(" nlexpr "," ident ")" : nlexpr
scoped syntax "elementAt(" nlexpr "," nlexpr ")" : nlexpr
scoped syntax (name := readableSequenceSlice) "slice(" nlexpr "," num "," num ")" : nlexpr
scoped syntax "enumTag(" nlexpr ")" : nlexpr
scoped syntax "enumMember(" ident "," ident ")" : nlexpr
scoped syntax "invoke(" ident "," "[" nlexpr,* "]" ")" : nlexpr

declare_syntax_cat noctium_bind_pattern
declare_syntax_cat noctium_bind_field
scoped syntax ident : noctium_bind_pattern
scoped syntax "_" : noctium_bind_pattern
scoped syntax "[" noctium_bind_pattern,* "]" : noctium_bind_pattern
scoped syntax "{" noctium_bind_field,* "}" : noctium_bind_pattern
scoped syntax ident (":=" noctium_bind_pattern)? : noctium_bind_field

declare_syntax_cat noctium_witness_statement
scoped syntax "public" ident ":" noctium_witness_input_type ("as" noctium_bind_pattern)? :
  noctium_witness_statement
scoped syntax "private" ident ":" noctium_witness_input_type ("as" noctium_bind_pattern)? :
  noctium_witness_statement
scoped syntax "let" ident (":" nltype)? ":=" nlexpr : noctium_witness_statement
scoped syntax "let" "[" noctium_bind_pattern,* "]" ":=" nlexpr : noctium_witness_statement
scoped syntax "let" "{" noctium_bind_field,* "}" ":=" nlexpr : noctium_witness_statement
scoped syntax "read" "private" ident "as" ident : noctium_witness_statement
scoped syntax "witness" ident "(" nlexpr,* ")" : noctium_witness_statement
scoped syntax "prove" nlexpr ("as" ident)? : noctium_witness_statement
scoped syntax "stage" ident ":=" nlexpr : noctium_witness_statement
scoped syntax "output" ident (":" nltype)? ":=" nlexpr : noctium_witness_statement
scoped syntax "for" ident "in" num "..<" num "do" noctium_witness_statement* "end" :
  noctium_witness_statement
scoped syntax "for" ident (":" nltype)? "in" nlexpr "do" noctium_witness_statement* "end" :
  noctium_witness_statement
scoped syntax (name := noctiumAuthoredWitnessCircuitCommand) "noctium_witness_circuit" ident
  ("using" ident,+)? ("with" ident)? "where" noctium_witness_statement* "end" : command

private abbrev SurfaceEnv := List (String × ResultType × Noctium.Helpers.Term)

private structure Lowered where
  type : ResultType
  term : Noctium.Helpers.Term
  before : List Statement := []
  signatures : List WitnessSignature := []
  witnessNames : List String := []
  generatedValidity : List String := []

private def Lowered.layoutType (value : Lowered) : Types.CompositeType :=
  match value.type with
  | .unit => .unit
  | .scalar (.bytes length) => .bytes length
  | .scalar ty => .scalar ty
  | .composite type => type

private structure IterationParameter where
  reference : String
  surfaceName : String
  views : List (String × ResultType) := []
  deriving Inhabited

private structure AuthoringExprState where
  codecs : List (Name × Helpers.Wire.Codec) := []
  composites : Types.CompositeEnv := {}
  iterationProgram : Option Helpers.Program := none
  iterationWitnesses : List Helpers.WitnessSignature := []
  requiresOutputViews : _root_.Bool := _root_.Bool.false
  nextCall : Nat := 0
  nextLet : Nat := 0
  iterationParameters : List IterationParameter := []
  allowAssertThen : _root_.Bool := _root_.Bool.false
  deriving Inhabited

private inductive LogicalAliasSource where
  | expression (value : TSyntax `nlexpr)
  | call (site : String)

private structure LogicalAliasBinding where
  name : String
  ty : Ty
  source : LogicalAliasSource

private structure AuthoredOutput where
  name : String
  value : Lowered
  span : SourceSpan
  ordinal : Nat
  source : LogicalAliasSource
  nominalBytes32 : Option NominalBytes32 := none

private def AuthoredOutput.layoutType (item : AuthoredOutput) : Types.CompositeType :=
  item.value.layoutType

private abbrev ExprM := StateT AuthoringExprState CommandElabM

private def freshIterationRef (kind : String) : ExprM String := do
  let state ← get
  let name := s!"__noctium:{kind}:{state.nextLet}"
  modify fun state => {state with nextLet := state.nextLet + 1}
  pure name

private def unresolvedIterationParameter (surfaceName : String) : ExprM String := do
  let reference ← freshIterationRef "iteration-parameter"
  modify fun state => {state with
    iterationParameters := state.iterationParameters ++
      [{reference, surfaceName, views := []}]}
  pure reference

private def lowerExpectedIterationRef (env : SurfaceEnv) (expected : ResultType)
    (stx : TSyntax `nlexpr) : ExprM (Option Lowered) := do
  let `(nlexpr| $id:ident) := stx | return none
  let some (_, _, .ref refName) := env.find? (fun value => value.1 == id.getId.toString)
    | return none
  let state ← get
  let some parameter := state.iterationParameters.find? (·.reference == refName)
    | return none
  if let some (viewName, viewType) := parameter.views.find? fun (_, viewType) =>
      Helpers.subtype viewType expected then
    return some {type := viewType, term := .ref viewName}
  let viewName ← freshIterationRef "iteration-view"
  modify fun state => {state with
    iterationParameters := state.iterationParameters.map fun parameter =>
      if parameter.reference == refName then
        {parameter with views := parameter.views ++ [(viewName, expected)]}
      else parameter}
  pure (some {type := expected, term := .ref viewName})

-- The partial checker sees each typed binding. Zero-length callbacks are never materialized.
private def iterationViewBindings (parameters : List IterationParameter)
    (refs : List String) : List Statement :=
  (parameters.filter fun parameter => refs.contains parameter.reference).flatMap fun parameter =>
    parameter.views.map fun (viewName, viewType) =>
      .bind viewName viewType (.ref parameter.reference)

private def retainIterationScope (parameters : List IterationParameter) (refs : List String) :
    List IterationParameter :=
  parameters.filter fun parameter => !refs.contains parameter.reference

private structure CallbackParameter where
  surfaceName : String
  reference : String
  type : Option ResultType

private def prepareCallbackParameters (parameters : List (TSyntax `ident))
    (types : List (Option ResultType)) : ExprM (List CallbackParameter) := do
  let mut bindings : List CallbackParameter := []
  for (parameter, type) in parameters.zip types do
    let surfaceName := parameter.getId.toString
    match type with
    | some type =>
      bindings := bindings ++ [⟨surfaceName, surfaceName, some type⟩]
    | none =>
      let reference ← unresolvedIterationParameter surfaceName
      bindings := bindings ++ [⟨surfaceName, reference, none⟩]
  pure bindings

private def callbackSurfaceEnv (bindings : List CallbackParameter) : SurfaceEnv :=
  bindings.map fun binding =>
    (binding.surfaceName, binding.type.getD .unit, .ref binding.reference)

private def stringTerm (value : String) : TSyntax `term := ⟨Syntax.mkStrLit value⟩
private def natTerm (value : Nat) : TSyntax `term := ⟨Syntax.mkNumLit (toString value)⟩

private partial def quoteByteLeaves : List String → CommandElabM (TSyntax `term)
  | [] => `(Noctium.Expr.bytesLiteral 0 [])
  | [name] => `(Noctium.Expr.sliceBytes
      (Noctium.Expr.toBytes32 (Noctium.Expr.cast Noctium.Ty.native
        (Noctium.Expr.cast (Noctium.Ty.uint 255) (@Noctium.Expr.ref Noctium.Ty.native $(stringTerm name))))) 0 1)
  | names => do
    let (left, right) := names.splitAt (names.length / 2)
    `(Noctium.Expr.concatBytes $(← quoteByteLeaves left) $(← quoteByteLeaves right))

private def spanTerm (stx : Syntax) : CommandElabM (TSyntax `term) := do
  let fileMap ← getFileMap
  let pos := fileMap.toPosition (stx.getPos?.getD 0)
  let file ← getFileName
  `({ file := $(stringTerm file), line := $(natTerm pos.line),
      column := $(natTerm (pos.column + 1)) : Noctium.SourceSpan })

private def spanValue (stx : Syntax) : CommandElabM SourceSpan := do
  let fileMap ← getFileMap
  let pos := fileMap.toPosition (stx.getPos?.getD 0)
  pure {file := (← getFileName), line := pos.line, column := pos.column + 1}

private def quoteSpan (span : SourceSpan) : CommandElabM (TSyntax `term) := do
  `( ({
    file := $(stringTerm span.file),
    line := $(natTerm span.line),
    column := $(natTerm span.column) : Noctium.SourceSpan }))

private def readScalarTy (stx : TSyntax `nltype) : CommandElabM Ty := do
  match stx with
  | `(nltype| Native) => pure .native
  | `(nltype| Bool) => pure .bool
  | `(nltype| UInt $bits:num) =>
    match ScalarPolicy.sized bits.getNat with
    | .ok (.uint maximum) => pure (.uint maximum)
    | .error message => throwErrorAt stx message
    | _ => throwErrorAt stx "invalid unsigned width"
  | `(nltype| UIntRange $exclusive:num) =>
    match ScalarPolicy.bounded exclusive.getNat with
    | .ok (.uint maximum) => pure (.uint maximum)
    | .error message => throwErrorAt stx message
    | _ => throwErrorAt stx "invalid unsigned range"
  | `(nltype| Bytes32) => pure (.bytes 32)
  | `(nltype| Bytes $length:num) => do
    if length.getNat > Types.defaultLimits.maxVectorLength then
      throwErrorAt stx s!"byte string length exceeds the maximum of {Types.defaultLimits.maxVectorLength}"
    pure (.bytes length.getNat)
  | `(nltype| OpaqueBytes) => pure .opaqueBytes
  | `(nltype| JubjubScalar) => pure .jubjubScalar
  | `(nltype| JubjubPoint) => pure .jubjubPoint
  | `(nltype| Secp256k1Base) => pure (.foreign (.base .secp256k1))
  | `(nltype| Secp256k1Scalar) => pure (.foreign (.scalar .secp256k1))
  | `(nltype| Secp256k1Point) => pure (.foreign (.point .secp256k1))
  | `(nltype| Secp256r1Base) => pure (.foreign (.base .secp256r1))
  | `(nltype| Secp256r1Scalar) => pure (.foreign (.scalar .secp256r1))
  | `(nltype| Secp256r1Point) => pure (.foreign (.point .secp256r1))
  | `(nltype| Curve25519Base) => pure (.foreign (.base .curve25519))
  | `(nltype| Curve25519Scalar) => pure (.foreign (.scalar .curve25519))
  | `(nltype| Curve25519Point) => pure (.foreign (.point .curve25519))
  | _ => throwErrorAt stx "unsupported readable witness scalar type"

private def tyTerm : Ty → CommandElabM (TSyntax `term)
  | .native => `(Noctium.Ty.native)
  | .bool => `(Noctium.Ty.bool)
  | .uint maximum => `(Noctium.Ty.uint $(natTerm maximum))
  | .bytes length => `(Noctium.Ty.bytes $(natTerm length))
  | .opaqueBytes => `(Noctium.Ty.opaqueBytes)
  | .opaqueString => `(Noctium.Ty.opaqueString)
  | .jubjubScalar => `(Noctium.Ty.jubjubScalar)
  | .jubjubPoint => `(Noctium.Ty.jubjubPoint)
  | .foreign (.base .secp256k1) => `(Noctium.Ty.foreign (Noctium.Foreign.Kind.base Noctium.Foreign.Curve.secp256k1))
  | .foreign (.scalar .secp256k1) => `(Noctium.Ty.foreign (Noctium.Foreign.Kind.scalar Noctium.Foreign.Curve.secp256k1))
  | .foreign (.point .secp256k1) => `(Noctium.Ty.foreign (Noctium.Foreign.Kind.point Noctium.Foreign.Curve.secp256k1))
  | .foreign (.base .secp256r1) => `(Noctium.Ty.foreign (Noctium.Foreign.Kind.base Noctium.Foreign.Curve.secp256r1))
  | .foreign (.scalar .secp256r1) => `(Noctium.Ty.foreign (Noctium.Foreign.Kind.scalar Noctium.Foreign.Curve.secp256r1))
  | .foreign (.point .secp256r1) => `(Noctium.Ty.foreign (Noctium.Foreign.Kind.point Noctium.Foreign.Curve.secp256r1))
  | .foreign (.base .curve25519) => `(Noctium.Ty.foreign (Noctium.Foreign.Kind.base Noctium.Foreign.Curve.curve25519))
  | .foreign (.scalar .curve25519) => `(Noctium.Ty.foreign (Noctium.Foreign.Kind.scalar Noctium.Foreign.Curve.curve25519))
  | .foreign (.point .curve25519) => `(Noctium.Ty.foreign (Noctium.Foreign.Kind.point Noctium.Foreign.Curve.curve25519))

private partial def compositeTypeTerm : Types.CompositeType → CommandElabM (TSyntax `term)
  | .unit => `(Noctium.Types.CompositeType.unit)
  | .scalar ty => do `(Noctium.Types.CompositeType.scalar $(← tyTerm ty))
  | .tuple items => do
    let items := (← items.mapM compositeTypeTerm).toArray
    `(Noctium.Types.CompositeType.tuple [$items,*])
  | .structure id => `(Noctium.Types.CompositeType.structure $(stringTerm id))
  | .enumeration id => `(Noctium.Types.CompositeType.enumeration $(stringTerm id))
  | .vector length element => do
    `(Noctium.Types.CompositeType.vector $(natTerm length) $(← compositeTypeTerm element))
  | .bytes length => `(Noctium.Types.CompositeType.bytes $(natTerm length))

private def resultTypeTerm : ResultType → CommandElabM (TSyntax `term)
  | .unit => `(Noctium.Helpers.ResultType.unit)
  | .scalar ty => do `(Noctium.Helpers.ResultType.scalar $(← tyTerm ty))
  | .composite type => do `(Noctium.Helpers.ResultType.composite $(← compositeTypeTerm type))

private def validIdentity (stx : Syntax) (value : String) : CommandElabM _root_.Unit :=
  unless Helpers.validWitnessIdentifier value do
    throwErrorAt stx s!"generated witness identity is invalid or too long: {value}"

private def generatedName (base : Name) (suffix : String) : Name :=
  base ++ Name.str .anonymous suffix

private def resolvedSurfaceName (id : TSyntax `ident) : CommandElabM String := do
  let current := ((← getCurrNamespace) ++ id.getId).toString
  let registry := noctiumWitnessSignatureRegistry.getState (← getEnv)
  if registry.any (·.name == current) then return current
  let direct := id.getId.toString
  if registry.any (·.name == direct) then return direct
  throwErrorAt id s!"unknown Noctium witness '{id.getId}'"

private def privateStateSchema (schema : Name) (stx : Syntax) : CommandElabM PrivateStateSchema := do
  let registry := noctiumPrivateStateRegistry.getState (← getEnv)
  let current := ((← getCurrNamespace) ++ schema).toString
  if let some value := registry.find? (·.name == current) then return value
  match registry.find? (·.name == schema.toString) with
  | some value => pure value
  | none => throwErrorAt stx s!"unknown private-state schema '{schema}'"

private def witnessSignature (function : TSyntax `ident) : CommandElabM WitnessSignature := do
  let registry := noctiumWitnessSignatureRegistry.getState (← getEnv)
  let name ← resolvedSurfaceName function
  match registry.find? (·.name == name) with
  | some signature => pure signature
  | none => throwErrorAt function s!"unknown Noctium witness '{function.getId}'"

private def splitSchemaField (fieldPath : TSyntax `ident) : CommandElabM (Name × String) := do
  match fieldPath.getId with
  | .str schema field => pure (schema, field)
  | _ => throwErrorAt fieldPath "private-state member must use Schema.field"

private def uniqueStrings (values : List String) : _root_.Bool :=
  values.length == values.eraseDups.length

private def lowerSchemaName (id : TSyntax `ident) : CommandElabM String := do
  let name := ((← getCurrNamespace) ++ id.getId).toString
  validIdentity id name
  pure name

private def quoteSignature (signature : WitnessSignature) : CommandElabM (TSyntax `term) := do
  let params ← signature.parameters.mapM fun parameter => do
    let result ← resultTypeTerm parameter.type
    `({ name := $(stringTerm parameter.name), type := $result : Noctium.Helpers.WitnessParameter })
  let params := params.toArray
  let parameters ← `([$params,*])
  let result ← resultTypeTerm signature.result
  let privateKey ← match signature.privateKey with
    | none => `(none)
    | some key => `(some $(stringTerm key))
  let span ← quoteSpan signature.span
  `( ({
    name := $(stringTerm signature.name),
    operation := $(stringTerm signature.operation),
    capability := $(stringTerm signature.capability),
    privateKey := $privateKey,
    parameters := $parameters,
    result := $result,
    span := $span : Noctium.Helpers.WitnessSignature }))

private def quoteField (field : PrivateStateField) : CommandElabM (TSyntax `term) := do
  let signature ← quoteSignature field.signature
  let codec ← match field.codec with
    | none => `(none)
    | some name => `(some $(quote name))
  `(Noctium.Authoring.PrivateStateField.mk $(stringTerm field.name)
    $(stringTerm field.key) $(stringTerm field.capability) $signature $codec)

private partial def renderType : TSyntax `nltype → String
  | `(nltype| Native) => "Native"
  | `(nltype| Bool) => "Bool"
  | `(nltype| UInt $bits:num) => s!"UInt {bits.getNat}"
  | `(nltype| UIntRange $exclusive:num) => s!"UIntRange {exclusive.getNat}"
  | `(nltype| Bytes32) => "Bytes32"
  | `(nltype| Bytes $length:num) => s!"Bytes {length.getNat}"
  | `(nltype| OpaqueBytes) => "OpaqueBytes"
  | `(nltype| OpaqueString) => "OpaqueString"
  | `(nltype| JubjubScalar) => "JubjubScalar"
  | `(nltype| JubjubPoint) => "JubjubPoint"
  | `(nltype| Secp256k1Base) => "Secp256k1Base"
  | `(nltype| Secp256k1Scalar) => "Secp256k1Scalar"
  | `(nltype| Secp256k1Point) => "Secp256k1Point"
  | `(nltype| Secp256r1Base) => "Secp256r1Base"
  | `(nltype| Secp256r1Scalar) => "Secp256r1Scalar"
  | `(nltype| Secp256r1Point) => "Secp256r1Point"
  | `(nltype| Curve25519Base) => "Curve25519Base"
  | `(nltype| Curve25519Scalar) => "Curve25519Scalar"
  | `(nltype| Curve25519Point) => "Curve25519Point"
  | _ => "?"

private def recordField (field : TSyntax `noctium_record_field) :
    Option (Option (TSyntax `ident) × TSyntax `nlexpr) :=
  match field with
  | `(noctium_record_field| $name:ident := $source:nlexpr) => some (some name, source)
  | `(noctium_record_field| ..$source:nlexpr) => some (none, source)
  | _ => none

private def tupleItem (item : TSyntax `noctium_tuple_item) :
    Option (_root_.Bool × TSyntax `nlexpr) :=
  match item with
  | `(noctium_tuple_item| ..$source:nlexpr) => some (_root_.Bool.true, source)
  | `(noctium_tuple_item| $source:nlexpr) => some (_root_.Bool.false, source)
  | _ => none

private def callbackStep (step : TSyntax `noctium_callback_step) :
    Option (Option Ident × TSyntax `nlexpr) :=
  match step with
  | `(noctium_callback_step| let $id:ident := $value:nlexpr) => some (some id, value)
  | `(noctium_callback_step| prove $value:nlexpr) => some (none, value)
  | _ => none

private partial def renderExpr (stx : TSyntax `nlexpr) : String :=
  match stx with
  | `(nlexpr| $id:ident) => id.getId.toString
  | `(nlexpr| $n:num) => toString n.getNat
  | `(nlexpr| true) => "true"
  | `(nlexpr| false) => "false"
  | `(nlexpr| let $id:ident := $value:nlexpr in $body:nlexpr) =>
    s!"let {id.getId} := {renderExpr value} in {renderExpr body}"
  | `(nlexpr| assertThen($condition, $body)) =>
    s!"assertThen({renderExpr condition}, {renderExpr body})"
  | `(nlexpr| do $steps:noctium_callback_step* return $result:nlexpr end) =>
    let lines := (steps.toList.filterMap callbackStep).map fun
      | (some id, value) => s!"let {id.getId} := {renderExpr value}"
      | (none, condition) => s!"prove {renderExpr condition}"
    "do " ++ String.intercalate " " (lines ++ [s!"return {renderExpr result} end"])
  | `(nlexpr| add($left, $right)) => s!"add({renderExpr left}, {renderExpr right})"
  | `(nlexpr| sub($left, $right)) => s!"sub({renderExpr left}, {renderExpr right})"
  | `(nlexpr| mul($left, $right)) => s!"mul({renderExpr left}, {renderExpr right})"
  | `(nlexpr| uint($n:num)) => s!"uint({n.getNat})"
  | `(nlexpr| cast($ty:nltype, $value:nlexpr)) =>
    s!"cast({renderType ty}, {renderExpr value})"
  | `(nlexpr| disclose($value)) => s!"disclose({renderExpr value})"
  | `(nlexpr| encode($codec:ident, $value)) => s!"encode({codec.getId}, {renderExpr value})"
  | `(nlexpr| decode($codec:ident, $value)) => s!"decode({codec.getId}, {renderExpr value})"
  | `(nlexpr| default(Payload $codec:ident)) => s!"default(Payload {codec.getId})"
  | `(nlexpr| default($type:nltype)) => s!"default({renderType type})"
  | `(nlexpr| record(Payload $codec:ident, { $fields,* })) =>
    let rendered := (fields.getElems.toList.filterMap recordField).map fun
      | (some name, value) => s!"{name.getId} := {renderExpr value}"
      | (none, value) => ".." ++ renderExpr value
    "record(Payload " ++ codec.getId.toString ++ ", {" ++ String.intercalate ", " rendered ++ "})"
  | `(nlexpr| tuple($items,*)) | `(nlexpr| packBytes($items,*))
  | `(nlexpr| vector($items,*)) | `(nlexpr| vector(Payload $_:ident, [$items,*])) =>
    let rendered := (items.getElems.toList.filterMap tupleItem).map fun (spread, value) =>
      (if spread then ".." else "") ++ renderExpr value
    let arguments := String.intercalate ", " rendered
    match stx with
    | `(nlexpr| vector(Payload $codec:ident, [$_items,*])) =>
      s!"vector(Payload {codec.getId}, [{arguments}])"
    | _ =>
      let name := if stx.raw.getKind == ``readablePackBytes then "packBytes"
        else if stx.raw.getKind == ``readableVector then "vector" else "tuple"
      name ++ "(" ++ arguments ++ ")"
  | `(nlexpr| some($value)) => s!"some({renderExpr value})"
  | `(nlexpr| none(Payload $codec:ident)) => s!"none(Payload {codec.getId})"
  | `(nlexpr| none($type:nltype)) => s!"none({renderType type})"
  | `(nlexpr| either($tag, $left, $right)) =>
    s!"either({renderExpr tag}, {renderExpr left}, {renderExpr right})"
  | `(nlexpr| field($value, $name:ident)) => s!"field({renderExpr value}, {name.getId})"
  | `(nlexpr| elementAt($value, $index)) => s!"elementAt({renderExpr value}, {renderExpr index})"
  | `(nlexpr| slice($value, $start:num, $stop:num)) =>
    s!"slice({renderExpr value}, {start.getNat}, {stop.getNat})"
  | `(nlexpr| enumTag($value)) => s!"enumTag({renderExpr value})"
  | `(nlexpr| enumMember($codec:ident, $variantName:ident)) =>
    s!"enumMember({codec.getId}, {variantName.getId})"
  | `(nlexpr| eq($left, $right)) => s!"eq({renderExpr left}, {renderExpr right})"
  | `(nlexpr| boolAnd($left, $right)) => s!"boolAnd({renderExpr left}, {renderExpr right})"
  | `(nlexpr| boolOr($left, $right)) => s!"boolOr({renderExpr left}, {renderExpr right})"
  | `(nlexpr| andThen($left, $right)) => s!"andThen({renderExpr left}, {renderExpr right})"
  | `(nlexpr| orElse($left, $right)) => s!"orElse({renderExpr left}, {renderExpr right})"
  | `(nlexpr| boolNot($value)) => s!"boolNot({renderExpr value})"
  | `(nlexpr| boolXor($left, $right)) => s!"boolXor({renderExpr left}, {renderExpr right})"
  | `(nlexpr| select($condition, $yes, $no)) =>
    s!"select({renderExpr condition}, {renderExpr yes}, {renderExpr no})"
  | `(nlexpr| ite($condition, $yes, $no))
  | `(nlexpr| if $condition then $yes else $no) =>
    s!"if {renderExpr condition} then {renderExpr yes} else {renderExpr no}"
  | `(nlexpr| poseidon2($domain:num, $left, $right)) =>
    s!"poseidon2({domain.getNat}, {renderExpr left}, {renderExpr right})"
  | `(nlexpr| persistentHash32($value)) => s!"persistentHash32({renderExpr value})"
  | `(nlexpr| sha256($value)) => s!"sha256({renderExpr value})"
  | `(nlexpr| sha512($value)) => s!"sha512({renderExpr value})"
  | `(nlexpr| keccak256($value)) => s!"keccak256({renderExpr value})"
  | `(nlexpr| bytes32($literal:str)) => s!"bytes32({(toJson literal.getString).compress})"
  | `(nlexpr| nativeToken()) => "nativeToken()"
  | `(nlexpr| tokenType($domain, $contractAddress)) =>
    s!"tokenType({renderExpr domain}, {renderExpr contractAddress})"
  | `(nlexpr| bytes($length:num, $literal:str)) =>
    s!"bytes({length.getNat}, {(toJson literal.getString).compress})"
  | `(nlexpr| byteAt($value, $index:num)) =>
    s!"byteAt({renderExpr value}, {index.getNat})"
  | `(nlexpr| persistentHashVector32([$values,*])) =>
    s!"persistentHashVector32([{String.intercalate ", " (values.getElems.toList.map renderExpr)}])"
  | `(nlexpr| persistentHashFab($environment:ident, $type:ident, [$values,*])) =>
    s!"persistentHashFab({environment.getId}, {type.getId}, [{String.intercalate ", " (values.getElems.toList.map renderExpr)}])"
  | `(nlexpr| hashToCurveFab($environment:ident, $type:ident, [$values,*])) =>
    s!"hashToCurveFab({environment.getId}, {type.getId}, [{String.intercalate ", " (values.getElems.toList.map renderExpr)}])"
  | `(nlexpr| sha512Fab($environment:ident, $type:ident, [$values,*])) =>
    s!"sha512Fab({environment.getId}, {type.getId}, [{String.intercalate ", " (values.getElems.toList.map renderExpr)}])"
  | `(nlexpr| persistentCommitFab($environment:ident, $type:ident, $opening, [$values,*])) =>
    s!"persistentCommitFab({environment.getId}, {type.getId}, {renderExpr opening}, [{String.intercalate ", " (values.getElems.toList.map renderExpr)}])"
  | `(nlexpr| transientCommitFab($environment:ident, $type:ident, $opening, [$values,*])) =>
    s!"transientCommitFab({environment.getId}, {type.getId}, {renderExpr opening}, [{String.intercalate ", " (values.getElems.toList.map renderExpr)}])"
  | `(nlexpr| persistentHashNative($value)) => s!"persistentHashNative({renderExpr value})"
  | `(nlexpr| persistentHashNativeVector([$values,*])) =>
    s!"persistentHashNativeVector([{String.intercalate ", " (values.getElems.toList.map renderExpr)}])"
  | `(nlexpr| transientHashNativeVector([$values,*])) =>
    s!"transientHashNativeVector([{String.intercalate ", " (values.getElems.toList.map renderExpr)}])"
  | `(nlexpr| transientHashValue($value)) => s!"transientHashValue({renderExpr value})"
  | `(nlexpr| persistentHashPoint($point)) => s!"persistentHashPoint({renderExpr point})"
  | `(nlexpr| reverseBytes32($value)) => s!"reverseBytes32({renderExpr value})"
  | `(nlexpr| reverseBytes($value)) => s!"reverseBytes({renderExpr value})"
  | `(nlexpr| sliceBytes($value, $start:num, $stop:num)) =>
    s!"sliceBytes({renderExpr value}, {start.getNat}, {stop.getNat})"
  | `(nlexpr| concatBytes($left, $right)) =>
    s!"concatBytes({renderExpr left}, {renderExpr right})"
  | `(nlexpr| toBytes($value, $width:num)) =>
    s!"toBytes({renderExpr value}, {width.getNat})"
  | `(nlexpr| degradeToNative($value)) => s!"degradeToNative({renderExpr value})"
  | `(nlexpr| upgradeFromNative($value)) => s!"upgradeFromNative({renderExpr value})"
  | `(nlexpr| toBytes32($value)) => s!"toBytes32({renderExpr value})"
  | `(nlexpr| jubjubScalarFromNative($value)) => s!"jubjubScalarFromNative({renderExpr value})"
  | `(nlexpr| jubjubScalarToNative($value)) => s!"jubjubScalarToNative({renderExpr value})"
  | `(nlexpr| jubjubMulGenerator($value)) => s!"jubjubMulGenerator({renderExpr value})"
  | `(nlexpr| jubjubMul($point, $scalar)) => s!"jubjubMul({renderExpr point}, {renderExpr scalar})"
  | `(nlexpr| jubjubAdd($left, $right)) => s!"jubjubAdd({renderExpr left}, {renderExpr right})"
  | `(nlexpr| jubjubNeg($point)) => s!"jubjubNeg({renderExpr point})"
  | `(nlexpr| jubjubX($point)) => s!"jubjubX({renderExpr point})"
  | `(nlexpr| jubjubY($point)) => s!"jubjubY({renderExpr point})"
  | `(nlexpr| jubjubFromCoordinates($x, $y)) =>
    s!"jubjubFromCoordinates({renderExpr x}, {renderExpr y})"
  | `(nlexpr| secp256k1Base($value:num)) => s!"secp256k1Base({value.getNat})"
  | `(nlexpr| secp256k1Scalar($value:num)) => s!"secp256k1Scalar({value.getNat})"
  | `(nlexpr| secp256k1Point($x:num, $y:num)) =>
    s!"secp256k1Point({x.getNat}, {y.getNat})"
  | `(nlexpr| secp256k1Identity()) => "secp256k1Identity()"
  | `(nlexpr| secp256r1Base($value:num)) => s!"secp256r1Base({value.getNat})"
  | `(nlexpr| secp256r1Scalar($value:num)) => s!"secp256r1Scalar({value.getNat})"
  | `(nlexpr| secp256r1Point($x:num, $y:num)) =>
    s!"secp256r1Point({x.getNat}, {y.getNat})"
  | `(nlexpr| secp256r1Identity()) => "secp256r1Identity()"
  | `(nlexpr| curve25519Base($value:num)) => s!"curve25519Base({value.getNat})"
  | `(nlexpr| curve25519Scalar($value:num)) => s!"curve25519Scalar({value.getNat})"
  | `(nlexpr| curve25519Point($x:num, $y:num)) =>
    s!"curve25519Point({x.getNat}, {y.getNat})"
  | `(nlexpr| curve25519Identity()) => "curve25519Identity()"
  | `(nlexpr| hashToCurve([$values,*])) =>
    s!"hashToCurve([{String.intercalate ", " (values.getElems.toList.map renderExpr)}])"
  | `(nlexpr| foreignAdd($left, $right)) => s!"foreignAdd({renderExpr left}, {renderExpr right})"
  | `(nlexpr| foreignSub($left, $right)) => s!"foreignSub({renderExpr left}, {renderExpr right})"
  | `(nlexpr| foreignMul($left, $right)) => s!"foreignMul({renderExpr left}, {renderExpr right})"
  | `(nlexpr| foreignNeg($value)) => s!"foreignNeg({renderExpr value})"
  | `(nlexpr| foreignInv($value)) => s!"foreignInv({renderExpr value})"
  | `(nlexpr| curveMul($point, $scalar)) =>
    s!"curveMul({renderExpr point}, {renderExpr scalar})"
  | `(nlexpr| curveMulGenerator($scalar)) => s!"curveMulGenerator({renderExpr scalar})"
  | `(nlexpr| curveX($point)) => s!"curveX({renderExpr point})"
  | `(nlexpr| curveY($point)) => s!"curveY({renderExpr point})"
  | `(nlexpr| curveFromCoordinates($x, $y)) =>
    s!"curveFromCoordinates({renderExpr x}, {renderExpr y})"
  | `(nlexpr| foreignToBytes($value)) => s!"foreignToBytes({renderExpr value})"
  | `(nlexpr| foreignFromBytes($type:nltype, $value)) =>
    s!"foreignFromBytes({renderType type}, {renderExpr value})"
  | `(nlexpr| invoke($function:ident, [$args:nlexpr,*])) =>
    s!"invoke({function.getId}, [{String.intercalate ", " (args.getElems.toList.map renderExpr)}])"
  | `(nlexpr| witness $function:ident($args:nlexpr,*)) =>
    s!"witness {function.getId}({String.intercalate ", " (args.getElems.toList.map renderExpr)})"
  | `(nlexpr| map([$sequences,*], fun $parameters:ident* => $body)) =>
    s!"map([{String.intercalate ", " (sequences.getElems.toList.map renderExpr)}], fun {String.intercalate " " (parameters.toList.map (·.getId.toString))} => {renderExpr body})"
  | `(nlexpr| fold($initial, [$sequences,*], fun $parameters:ident* => $body)) =>
    s!"fold({renderExpr initial}, [{String.intercalate ", " (sequences.getElems.toList.map renderExpr)}], fun {String.intercalate " " (parameters.toList.map (·.getId.toString))} => {renderExpr body})"
  | _ => "<unsupported-expression>"

private partial def disclosedValues (stx : TSyntax `nlexpr) : List String :=
  match stx with
  | `(nlexpr| disclose($value)) => renderExpr value :: disclosedValues value
  | `(nlexpr| record(Payload $_:ident, { $fields,* })) =>
    (fields.getElems.toList.filterMap recordField).flatMap (disclosedValues ∘ Prod.snd)
  | `(nlexpr| tuple($items,*)) | `(nlexpr| packBytes($items,*))
  | `(nlexpr| vector($items,*)) | `(nlexpr| vector(Payload $_:ident, [$items,*])) =>
    (items.getElems.toList.filterMap tupleItem).flatMap (disclosedValues ∘ Prod.snd)
  | `(nlexpr| let $_:ident := $value:nlexpr in $body:nlexpr) => disclosedValues value ++ disclosedValues body
  | `(nlexpr| assertThen($condition, $body)) => disclosedValues condition ++ disclosedValues body
  | `(nlexpr| do $steps:noctium_callback_step* return $result:nlexpr end) =>
    (steps.toList.filterMap callbackStep).flatMap (disclosedValues ∘ Prod.snd) ++
      disclosedValues result
  | `(nlexpr| add($left, $right)) | `(nlexpr| sub($left, $right))
  | `(nlexpr| mul($left, $right)) | `(nlexpr| eq($left, $right))
  | `(nlexpr| boolAnd($left, $right)) | `(nlexpr| boolOr($left, $right))
  | `(nlexpr| andThen($left, $right)) | `(nlexpr| orElse($left, $right))
  | `(nlexpr| boolXor($left, $right)) =>
    disclosedValues left ++ disclosedValues right
  | `(nlexpr| boolNot($value)) => disclosedValues value
  | `(nlexpr| cast($_:nltype, $value:nlexpr)) => disclosedValues value
  | `(nlexpr| select($condition, $yes, $no))
  | `(nlexpr| ite($condition, $yes, $no))
  | `(nlexpr| if $condition then $yes else $no) =>
    disclosedValues condition ++ disclosedValues yes ++ disclosedValues no
  | `(nlexpr| poseidon2($_:num, $left, $right)) => disclosedValues left ++ disclosedValues right
  | `(nlexpr| elementAt($value, $index)) => disclosedValues value ++ disclosedValues index
  | `(nlexpr| slice($value, $_:num, $_:num)) => disclosedValues value
  | `(nlexpr| persistentHash32($value)) | `(nlexpr| persistentHashNative($value))
  | `(nlexpr| persistentHashPoint($value)) | `(nlexpr| sha256($value))
  | `(nlexpr| sha512($value))
  | `(nlexpr| keccak256($value)) | `(nlexpr| degradeToNative($value))
  | `(nlexpr| upgradeFromNative($value))
  | `(nlexpr| serialize($value, $_:num)) | `(nlexpr| toBytes($value, $_:num))
  | `(nlexpr| fromBytesChecked($_:nltype, $value))
  | `(nlexpr| deserialize($_:nltype, $value))
  | `(nlexpr| encode($_:ident, $value)) | `(nlexpr| decode($_:ident, $value))
  | `(nlexpr| some($value))
  | `(nlexpr| field($value, $_:ident))
  | `(nlexpr| enumTag($value))
  | `(nlexpr| toBytes32($value)) | `(nlexpr| reverseBytes32($value))
  | `(nlexpr| reverseBytes($value)) => disclosedValues value
  | `(nlexpr| either($tag, $left, $right)) =>
    disclosedValues tag ++ disclosedValues left ++ disclosedValues right
  | `(nlexpr| sliceBytes($value, $_:num, $_:num)) => disclosedValues value
  | `(nlexpr| concatBytes($left, $right)) => disclosedValues left ++ disclosedValues right
  | `(nlexpr| byteAt($value, $_:num)) => disclosedValues value
  | `(nlexpr| persistentHashVector32([$values,*]))
  | `(nlexpr| persistentHashFab($_:ident, $_:ident, [$values,*]))
  | `(nlexpr| hashToCurveFab($_:ident, $_:ident, [$values,*]))
  | `(nlexpr| sha512Fab($_:ident, $_:ident, [$values,*]))
  | `(nlexpr| persistentHashNativeVector([$values,*]))
  | `(nlexpr| transientHashNativeVector([$values,*])) =>
    values.getElems.toList.flatMap disclosedValues
  | `(nlexpr| transientHashValue($value)) => disclosedValues value
  | `(nlexpr| tokenType($domain, $contractAddress)) =>
    disclosedValues domain ++ disclosedValues contractAddress
  | `(nlexpr| persistentCommitFab($_:ident, $_:ident, $opening, [$values,*]))
  | `(nlexpr| transientCommitFab($_:ident, $_:ident, $opening, [$values,*])) =>
    disclosedValues opening ++ values.getElems.toList.flatMap disclosedValues
  | `(nlexpr| jubjubScalarFromNative($value))
  | `(nlexpr| jubjubScalarToNative($value))
  | `(nlexpr| jubjubMulGenerator($value))
  | `(nlexpr| jubjubNeg($value))
  | `(nlexpr| jubjubX($value))
  | `(nlexpr| jubjubY($value)) => disclosedValues value
  | `(nlexpr| jubjubMul($point, $scalar)) | `(nlexpr| jubjubAdd($point, $scalar)) =>
    disclosedValues point ++ disclosedValues scalar
  | `(nlexpr| jubjubFromCoordinates($x, $y)) => disclosedValues x ++ disclosedValues y
  | `(nlexpr| hashToCurve([$values,*])) => values.getElems.toList.flatMap disclosedValues
  | `(nlexpr| foreignNeg($value)) | `(nlexpr| foreignInv($value))
  | `(nlexpr| curveMulGenerator($value)) | `(nlexpr| curveX($value))
  | `(nlexpr| curveY($value)) | `(nlexpr| foreignToBytes($value)) => disclosedValues value
  | `(nlexpr| foreignAdd($left, $right)) | `(nlexpr| foreignSub($left, $right))
  | `(nlexpr| foreignMul($left, $right)) | `(nlexpr| curveMul($left, $right))
  | `(nlexpr| curveFromCoordinates($left, $right)) =>
    disclosedValues left ++ disclosedValues right
  | `(nlexpr| foreignFromBytes($_:nltype, $value)) => disclosedValues value
  | `(nlexpr| invoke($_:ident, [$args:nlexpr,*]))
  | `(nlexpr| witness $_:ident($args:nlexpr,*)) => args.getElems.toList.flatMap disclosedValues
  | `(nlexpr| map([$sequences,*], fun $_:ident* => $body)) =>
    sequences.getElems.toList.flatMap disclosedValues ++ disclosedValues body
  | `(nlexpr| fold($initial, [$sequences,*], fun $_:ident* => $body)) =>
    disclosedValues initial ++ sequences.getElems.toList.flatMap disclosedValues ++ disclosedValues body
  | _ => []

private partial def inlineAssertions (stx : TSyntax `nlexpr) : List String :=
  match stx with
  | `(nlexpr| record(Payload $_:ident, { $fields,* })) =>
    (fields.getElems.toList.filterMap recordField).flatMap (inlineAssertions ∘ Prod.snd)
  | `(nlexpr| tuple($items,*)) | `(nlexpr| packBytes($items,*))
  | `(nlexpr| vector($items,*)) | `(nlexpr| vector(Payload $_:ident, [$items,*])) =>
    (items.getElems.toList.filterMap tupleItem).flatMap (inlineAssertions ∘ Prod.snd)
  | `(nlexpr| assertThen($condition, $body)) =>
    renderExpr condition :: (inlineAssertions condition ++ inlineAssertions body)
  | `(nlexpr| do $steps:noctium_callback_step* return $result:nlexpr end) =>
    ((steps.toList.filterMap callbackStep).flatMap fun
      | (some _, value) => inlineAssertions value
      | (none, condition) => renderExpr condition :: inlineAssertions condition) ++
      inlineAssertions result
  | `(nlexpr| let $_:ident := $value:nlexpr in $body:nlexpr) =>
    inlineAssertions value ++ inlineAssertions body
  | `(nlexpr| add($left, $right)) | `(nlexpr| sub($left, $right))
  | `(nlexpr| mul($left, $right)) | `(nlexpr| eq($left, $right))
  | `(nlexpr| boolAnd($left, $right)) | `(nlexpr| boolOr($left, $right))
  | `(nlexpr| andThen($left, $right)) | `(nlexpr| orElse($left, $right))
  | `(nlexpr| boolXor($left, $right)) =>
    inlineAssertions left ++ inlineAssertions right
  | `(nlexpr| boolNot($value)) => inlineAssertions value
  | `(nlexpr| cast($_:nltype, $value:nlexpr)) | `(nlexpr| disclose($value)) => inlineAssertions value
  | `(nlexpr| select($condition, $yes, $no))
  | `(nlexpr| ite($condition, $yes, $no))
  | `(nlexpr| if $condition then $yes else $no) =>
    inlineAssertions condition ++ inlineAssertions yes ++ inlineAssertions no
  | `(nlexpr| poseidon2($_:num, $left, $right)) => inlineAssertions left ++ inlineAssertions right
  | `(nlexpr| elementAt($value, $index)) => inlineAssertions value ++ inlineAssertions index
  | `(nlexpr| slice($value, $_:num, $_:num)) => inlineAssertions value
  | `(nlexpr| persistentHash32($value)) | `(nlexpr| persistentHashNative($value))
  | `(nlexpr| persistentHashPoint($value)) | `(nlexpr| sha256($value))
  | `(nlexpr| sha512($value))
  | `(nlexpr| keccak256($value)) | `(nlexpr| degradeToNative($value))
  | `(nlexpr| upgradeFromNative($value))
  | `(nlexpr| serialize($value, $_:num)) | `(nlexpr| toBytes($value, $_:num))
  | `(nlexpr| fromBytesChecked($_:nltype, $value))
  | `(nlexpr| deserialize($_:nltype, $value))
  | `(nlexpr| encode($_:ident, $value)) | `(nlexpr| decode($_:ident, $value))
  | `(nlexpr| some($value))
  | `(nlexpr| field($value, $_:ident))
  | `(nlexpr| enumTag($value))
  | `(nlexpr| toBytes32($value)) | `(nlexpr| reverseBytes32($value))
  | `(nlexpr| reverseBytes($value)) => inlineAssertions value
  | `(nlexpr| either($tag, $left, $right)) =>
    inlineAssertions tag ++ inlineAssertions left ++ inlineAssertions right
  | `(nlexpr| sliceBytes($value, $_:num, $_:num)) => inlineAssertions value
  | `(nlexpr| concatBytes($left, $right)) => inlineAssertions left ++ inlineAssertions right
  | `(nlexpr| byteAt($value, $_:num)) => inlineAssertions value
  | `(nlexpr| persistentHashVector32([$values,*]))
  | `(nlexpr| persistentHashFab($_:ident, $_:ident, [$values,*]))
  | `(nlexpr| hashToCurveFab($_:ident, $_:ident, [$values,*]))
  | `(nlexpr| sha512Fab($_:ident, $_:ident, [$values,*]))
  | `(nlexpr| persistentHashNativeVector([$values,*]))
  | `(nlexpr| transientHashNativeVector([$values,*])) =>
    values.getElems.toList.flatMap inlineAssertions
  | `(nlexpr| transientHashValue($value)) => inlineAssertions value
  | `(nlexpr| tokenType($domain, $contractAddress)) =>
    inlineAssertions domain ++ inlineAssertions contractAddress
  | `(nlexpr| persistentCommitFab($_:ident, $_:ident, $opening, [$values,*]))
  | `(nlexpr| transientCommitFab($_:ident, $_:ident, $opening, [$values,*])) =>
    inlineAssertions opening ++ values.getElems.toList.flatMap inlineAssertions
  | `(nlexpr| jubjubScalarFromNative($value))
  | `(nlexpr| jubjubScalarToNative($value))
  | `(nlexpr| jubjubMulGenerator($value))
  | `(nlexpr| jubjubNeg($value))
  | `(nlexpr| jubjubX($value))
  | `(nlexpr| jubjubY($value)) => inlineAssertions value
  | `(nlexpr| jubjubMul($point, $scalar)) | `(nlexpr| jubjubAdd($point, $scalar)) =>
    inlineAssertions point ++ inlineAssertions scalar
  | `(nlexpr| jubjubFromCoordinates($x, $y)) => inlineAssertions x ++ inlineAssertions y
  | `(nlexpr| hashToCurve([$values,*])) => values.getElems.toList.flatMap inlineAssertions
  | `(nlexpr| foreignNeg($value)) | `(nlexpr| foreignInv($value))
  | `(nlexpr| curveMulGenerator($value)) | `(nlexpr| curveX($value))
  | `(nlexpr| curveY($value)) | `(nlexpr| foreignToBytes($value)) => inlineAssertions value
  | `(nlexpr| foreignAdd($left, $right)) | `(nlexpr| foreignSub($left, $right))
  | `(nlexpr| foreignMul($left, $right)) | `(nlexpr| curveMul($left, $right))
  | `(nlexpr| curveFromCoordinates($left, $right)) =>
    inlineAssertions left ++ inlineAssertions right
  | `(nlexpr| foreignFromBytes($_:nltype, $value)) => inlineAssertions value
  | `(nlexpr| invoke($_:ident, [$args:nlexpr,*]))
  | `(nlexpr| witness $_:ident($args:nlexpr,*)) => args.getElems.toList.flatMap inlineAssertions
  | `(nlexpr| map([$sequences,*], fun $_:ident* => $body)) =>
    sequences.getElems.toList.flatMap inlineAssertions ++ inlineAssertions body
  | `(nlexpr| fold($initial, [$sequences,*], fun $_:ident* => $body)) =>
    inlineAssertions initial ++ sequences.getElems.toList.flatMap inlineAssertions ++ inlineAssertions body
  | _ => []

private def commonType (stx : Syntax) (left right : Ty) : CommandElabM Ty := do
  if left == right then return left
  match left, right with
  | .uint m, .uint n => pure (.uint (max m n))
  | .native, .uint _ | .uint _, .native => pure .native
  | _, _ => throwErrorAt stx "readable witness expression type mismatch"

private def coerce (stx : Syntax) (value : Lowered) (target : Ty) : CommandElabM Lowered := do
  let .scalar found := value.type | throwErrorAt stx "Unit cannot be used as a scalar expression"
  if found == target then return value
  match found, target with
  | .uint m, .uint n =>
    unless m ≤ n do throwErrorAt stx "readable witness type narrowing needs an explicit cast"
    pure {value with type := .scalar target, term := .cast target value.term}
  | .uint _, .native => pure {value with type := .scalar .native, term := .cast .native value.term}
  | _, _ => throwErrorAt stx "readable witness expression type mismatch"

private def uniqueWitnesses (signatures : List WitnessSignature) : List WitnessSignature :=
  signatures.foldl (fun acc item => if acc.any (·.name == item.name) then acc else acc ++ [item]) []

private def mergeLowered (type : ResultType) (term : Noctium.Helpers.Term) (values : List Lowered) : Lowered := {
  type, term, before := values.flatMap (·.before),
  signatures := uniqueWitnesses (values.flatMap (·.signatures)),
  witnessNames := values.flatMap (·.witnessNames) |>.eraseDups,
  generatedValidity := values.flatMap (·.generatedValidity) |>.eraseDups
}

private def iterationProgram (stx : Syntax) (programName : String)
    (signatures : List WitnessSignature) : ExprM Helpers.Program := do
  let state ← get
  let program ← match state.iterationProgram with
    | some program => pure program
    | none =>
      match Helpers.Wire.attach {
        declarations := [{
          id := ⟨0, 0⟩, name := programName, result := .unit, body := [.return none]
        }]
        witnesses := state.iterationWitnesses
      } (state.codecs.map (·.2)) with
      | .ok program => pure program
      | .error message => throwErrorAt stx message
  let state ← get
  pure {program with
    composites := {
      program.composites with
      structures := (program.composites.structures ++ state.composites.structures).eraseDups
      enumerations := (program.composites.enumerations ++ state.composites.enumerations).eraseDups},
    witnesses := uniqueWitnesses (program.witnesses ++ signatures)}

private def iterationEnvironment (env : SurfaceEnv)
    (staged : List (String × ResultType))
    (parameters : List IterationParameter) : Helpers.Environment :=
  let unresolved := parameters.map (·.reference)
  let locals := env.filterMap fun (_, type, term) =>
    match term with
    | .ref name => if unresolved.contains name then none else some (name, type)
    | _ => none
  locals ++ parameters.flatMap (·.views) ++ staged

private def stageIterationValues (callPrefix : String) (env : SurfaceEnv)
    (span : SourceSpan) (values : List Lowered) :
    ExprM (List Statement × List Helpers.Term × List (String × ResultType)) := do
  let mut statements := []
  let mut terms := []
  let mut staged := []
  for value in values do
    let state ← get
    let mut suffix := state.nextLet
    let pathPrefix := String.intercalate "_" (callPrefix.splitOn ".")
    let mut name := s!"__noctium_iteration_value_{pathPrefix}_{suffix}"
    while env.any (fun item => item.1 == name) ||
        staged.any (fun item => item.1 == name) ||
        ((state.iterationProgram.map fun program =>
          program.declarations.any (fun declaration => declaration.name == name))
          |>.getD _root_.Bool.false) do
      suffix := suffix + 1
      name := s!"__noctium_iteration_value_{pathPrefix}_{suffix}"
    modify fun state => {state with nextLet := suffix + 1}
    statements := statements ++ value.before ++ [.bind name value.type (.at span value.term)]
    terms := terms ++ [.ref name]
    staged := staged ++ [(name, value.type)]
  pure (statements, terms, staged)

private def lowerConditionalArm (stx : Syntax) (programName : String) (env : SurfaceEnv)
    (arm : Lowered) : ExprM Helpers.Term := do
  if arm.before.isEmpty then return arm.term
  let program ← iterationProgram stx programName arm.signatures
  let helperEnv := iterationEnvironment env [] (← get).iterationParameters
  let span ← liftM (spanValue stx)
  -- Keep the arm's statements inside the call guarded by the conditional.
  let operator := Iteration.Operator.anonymous [] (some arm.type)
    (arm.before ++ [.return (some arm.term)])
  match Iteration.applyWithLimits {} program 0 helperEnv span operator [] with
  | .ok (program, term) =>
    modify fun state => {state with iterationProgram := some program}
    pure term
  | .error diagnostic => throwErrorAt stx diagnostic.message

private def selectedCodec (name : TSyntax `ident) : ExprM (Helpers.Wire.Codec × String) := do
  let some ((_, codec), index) := (← get).codecs.zipIdx.find? (fun (candidate, _) => candidate.1 == name.getId)
    | throwErrorAt name s!"add codec '{name.getId}' to the circuit's using clause"
  pure (codec, Helpers.Wire.codecName index)

private def checkedPayloadLayout (site : Syntax) (payload : Types.CompositeType) :
    ExprM Types.CompiledType := do
  let composites := (← get).composites
  match Types.compileType composites payload with
  | .ok compiled => pure compiled
  | .error diagnostic => throwErrorAt site diagnostic.message

private def checkedFieldlessEnumMembers (site : Syntax) (payload : Types.CompositeType) :
    ExprM (List String) := do
  let compiled ← checkedPayloadLayout site payload
  let .enumeration _ _ _ 0 _ variants := compiled.checked.value
    | throwErrorAt site "expected a checked fieldless enum"
  unless variants.all (·.2.1.isEmpty) do
    throwErrorAt site "expected a checked fieldless enum"
  pure (variants.map Prod.fst)

private def zeroSourceLeaf (site : Syntax) : Ty → ExprM Helpers.Term
  | .native => pure (.native 0)
  | .bool => pure (.bool _root_.Bool.false)
  | .uint maximum => pure (.uint maximum 0)
  | type => throwErrorAt site s!"typed composite zero does not support source leaf type '{typeName type}'"

private def zeroScalarTerm (site : Syntax) (type : Ty) : ExprM Helpers.Term := do
  match type with
  | .native | .bool | .uint _ => zeroSourceLeaf site type
  | .bytes 32 => pure (.bytes32Literal (List.replicate 32 0))
  | .bytes length => pure (.bytes (.bytesLiteral length (List.replicate length 0)) [])
  | .jubjubScalar => pure (.curve .scalarFromNative [.native 0])
  | .jubjubPoint => pure (.curve .fromCoordinates [.native 0, .native 1])
  | .foreign kind =>
    match kind with
    | .base _ | .scalar _ =>
      let encoding ← match Foreign.encodeField kind 0 with
        | .ok encoding => pure encoding
        | .error message => throwErrorAt site message
      pure (.foreignConstant kind encoding)
    | .point curve => pure (.foreignConstant kind (Foreign.identityEncoding curve))
  | _ => throwErrorAt site s!"readable scalar default does not support type '{typeName type}'"

private def zeroPayloadLeaves (site : Syntax) (compiled : Types.CompiledType) :
    ExprM (List Helpers.Term) :=
  (Helpers.sourceLeafTypes compiled.checked.value).mapM (zeroScalarTerm site)

private def compositeMaybeType (programName : String) (site : Syntax)
    (payload : Types.CompositeType) (fingerprint : String) : ExprM Types.CompositeType := do
  let typeId := s!"{programName}.MaybeComposite{hash fingerprint}"
  unless Types.validDeclId typeId do
    throwErrorAt site "generated composite Maybe type id is invalid"
  let expectedFields : List (String × Types.CompositeType) := [
    ("is_some", .scalar .bool),
    ("value", payload)
  ]
  let state ← get
  if state.composites.enumerations.any (·.id == typeId) then
    throwErrorAt site s!"composite Maybe type id '{typeId}' collides with an enum"
  match state.composites.structures.find? (·.id == typeId) with
  | some existing =>
    unless existing.fields.map (fun field => (field.name, field.type)) == expectedFields do
      throwErrorAt site s!"composite Maybe type id '{typeId}' collides with another structure"
  | none =>
    modify fun state => {state with composites := {
      state.composites with
      structures := state.composites.structures ++ [{
        id := typeId
        fields := expectedFields.map fun (name, type) => {name, type}
      }]}}
  pure (.structure typeId)

private def scalarMaybeType (programName : String) (stx : Syntax) (payloadType : Ty) :
    ExprM Types.CompositeType := do
  let typeId ← match Types.Maybe.scalarTypeId programName payloadType with
    | .ok value => pure value
    | .error message => throwErrorAt stx message
  let environment ← match Types.Maybe.scalarEnvironment typeId payloadType with
    | .ok value => pure value
    | .error message => throwErrorAt stx message
  let some declaration := environment.structures.head?
    | throwErrorAt stx "scalar Maybe schema has no structure declaration"
  let state ← get
  if state.composites.enumerations.any (·.id == typeId) then
    throwErrorAt stx s!"scalar Maybe type id '{typeId}' collides with an enum"
  match state.composites.structures.find? (·.id == typeId) with
  | some existing =>
    unless existing.fields.map (fun field => (field.name, field.type)) ==
        declaration.fields.map (fun field => (field.name, field.type)) do
      throwErrorAt stx s!"scalar Maybe type id '{typeId}' collides with another structure"
  | none =>
    modify fun state => {state with composites := {
      state.composites with
      structures := state.composites.structures ++ [declaration]}}
  pure (Types.Maybe.scalarType typeId)

private def scalarMaybeZero : Ty → Option Noctium.Helpers.Term
  | .native => some (.native 0)
  | .bool => some (.bool _root_.Bool.false)
  | .uint maximum => some (.uint maximum 0)
  | _ => none

private def compositeEitherType (programName : String) (site : Syntax)
    (left right : Types.CompositeType) (fingerprint : String) : ExprM Types.CompositeType := do
  let typeId := s!"{programName}.EitherComposite{hash fingerprint}"
  unless Types.validDeclId typeId do
    throwErrorAt site "generated composite Either type id is invalid"
  let expectedFields : List (String × Types.CompositeType) := [
    ("is_left", .scalar .bool),
    ("left", left),
    ("right", right)
  ]
  let state ← get
  if state.composites.enumerations.any (·.id == typeId) then
    throwErrorAt site s!"composite Either type id '{typeId}' collides with an enum"
  match state.composites.structures.find? (·.id == typeId) with
  | some existing =>
    unless existing.fields.map (fun field => (field.name, field.type)) == expectedFields do
      throwErrorAt site s!"composite Either type id '{typeId}' collides with another structure"
  | none =>
    modify fun state => {state with composites := {
      state.composites with
      structures := state.composites.structures ++ [{
        id := typeId
        fields := expectedFields.map fun (name, type) => {name, type}
      }]}}
  pure (.structure typeId)

private def nominalBytes32ForCodec? (codec : Helpers.Wire.Codec) :
    Option NominalBytes32 :=
  if codec.frameBytes != 32 then none else
  match codec.payload with
  | .structure id => do
    let kind ← [NominalBytes32.contractAddress, .userAddress, .zswapCoinPublicKey].find? fun candidate =>
      candidate.declarationId == id
    let some declaration := codec.composites.structures.find? (·.id == id) | none
    let [field] := declaration.fields | none
    if field.name == "bytes" && field.type == .bytes 32 then some kind else none
  | _ => none

private partial def nominalBytes32OfOutput? (state : AuthoringExprState)
    (source : TSyntax `nlexpr) : Option NominalBytes32 := do
  match source with
  | `(nlexpr| disclose($value)) => nominalBytes32OfOutput? state value
  | `(nlexpr| encode($codecName:ident, $_value:nlexpr)) => do
    let some (_, codec) := state.codecs.find? (·.1 == codecName.getId) | none
        nominalBytes32ForCodec? codec
  | _ => none

private def lowerProjection (stx : Syntax) (value : Lowered)
    (projection : Types.Projection) : ExprM Lowered := do
  let .composite parent := value.type | throwErrorAt stx "projection requires an aggregate value"
  let composites := (← get).composites
  let span ← spanValue stx
  let child ← match Helpers.projectedType composites span parent projection with
    | .ok child => pure child
    | .error diagnostic => throwErrorAt stx diagnostic.message
  pure {value with type := Helpers.resultTypeOfComposite child, term := .project value.term projection}

private def sequenceItems (site : Syntax) (type : ResultType) (source : Helpers.Term)
    (start : Nat := 0) (stop? : Option Nat := none) : ExprM (List Lowered) :=
  let count (length : Nat) : ExprM Nat := do
    let stop := stop?.getD length
    unless start ≤ stop && stop ≤ length do
      throwErrorAt site "slice requires start ≤ stop ≤ sequence length"
    pure (stop - start)
  match type with
  | .unit => do
    let _ ← count 0
    pure []
  | .composite (.tuple types) => do
    let length ← count types.length
    pure (((types.drop start).take length).zipIdx.map fun (type, index) =>
      {type := Helpers.resultTypeOfComposite type, term := .project source (.tupleIndex (start + index))})
  | .composite (.vector length type) => do
    pure ((List.range (← count length)).map fun index =>
      {type := Helpers.resultTypeOfComposite type, term := .project source (.vectorIndex (start + index))})
  | .composite (.bytes length) => do
    pure ((List.range (← count length)).map fun index =>
      {type := .scalar (.uint 255), term := .project source (.byteIndex (start + index))})
  | .scalar (.bytes length) => do
    pure ((List.range (← count length)).map fun index =>
      {type := .scalar (.uint 255), term := .bytesAt source (start + index)})
  | _ => throwErrorAt site "expected a tuple, vector, fixed Bytes or Unit"

private def checkedSequenceTerm (site : Syntax) (payload : Types.CompositeType)
    (fields : List Lowered) : ExprM Helpers.Term := do
  let compiled ← checkedPayloadLayout site payload
  let layouts ← match compiled.checked.value with
    | .tuple layouts => pure layouts
    | .vector length element => pure (List.replicate length element)
    | _ => throwErrorAt site "checked sequence layout mismatch"
  unless fields.length == layouts.length do
    throwErrorAt site "checked sequence length mismatch"
  let span ← liftM (spanValue site)
  let leaves ← (fields.zip layouts).flatMapM fun (value, layout) => do
    match Helpers.Iteration.flattenResult span value.type layout value.term with
    | .ok leaves => pure leaves
    | .error diagnostic => throwErrorAt site diagnostic.message
  pure (.composite payload leaves)

private def vectorPayload (site : Syntax) (codecName : Option (TSyntax `ident))
    (items : List Types.CompositeType) : ExprM Types.CompositeType := do
  match codecName with
  | some name =>
    let (codec, _) ← selectedCodec name
    let .vector length element := codec.payload
      | throwErrorAt name "vector requires a fixed vector Payload codec"
    unless items.length == length do
      throwErrorAt site "vector element count does not match its declared length"
    unless items.all (·.isSubtype element) do
      throwErrorAt site "vector element has an incompatible declared type"
    pure codec.payload
  | none =>
    let first :: rest := items
      | throwErrorAt site "empty vector construction requires a fixed vector Payload codec"
    let element ← rest.foldlM (fun common next => do
      let some joined := common.leastUpperBound? next
        | throwErrorAt site "vector elements have no common type"
      pure joined) first
    pure (.vector items.length element)

private def byteSegments (site : Syntax) (spread : _root_.Bool) (value : Lowered) :
    ExprM (List (Nat × Helpers.Term)) := do
  if spread then
    if let .scalar (.bytes length) := value.type then
      return if length == 0 then [] else [(length, value.term)]
  let items ← if spread then sequenceItems site value.type value.term else pure [value]
  items.mapM fun item => do
    let .scalar (.uint maximum) := item.type
      | throwErrorAt site "packBytes element requires an unsigned type within UInt8"
    unless maximum ≤ 255 do
      throwErrorAt site "packBytes element requires an unsigned type within UInt8"
    pure (1, .bytes (.serialize (.uint maximum) 1) [item.term])

private partial def joinByteSegments : List (Nat × Helpers.Term) → Nat × Helpers.Term
  | [] => (0, .bytes (.bytesLiteral 0 []) [])
  | [part] => part
  | parts =>
    let (left, right) := parts.splitAt (parts.length / 2)
    let (leftLength, left) := joinByteSegments left
    let (rightLength, right) := joinByteSegments right
    (leftLength + rightLength, .bytes (.concatBytes leftLength rightLength) [left, right])

private def lowerForeignFieldConstant (stx : Syntax) (kind : Foreign.Kind) (value : Nat) : ExprM Lowered := do
  let encoding ← match Foreign.encodeField kind value with
    | .ok encoding => pure encoding
    | .error message => throwErrorAt stx message
  pure {type := .scalar (.foreign kind), term := .foreignConstant kind encoding}

private def lowerForeignPointConstant (stx : Syntax) (curve : Foreign.Curve)
    (x y : Nat) : ExprM Lowered := do
  let encoding ← match Foreign.encodePoint curve (.affine x y) with
    | .ok encoding => pure encoding
    | .error message => throwErrorAt stx message
  pure {
    type := .scalar (.foreign (.point curve))
    term := .foreignConstant (.point curve) encoding
  }

private def freshReadableLet (id : Ident) : ExprM String := do
  let ordinal := (← get).nextLet
  modify fun state => {state with nextLet := ordinal + 1}
  pure s!"__noctium_let_{ordinal}_{id.getId}"

private partial def lowerExpr (programName callPrefix : String) (env : SurfaceEnv)
    (stx : TSyntax `nlexpr) : ExprM Lowered := do
  match stx with
  | `(nlexpr| $id:ident) =>
    match env.find? (fun value => value.1 == id.getId.toString) with
    | some (_, type, term) =>
      if let .ref refName := term then
        match (← get).iterationParameters.find? (·.reference == refName) with
        | some parameter =>
          match parameter.views with
          | [(viewName, viewType)] => pure {type := viewType, term := .ref viewName}
          | [] => throwErrorAt id s!"cannot infer the type of empty tuple item '{parameter.surfaceName}'. Use a typed binding or loop annotation"
          | _ => throwErrorAt id s!"empty tuple item '{parameter.surfaceName}' has multiple inferred types. Use a typed binding"
        | none => pure {type, term}
      else pure {type, term}
    | none => throwErrorAt id s!"unknown readable witness value '{id.getId}'"
  | `(nlexpr| $n:num) =>
    if n.getNat ≥ Field.modulus then throwErrorAt n "Native literal is not canonical"
    pure {type := .scalar .native, term := .native n.getNat}
  | `(nlexpr| true) => pure {type := .scalar .bool, term := .bool _root_.Bool.true}
  | `(nlexpr| false) => pure {type := .scalar .bool, term := .bool _root_.Bool.false}
  | `(nlexpr| either($tagSource, $leftSource, $rightSource)) => do
    let tag ← lowerExpr programName callPrefix env tagSource
    unless tag.type == .scalar .bool do
      throwErrorAt tagSource "Either tag requires Bool"
    let left ← lowerExpr programName callPrefix env leftSource
    let right ← lowerExpr programName callPrefix env rightSource
    let leftLayout := left.layoutType
    let rightLayout := right.layoutType
    let leftCompiled ← checkedPayloadLayout stx leftLayout
    let rightCompiled ← checkedPayloadLayout stx rightLayout
    let zerosLeft ← zeroPayloadLeaves stx leftCompiled
    let zerosRight ← zeroPayloadLeaves stx rightCompiled
    let fingerprint :=
      s!"{leftCompiled.fingerprint.length}:{leftCompiled.fingerprint}{rightCompiled.fingerprint.length}:{rightCompiled.fingerprint}"
    let eitherType ← compositeEitherType programName stx leftLayout rightLayout fingerprint
    let span ← liftM (spanValue stx)
    let (before, terms, _) ← stageIterationValues callPrefix env span [tag, left, right]
    let [tagTerm, leftTerm, rightTerm] := terms
      | throwErrorAt stx "composite Either argument staging failed"
    let leftLeaves ← match Helpers.Iteration.flattenResult span left.type
        leftCompiled.checked.value leftTerm with
      | .ok leaves => pure leaves
      | .error diagnostic => throwErrorAt stx diagnostic.message
    let rightLeaves ← match Helpers.Iteration.flattenResult span right.type
        rightCompiled.checked.value rightTerm with
      | .ok leaves => pure leaves
      | .error diagnostic => throwErrorAt stx diagnostic.message
    unless leftLeaves.length == zerosLeft.length && rightLeaves.length == zerosRight.length do
      throwErrorAt stx "composite Either payload leaf count mismatch"
    let selectedLeft := (leftLeaves.zip zerosLeft).map fun (payload, zero) =>
      Helpers.Term.select tagTerm payload zero
    let selectedRight := (zerosRight.zip rightLeaves).map fun (zero, payload) =>
      Helpers.Term.select tagTerm zero payload
    let result := mergeLowered (.composite eitherType)
      (.composite eitherType (tagTerm :: selectedLeft ++ selectedRight))
      [tag, left, right]
    pure {result with before}
  | `(nlexpr| some($source)) => do
    let value ← lowerExpr programName callPrefix env source
    match value.type with
    | .scalar payloadType => do
      let maybeType ← scalarMaybeType programName stx payloadType
      pure (mergeLowered (.composite maybeType)
        (.composite maybeType [.bool _root_.Bool.true, value.term]) [value])
    | .composite payloadType => do
      let compiled ← checkedPayloadLayout stx payloadType
      let maybeType ← compositeMaybeType programName stx payloadType compiled.fingerprint
      let span ← liftM (spanValue stx)
      let (before, terms, _) ← stageIterationValues callPrefix env span [value]
      let some stagedPayload := terms.head?
        | throwErrorAt stx "composite some payload staging failed"
      let payloadLeaves ← match Helpers.Iteration.flattenResult span value.type
          compiled.checked.value stagedPayload with
        | .ok leaves => pure leaves
        | .error diagnostic => throwErrorAt stx diagnostic.message
      let stagedValue := {value with before}
      pure (mergeLowered (.composite maybeType)
        (.composite maybeType (.bool _root_.Bool.true :: payloadLeaves)) [stagedValue])
    | .unit => throwErrorAt stx "some does not accept Unit"
  | `(nlexpr| none($type:nltype)) => do
    let payloadType ← liftM (readScalarTy type)
    let maybeType ← scalarMaybeType programName stx payloadType
    let zero ← match scalarMaybeZero payloadType with
      | some zero => pure zero
      | none => throwErrorAt type "none requires a Native, Bool, or UInt scalar"
    pure (mergeLowered (.composite maybeType)
      (.composite maybeType [.bool _root_.Bool.false, zero]) [])
  | `(nlexpr| none(Payload $name:ident)) => do
    let (codec, _) ← selectedCodec name
    let compiled ← checkedPayloadLayout name codec.payload
    match codec.payload with
    | .scalar payloadType => do
      let maybeType ← scalarMaybeType programName name payloadType
      let zero ← match scalarMaybeZero payloadType with
        | some zero => pure zero
        | none => throwErrorAt name "none requires a Native, Bool, or UInt scalar payload"
      pure (mergeLowered (.composite maybeType)
        (.composite maybeType [.bool _root_.Bool.false, zero]) [])
    | .unit => do
      let maybeType ← compositeMaybeType programName name .unit compiled.fingerprint
      pure (mergeLowered (.composite maybeType)
        (.composite maybeType [.bool _root_.Bool.false]) [])
    | payloadType => do
      let zeros ← zeroPayloadLeaves name compiled
      let maybeType ← compositeMaybeType programName name payloadType compiled.fingerprint
      pure (mergeLowered (.composite maybeType)
        (.composite maybeType (.bool _root_.Bool.false :: zeros)) [])
  | `(nlexpr| default(Payload $name:ident)) => do
    let (codec, _) ← selectedCodec name
    let compiled ← checkedPayloadLayout name codec.payload
    let zeros ← zeroPayloadLeaves name compiled
    let resultType := Helpers.resultTypeOfComposite codec.payload
    let term := Helpers.Term.composite codec.payload zeros
    pure {type := resultType, term}
  | `(nlexpr| default($target:nltype)) => do
    let payloadType ← liftM (readScalarTy target)
    let term ← zeroScalarTerm target payloadType
    pure {type := .scalar payloadType, term}
  | `(nlexpr| record(Payload $name:ident, { $fields,* })) => do
    let (codec, _) ← selectedCodec name
    let .structure id := codec.payload
      | throwErrorAt name "record requires a nominal structure Payload codec"
    let compiled ← checkedPayloadLayout name codec.payload
    let .structure _ layoutFields := compiled.checked.value
      | throwErrorAt name "checked record Payload has a non-structure layout"
    let some declaration := compiled.environment.structures.find? (·.id == id)
      | throwErrorAt name "checked record Payload has no structure declaration"
    let mut spread : Option (TSyntax `nlexpr) := none
    let mut initializers : List (String × TSyntax `nlexpr) := []
    for (field, index) in fields.getElems.toList.zipIdx do
      let some (fieldName, source) := recordField field
        | throwErrorAt field "invalid record field initializer"
      let some fieldName := fieldName
        | unless index == 0 do throwErrorAt field "record spread must appear once, before named fields"
          spread := some source
          continue
      let key := fieldName.getId.toString
      if initializers.any (·.1 == key) then
        throwErrorAt fieldName s!"duplicate record field '{key}'"
      unless declaration.fields.any (·.name == key) do
        throwErrorAt fieldName s!"unknown record field '{key}'"
      initializers := initializers ++ [(key, source)]
    let span ← liftM (spanValue stx)
    let (spreadBefore, base) ← match spread with
      | none => pure ([], none)
      | some source => do
        let expected := ResultType.composite codec.payload
        let value ← match ← lowerExpectedIterationRef env expected source with
          | some value => pure value
          | none => lowerExpr programName callPrefix env source
        unless value.type == expected do
          throwErrorAt source "record spread requires the same nominal Payload type"
        let (before, references, _) ← stageIterationValues callPrefix env span [value]
        let [reference] := references
          | throwErrorAt source "record spread value staging failed"
        pure (before, some (value, reference))
    -- The pinned Compact compiler evaluates named initializers in declaration order.
    let values ← layoutFields.mapM fun (key, _) => do
      let some declared := declaration.fields.find? (·.name == key)
        | throwErrorAt stx s!"checked record field '{key}' has no declaration"
      let expected := Helpers.resultTypeOfComposite declared.type
      let some (_, source) := initializers.find? (·.1 == key)
        | match base with
          | some (_, reference) => pure {type := expected, term := .project reference (.field key)}
          | none => throwErrorAt stx s!"missing record field '{key}'"
      let value ← match ← lowerExpectedIterationRef env expected source with
        | some value => pure value
        | none => lowerExpr programName callPrefix env source
      match expected with
      | .scalar target => coerce source value target
      | _ => do
        let matchingBytes := match value.type, declared.type with
          | .scalar (.bytes actual), .bytes wanted => actual == wanted
          | _, _ => _root_.Bool.false
        unless value.type == expected || matchingBytes do
          throwErrorAt source s!"record field '{key}' has the wrong Payload type"
        pure value
    let (before, terms, _) ← stageIterationValues callPrefix env span values
    let leaves ← (layoutFields.zip (values.zip terms)).flatMapM fun ((_, layout), value, reference) => do
      match Helpers.Iteration.flattenResult span value.type layout reference with
      | .ok leaves => pure leaves
      | .error diagnostic => throwErrorAt stx diagnostic.message
    let result := mergeLowered (.composite codec.payload) (.composite codec.payload leaves)
      (base.toList.map Prod.fst ++ values)
    pure {result with before := spreadBefore ++ before}
  | `(nlexpr| tuple($items,*)) | `(nlexpr| packBytes($items,*))
  | `(nlexpr| vector($items,*)) | `(nlexpr| vector(Payload $_:ident, [$items,*])) => do
    let pack := stx.raw.getKind == ``readablePackBytes
    let arguments ← items.getElems.toList.mapM fun item => do
      let some (spread, source) := tupleItem item
        | throwErrorAt item "invalid sequence construction argument"
      let value ← match source with
        | `(nlexpr| $number:num) =>
          if pack && !spread then
            let n := number.getNat
            pure {type := .scalar (.uint n), term := .uint n n}
          else lowerExpr programName callPrefix env source
        | _ => lowerExpr programName callPrefix env source
      pure (spread, source, value)
    let values := arguments.map fun (_, _, value) => value
    let span ← liftM (spanValue stx)
    let (before, references, _) ← stageIterationValues callPrefix env span values
    modify fun state => {state with requiresOutputViews := _root_.Bool.true}
    if pack then
      let mut parts := []
      let mut length := 0
      for ((spread, source, value), reference) in arguments.zip references do
        let segments ← byteSegments source spread {value with term := reference}
        length := length + (segments.map Prod.fst).sum
        if length > Types.defaultLimits.maxVectorLength then
          throwErrorAt source "packBytes exceeds the fixed byte-string length limit"
        parts := segments :: parts
      let (_, term) := joinByteSegments parts.reverse.flatten
      return {mergeLowered (.scalar (.bytes length)) term values with before}
    let mut parts : List (List Lowered) := []
    let mut size := 1
    for ((spread, source, value), reference) in arguments.zip references do
      let fields ← if spread then sequenceItems source value.type reference
        else pure [{type := value.type, term := reference}]
      size := size + fields.length
      if size > Types.defaultLimits.maxLayoutNodes then
        throwErrorAt source "tuple construction exceeds the layout node limit"
      parts := fields :: parts
    let fields := parts.reverse.flatten
    let layouts := fields.map Lowered.layoutType
    let payload ← match stx with
      | `(nlexpr| vector(Payload $codec:ident, [$_items,*])) =>
        vectorPayload stx (some codec) layouts
      | _ =>
        if stx.raw.getKind == ``readableVector then vectorPayload stx none layouts
        else pure (.tuple layouts)
    let term ← checkedSequenceTerm stx payload fields
    pure {mergeLowered (.composite payload) term values with before}
  | `(nlexpr| uint($n:num)) => do
    match ScalarPolicy.validate (.uint n.getNat) with
    | .error message => throwErrorAt stx message
    | .ok _ => pure {type := .scalar (.uint n.getNat), term := .uint n.getNat n.getNat}
  | `(nlexpr| map([$sequences,*], fun $parameters:ident* => $body)) => do
    let sequenceSources := sequences.getElems.toList
    if sequenceSources.isEmpty then throwErrorAt stx "map requires at least one sequence"
    let mut values := []
    for source in sequenceSources do
      values := values ++ [← lowerExpr programName callPrefix env source]
    let sourceSpan ← liftM (spanValue stx)
    let (before, terms, staged) ← stageIterationValues callPrefix env sourceSpan values
    let program ← iterationProgram stx programName (values.flatMap (·.signatures))
    let helperEnv := iterationEnvironment env staged (← get).iterationParameters
    let elementTypes ← match Iteration.sequenceElementTypesWithLimits {}
        program 0 helperEnv sourceSpan terms with
      | .ok elementTypes => pure elementTypes
      | .error diagnostic => throwErrorAt stx diagnostic.message
    let parameterNames := parameters.toList
    unless parameterNames.length == terms.length do
      throwErrorAt stx "map callback parameter count must match its sequence count"
    unless (parameterNames.map (·.getId.toString) |>.eraseDups).length == parameterNames.length do
      throwErrorAt stx "duplicate iteration callback parameter"
    modify fun state => {state with
      iterationProgram := some program
      requiresOutputViews := _root_.Bool.true}
    let bindings ← prepareCallbackParameters parameterNames elementTypes
    let callback ← lowerExpr programName (callPrefix ++ ".map")
      (callbackSurfaceEnv bindings ++ env) body
    let callbackState ← get
    let localRefs := bindings.filterMap fun binding =>
      if binding.type.isNone then some binding.reference else none
    let localViews := iterationViewBindings callbackState.iterationParameters localRefs
    let retainedParameters := retainIterationScope callbackState.iterationParameters localRefs
    modify fun state => {state with iterationParameters := retainedParameters}
    let helperEnv := iterationEnvironment env staged retainedParameters
    let operatorParameters := bindings.map fun binding =>
      {name := binding.reference, type := none}
    let operator := Iteration.Operator.anonymous
      operatorParameters none
      (localViews ++ callback.before ++ [.return (some callback.term)])
    let program ← iterationProgram stx programName
      (values.flatMap (·.signatures) ++ callback.signatures)
    let (compiledProgram, term) ←
      match Iteration.mapWithLimits {} program 0 helperEnv sourceSpan terms operator with
      | .ok result => pure result
      | .error diagnostic => throwErrorAt stx diagnostic.message
    let type ← match Helpers.inferWithLimits {} compiledProgram 0 helperEnv sourceSpan term with
      | .ok value => pure value.ty
      | .error diagnostic => throwErrorAt stx diagnostic.message
    modify fun state => {state with
      iterationProgram := some compiledProgram
      iterationWitnesses := compiledProgram.witnesses
      requiresOutputViews := _root_.Bool.true}
    pure {
      type, term, before
      signatures := uniqueWitnesses (values.flatMap (·.signatures) ++ callback.signatures)
      witnessNames := (values.flatMap (·.witnessNames) ++ callback.witnessNames).eraseDups
      generatedValidity :=
        (values.flatMap (·.generatedValidity) ++ callback.generatedValidity).eraseDups
    }
  | `(nlexpr| fold($initial, [$sequences,*], fun $parameters:ident* => $body)) => do
    let sequenceSources := sequences.getElems.toList
    if sequenceSources.isEmpty then throwErrorAt stx "fold requires at least one sequence"
    let initial ← lowerExpr programName callPrefix env initial
    let mut values := [initial]
    for source in sequenceSources do
      values := values ++ [← lowerExpr programName callPrefix env source]
    let sourceSpan ← liftM (spanValue stx)
    let (before, terms, staged) ← stageIterationValues callPrefix env sourceSpan values
    let program ← iterationProgram stx programName (values.flatMap (·.signatures))
    let helperEnv := iterationEnvironment env staged (← get).iterationParameters
    let elementTypes ← match Iteration.sequenceElementTypesWithLimits {}
        program 0 helperEnv sourceSpan (terms.drop 1) with
      | .ok elementTypes => pure elementTypes
      | .error diagnostic => throwErrorAt stx diagnostic.message
    let parameterNames := parameters.toList
    unless parameterNames.length == elementTypes.length + 1 do
      throwErrorAt stx "fold callback needs an accumulator and one parameter per sequence"
    unless (parameterNames.map (·.getId.toString) |>.eraseDups).length == parameterNames.length do
      throwErrorAt stx "duplicate iteration callback parameter"
    modify fun state => {state with
      iterationProgram := some program
      requiresOutputViews := _root_.Bool.true}
    let bindings ← prepareCallbackParameters parameterNames
      (some initial.type :: elementTypes)
    let callback ← lowerExpr programName (callPrefix ++ ".fold")
      (callbackSurfaceEnv bindings ++ env) body
    let callbackState ← get
    let localRefs := bindings.filterMap fun binding =>
      if binding.type.isNone then some binding.reference else none
    let localViews := iterationViewBindings callbackState.iterationParameters localRefs
    let retainedParameters := retainIterationScope callbackState.iterationParameters localRefs
    modify fun state => {state with iterationParameters := retainedParameters}
    let helperEnv := iterationEnvironment env staged retainedParameters
    let operatorParameters := bindings.map fun binding =>
      {name := binding.reference, type := none}
    let operator := Iteration.Operator.anonymous
      operatorParameters none
      (localViews ++ callback.before ++ [.return (some callback.term)])
    let program ← iterationProgram stx programName
      (values.flatMap (·.signatures) ++ callback.signatures)
    let (compiledProgram, term) ←
      match Iteration.foldWithLimits {} program 0 helperEnv sourceSpan
        terms.head! (terms.drop 1) operator with
      | .ok result => pure result
      | .error diagnostic => throwErrorAt stx diagnostic.message
    let type ← match Helpers.inferWithLimits {} compiledProgram 0 helperEnv sourceSpan term with
      | .ok value => pure value.ty
      | .error diagnostic => throwErrorAt stx diagnostic.message
    modify fun state => {state with
      iterationProgram := some compiledProgram
      iterationWitnesses := compiledProgram.witnesses
      requiresOutputViews := _root_.Bool.true}
    pure {
      type, term, before
      signatures := uniqueWitnesses (values.flatMap (·.signatures) ++ callback.signatures)
      witnessNames := (values.flatMap (·.witnessNames) ++ callback.witnessNames).eraseDups
      generatedValidity :=
        (values.flatMap (·.generatedValidity) ++ callback.generatedValidity).eraseDups
    }
  | `(nlexpr| let $id:ident := $value:nlexpr in $body:nlexpr) => do
    let value ← lowerExpr programName callPrefix env value
    let internalName ← freshReadableLet id
    let ref := Noctium.Helpers.Term.ref internalName
    let body ← lowerExpr programName callPrefix ((id.getId.toString, value.type, ref) :: env) body
    pure
      { body with
        before := value.before ++ [.bind internalName value.type value.term] ++ body.before,
        signatures := uniqueWitnesses (value.signatures ++ body.signatures),
        witnessNames := (value.witnessNames ++ body.witnessNames).eraseDups,
        generatedValidity := (value.generatedValidity ++ body.generatedValidity).eraseDups }
  | `(nlexpr| do $steps:noctium_callback_step* return $result:nlexpr end) => do
    let mut localEnv := env
    let mut loweredSteps := []
    for step in steps do
      let some (binder, source) := callbackStep step
        | throwErrorAt step "invalid readable callback statement"
      let span ← liftM (spanValue step)
      match binder with
      | some id =>
        let value ← lowerExpr programName callPrefix localEnv source
        let name ← freshReadableLet id
        localEnv := (id.getId.toString, value.type, .ref name) :: localEnv
        loweredSteps := {value with before := value.before ++
          [.bind name value.type (.at span value.term)]} :: loweredSteps
      | none =>
        let allowAssertThen := (← get).allowAssertThen
        modify fun state => {state with allowAssertThen := _root_.Bool.true}
        let value ← lowerExpr programName callPrefix localEnv source
        modify fun state => {state with allowAssertThen}
        let value ← coerce source value .bool
        loweredSteps := {value with before := value.before ++
          [.assert (.at span value.term)]} :: loweredSteps
    let result ← lowerExpr programName callPrefix localEnv result
    pure (mergeLowered result.type result.term (loweredSteps.reverse ++ [result]))
  | `(nlexpr| assertThen($condition, $body)) => do
    unless (← get).allowAssertThen do
      throwErrorAt stx "assertThen is accepted only inside an explicit prove statement"
    let condition ← lowerExpr programName callPrefix env condition
    let condition ← coerce stx condition .bool
    let body ← lowerExpr programName callPrefix env body
    pure
      { body with
        before := condition.before ++ [.assert condition.term] ++ body.before,
        signatures := uniqueWitnesses (condition.signatures ++ body.signatures),
        witnessNames := (condition.witnessNames ++ body.witnessNames).eraseDups,
        generatedValidity := (condition.generatedValidity ++ body.generatedValidity).eraseDups }
  | `(nlexpr| cast($target:nltype, $value:nlexpr)) => do
    let target ← readScalarTy target
    let value ← lowerExpr programName callPrefix env value
    let .scalar source := value.type | throwErrorAt stx "cannot cast Unit"
    if source.isJubjub || target.isJubjub then
      throwErrorAt stx "Jubjub values require an explicitly supported curve route"
    if source.isBytes || target.isBytes then
      throwErrorAt stx "byte strings do not support scalar casts"
    pure {value with
      type := .scalar target,
      term := .cast target value.term,
      generatedValidity := (s!"checked cast {renderExpr stx}") :: value.generatedValidity
    }
  | `(nlexpr| disclose($value)) => do
    let value ← lowerExpr programName callPrefix env value
    pure {value with term := .disclose (← liftM (spanValue stx)) value.term}
  | `(nlexpr| add($left, $right)) => lowerArithmetic programName callPrefix env stx .add left right
  | `(nlexpr| sub($left, $right)) => lowerArithmetic programName callPrefix env stx .sub left right
  | `(nlexpr| mul($left, $right)) => lowerArithmetic programName callPrefix env stx .mul left right
  | `(nlexpr| eq($left, $right)) => do
    let left ← lowerExpr programName callPrefix env left
    let right ← lowerExpr programName callPrefix env right
    match left.type, right.type with
    | .composite leftType, .composite rightType => do
      unless (leftType.leastUpperBound? rightType).isSome do
        let message := match leftType, rightType with
          | .enumeration _, .enumeration _ => "eq enum operands must have the same nominal type"
          | .structure _, .structure _ => "eq record operands must have the same nominal type"
          | _, _ => "eq aggregate operands must have compatible checked types"
        throwErrorAt stx message
      modify fun state => {state with requiresOutputViews := _root_.Bool.true}
      pure (mergeLowered (.scalar .bool) (.eq left.term right.term) [left, right])
    | .composite _, _ | _, .composite _ =>
      throwErrorAt stx "eq aggregate operands must have compatible checked types"
    | _, _ => do
      let .scalar leftTy := left.type | throwErrorAt stx "eq does not accept Unit"
      let .scalar rightTy := right.type | throwErrorAt stx "eq does not accept Unit"
      let ty ← commonType stx leftTy rightTy
      let left ← coerce stx left ty
      let right ← coerce stx right ty
      pure (mergeLowered (.scalar .bool) (.eq left.term right.term) [left, right])
  | `(nlexpr| boolAnd($left, $right)) => do
    let left ← lowerExpr programName callPrefix env left
    let right ← lowerExpr programName callPrefix env right
    unless left.type == .scalar .bool && right.type == .scalar .bool do
      throwErrorAt stx "boolAnd operands require Bool"
    pure (mergeLowered (.scalar .bool) (.boolAnd left.term right.term) [left, right])
  | `(nlexpr| boolOr($left, $right)) => do
    let left ← lowerExpr programName callPrefix env left
    let right ← lowerExpr programName callPrefix env right
    unless left.type == .scalar .bool && right.type == .scalar .bool do
      throwErrorAt stx "boolOr operands require Bool"
    pure (mergeLowered (.scalar .bool) (.boolOr left.term right.term) [left, right])
  | `(nlexpr| andThen($left, $right)) | `(nlexpr| orElse($left, $right)) => do
    let leftValue ← lowerExpr programName callPrefix env left
    let rightValue ← lowerExpr programName callPrefix env right
    unless leftValue.type == .scalar .bool && rightValue.type == .scalar .bool do
      throwErrorAt stx "short-circuit operands require Bool"
    let rightTerm ← lowerConditionalArm right programName env rightValue
    let term := match stx with
      | `(nlexpr| andThen($_left, $_right)) => Helpers.Term.andThen leftValue.term rightTerm
      | _ => Helpers.Term.orElse leftValue.term rightTerm
    modify fun state => {state with requiresOutputViews := _root_.Bool.true}
    let result := mergeLowered (.scalar .bool) term [leftValue, rightValue]
    pure {result with before := leftValue.before}
  | `(nlexpr| boolXor($left, $right)) => do
    let left ← lowerExpr programName callPrefix env left
    let right ← lowerExpr programName callPrefix env right
    unless left.type == .scalar .bool && right.type == .scalar .bool do
      throwErrorAt stx "boolXor operands require Bool"
    pure (mergeLowered (.scalar .bool) (.boolXor left.term right.term) [left, right])
  | `(nlexpr| boolNot($value)) => do
    let value ← lowerExpr programName callPrefix env value
    unless value.type == .scalar .bool do
      throwErrorAt stx "boolNot operand requires Bool"
    pure (mergeLowered (.scalar .bool) (.boolXor value.term (.bool Bool.true)) [value])
  | `(nlexpr| ite($condition, $yes, $no))
  | `(nlexpr| if $condition then $yes else $no) => do
    let predicate ← lowerExpr programName callPrefix env condition
    let predicate ← coerce condition predicate .bool
    let yesValue ← lowerExpr programName callPrefix env yes
    let noValue ← lowerExpr programName callPrefix env no
    let some type := Helpers.commonType yesValue.type noValue.type
      | throwErrorAt stx "conditional branches require a common type"
    let yesTerm ← lowerConditionalArm yes programName env yesValue
    let noTerm ← lowerConditionalArm no programName env noValue
    modify fun state => {state with requiresOutputViews := _root_.Bool.true}
    let result := mergeLowered type (.ite predicate.term yesTerm noTerm) [predicate, yesValue, noValue]
    pure {result with before := predicate.before}
  | `(nlexpr| select($condition, $yes, $no)) => do
    let condition ← lowerExpr programName callPrefix env condition
    let condition ← coerce stx condition .bool
    let yes ← lowerExpr programName callPrefix env yes
    let no ← lowerExpr programName callPrefix env no
    let .scalar yesTy := yes.type | throwErrorAt stx "select does not accept Unit"
    let .scalar noTy := no.type | throwErrorAt stx "select does not accept Unit"
    let ty ← commonType stx yesTy noTy
    let yes ← coerce stx yes ty
    let no ← coerce stx no ty
    pure (mergeLowered (.scalar ty) (.select condition.term yes.term no.term) [condition, yes, no])
  | `(nlexpr| poseidon2($domain:num, $left, $right)) => do
    let left ← lowerExpr programName callPrefix env left
    let right ← lowerExpr programName callPrefix env right
    let left ← coerce stx left .native
    let right ← coerce stx right .native
    pure (mergeLowered (.scalar .native) (.poseidon2 domain.getNat left.term right.term) [left, right])
  | `(nlexpr| secp256k1Base($value:num)) =>
    lowerForeignFieldConstant stx (.base .secp256k1) value.getNat
  | `(nlexpr| secp256k1Scalar($value:num)) =>
    lowerForeignFieldConstant stx (.scalar .secp256k1) value.getNat
  | `(nlexpr| secp256k1Point($x:num, $y:num)) =>
    lowerForeignPointConstant stx .secp256k1 x.getNat y.getNat
  | `(nlexpr| secp256k1Identity()) =>
    pure {
      type := .scalar (.foreign (.point .secp256k1))
      term := .foreignConstant (.point .secp256k1) (Foreign.identityEncoding .secp256k1)
    }
  | `(nlexpr| secp256r1Base($value:num)) =>
    lowerForeignFieldConstant stx (.base .secp256r1) value.getNat
  | `(nlexpr| secp256r1Scalar($value:num)) =>
    lowerForeignFieldConstant stx (.scalar .secp256r1) value.getNat
  | `(nlexpr| secp256r1Point($x:num, $y:num)) =>
    lowerForeignPointConstant stx .secp256r1 x.getNat y.getNat
  | `(nlexpr| secp256r1Identity()) =>
    pure {
      type := .scalar (.foreign (.point .secp256r1))
      term := .foreignConstant (.point .secp256r1) (Foreign.identityEncoding .secp256r1)
    }
  | `(nlexpr| curve25519Base($value:num)) =>
    lowerForeignFieldConstant stx (.base .curve25519) value.getNat
  | `(nlexpr| curve25519Scalar($value:num)) =>
    lowerForeignFieldConstant stx (.scalar .curve25519) value.getNat
  | `(nlexpr| curve25519Point($x:num, $y:num)) =>
    lowerForeignPointConstant stx .curve25519 x.getNat y.getNat
  | `(nlexpr| curve25519Identity()) =>
    pure {
      type := .scalar (.foreign (.point .curve25519))
      term := .foreignConstant (.point .curve25519) (Foreign.identityEncoding .curve25519)
    }
  | `(nlexpr| nativeToken()) | `(nlexpr| tokenType($_:nlexpr, $_:nlexpr)) => do
    let some expanded ← Noctium.expandTokenHelperSyntax stx
      | throwErrorAt stx "token helper expansion failed"
    lowerExpr programName callPrefix env expanded
  | `(nlexpr| bytes32($literal:str)) => do
    let bytes := literal.getString.toUTF8.data.toList.map UInt8.toNat
    if bytes.length > 32 then throwErrorAt stx "Bytes32 string literal exceeds 32 UTF-8 bytes"
    pure {type := .scalar (.bytes 32), term := .bytes32Literal (bytes ++ List.replicate (32 - bytes.length) 0)}
  | `(nlexpr| bytes($length:num, $literal:str)) => do
    let length := length.getNat
    if length > Types.defaultLimits.maxVectorLength then
      throwErrorAt stx s!"byte string length exceeds the maximum of {Types.defaultLimits.maxVectorLength}"
    let bytes := literal.getString.toUTF8.data.toList.map UInt8.toNat
    if bytes.length > length then
      throwErrorAt stx s!"byte string literal exceeds its declared length {length}"
    let values := bytes ++ List.replicate (length - bytes.length) 0
    let operation := Noctium.Helpers.BytesOp.bytesLiteral length values
    match operation.signature 0 with
    | .error message => throwErrorAt stx message
    | .ok _ => pure ()
    pure {type := .scalar (.bytes length), term := .bytes operation []}
  | `(nlexpr| byteAt($value, $index:num)) => do
    let value ← lowerExpr programName callPrefix env value
    let .scalar (.bytes length) := value.type
      | throwErrorAt stx "byteAt requires a fixed byte-string value"
    unless index.getNat < length do throwErrorAt stx "byteAt index is outside the byte string"
    pure (mergeLowered (.scalar (.uint 255)) (.bytesAt value.term index.getNat) [value])
  | `(nlexpr| persistentHash32($value)) =>
    lowerBytesOperation programName callPrefix env stx .persistentHash32 [value]
  | `(nlexpr| persistentHashVector32([$values,*])) =>
    lowerBytesOperation programName callPrefix env stx .persistentHashVector32 values.getElems.toList
  | `(nlexpr| persistentHashNative($value)) =>
    lowerBytesOperation programName callPrefix env stx .persistentHashNative [value]
  | `(nlexpr| persistentHashNativeVector([$values,*])) =>
    lowerBytesOperation programName callPrefix env stx .persistentHashNativeVector values.getElems.toList
  | `(nlexpr| transientHashNativeVector([$values,*])) =>
    lowerBytesOperation programName callPrefix env stx .transientHashNativeVector values.getElems.toList
  | `(nlexpr| transientHashValue($source)) => do
    let value ← lowerExpr programName callPrefix env source
    let (before, operands) ← match value.type with
      | .unit => do
        modify fun state => {state with requiresOutputViews := _root_.Bool.true}
        pure (value.before ++ [.evaluate value.term], [])
      | .scalar ty => do
        unless (ScalarPolicy.validate ty.scalarKind).isOk do
          throwErrorAt source "transientHashValue requires Native, Bool or UInt"
        let operand := if ty == .native then value.term else .cast .native value.term
        pure (value.before, [operand])
      | .composite type => do
        modify fun state => {state with requiresOutputViews := _root_.Bool.true}
        let compiled ← match Types.compileType (← get).composites type with
          | .ok result => pure result
          | .error diagnostic => throwErrorAt source diagnostic.message
        let (before, reference) ← match value.term with
          | .ref _ => pure (value.before, value.term)
          | _ => do
            let binding ← freshIterationRef "hash-payload"
            pure (value.before ++ [.bind binding value.type value.term],
              Noctium.Helpers.Term.ref binding)
        let operands ← match Helpers.Wire.transientHashOperands compiled reference with
          | .ok result => pure result
          | .error message => throwErrorAt source message
        pure (before, operands)
    pure {
      value with
      type := .scalar .native
      term := .bytes .transientHashNativeVector operands
      before
    }
  | `(nlexpr| persistentHashPoint($point)) =>
    lowerBytesOperation programName callPrefix env stx .persistentHashPoint [point]
  | `(nlexpr| sha256($value)) => do
    let value ← lowerExpr programName callPrefix env value
    let .scalar (.bytes length) := value.type
      | throwErrorAt stx "sha256 requires a fixed byte-string value"
    let operation := Noctium.Helpers.BytesOp.sha256 length
    let (_, result) ← match operation.signature 1 with
      | .error message => throwErrorAt stx message
      | .ok signature => pure signature
    pure (mergeLowered (.scalar result) (.bytes operation [value.term]) [value])
  | `(nlexpr| sha512($value)) => do
    let value ← lowerExpr programName callPrefix env value
    let .scalar (.bytes length) := value.type
      | throwErrorAt stx "sha512 requires a fixed byte-string value"
    let operation := Noctium.Helpers.BytesOp.sha512 length
    let (_, result) ← match operation.signature 1 with
      | .error message => throwErrorAt stx message
      | .ok signature => pure signature
    pure (mergeLowered (.scalar result) (.bytes operation [value.term]) [value])
  | `(nlexpr| keccak256($value)) => do
    let value ← lowerExpr programName callPrefix env value
    let operation ← match value.type with
      | .scalar (.bytes length) => pure (Noctium.Helpers.BytesOp.keccak256 length)
      | .scalar (.foreign (.point .secp256k1)) => pure .keccak256Secp256k1Point
      | .scalar (.foreign (.point _)) =>
        throwErrorAt stx "keccak256 point overload supports Secp256k1Point"
      | _ => throwErrorAt stx "keccak256 requires a fixed byte string or Secp256k1Point"
    let (_, result) ← match operation.signature 1 with
      | .error message => throwErrorAt stx message
      | .ok signature => pure signature
    pure (mergeLowered (.scalar result) (.bytes operation [value.term]) [value])
  | `(nlexpr| reverseBytes32($value)) =>
    lowerBytesOperation programName callPrefix env stx .reverseBytes32 [value]
  | `(nlexpr| reverseBytes($value)) => do
    let value ← lowerExpr programName callPrefix env value
    let .scalar (.bytes length) := value.type
      | throwErrorAt stx "reverseBytes requires a fixed byte-string value"
    let operation := Noctium.Helpers.BytesOp.reverseBytes length
    match operation.signature 1 with
    | .error message => throwErrorAt stx message
    | .ok _ => pure ()
    pure (mergeLowered (.scalar (.bytes length)) (.bytes operation [value.term]) [value])
  | `(nlexpr| sliceBytes($source, $start:num, $stop:num))
  | `(nlexpr| slice($source, $start:num, $stop:num)) => do
    let value ← lowerExpr programName callPrefix env source
    let first := start.getNat
    let limit := stop.getNat
    let length := limit - first
    let sequence := stx.raw.getKind == ``readableSequenceSlice
    if sequence then
      modify fun state => {state with requiresOutputViews := _root_.Bool.true}
    if let .scalar (.bytes width) := value.type then
      let operation := Noctium.Helpers.BytesOp.sliceBytes width first limit
      match operation.signature 1 with
      | .error message => throwErrorAt stx message
      | .ok _ => pure ()
      return {value with type := .scalar (.bytes length), term := .bytes operation [value.term]}
    unless sequence do throwErrorAt stx "sliceBytes requires a fixed byte-string value"
    let span ← liftM (spanValue stx)
    let (before, references, _) ← stageIterationValues callPrefix env span [value]
    let [reference] := references | throwErrorAt stx "sequence slice staging failed"
    let fields ← sequenceItems stx value.type reference first (some limit)
    if let .composite (.bytes _) := value.type then
      let segments ← fields.flatMapM (byteSegments stx _root_.Bool.false)
      let (_, term) := joinByteSegments segments
      return {value with type := .scalar (.bytes length), term, before}
    let payload := match value.type with
      | .composite (.vector _ element) => Types.CompositeType.vector length element
      | _ => .tuple (fields.map Lowered.layoutType)
    let term ← checkedSequenceTerm stx payload fields
    pure {value with type := .composite payload, term, before}
  | `(nlexpr| concatBytes($left, $right)) => do
    let left ← lowerExpr programName callPrefix env left
    let right ← lowerExpr programName callPrefix env right
    let .scalar (.bytes leftLength) := left.type
      | throwErrorAt stx "concatBytes requires fixed byte-string values"
    let .scalar (.bytes rightLength) := right.type
      | throwErrorAt stx "concatBytes requires fixed byte-string values"
    let operation := Noctium.Helpers.BytesOp.concatBytes leftLength rightLength
    let (_, resultType) ← match operation.signature 2 with
      | .error message => throwErrorAt stx message
      | .ok signature => pure signature
    pure (mergeLowered (.scalar resultType) (.bytes operation [left.term, right.term]) [left, right])
  | `(nlexpr| degradeToNative($value)) =>
    lowerBytesOperation programName callPrefix env stx .degradeToNative [value]
  | `(nlexpr| upgradeFromNative($value)) => do
    let value ← lowerExpr programName callPrefix env value
    unless value.type == .scalar .native do throwErrorAt stx "upgradeFromNative requires Native"
    let bytes := Noctium.Helpers.Term.bytes (.toBytes32 .native) [value.term]
    let low := Noctium.Helpers.Term.bytes (.sliceBytes 32 0 31) [bytes]
    let high := Noctium.Helpers.Term.bytes (.bytesLiteral 1 [0]) []
    pure (mergeLowered (.scalar (.bytes 32)) (.bytes (.concatBytes 31 1) [low, high]) [value])
  | `(nlexpr| toBytes32($value)) => do
    let value ← lowerExpr programName callPrefix env value
    let .scalar source := value.type | throwErrorAt stx "toBytes32 does not accept Unit"
    let operation := Noctium.Helpers.BytesOp.toBytes32 source
    match operation.signature 1 with
    | .error message => throwErrorAt stx message
    | .ok _ => pure ()
    pure (mergeLowered (.scalar (.bytes 32)) (.bytes operation [value.term]) [value])
  | `(nlexpr| serialize($value, $length:num)) => do
    let value ← lowerExpr programName callPrefix env value
    let .scalar source := value.type | throwErrorAt stx "serialize requires a scalar or fixed bytes"
    let operation := Noctium.Helpers.BytesOp.serialize source length.getNat
    let (_, result) ← match operation.signature 1 with
      | .ok signature => pure signature
      | .error message => throwErrorAt stx message
    pure (mergeLowered (.scalar result) (.bytes operation [value.term]) [value])
  | `(nlexpr| toBytes($sourceValue, $length:num)) => do
    let value ← lowerExpr programName callPrefix env sourceValue
    let .scalar source := value.type
      | throwErrorAt stx "toBytes requires Native or UInt"
    let target ← match Noctium.Wire.numericBytesTarget source length.getNat with
      | .ok target => pure target
      | .error message => throwErrorAt stx message
    let operation := Noctium.Helpers.BytesOp.serialize target length.getNat
    let (_, resultType) ← match operation.signature 1 with
      | .ok signature => pure signature
      | .error message => throwErrorAt stx message
    let encoded := if target == source then value.term else .cast target value.term
    let result := mergeLowered (.scalar resultType) (.bytes operation [encoded]) [value]
    pure {result with generatedValidity :=
      (if target == source then [] else [s!"checked byte fit {renderExpr stx}"]) ++
        result.generatedValidity |>.eraseDups}
  | `(nlexpr| deserialize($target:nltype, $value)) => do
    let target ← readScalarTy target
    let value ← lowerExpr programName callPrefix env value
    let .scalar (.bytes length) := value.type | throwErrorAt stx "deserialize requires fixed bytes"
    let operation := Noctium.Helpers.BytesOp.deserialize target length
    match operation.signature 1 with
    | .error message => throwErrorAt stx message
    | .ok _ => pure ()
    let result := mergeLowered (.scalar target) (.bytes operation [value.term]) [value]
    pure {result with generatedValidity := s!"checked wire decode {renderExpr stx}" :: result.generatedValidity}
  | `(nlexpr| fromBytesChecked($target:nltype, $value)) => do
    let target ← readScalarTy target
    unless target == .native ||
        (match target with | .uint _ => _root_.Bool.true | _ => _root_.Bool.false) do
      throwErrorAt stx "fromBytesChecked supports only Native and UInt"
    let value ← lowerExpr programName callPrefix env value
    let .scalar (.bytes length) := value.type
      | throwErrorAt stx "fromBytesChecked requires fixed bytes"
    let operation := Noctium.Helpers.BytesOp.fromBytesChecked target length
    let (expected, resultType) ← match operation.signature 1 with
      | .ok signature => pure signature
      | .error message => throwErrorAt stx message
    unless expected == [.bytes length] && resultType == target do
      throwErrorAt stx "fromBytesChecked argument type mismatch"
    let lowered := mergeLowered (.scalar target) (.bytes operation [value.term]) [value]
    pure {lowered with generatedValidity :=
      s!"checked byte decode {renderExpr stx}" :: lowered.generatedValidity |>.eraseDups}
  | `(nlexpr| encode($name:ident, $value)) => do
    let (codec, helper) ← selectedCodec name
    let value ← lowerExpr programName callPrefix env value
    unless value.type == .composite codec.payload do
      throwErrorAt stx s!"encode requires the payload type of codec '{name.getId}'"
    pure (mergeLowered (.scalar (.bytes codec.frameBytes)) (.call (helper ++ "Encode") [value.term]) [value])
  | `(nlexpr| decode($name:ident, $value)) => do
    let (codec, helper) ← selectedCodec name
    let value ← lowerExpr programName callPrefix env value
    unless value.type == .scalar (.bytes codec.frameBytes) do
      throwErrorAt stx s!"decode requires Bytes {codec.frameBytes} for codec '{name.getId}'"
    let result := mergeLowered (.composite codec.payload) (.call (helper ++ "Decode") [value.term]) [value]
    pure {result with generatedValidity := s!"checked wire decode {renderExpr stx}" :: result.generatedValidity}
  | `(nlexpr| field($value, $name:ident)) =>
    lowerProjection stx (← lowerExpr programName callPrefix env value) (.field name.getId.toString)
  | `(nlexpr| elementAt($value, $index)) => do
    let value ← lowerExpr programName callPrefix env value
    if let `(nlexpr| $literal:num) := index then
      let offset := literal.getNat
      let projection ← match value.type with
        | .composite (.tuple _) => pure (Types.Projection.tupleIndex offset)
        | .composite (.vector _ _) => pure (.vectorIndex offset)
        | .composite (.bytes _) => pure (.byteIndex offset)
        | _ => throwErrorAt stx "elementAt requires an aggregate tuple, vector or byte string"
      return ← lowerProjection stx value projection
    let offset ← lowerExpr programName callPrefix env index
    let type ← match Helpers.indexResultType (← spanValue stx) value.type offset.type with
      | .ok type => pure type
      | .error diagnostic => throwErrorAt stx diagnostic.message
    let result := mergeLowered type (.index value.term offset.term) [value, offset]
    let result := {result with generatedValidity := s!"checked vector index {renderExpr index}" :: result.generatedValidity}
    if offset.before.isEmpty then return result
    -- Evaluate the vector before bindings introduced by the index expression.
    let next := (← get).nextLet
    modify fun state => {state with nextLet := state.nextLet + 1}
    let vector := s!"__noctium_index_vector_{next}"
    return { result with
      term := .index (.ref vector) offset.term
      before := value.before ++ [.bind vector value.type value.term] ++ offset.before}
  | `(nlexpr| enumTag($value)) =>
    lowerProjection stx (← lowerExpr programName callPrefix env value) .enumTag
  | `(nlexpr| enumMember($codecName:ident, $variantName:ident)) => do
    let (codec, _) ← selectedCodec codecName
    let members ← checkedFieldlessEnumMembers codecName codec.payload
    let some ordinal := members.findIdx? (· == variantName.getId.toString)
      | throwErrorAt variantName s!"unknown enum member '{variantName.getId}'"
    modify fun state => {state with requiresOutputViews := _root_.Bool.true}
    pure {type := .composite codec.payload, term := .composite codec.payload [.native ordinal]}
  | `(nlexpr| jubjubScalarFromNative($value)) =>
    lowerCurve programName callPrefix env stx .scalarFromNative [value]
  | `(nlexpr| jubjubScalarToNative($value)) =>
    lowerCurve programName callPrefix env stx .scalarToNative [value]
  | `(nlexpr| jubjubMulGenerator($value)) =>
    lowerCurve programName callPrefix env stx .mulGenerator [value]
  | `(nlexpr| jubjubMul($point, $scalar)) =>
    lowerCurve programName callPrefix env stx .mul [point, scalar]
  | `(nlexpr| jubjubAdd($left, $right)) =>
    lowerCurve programName callPrefix env stx .add [left, right]
  | `(nlexpr| jubjubNeg($point)) => lowerCurve programName callPrefix env stx .neg [point]
  | `(nlexpr| jubjubX($point)) => lowerCurve programName callPrefix env stx .x [point]
  | `(nlexpr| jubjubY($point)) => lowerCurve programName callPrefix env stx .y [point]
  | `(nlexpr| jubjubFromCoordinates($x, $y)) =>
    lowerCurve programName callPrefix env stx .fromCoordinates [x, y]
  | `(nlexpr| hashToCurve([$values,*])) => do
    let arguments := values.getElems.toList
    if arguments.length > Types.defaultLimits.maxVectorLength then
      throwErrorAt stx s!"hashToCurve input count exceeds the maximum of {Types.defaultLimits.maxVectorLength}"
    lowerCurve programName callPrefix env stx (.hashToCurve arguments.length) arguments
  | `(nlexpr| foreignNeg($value)) => lowerForeignUnary programName callPrefix env stx "neg" value
  | `(nlexpr| foreignInv($value)) => lowerForeignUnary programName callPrefix env stx "inv" value
  | `(nlexpr| curveMulGenerator($value)) =>
    lowerForeignUnary programName callPrefix env stx "mulGenerator" value
  | `(nlexpr| curveX($value)) => lowerForeignUnary programName callPrefix env stx "x" value
  | `(nlexpr| curveY($value)) => lowerForeignUnary programName callPrefix env stx "y" value
  | `(nlexpr| foreignAdd($left, $right)) =>
    lowerForeignBinary programName callPrefix env stx "add" left right
  | `(nlexpr| foreignSub($left, $right)) =>
    lowerForeignBinary programName callPrefix env stx "sub" left right
  | `(nlexpr| foreignMul($left, $right)) =>
    lowerForeignBinary programName callPrefix env stx "mul" left right
  | `(nlexpr| curveMul($point, $scalar)) =>
    lowerForeignBinary programName callPrefix env stx "ecMul" point scalar
  | `(nlexpr| curveFromCoordinates($x, $y)) =>
    lowerForeignBinary programName callPrefix env stx "fromCoordinates" x y
  | `(nlexpr| foreignToBytes($value)) => do
    let value ← lowerExpr programName callPrefix env value
    let .scalar (.foreign kind) := value.type
      | throwErrorAt stx "foreignToBytes requires a foreign value"
    let operation := Noctium.Helpers.BytesOp.foreignToBytes kind
    let (expected, result) ← match operation.signature 1 with
      | .ok signature => pure signature
      | .error message => throwErrorAt stx message
    unless expected == [.foreign kind] do throwErrorAt stx "foreignToBytes argument type mismatch"
    pure (mergeLowered (.scalar result) (.bytes operation [value.term]) [value])
  | `(nlexpr| foreignFromBytes($target:nltype, $value)) => do
    let target ← readScalarTy target
    let .foreign kind := target
      | throwErrorAt stx "foreignFromBytes requires a foreign target type"
    let value ← lowerExpr programName callPrefix env value
    let .scalar (.bytes length) := value.type
      | throwErrorAt stx "foreignFromBytes requires a fixed byte string"
    let operation := Noctium.Helpers.BytesOp.foreignFromBytes kind length
    let (expected, result) ← match operation.signature 1 with
      | .ok signature => pure signature
      | .error message => throwErrorAt stx message
    unless expected == [.bytes length] && result == target do
      throwErrorAt stx "foreignFromBytes argument type mismatch"
    let lowered := mergeLowered (.scalar result) (.bytes operation [value.term]) [value]
    pure {lowered with generatedValidity :=
      (lowered.generatedValidity ++
        if let .point _ := kind then ["canonical foreign point decoding"] else []).eraseDups}
  | `(nlexpr| invoke($function:ident, [$args:nlexpr,*])) => do
    let values ← args.getElems.toList.mapM (lowerExpr programName callPrefix env)
    let span ← liftM (spanValue stx)
    let (before, arguments, staged) ← stageIterationValues callPrefix env span values
    let program ← iterationProgram stx programName (values.flatMap (·.signatures))
    let helperEnv := iterationEnvironment env staged (← get).iterationParameters
    let (program, term) ←
      match Iteration.applyWithLimits {} program 0 helperEnv span (.named function.getId.toString) arguments with
      | .ok result => pure result
      | .error diagnostic => throwErrorAt function diagnostic.message
    let type ← match Helpers.inferWithLimits {} program 0 helperEnv span term with
      | .ok value => pure value.ty
      | .error diagnostic => throwErrorAt function diagnostic.message
    modify fun state => {state with iterationProgram := some program, requiresOutputViews := _root_.Bool.true}
    pure {mergeLowered type term values with before}
  | `(nlexpr| witness $function:ident($args:nlexpr,*)) => do
    let signature ← liftM (witnessSignature function)
    let signatureName := signature.name
    validIdentity function signatureName
    unless signature.parameters.all (fun p => match p.type with
      | .scalar _ | .composite _ => _root_.Bool.true
      | _ => _root_.Bool.false) do
      throwErrorAt function "witness callback parameters must use supported scalar or Payload types"
    unless args.getElems.size == signature.parameters.length do
      throwErrorAt stx s!"witness '{function.getId}' argument count does not match its declaration"
    let mut loweredArgs := []
    for (argument, parameter) in (args.getElems.toList.zip signature.parameters) do
      let value ← match parameter.type with
        | .scalar parameterTy => do
          let value ← match ← lowerExpectedIterationRef env (.scalar parameterTy) argument with
            | some value => pure value
            | none => lowerExpr programName callPrefix env argument
          coerce argument value parameterTy
        | .composite parameterType => do
          let value ← lowerExpr programName callPrefix env argument
          unless value.type == .composite parameterType do
            throwErrorAt argument "witness callback aggregate argument must use the declared Payload codec"
          pure value
        | .unit => throwErrorAt function "Unit witness parameters are unsupported"
      loweredArgs := loweredArgs ++ [value]
    let callNo ← get
    modify fun state => {state with nextCall := state.nextCall + 1}
    let site := s!"{programName}.call.{callPrefix}.{callNo.nextCall}"
    validIdentity stx site
    let term := .witnessCall site signatureName (loweredArgs.map (·.term))
    let result := signature.result
    pure
      { mergeLowered result term loweredArgs with
        signatures := uniqueWitnesses (signature :: loweredArgs.flatMap (·.signatures)),
        witnessNames := (signatureName :: loweredArgs.flatMap (·.witnessNames)).eraseDups,
        generatedValidity := (loweredArgs.flatMap (·.generatedValidity) ++
          [s!"typed witness reply: {signatureName}"]).eraseDups }
  | _ => throwErrorAt stx "unsupported readable witness expression"
where
  lowerBytesOperation (programName callPrefix : String) (env : SurfaceEnv) (stx : Syntax)
      (operation : Noctium.Helpers.BytesOp) (arguments : List (TSyntax `nlexpr)) : ExprM Lowered := do
    let (expected, result) ← match operation.signature arguments.length with
      | .ok signature => pure signature
      | .error message => throwErrorAt stx message
    let values ← arguments.mapM (lowerExpr programName callPrefix env)
    for (value, expectedType) in values.zip expected do
      let .scalar actualType := value.type | throwErrorAt stx "byte operation argument cannot be Unit"
      unless actualType == expectedType do
        throwErrorAt stx s!"{operation.operationName} argument type mismatch"
    let term := Noctium.Helpers.Term.bytes operation (values.map (·.term))
    pure (mergeLowered (.scalar result) term values)

  lowerCurve (programName callPrefix : String) (env : SurfaceEnv) (stx : Syntax)
      (operation : Noctium.Helpers.CurveOp) (arguments : List (TSyntax `nlexpr)) : ExprM Lowered := do
    if let .hashToCurve arity := operation then
      if arity > Types.defaultLimits.maxVectorLength then
        throwErrorAt stx s!"hashToCurve input count exceeds the maximum of {Types.defaultLimits.maxVectorLength}"
      unless arity == arguments.length do
        throwErrorAt stx "hashToCurve argument count mismatch"
    let (expected, result) := operation.signature
    unless arguments.length == expected.length do
      throwErrorAt stx s!"{operation.operationName} argument count mismatch"
    let values ← arguments.mapM (lowerExpr programName callPrefix env)
    for (value, expectedType) in values.zip expected do
      let .scalar actualType := value.type | throwErrorAt stx "curve operation argument cannot be Unit"
      unless actualType == expectedType do
        throwErrorAt stx s!"{operation.operationName} argument type mismatch"
    let term := Noctium.Helpers.Term.curve operation (values.map (·.term))
    pure { mergeLowered (.scalar result) term values with
      generatedValidity := (values.flatMap (·.generatedValidity) ++
        if operation == .fromCoordinates then ["Jubjub point coordinate validation"] else []).eraseDups }

  lowerForeignUnary (programName callPrefix : String) (env : SurfaceEnv) (stx : Syntax)
      (operationName : String) (valueStx : TSyntax `nlexpr) : ExprM Lowered := do
    let value ← lowerExpr programName callPrefix env valueStx
    let .scalar (.foreign kind) := value.type
      | throwErrorAt stx s!"{operationName} requires a foreign value"
    let operation ← match operationName with
      | "neg" => pure (Foreign.UnaryOp.neg kind)
      | "inv" =>
        match kind.fieldKind? with
        | some field => pure (Foreign.UnaryOp.inv field)
        | none => throwErrorAt stx "foreignInv does not accept points"
      | "mulGenerator" =>
        if let .scalar curve := kind then pure (Foreign.UnaryOp.mulGenerator curve)
        else throwErrorAt stx "curveMulGenerator requires a foreign scalar"
      | "x" =>
        if let .point curve := kind then pure (Foreign.UnaryOp.x curve)
        else throwErrorAt stx "curveX requires a foreign point"
      | "y" =>
        if let .point curve := kind then pure (Foreign.UnaryOp.y curve)
        else throwErrorAt stx "curveY requires a foreign point"
      | _ => throwErrorAt stx "unsupported foreign unary operation"
    finishForeignCurve stx (.foreignUnary operation) [value]

  lowerForeignBinary (programName callPrefix : String) (env : SurfaceEnv) (stx : Syntax)
      (operationName : String) (leftStx rightStx : TSyntax `nlexpr) : ExprM Lowered := do
    let left ← lowerExpr programName callPrefix env leftStx
    let right ← lowerExpr programName callPrefix env rightStx
    let .scalar (.foreign leftKind) := left.type
      | throwErrorAt stx s!"{operationName} requires foreign values"
    let .scalar (.foreign rightKind) := right.type
      | throwErrorAt stx s!"{operationName} requires foreign values"
    let operation ← match operationName with
      | "add" =>
        unless leftKind == rightKind do throwErrorAt stx "foreignAdd requires matching foreign types"
        pure (Foreign.BinaryOp.add leftKind)
      | "sub" =>
        unless leftKind == rightKind do throwErrorAt stx "foreignSub requires matching foreign types"
        pure (Foreign.BinaryOp.sub leftKind)
      | "mul" =>
        unless leftKind == rightKind do throwErrorAt stx "foreignMul requires matching foreign types"
        match leftKind.fieldKind? with
        | some field => pure (Foreign.BinaryOp.mul field)
        | none => throwErrorAt stx "foreignMul does not multiply points"
      | "ecMul" =>
        match leftKind, rightKind with
        | .point curve, .scalar otherCurve =>
          unless curve == otherCurve do throwErrorAt stx "curveMul requires a matching curve scalar"
          pure (Foreign.BinaryOp.ecMul curve)
        | _, _ => throwErrorAt stx "curveMul requires a foreign point and matching scalar"
      | "fromCoordinates" =>
        match leftKind, rightKind with
        | .base curve, .base otherCurve =>
          unless curve == otherCurve do throwErrorAt stx "curveFromCoordinates requires a matching curve family"
          pure (Foreign.BinaryOp.fromCoordinates curve)
        | _, _ => throwErrorAt stx "curveFromCoordinates requires two matching foreign base values"
      | _ => throwErrorAt stx "unsupported foreign binary operation"
    finishForeignCurve stx (.foreignBinary operation) [left, right]

  finishForeignCurve (stx : Syntax) (operation : Noctium.Helpers.CurveOp)
      (values : List Lowered) : ExprM Lowered := do
    let (expected, result) := operation.signature
    unless values.length == expected.length do
      throwErrorAt stx s!"{operation.operationName} argument count mismatch"
    for (value, expectedType) in values.zip expected do
      unless value.type == .scalar expectedType do
        throwErrorAt stx s!"{operation.operationName} argument type mismatch"
    let validity := match operation with
      | .foreignUnary (.inv _) => ["foreign inverse nonzero check"]
      | .foreignUnary (.x _) | .foreignUnary (.y _) => ["foreign point coordinate validity"]
      | .foreignBinary (.fromCoordinates _) => ["foreign point membership validation"]
      | _ => []
    let term := Noctium.Helpers.Term.curve operation (values.map (·.term))
    pure {mergeLowered (.scalar result) term values with
      generatedValidity := (values.flatMap (·.generatedValidity) ++ validity).eraseDups}

  lowerArithmetic (programName callPrefix : String) (env : SurfaceEnv) (stx : Syntax)
      (op : ScalarPolicy.Binary) (leftStx rightStx : TSyntax `nlexpr) : ExprM Lowered := do
    let left ← lowerExpr programName callPrefix env leftStx
    let right ← lowerExpr programName callPrefix env rightStx
    let .scalar leftTy := left.type | throwErrorAt stx "arithmetic does not accept Unit"
    let .scalar rightTy := right.type | throwErrorAt stx "arithmetic does not accept Unit"
    let result ← match ScalarPolicy.infer op leftTy.scalarKind rightTy.scalarKind with
      | .ok (.native) => pure .native
      | .ok (.uint maximum) => pure (.uint maximum)
      | .ok _ => throwErrorAt stx "unsupported scalar arithmetic result"
      | .error message => throwErrorAt stx message
    let left ← match result with
      | .native => coerce stx left .native
      | .uint _ => pure left
      | _ => throwErrorAt stx "unsupported arithmetic result type"
    let right ← match result with
      | .native => coerce stx right .native
      | .uint _ => pure right
      | _ => throwErrorAt stx "unsupported arithmetic result type"
    let term := Noctium.Helpers.Term.binary op left.term right.term
    let underflow := match op, leftTy, rightTy with
      | .sub, .uint _, .uint _ => ["unsigned subtraction underflow"]
      | _, _, _ => []
    pure {
      type := .scalar result, term,
      before := left.before ++ right.before,
      signatures := uniqueWitnesses (left.signatures ++ right.signatures),
      witnessNames := (left.witnessNames ++ right.witnessNames).eraseDups,
      generatedValidity := (left.generatedValidity ++ right.generatedValidity ++ underflow).eraseDups
    }

private def authoringForeignCurveTerm : Foreign.Curve → CommandElabM (TSyntax `term)
  | .secp256k1 => `(Noctium.Foreign.Curve.secp256k1)
  | .secp256r1 => `(Noctium.Foreign.Curve.secp256r1)
  | .curve25519 => `(Noctium.Foreign.Curve.curve25519)

private def authoringForeignKindTerm : Foreign.Kind → CommandElabM (TSyntax `term)
  | .base curve => do
    let curve ← authoringForeignCurveTerm curve
    `(Noctium.Foreign.Kind.base $curve)
  | .scalar curve => do
    let curve ← authoringForeignCurveTerm curve
    `(Noctium.Foreign.Kind.scalar $curve)
  | .point curve => do
    let curve ← authoringForeignCurveTerm curve
    `(Noctium.Foreign.Kind.point $curve)

private def authoringForeignFieldKindTerm : Foreign.FieldKind → CommandElabM (TSyntax `term)
  | .base curve => do
    let curve ← authoringForeignCurveTerm curve
    `(Noctium.Foreign.FieldKind.base $curve)
  | .scalar curve => do
    let curve ← authoringForeignCurveTerm curve
    `(Noctium.Foreign.FieldKind.scalar $curve)

private def authoringForeignUnaryTerm : Foreign.UnaryOp → CommandElabM (TSyntax `term)
  | .neg kind => do
    let kind ← authoringForeignKindTerm kind
    `(Noctium.Foreign.UnaryOp.neg $kind)
  | .inv kind => do
    let kind ← authoringForeignFieldKindTerm kind
    `(Noctium.Foreign.UnaryOp.inv $kind)
  | .mulGenerator curve => do
    let curve ← authoringForeignCurveTerm curve
    `(Noctium.Foreign.UnaryOp.mulGenerator $curve)
  | .x curve => do
    let curve ← authoringForeignCurveTerm curve
    `(Noctium.Foreign.UnaryOp.x $curve)
  | .y curve => do
    let curve ← authoringForeignCurveTerm curve
    `(Noctium.Foreign.UnaryOp.y $curve)

private def authoringForeignBinaryTerm : Foreign.BinaryOp → CommandElabM (TSyntax `term)
  | .add kind => do
    let kind ← authoringForeignKindTerm kind
    `(Noctium.Foreign.BinaryOp.add $kind)
  | .sub kind => do
    let kind ← authoringForeignKindTerm kind
    `(Noctium.Foreign.BinaryOp.sub $kind)
  | .mul kind => do
    let kind ← authoringForeignFieldKindTerm kind
    `(Noctium.Foreign.BinaryOp.mul $kind)
  | .ecMul curve => do
    let curve ← authoringForeignCurveTerm curve
    `(Noctium.Foreign.BinaryOp.ecMul $curve)
  | .fromCoordinates curve => do
    let curve ← authoringForeignCurveTerm curve
    `(Noctium.Foreign.BinaryOp.fromCoordinates $curve)

private partial def termTerm : Noctium.Helpers.Term → CommandElabM (TSyntax `term)
  | .unit => `(Noctium.Helpers.Term.unit)
  | .native value => `(Noctium.Helpers.Term.native $(natTerm value))
  | .bool value => do
    let value ← if value then `(Bool.true) else `(Bool.false)
    `(Noctium.Helpers.Term.bool $value)
  | .uint maximum value => `(Noctium.Helpers.Term.uint $(natTerm maximum) $(natTerm value))
  | .ref name => `(Noctium.Helpers.Term.ref $(stringTerm name))
  | .binary op left right => do
    let op ← match op with
      | .add => `(Noctium.ScalarPolicy.Binary.add)
      | .sub => `(Noctium.ScalarPolicy.Binary.sub)
      | .mul => `(Noctium.ScalarPolicy.Binary.mul)
    `(Noctium.Helpers.Term.binary $op $(← termTerm left) $(← termTerm right))
  | .boolAnd left right => do
    `(Noctium.Helpers.Term.boolAnd $(← termTerm left) $(← termTerm right))
  | .boolOr left right => do
    `(Noctium.Helpers.Term.boolOr $(← termTerm left) $(← termTerm right))
  | .boolXor left right => do
    `(Noctium.Helpers.Term.boolXor $(← termTerm left) $(← termTerm right))
  | .foreignConstant kind encoding => do
    let kind ← match kind with
      | .base .secp256k1 => `(Noctium.Foreign.Kind.base Noctium.Foreign.Curve.secp256k1)
      | .scalar .secp256k1 => `(Noctium.Foreign.Kind.scalar Noctium.Foreign.Curve.secp256k1)
      | .point .secp256k1 => `(Noctium.Foreign.Kind.point Noctium.Foreign.Curve.secp256k1)
      | .base .secp256r1 => `(Noctium.Foreign.Kind.base Noctium.Foreign.Curve.secp256r1)
      | .scalar .secp256r1 => `(Noctium.Foreign.Kind.scalar Noctium.Foreign.Curve.secp256r1)
      | .point .secp256r1 => `(Noctium.Foreign.Kind.point Noctium.Foreign.Curve.secp256r1)
      | .base .curve25519 => `(Noctium.Foreign.Kind.base Noctium.Foreign.Curve.curve25519)
      | .scalar .curve25519 => `(Noctium.Foreign.Kind.scalar Noctium.Foreign.Curve.curve25519)
      | .point .curve25519 => `(Noctium.Foreign.Kind.point Noctium.Foreign.Curve.curve25519)
    let encoding := encoding.map natTerm |>.toArray
    `(Noctium.Helpers.Term.foreignConstant $kind [$encoding,*])
  | .eq left right => do `(Noctium.Helpers.Term.eq $(← termTerm left) $(← termTerm right))
  | .cast ty value => do `(Noctium.Helpers.Term.cast $(← tyTerm ty) $(← termTerm value))
  | .disclose span value => do
    let span ← quoteSpan span
    `(Noctium.Helpers.Term.disclose $span $(← termTerm value))
  | .ite condition yes no => do
    `(Noctium.Helpers.Term.ite $(← termTerm condition) $(← termTerm yes) $(← termTerm no))
  | .andThen left right => do
    `(Noctium.Helpers.Term.andThen $(← termTerm left) $(← termTerm right))
  | .orElse left right => do
    `(Noctium.Helpers.Term.orElse $(← termTerm left) $(← termTerm right))
  | .select condition yes no => do
    `(Noctium.Helpers.Term.select $(← termTerm condition) $(← termTerm yes) $(← termTerm no))
  | .witnessCall site name args => do
    let args ← args.mapM termTerm
    let args := args.toArray
    `(Noctium.Helpers.Term.witnessCall $(stringTerm site) $(stringTerm name) [$args,*])
  | .call name args => do
    let args := (← args.mapM termTerm).toArray
    `(Noctium.Helpers.Term.call $(stringTerm name) [$args,*])
  | .poseidon2 domain left right => do
    `(Noctium.Helpers.Term.poseidon2 $(natTerm domain) $(← termTerm left) $(← termTerm right))
  | .curve operation arguments => do
    let operation ← match operation with
      | .scalarFromNative => `(Noctium.Helpers.CurveOp.scalarFromNative)
      | .scalarToNative => `(Noctium.Helpers.CurveOp.scalarToNative)
      | .mulGenerator => `(Noctium.Helpers.CurveOp.mulGenerator)
      | .mul => `(Noctium.Helpers.CurveOp.mul)
      | .add => `(Noctium.Helpers.CurveOp.add)
      | .neg => `(Noctium.Helpers.CurveOp.neg)
      | .x => `(Noctium.Helpers.CurveOp.x)
      | .y => `(Noctium.Helpers.CurveOp.y)
      | .fromCoordinates => `(Noctium.Helpers.CurveOp.fromCoordinates)
      | .hashToCurve arity => `(Noctium.Helpers.CurveOp.hashToCurve $(natTerm arity))
      | .foreignUnary foreignOperation => do
        let operation ← authoringForeignUnaryTerm foreignOperation
        `(Noctium.Helpers.CurveOp.foreignUnary $operation)
      | .foreignBinary foreignOperation => do
        let operation ← authoringForeignBinaryTerm foreignOperation
        `(Noctium.Helpers.CurveOp.foreignBinary $operation)
    let arguments ← arguments.mapM termTerm
    let arguments := arguments.toArray
    `(Noctium.Helpers.Term.curve $operation [$arguments,*])
  | .bytes operation arguments => do
    let operation ← match operation with
      | .persistentHash32 => `(Noctium.Helpers.BytesOp.persistentHash32)
      | .persistentHashVector32 => `(Noctium.Helpers.BytesOp.persistentHashVector32)
      | .persistentHashNative => `(Noctium.Helpers.BytesOp.persistentHashNative)
      | .persistentHashNativeVector => `(Noctium.Helpers.BytesOp.persistentHashNativeVector)
      | .transientHashNativeVector => `(Noctium.Helpers.BytesOp.transientHashNativeVector)
      | .persistentHashPoint => `(Noctium.Helpers.BytesOp.persistentHashPoint)
      | .sha256 length => `(Noctium.Helpers.BytesOp.sha256 $(natTerm length))
      | .sha512 length => `(Noctium.Helpers.BytesOp.sha512 $(natTerm length))
      | .keccak256 length => `(Noctium.Helpers.BytesOp.keccak256 $(natTerm length))
      | .keccak256Secp256k1Point => `(Noctium.Helpers.BytesOp.keccak256Secp256k1Point)
      | .reverseBytes32 => `(Noctium.Helpers.BytesOp.reverseBytes32)
      | .reverseBytes length => `(Noctium.Helpers.BytesOp.reverseBytes $(natTerm length))
      | .sliceBytes length start stop =>
        `(Noctium.Helpers.BytesOp.sliceBytes $(natTerm length) $(natTerm start) $(natTerm stop))
      | .concatBytes leftLength rightLength =>
        `(Noctium.Helpers.BytesOp.concatBytes $(natTerm leftLength) $(natTerm rightLength))
      | .foreignToBytes kind => do
        let kind ← authoringForeignKindTerm kind
        `(Noctium.Helpers.BytesOp.foreignToBytes $kind)
      | .foreignFromBytes kind length => do
        let kind ← authoringForeignKindTerm kind
        `(Noctium.Helpers.BytesOp.foreignFromBytes $kind $(natTerm length))
      | .degradeToNative => `(Noctium.Helpers.BytesOp.degradeToNative)
      | .toBytes32 source => `(Noctium.Helpers.BytesOp.toBytes32 $(← tyTerm source))
      | .serialize source length =>
        `(Noctium.Helpers.BytesOp.serialize $(← tyTerm source) $(natTerm length))
      | .deserialize target length =>
        `(Noctium.Helpers.BytesOp.deserialize $(← tyTerm target) $(natTerm length))
      | .fromBytesChecked target length =>
        `(Noctium.Helpers.BytesOp.fromBytesChecked $(← tyTerm target) $(natTerm length))
      | .bytesLiteral length values => do
        let values := values.map natTerm |>.toArray
        `(Noctium.Helpers.BytesOp.bytesLiteral $(natTerm length) [$values,*])
    let arguments ← arguments.mapM termTerm
    let arguments := arguments.toArray
    `(Noctium.Helpers.Term.bytes $operation [$arguments,*])
  | .bytes32Literal values => do
    let values := values.map natTerm |>.toArray
    `(Noctium.Helpers.Term.bytes32Literal [$values,*])
  | .bytesAt value index => do
    `(Noctium.Helpers.Term.bytesAt $(← termTerm value) $(natTerm index))
  | .composite type leaves => do
    let type ← compositeTypeTerm type
    let leaves ← leaves.mapM termTerm
    let leaves := leaves.toArray
    `(Noctium.Helpers.Term.composite $type [$leaves,*])
  | .project value projection => do
    let projection ← match projection with
      | .field name => `(Noctium.Types.Projection.field $(stringTerm name))
      | .tupleIndex index => `(Noctium.Types.Projection.tupleIndex $(natTerm index))
      | .vectorIndex index => `(Noctium.Types.Projection.vectorIndex $(natTerm index))
      | .byteIndex index => `(Noctium.Types.Projection.byteIndex $(natTerm index))
      | .enumTag => `(Noctium.Types.Projection.enumTag)
      | .enumField variant name =>
        `(Noctium.Types.Projection.enumField $(stringTerm variant) $(stringTerm name))
    `(Noctium.Helpers.Term.project $(← termTerm value) $projection)
  | .index value index => do
    `(Noctium.Helpers.Term.index $(← termTerm value) $(← termTerm index))
  | .at span value => do
    let span ← quoteSpan span
    `(Noctium.Helpers.Term.at $span $(← termTerm value))
  | _ => throwError "unsupported generated helper term"

private partial def statementTerm : Statement → CommandElabM (TSyntax `term)
  | .bind name type value => do
    `(Noctium.Helpers.Statement.bind $(stringTerm name) $(← resultTypeTerm type) $(← termTerm value))
  | .evaluate value => do `(Noctium.Helpers.Statement.evaluate $(← termTerm value))
  | .assert value => do `(Noctium.Helpers.Statement.assert $(← termTerm value))
  | .return value => do
    let value ← match value with
      | none => `(none)
      | some value => `(some $(← termTerm value))
    `(Noctium.Helpers.Statement.«return» $value)
  | .stage capability key ty value => do
    `(Noctium.Helpers.Statement.stage $(stringTerm capability) $(stringTerm key)
      $(← tyTerm ty) $(← termTerm value))
  | .readCell .. => throwError "readable witness source does not support ledger cell reads"
  | .writeCell .. => throwError "readable witness source does not support ledger cell writes"
  | .readMap .. | .readMember .. =>
    throwError "readable witness source does not support ledger map reads"
  | .writeMap .. => throwError "readable witness source does not support ledger map writes"
  | .emitEvent .. => throwError "readable witness source does not support ledger events"
  | .branch .. => throwError "readable witness source does not support branch statements yet"
  | .forRange index start stop body => do
    let body ← body.toArray.mapM statementTerm
    `(Noctium.Helpers.Statement.forRange $(stringTerm index) $(natTerm start) $(natTerm stop)
      [$body,*])

private def inputTerm (name : String) (ty : Ty) (visibility : Noctium.Visibility)
    (span : SourceSpan) : CommandElabM (TSyntax `term) := do
  let visibility ← if visibility == .public then `(Noctium.Visibility.public)
    else `(Noctium.Visibility.private)
  let span ← quoteSpan span
  let ty ← tyTerm ty
  `(Noctium.Input.mk $(stringTerm name) $ty $visibility $span)

private def observationTerm (metadata : ObservationMetadata) : CommandElabM (TSyntax `term) := do
  let inputs ← metadata.inputs.mapM fun input => do
    let visibility ← if input.visibility == .public then `(Noctium.Visibility.public)
      else `(Noctium.Visibility.private)
    `(Noctium.Authoring.ObservationInput.mk $(stringTerm input.name) $(stringTerm input.type) $visibility)
  let inputs := inputs.toArray
  let list (values : List String) := (values.map stringTerm).toArray
  let entryText := stringTerm metadata.entryName
  let reads := list metadata.privateReads
  let stages := list metadata.privateStages
  let witnesses := list metadata.witnessNames
  let proves := list metadata.authoredProves
  let releases := list metadata.explicitReleases
  let validity := list metadata.generatedValidity
  `(Noctium.Authoring.ObservationMetadata.mk $entryText [$inputs,*] [$reads,*] [$stages,*]
    [$witnesses,*] [$proves,*] [$releases,*] [$validity,*])

@[command_elab noctiumPrivateStateCommand] unsafe def elabPrivateState : CommandElab := fun stx => do
  match stx with
  | `(noctium_private_state $name:ident where $fields:noctium_private_field* end) => do
    let schemaName ← lowerSchemaName name
    let mut fieldValues : List PrivateStateField := []
    for fieldStx in fields do
      match fieldStx with
      | `(noctium_private_field| cell $field:ident : $type:noctium_witness_input_type) => do
        let (result, codec) ← match type with
          | `(noctium_witness_input_type| $scalar:nltype) => do
            pure (ResultType.scalar (← readScalarTy scalar), none)
          | `(noctium_witness_input_type| Payload $name:ident) => do
            let constant ← liftCoreM <| resolveGlobalConstNoOverload name
            let codec ← evalConstCheck Helpers.Wire.Codec ``Helpers.Wire.Codec constant
            let result := if codec.payload == .unit then .unit else .composite codec.payload
            pure (result, some constant)
          | _ => throwErrorAt type "unsupported private-state cell type"
        let key := "noctium/" ++ schemaName ++ "/" ++ field.getId.toString
        let capability := "private_state:" ++ schemaName
        let signatureName := "private_state.read." ++ schemaName ++ "." ++ field.getId.toString ++ ".v1"
        let operation := "private_state.read.v1"
        validIdentity field signatureName
        validIdentity field capability
        let fieldSpan ← spanValue fieldStx
        let signature : WitnessSignature :=
          { name := signatureName,
            operation := operation,
            capability := capability,
            privateKey := some key,
            result,
            span := fieldSpan }
        fieldValues := fieldValues ++ [PrivateStateField.mk
          field.getId.toString key capability signature codec]
      | _ => throwErrorAt fieldStx "unsupported private-state field"
    let fields := fieldValues
    if !uniqueStrings (fields.map (·.name)) then throwErrorAt name "duplicate private-state field"
    let fullName := (← getCurrNamespace) ++ name.getId
    let generated := generatedName fullName "__privateStateSchema"
    let generatedSyntaxName := generatedName name.getId "__privateStateSchema"
    if (← getEnv).contains generated then throwErrorAt name "private-state schema descriptor already exists"
    let schemaTerm ← do
      let fieldTerms ← fields.mapM quoteField
      let fieldTerms := fieldTerms.toArray
      `(Noctium.Authoring.PrivateStateSchema.mk $(stringTerm schemaName) [$fieldTerms,*])
    elabCommand (← `(def $(mkIdent generatedSyntaxName) : Noctium.Authoring.PrivateStateSchema := $schemaTerm))
    modifyEnv fun env => noctiumPrivateStateRegistry.addEntry env
      {name := schemaName, fields := fields}
  | _ => throwUnsupportedSyntax

@[command_elab noctiumWitnessDeclarationCommand] unsafe def elabWitnessDeclaration : CommandElab := fun stx => do
  match stx with
  | `(noctium_witness $name:ident ($params:noctium_witness_parameter,*) : $result:noctium_witness_result) => do
    let fullName := ((← getCurrNamespace) ++ name.getId).toString
    let signatureName := fullName
    let operation := "noctium.witness." ++ fullName ++ ".v1"
    let capability := fullName
    validIdentity name signatureName
    validIdentity name operation
    validIdentity name capability
    let mut parameters : List WitnessParameter := []
    let mut parameterCodecs : List WitnessParameterCodec := []
    for parameterStx in params.getElems do
      match parameterStx with
      | `(noctium_witness_parameter| $parameter:ident : $type:nltype) => do
        let ty ← readScalarTy type
        parameters := parameters ++ [{name := parameter.getId.toString, type := .scalar ty}]
      | `(noctium_witness_parameter| $parameter:ident : Payload $codecName:ident) => do
        let source ← liftCoreM <| resolveGlobalConstNoOverload codecName
        let codec ← evalConstCheck Helpers.Wire.Codec ``Helpers.Wire.Codec source
        match codec.payload with
        | .unit | .scalar _ =>
          throwErrorAt codecName "witness callback Payload parameters must use an aggregate"
        | _ => pure ()
        let compiled ← match Types.compileType codec.composites codec.payload with
          | .ok value => pure value
          | .error diagnostic => throwErrorAt codecName diagnostic.message
        let _ ← match Helpers.Wire.declarations compiled
            (fullName ++ ".parameter." ++ parameter.getId.toString) codec.frameBytes ⟨0, 1⟩ ⟨0, 2⟩ with
          | .ok declarations => pure declarations
          | .error message => throwErrorAt codecName message
        let parameterName := parameter.getId.toString
        parameters := parameters ++ [{name := parameterName, type := .composite codec.payload}]
        parameterCodecs := parameterCodecs ++ [{signatureName := fullName, parameterName, codec := source}]
      | _ => throwErrorAt parameterStx "unsupported witness parameter"
    let parameterNames := parameters.map (·.name)
    unless uniqueStrings parameterNames do throwErrorAt name "duplicate witness parameter"
    let mut resultCodec : Option Name := none
    let result ← match result with
      | `(noctium_witness_result| $unitType:ident) => do
        unless unitType.getId == `Unit do
          throwErrorAt unitType "only Unit or a supported scalar witness result is allowed"
        pure .unit
      | `(noctium_witness_result| $type:nltype) => .scalar <$> readScalarTy type
      | `(noctium_witness_result| Payload $codecName:ident) => do
        let source ← liftCoreM <| resolveGlobalConstNoOverload codecName
        let codec ← evalConstCheck Helpers.Wire.Codec ``Helpers.Wire.Codec source
        let compiled ← match Types.compileType codec.composites codec.payload with
          | .ok value => pure value
          | .error diagnostic => throwErrorAt codecName diagnostic.message
        let _ ← match Helpers.Wire.declarations compiled
            (fullName ++ ".result") codec.frameBytes ⟨0, 1⟩ ⟨0, 2⟩ with
          | .ok declarations => pure declarations
          | .error message => throwErrorAt codecName message
        resultCodec := some source
        pure (.composite codec.payload)
      | _ => throwErrorAt result "unsupported witness result"
    let signatureSpan ← spanValue name
    let signature : WitnessSignature :=
      { name := signatureName,
        operation := operation,
        capability := capability,
        parameters := parameters,
        result := result,
        span := signatureSpan }
    let generated := generatedName ((← getCurrNamespace) ++ name.getId) "__witnessSignature"
    let generatedSyntaxName := generatedName name.getId "__witnessSignature"
    if (← getEnv).contains generated then throwErrorAt name "witness signature already exists"
    let signatureTerm ← quoteSignature signature
    elabCommand (← `(def $(mkIdent generatedSyntaxName) : Noctium.Helpers.WitnessSignature := $signatureTerm))
    modifyEnv fun env => noctiumWitnessSignatureRegistry.addEntry env signature
    for parameterCodec in parameterCodecs do
      modifyEnv fun env => noctiumWitnessParameterCodecRegistry.addEntry env parameterCodec
    if let some codec := resultCodec then
      modifyEnv fun env => noctiumWitnessResultCodecRegistry.addEntry env
        {signatureName, codec}
  | _ => throwUnsupportedSyntax

private def collectExpressionMetadata (metadata : ObservationMetadata) (stx : TSyntax `nlexpr) :
    ObservationMetadata :=
  { metadata with
    explicitReleases := (metadata.explicitReleases ++ disclosedValues stx).eraseDups,
    authoredProves := (metadata.authoredProves ++ inlineAssertions stx).eraseDups }

private structure ReadableBody where
  env : SurfaceEnv := []
  statements : List Statement := []
  witnesses : List WitnessSignature := []
  observation : ObservationMetadata
  composites : Types.CompositeEnv := {}
  logicalAliases : List LogicalAliasBinding := []
  nextLet : Nat := 0
  helperProgram : Option Helpers.Program := none
  requiresOutputViews : _root_.Bool := _root_.Bool.false
  iterationParameters : List IterationParameter := []
  deriving Inhabited

private def ReadableBody.lower (body : ReadableBody) (programName path : String)
    (exprState : AuthoringExprState) (source : TSyntax `nlexpr)
    (expected : Option ResultType := none) :
    CommandElabM (Lowered × ReadableBody) := do
  let action : ExprM Lowered := do
    match expected with
    | some type =>
      match ← lowerExpectedIterationRef body.env type source with
      | some value => pure value
      | none => lowerExpr programName ("s" ++ path) body.env source
    | none => lowerExpr programName ("s" ++ path) body.env source
  let (value, state) ← action.run
    {exprState with
      composites := body.composites
      iterationProgram := body.helperProgram
      iterationWitnesses := body.witnesses
      requiresOutputViews := body.requiresOutputViews
      nextLet := body.nextLet
      iterationParameters := body.iterationParameters}
  pure (value, {body with
    composites := state.composites
    nextLet := state.nextLet
    helperProgram := state.iterationProgram
    requiresOutputViews := state.requiresOutputViews
    iterationParameters := state.iterationParameters})

private def ReadableBody.observe (body : ReadableBody) (value : Lowered)
    (sources : List (TSyntax `nlexpr)) (extraValidity : List String := [])
    (typedReplies : _root_.Bool := _root_.Bool.true) : ReadableBody :=
  let observation := sources.foldl collectExpressionMetadata body.observation
  let replies := if typedReplies then
    value.witnessNames.map fun name => s!"typed witness reply: {name}"
    else []
  {body with
    witnesses := uniqueWitnesses (body.witnesses ++ value.signatures)
    observation := {observation with
      witnessNames := (observation.witnessNames ++ value.witnessNames).eraseDups
      generatedValidity :=
        (observation.generatedValidity ++ value.generatedValidity ++ extraValidity ++ replies).eraseDups}}

private def readableAliasSource (value : Lowered) (source : TSyntax `nlexpr) : LogicalAliasSource :=
  match value.term with
  | .witnessCall site .. | .at _ (.witnessCall site ..) => .call site
  | _ => .expression source

private def lookupPrivateField (fieldPath : TSyntax `ident) : CommandElabM PrivateStateField := do
  let (schemaName, fieldName) ← splitSchemaField fieldPath
  let schema ← privateStateSchema schemaName fieldPath
  let some field := schema.fields.find? (·.name == fieldName)
    | throwErrorAt fieldPath "schema '{schema.name}' has no field '{fieldName}'"
  pure field

private abbrev PatternBinding := TSyntax `ident × ResultType × (Helpers.Term → Helpers.Term)

private partial def patternBindings (composites : Types.CompositeEnv)
    (pattern : TSyntax `noctium_bind_pattern) (type : ResultType)
    (select : Helpers.Term → Helpers.Term) : CommandElabM (List PatternBinding) := do
  match pattern with
  | `(noctium_bind_pattern| $id:ident) => pure [(id, type, select)]
  | `(noctium_bind_pattern| _) => pure []
  | `(noctium_bind_pattern| [$items,*]) => do
    let (types, project) : List Types.CompositeType × (Nat → Helpers.Term → Helpers.Term) ←
      match type with
      | .unit => pure ([], fun _ value => value)
      | .composite (.tuple types) => pure (types, fun index value => .project value (.tupleIndex index))
      | .composite (.vector length type) =>
        pure (List.replicate length type, fun index value => .project value (.vectorIndex index))
      | .composite (.bytes length) =>
        pure (List.replicate length (.scalar (.uint 255)), fun index value => .project value (.byteIndex index))
      | .scalar (.bytes length) =>
        pure (List.replicate length (.scalar (.uint 255)), fun index value => .bytesAt value index)
      | _ => throwErrorAt pattern "positional pattern requires a tuple, vector or fixed bytes"
    unless items.getElems.size == types.length do
      throwErrorAt pattern s!"positional pattern requires {types.length} positions"
    (items.getElems.toList.zip types).zipIdx.flatMapM fun ((item, child), index) =>
      patternBindings composites item (Helpers.resultTypeOfComposite child) (project index ∘ select)
  | `(noctium_bind_pattern| {$fields,*}) => do
    let .composite (.structure id) := type | throwErrorAt pattern "record pattern requires a nominal record value"
    let mut seen : List String := []
    let mut bindings := []
    for field in fields.getElems do
      let `(noctium_bind_field| $name:ident $[:= $nested:noctium_bind_pattern]?) := field
        | throwErrorAt field "invalid record pattern field"
      let key := name.getId.toString
      if seen.contains key then throwErrorAt name s!"duplicate record pattern field '{key}'"
      let projection := Types.Projection.field key
      let span ← spanValue name
      let child ← match Helpers.projectedType composites span (.structure id) projection with
        | .ok child => pure (Helpers.resultTypeOfComposite child)
        | .error diagnostic => throwErrorAt name diagnostic.message
      let projectChild := fun value => Helpers.Term.project (select value) projection
      let selected ← match nested with
        | none => pure [(name, child, projectChild)]
        | some binding => patternBindings composites binding child projectChild
      seen := seen ++ [key]
      bindings := bindings ++ selected
    pure bindings
  | _ => throwErrorAt pattern "unsupported readable binding pattern"

private def extendPatternEnvironment (initial : SurfaceEnv) (bindings : List PatternBinding) :
    CommandElabM SurfaceEnv := do
  let mut env := initial
  for (id, type, _) in bindings do
    let name := id.getId.toString
    if env.any (·.1 == name) then throwErrorAt id s!"duplicate readable witness value '{name}'"
    env := (name, type, .ref name) :: env
  pure env

private def patternStatements (bindings : List PatternBinding) (source : Helpers.Term) :
    CommandElabM (List Statement) :=
  bindings.mapM fun (id, type, project) => do
    pure (.bind id.getId.toString type (.at (← spanValue id) (project source)))

private def lowerReadablePattern (programName path : String) (exprState : AuthoringExprState)
    (body : ReadableBody) (statement : Syntax) (pattern : TSyntax `noctium_bind_pattern)
    (source : TSyntax `nlexpr) : CommandElabM ReadableBody := do
  let (value, body) ← body.lower programName path exprState source
  let bindings ← patternBindings body.composites pattern value.type id
  let env ← extendPatternEnvironment body.env bindings
  let span ← spanValue statement
  let ((before, terms, _), state) ← (stageIterationValues ("s" ++ path) env span [value]).run
    {exprState with nextLet := body.nextLet, iterationProgram := body.helperProgram}
  let [staged] := terms | throwErrorAt statement "binding pattern must stage one source value"
  let projected ← patternStatements bindings staged
  let body := body.observe value [source]
  pure {body with
    env := env
    statements := body.statements ++ before ++ projected
    nextLet := state.nextLet
    requiresOutputViews := _root_.Bool.true}

private partial def lowerReadableStatement (programName path : String)
    (exprState : AuthoringExprState) (codecTerms : Array (TSyntax `term))
    (body : ReadableBody) (statement : TSyntax `noctium_witness_statement) :
    CommandElabM ReadableBody := do
  match statement with
  | `(noctium_witness_statement| let [$items,*] := $source:nlexpr) =>
    lowerReadablePattern programName path exprState body statement (← `(noctium_bind_pattern| [$items,*])) source
  | `(noctium_witness_statement| let {$fields,*} := $source:nlexpr) =>
    lowerReadablePattern programName path exprState body statement (← `(noctium_bind_pattern| {$fields,*})) source
  | `(noctium_witness_statement| read private $fieldPath:ident as $id:ident) => do
    let field ← lookupPrivateField fieldPath
    let valueName := id.getId.toString
    if body.env.any (·.1 == valueName) then
      throwErrorAt id s!"duplicate readable witness value '{valueName}'"
    let site := s!"{programName}.read.{path}"
    validIdentity statement site
    if let some codec := field.codec then
      unless codecTerms.any (·.raw.getId == codec) do
        throwErrorAt fieldPath s!"add codec '{privateToUserName codec}' to the circuit's using clause"
    let signature := field.signature
    let readTerm := Noctium.Helpers.Term.witnessCall site signature.name []
    let logicalAliases := match signature.result with
      | .scalar ty => body.logicalAliases ++ [{name := valueName, ty, source := .call site}]
      | _ => body.logicalAliases
    pure {body with
      env := (valueName, signature.result, .ref valueName) :: body.env
      statements := body.statements ++ [.bind valueName signature.result (.at (← spanValue statement) readTerm)]
      witnesses := uniqueWitnesses (body.witnesses ++ [signature])
      logicalAliases
      observation := {body.observation with
        privateReads := (body.observation.privateReads ++ [field.key]).eraseDups
        generatedValidity :=
          (body.observation.generatedValidity ++ [s!"typed private-state read reply: {field.key}"]).eraseDups}}
  | `(noctium_witness_statement| witness $function:ident($args:nlexpr,*)) => do
    let source ← `(nlexpr| witness $function($args,*))
    let (value, body) ← body.lower programName path exprState source
    let .unit := value.type | throwErrorAt statement "standalone witness statements must call a Unit witness"
    let body := body.observe value args.getElems.toList (typedReplies := _root_.Bool.false)
    pure {body with statements := body.statements ++ value.before ++ [.evaluate value.term]}
  | `(noctium_witness_statement| let $id:ident $[: $type:nltype]? := $source:nlexpr) => do
    let valueName := id.getId.toString
    if body.env.any (·.1 == valueName) then
      throwErrorAt id s!"duplicate readable witness value '{valueName}'"
    let annotation ← match type with
      | some annotation => some <$> readScalarTy annotation
      | none => pure none
    let (lowered, body) ← body.lower programName path exprState source
      (annotation.map ResultType.scalar)
    let value ← match annotation with
      | some annotation => coerce source lowered annotation
      | none => pure lowered
    let logicalAliases := match value.type with
      | .scalar ty => body.logicalAliases ++ [{name := valueName, ty, source := readableAliasSource value source}]
      | _ => body.logicalAliases
    let body := body.observe value [source]
    pure {body with
      env := (valueName, value.type, .ref valueName) :: body.env
      statements := body.statements ++ value.before ++ [.bind valueName value.type (.at (← spanValue statement) value.term)]
      logicalAliases}
  | `(noctium_witness_statement| prove $source:nlexpr $[as $binder:ident]?) => do
    if let some id := binder then
      if body.env.any (·.1 == id.getId.toString) then
        throwErrorAt id s!"duplicate readable witness value '{id.getId}'"
    let (lowered, body) ← body.lower programName path
      {exprState with allowAssertThen := _root_.Bool.true} source
    let value ← coerce source lowered .bool
    let observation := {body.observation with
      authoredProves := (body.observation.authoredProves ++ [renderExpr source]).eraseDups}
    let body := {body with observation}.observe value [source]
    let span ← spanValue statement
    let body := {body with statements := body.statements ++ value.before ++ [.assert (.at span value.term)]}
    match binder with
    | none => pure body
    | some id =>
      let name := id.getId.toString
      pure {body with
        env := (name, .unit, .ref name) :: body.env
        statements := body.statements ++ [.bind name .unit (.at span .unit)]}
  | `(noctium_witness_statement| stage $fieldPath:ident := $source:nlexpr) => do
    let field ← lookupPrivateField fieldPath
    let .scalar ty := field.signature.result
      | throwErrorAt fieldPath "private staging currently requires a scalar cell"
    let (lowered, body) ← body.lower programName path exprState source
    let value ← coerce source lowered ty
    let body := body.observe value [source] [s!"typed staged private-state value: {field.key}"]
    pure {body with
      statements := body.statements ++ value.before ++ [.stage field.capability field.key ty (.at (← spanValue statement) value.term)]
      observation := {body.observation with
        privateStages := (body.observation.privateStages ++ [field.key]).eraseDups}}
  | `(noctium_witness_statement| for $index:ident in $start:num ..< $stop:num do
      $nested:noctium_witness_statement* end) => do
    let indexName := index.getId.toString
    if body.env.any (·.1 == indexName) then
      throwErrorAt index s!"finite loop index '{indexName}' conflicts with an enclosing readable witness value"
    let mut loop := {body with
      env := (indexName, .scalar .native, .ref indexName) :: body.env
      statements := []
      logicalAliases := []}
    for (child, ordinal) in nested.toList.zipIdx do
      loop ← lowerReadableStatement programName s!"{path}.{ordinal}" exprState codecTerms loop child
    pure {body with
      statements := body.statements ++ [.forRange indexName start.getNat stop.getNat loop.statements]
      witnesses := loop.witnesses
      observation := loop.observation
      nextLet := loop.nextLet
      helperProgram := loop.helperProgram
      requiresOutputViews := loop.requiresOutputViews
      iterationParameters := loop.iterationParameters}
  | `(noctium_witness_statement| for $item:ident $[: $annotation:nltype]? in $sequence:nlexpr do
      $nested:noctium_witness_statement* end) => do
    let itemName := item.getId.toString
    if body.env.any (·.1 == itemName) then
      throwErrorAt item s!"sequence loop variable '{itemName}' conflicts with an enclosing readable witness value"
    let (sequenceValue, sourceBody) ← body.lower programName path exprState sequence
    let sourceBody := sourceBody.observe sequenceValue [sequence]
    let sequenceSpan ← spanValue statement
    let loopExprState : AuthoringExprState := {
      exprState with
      iterationProgram := sourceBody.helperProgram
      iterationWitnesses := sourceBody.witnesses
      requiresOutputViews := sourceBody.requiresOutputViews
      nextLet := sourceBody.nextLet
      iterationParameters := sourceBody.iterationParameters}
    let ((before, terms, staged), loopExprState) ←
      (stageIterationValues ("s" ++ path) sourceBody.env sequenceSpan [sequenceValue]).run loopExprState
    let [sequenceTerm] := terms
      | throwErrorAt statement "sequence loop must contain one sequence"
    let helperEnv := iterationEnvironment
      sourceBody.env staged sourceBody.iterationParameters
    let (program, _) ← (iterationProgram statement programName sequenceValue.signatures).run loopExprState
    let inferred ← match Iteration.sequenceElementTypesWithLimits {}
        program 0 helperEnv sequenceSpan [sequenceTerm] with
      | .ok [elementType] => pure elementType
      | .ok _ => throwErrorAt statement "sequence loop type inference failed"
      | .error diagnostic => throwErrorAt sequence diagnostic.message
    let knownElementType ← match annotation with
      | some type => some <$> (ResultType.scalar <$> readScalarTy type)
      | none => pure inferred
    let initialLoopState : AuthoringExprState := {
      exprState with
      iterationProgram := some program
      iterationWitnesses := sourceBody.witnesses
      requiresOutputViews := sourceBody.requiresOutputViews
      nextLet := loopExprState.nextLet
      iterationParameters := sourceBody.iterationParameters}
    let (elementRef, loopExprState) ← match knownElementType with
      | some _ => pure (itemName, initialLoopState)
      | none =>
        (unresolvedIterationParameter itemName).run initialLoopState
    let placeholderType := knownElementType.getD .unit
    let mut loop := {sourceBody with
      env := (itemName, placeholderType, .ref elementRef) :: sourceBody.env
      statements := []
      logicalAliases := []
      helperProgram := some program
      nextLet := loopExprState.nextLet
      iterationParameters := loopExprState.iterationParameters}
    for (child, ordinal) in nested.toList.zipIdx do
      loop ← lowerReadableStatement programName s!"{path}.{ordinal}" exprState codecTerms loop child
    let localViews := iterationViewBindings loop.iterationParameters [elementRef]
    let retainedParameters := retainIterationScope loop.iterationParameters [elementRef]
    let resolvedHelperEnv := iterationEnvironment
      sourceBody.env staged retainedParameters
    let operator := Iteration.Operator.anonymous
      [{name := elementRef, type := knownElementType}] (some .unit)
      (localViews ++ loop.statements ++ [.return none])
    let callbackState : AuthoringExprState := {
      exprState with
      iterationProgram := loop.helperProgram
      iterationWitnesses := loop.witnesses
      requiresOutputViews := loop.requiresOutputViews
      nextLet := loop.nextLet
      iterationParameters := retainedParameters}
    let (callbackProgram, _) ←
      (iterationProgram statement programName loop.witnesses).run callbackState
    let (compiledProgram, term) ← match Iteration.mapWithLimits {}
        callbackProgram 0 resolvedHelperEnv sequenceSpan [sequenceTerm] operator with
      | .ok result => pure result
      | .error diagnostic => throwErrorAt statement diagnostic.message
    pure {body with
      statements := body.statements ++ before ++ [.evaluate term]
      witnesses := loop.witnesses
      observation := loop.observation
      nextLet := loop.nextLet
      helperProgram := some compiledProgram
      requiresOutputViews := loop.requiresOutputViews
      iterationParameters := retainedParameters}
  | _ => throwErrorAt statement "finite range bodies accept let, prove, witness, private read and stage, and nested for statements"

@[command_elab noctiumAuthoredWitnessCircuitCommand] unsafe def elabAuthoredWitnessCircuit : CommandElab := fun stx => do
  match stx with
  | `(noctium_witness_circuit $name:ident $[using $usingCodecs:ident,*]?
      $[with $librarySource:ident]? where $statements:noctium_witness_statement* end) => do
    let fullName := (← getCurrNamespace) ++ name.getId
    let programName := generatedName fullName "__program"
    let observationName := generatedName fullName "__observation"
    let programSyntaxName := generatedName name.getId "__program"
    let observationSyntaxName := generatedName name.getId "__observation"
    if (← getEnv).contains programName || (← getEnv).contains observationName then
      throwErrorAt name "generated readable witness program name already exists"
    let programNameText := fullName.toString
    validIdentity name programNameText
    let exportName := "noctium.witness-circuit." ++ programNameText ++ ".v1"
    validIdentity name exportName
    let codecNames := (usingCodecs.map (·.getElems)).getD #[]
    let mut codecs : List (Name × Helpers.Wire.Codec) := []
    let mut resolvedCodecs : List (Name × Helpers.Wire.Codec) := []
    let mut codecTerms : Array (TSyntax `term) := #[]
    for codecName in codecNames do
      if codecs.any (·.1 == codecName.getId) then
        throwErrorAt codecName "duplicate readable wire codec"
      let source ← liftCoreM <| resolveGlobalConstNoOverload codecName
      let codec ← evalConstCheck Helpers.Wire.Codec ``Helpers.Wire.Codec source
      codecs := codecs ++ [(codecName.getId, codec)]
      resolvedCodecs := resolvedCodecs ++ [(source, codec)]
      codecTerms := codecTerms.push ⟨mkIdent source⟩
    let (libraryName, library) ← match librarySource with
      | none => pure (none, none)
      | some librarySource => do
        let source ← liftCoreM <| resolveGlobalConstNoOverload librarySource
        let library ← evalConstCheck Helpers.Program ``Helpers.Program source
        pure (some source, some library)
    let attached ← match library with
      | none => pure none
      | some library =>
        match Helpers.Wire.attach library (codecs.map (·.2)) with
        | .ok program => pure (some program)
        | .error message => throwErrorAt stx message
    let initialComposites := (attached.map (·.composites)).getD
      (Helpers.Wire.compositeEnv {} (codecs.map (·.2)))
    let exprState : AuthoringExprState := {codecs, composites := initialComposites}
    let mut sourceBody : ReadableBody := {
      observation := {entryName := exportName}
      composites := initialComposites
      helperProgram := attached
      witnesses := (attached.map (·.witnesses)).getD []}
    let mut parameters : List Parameter := []
    let mut inputs : List Input := []
    let mut aggregateInputs : List AggregateInput := []
    let mut outputName := ""
    let mut outputType : ResultType := .unit
    let mut authoredOutputs : List AuthoredOutput := []
    for (statement, ordinal) in statements.toList.zip (List.range statements.size) do
      sourceBody := {sourceBody with nextLet := 0}
      let isOutput := statement.raw[0].getAtomVal == "output"
      if !authoredOutputs.isEmpty && !isOutput then
        throwErrorAt statement "no statements may follow the circuit outputs"
      match statement with
      | `(noctium_witness_statement| public $id:ident : $type:noctium_witness_input_type $[as $pattern:noctium_bind_pattern]?)
      | `(noctium_witness_statement| private $id:ident : $type:noctium_witness_input_type $[as $pattern:noctium_bind_pattern]?) => do
        let valueName := id.getId.toString
        if sourceBody.env.any (·.1 == valueName) then throwErrorAt id s!"duplicate readable witness value '{valueName}'"
        let visibility := if statement.raw[0].getAtomVal == "public" then Noctium.Visibility.public else Noctium.Visibility.private
        let span ← spanValue statement
        let (inputType, inputLabel) : ResultType × String ← match type with
          | `(noctium_witness_input_type| $scalar:nltype) => do
            let ty ← readScalarTy scalar
            parameters := parameters ++ [{name := valueName, ty}]
            inputs := inputs ++ [{name := valueName, ty, visibility, span}]
            pure (.scalar ty, typeName ty)
          | `(noctium_witness_input_type| Payload $codecName:ident) => do
            let (codec, _) ← (selectedCodec codecName).run' exprState
            let result := if codec.payload == .unit then .unit else .composite codec.payload
            parameters := parameters ++ [{name := valueName, ty := .native}]
            aggregateInputs := aggregateInputs ++ [{name := valueName, type := codec.payload, visibility, span}]
            pure (result, s!"Payload {codecName.getId}")
          | _ => throwErrorAt type "unsupported readable witness input type"
        let input : ObservationInput := {name := valueName, type := inputLabel, visibility}
        let source := Helpers.Term.ref valueName
        sourceBody := {sourceBody with
          env := (valueName, inputType, source) :: sourceBody.env
          observation := {sourceBody.observation with inputs := sourceBody.observation.inputs ++ [input]}}
        if let some pattern := pattern then
          let bindings ← patternBindings sourceBody.composites pattern inputType _root_.id
          let env ← extendPatternEnvironment sourceBody.env bindings
          let projected ← patternStatements bindings source
          sourceBody := {sourceBody with
            env := env
            statements := sourceBody.statements ++ projected
            requiresOutputViews := _root_.Bool.true}
      | `(noctium_witness_statement| output $id:ident $[: $type:nltype]? := $value:nlexpr) => do
        let valueName := id.getId.toString
        if sourceBody.env.any (·.1 == valueName) || authoredOutputs.any (·.name == valueName) then
          throwErrorAt id s!"duplicate readable witness output '{valueName}'"
        let sourceExpr := value
        let (lowered, updatedBody) ← sourceBody.lower programNameText (toString ordinal) exprState sourceExpr
        let outputSpan ← spanValue statement
        let value ← match type with
          | some annotation => coerce sourceExpr lowered (← readScalarTy annotation)
          | none => do
            let .composite _ := lowered.type
              | throwErrorAt id "scalar outputs require a type annotation"
            pure lowered
        let source := readableAliasSource value sourceExpr
        let nominalBytes32? := if value.type == .scalar (.bytes 32) then
            nominalBytes32OfOutput? exprState sourceExpr
          else none
        authoredOutputs := authoredOutputs ++ [{
          name := valueName
          value := value
          span := outputSpan
          ordinal := ordinal
          source := source
          nominalBytes32 := nominalBytes32?
        }]
        sourceBody := updatedBody.observe value [sourceExpr]
      | _ =>
        sourceBody ← lowerReadableStatement programNameText (toString ordinal) exprState codecTerms
          sourceBody statement
    let witnesses := sourceBody.witnesses
    let resultCodecs := (noctiumWitnessResultCodecRegistry.getState (← getEnv)).toList
    let parameterCodecs := (noctiumWitnessParameterCodecRegistry.getState (← getEnv)).toList
    for signature in witnesses do
      if let some required := resultCodecs.find? (·.signatureName == signature.name) then
        let some (_, requiredCodec) := resolvedCodecs.find? (·.1 == required.codec)
          | throwErrorAt name
              s!"witness result '{signature.name}' requires codec '{required.codec}' in this circuit's using clause"
        if let .composite payload := signature.result then
          for (candidateName, candidate) in resolvedCodecs do
            let conflicts := candidate.payload == payload &&
              (candidate.frameBytes != requiredCodec.frameBytes ||
                candidate.composites != requiredCodec.composites)
            if conflicts then
              throwErrorAt name
                s!"witness result '{signature.name}' has conflicting codecs '{required.codec}' and '{candidateName}' in this circuit's using clause"
      for parameter in signature.parameters do
        if let some required := parameterCodecs.find? (fun item =>
            item.signatureName == signature.name && item.parameterName == parameter.name) then
          let some (_, requiredCodec) := resolvedCodecs.find? (·.1 == required.codec)
            | throwErrorAt name
                s!"witness parameter '{signature.name}.{parameter.name}' requires codec '{required.codec}' in this circuit's using clause"
          if let .composite payload := parameter.type then
            unless requiredCodec.payload == payload do
              throwErrorAt name s!"witness parameter '{signature.name}.{parameter.name}' codec payload identity mismatch"
            for (candidateName, candidate) in resolvedCodecs do
              let conflicts := candidate.payload == payload &&
                (candidate.frameBytes != requiredCodec.frameBytes ||
                  candidate.composites != requiredCodec.composites)
              if conflicts then
                throwErrorAt name
                  s!"witness parameter '{signature.name}.{parameter.name}' has conflicting codecs '{required.codec}' and '{candidateName}' in this circuit's using clause"
    let mut body := sourceBody.statements
    let compositeId := programNameText ++ ".Output"
    let compositeType := Types.CompositeType.structure compositeId
    let grouped := authoredOutputs.length > 1
    let hasAggregate := authoredOutputs.any fun item =>
      match item.value.type with
      | .composite _ => _root_.Bool.true
      | _ => _root_.Bool.false
    let hasAggregateRead := witnesses.any fun signature =>
      signature.privateKey.isSome && match signature.result with
      | .composite _ => _root_.Bool.true
      | _ => _root_.Bool.false
    let useOutputViews := hasAggregate ||
      (grouped && (sourceBody.requiresOutputViews || !aggregateInputs.isEmpty || hasAggregateRead))
    let compositeFields : List Types.Field := authoredOutputs.map fun item =>
      {name := item.name, type := item.layoutType, span := item.span}
    let declarationSpan ← spanValue stx
    let compositeEnv : Types.CompositeEnv := if grouped then
      {structures := [{id := compositeId, fields := compositeFields, span := declarationSpan}]}
      else {}
    match authoredOutputs with
    | [] => body := body ++ [.return none]
    | [item] =>
      if let .scalar _ := item.value.type then outputName := item.name
      outputType := item.value.type
      body := body ++ item.value.before ++ [.return (some (.at item.span item.value.term))]
    | _ =>
      outputType := .composite compositeType
      let mut outputReferences := []
      for item in authoredOutputs do
        let bindingName := s!"__noctium_output_{item.ordinal}_{item.name}"
        if sourceBody.env.any (·.1 == bindingName) || authoredOutputs.any (·.name == bindingName) then
          throwErrorAt stx "generated composite output binding collides with a source name"
        body := body ++ item.value.before ++ [
          .bind bindingName item.value.type (.at item.span item.value.term)]
        let leaves : List Noctium.Helpers.Term ← match item.value.type with
          | .scalar (.bytes length) =>
            pure ((List.range length).map fun index => .cast .native (.bytesAt (.ref bindingName) index))
          | .composite payload => do
            let .ok layout := Types.compileType sourceBody.composites payload
              | throwErrorAt stx s!"invalid aggregate output layout for '{item.name}'"
            match Helpers.Iteration.flattenResult item.span item.value.type
                layout.checked.value (.ref bindingName) with
            | .ok leaves => pure leaves
            | .error diagnostic => throwErrorAt stx diagnostic.message
          | _ => pure [.ref bindingName]
        outputReferences := outputReferences ++ leaves
      body := body ++ [.return (some (.composite compositeType outputReferences))]
    let observation := sourceBody.observation
    let helperProgram := sourceBody.helperProgram
    let mut ordinal := 0
    if library.isSome then
      let declarations := (helperProgram.map (·.declarations)).getD []
      while declarations.any (fun declaration => declaration.id == ⟨0, ordinal⟩) do
        ordinal := ordinal + 1
    let declId : DeclarationId := ⟨0, ordinal⟩
    let declaration : Noctium.Helpers.Declaration :=
      { id := declId,
        name := programNameText,
        parameters := parameters,
        compositeParameters := aggregateInputs.map fun input => (input.name, input.type),
        result := outputType,
        body := body,
        span := declarationSpan }
    let exportSpan ← spanValue stx
    let entryExport : Export :=
      { name := exportName,
        target := declId,
        inputs := inputs,
        compositeInputs := aggregateInputs,
        span := exportSpan }
    let program : Program := match helperProgram with
      | none =>
        {declarations := [declaration], exports := [entryExport],
          composites := {
            sourceBody.composites with
            structures := (sourceBody.composites.structures ++ compositeEnv.structures).eraseDups
            enumerations := (sourceBody.composites.enumerations ++ compositeEnv.enumerations).eraseDups},
          witnesses := witnesses}
      | some program =>
        {program with
          declarations := (program.declarations.filter fun item =>
            library.isSome || item.id != ⟨0, 0⟩) ++ [declaration]
          exports := [entryExport]
          composites := {
            sourceBody.composites with
            structures := (sourceBody.composites.structures ++ compositeEnv.structures ++
              program.composites.structures).eraseDups
            enumerations := (sourceBody.composites.enumerations ++ compositeEnv.enumerations ++
              program.composites.enumerations).eraseDups},
          witnesses := witnesses}
    if helperProgram.isNone then
      match Helpers.Wire.attach program (codecs.map (·.2)) with
      | .ok _ => pure ()
      | .error message => throwErrorAt stx message
    let describeOutputs (program : Program) (compiled : Witness.Compiled) : CommandElabM _ := do
      let mut logicalEnv : List (String × Ty × TSyntax `term) := []
      for input in inputs do
        let value ← `(@Noctium.Expr.ref $(← tyTerm input.ty) $(stringTerm input.name))
        logicalEnv := logicalEnv ++ [(input.name, input.ty, value)]
      let mut logicalOutputAliases : List (String × Ty × Name) := []
      let nominalBytes32Outputs := authoredOutputs.filterMap fun item =>
        item.nominalBytes32.map fun nominal => (item.name, nominal)
      let defineAlias (item : AuthoredOutput) (ty : Ty) (value : TSyntax `term) : CommandElabM Name := do
        let suffix := s!"__logicalOutput_{item.ordinal}_{item.name}"
        let aliasName := generatedName fullName suffix
        if (← getEnv).contains aliasName then
          throwErrorAt stx "generated logical output alias name already exists"
        let localName := generatedName name.getId suffix
        elabCommand (← `(def $(mkIdent localName) : Noctium.Expr $(← tyTerm ty) := $value))
        pure aliasName
      for binding in (if grouped && !useOutputViews then sourceBody.logicalAliases else []) do
        if logicalEnv.any (fun alias => alias.1 == binding.name) then
          throwErrorAt stx s!"duplicate logical output alias source '{binding.name}'"
        let value ← match binding.source with
          | .expression source =>
            Noctium.quoteSourceExpression logicalEnv source binding.ty
          | .call site => do
            let some call := compiled.calls.find? (·.site == site)
              | throwErrorAt stx s!"compiled witness call '{site}' is missing its result binding"
            unless call.result == .scalar binding.ty do
              throwErrorAt stx s!"witness call '{site}' does not produce a scalar logical alias"
            let some inputName := call.inputs.head?
              | throwErrorAt stx s!"witness call '{site}' has no scalar result binding"
            `(@Noctium.Expr.ref $(← tyTerm binding.ty) $(stringTerm inputName))
        logicalEnv := logicalEnv ++ [(binding.name, binding.ty, value)]
      if grouped && !useOutputViews then
        for item in authoredOutputs do
          let .scalar fieldType := item.value.type
            | throwErrorAt stx "expected a grouped scalar circuit output"
          let value ← match item.source with
            | .expression expression =>
              Noctium.quoteSourceExpression logicalEnv expression fieldType
            | .call site => do
              let some call := compiled.calls.find? (·.site == site)
                | throwErrorAt stx s!"compiled witness call '{site}' is missing its result binding"
              unless call.result == .scalar fieldType do
                throwErrorAt stx s!"witness call '{site}' does not produce a scalar logical output"
              let some inputName := call.inputs.head?
                | throwErrorAt stx s!"witness call '{site}' has no scalar result binding"
              `(@Noctium.Expr.ref $(← tyTerm fieldType) $(stringTerm inputName))
          let aliasName ← defineAlias item fieldType value
          logicalOutputAliases := logicalOutputAliases ++ [(item.name, fieldType, aliasName)]
      let mut registeredAggregates := []
      if useOutputViews then
        let mut remaining := compiled.circuit.outputs.map (·.name)
        for item in authoredOutputs do
          let .ok layout := Types.compileType program.composites item.layoutType
            | throwErrorAt stx s!"invalid circuit output layout for '{item.name}'"
          let (fields, rest) := remaining.splitAt layout.checked.value.leafCount
          unless fields.length == layout.checked.value.leafCount do
            throwErrorAt stx "circuit output layout exceeds the compiled Native fields"
          remaining := rest
          match item.value.type with
          | .composite payload =>
            let suffix := if grouped then s!"__returnView_{item.ordinal}" else "__returnView"
            let localName := generatedName name.getId suffix
            let fullViewName := generatedName fullName suffix
            if (← getEnv).contains fullViewName then throwErrorAt name "aggregate return view already exists"
            let fieldTerms := (fields.map stringTerm).toArray
            let payload ← compositeTypeTerm payload
            elabCommand (← `(def $(mkIdent localName) : Noctium.ReturnView := {
              name := $(stringTerm item.name)
              environment := $(mkIdent programName).composites
              type := $payload
              fields := [$fieldTerms,*]
            }))
            registeredAggregates := registeredAggregates ++ [(item.name, fullViewName, fields)]
          | .scalar ty =>
            let value ← match ty with
              | .bytes _ => quoteByteLeaves fields
              | .jubjubScalar | .jubjubPoint | .foreign _ => do
                let inputs ← fields.toArray.mapM fun field =>
                  `(@Noctium.Expr.ref Noctium.Ty.native $(stringTerm field))
                let type ← tyTerm ty
                `((Noctium.Wire.decodeCurveFields $type [$inputs,*]).toOption.get (by decide))
              | _ => do
                let [field] := fields | throwErrorAt stx "expected one Native field for a scalar output"
                let ref ← `(@Noctium.Expr.ref Noctium.Ty.native $(stringTerm field))
                if ty == .native then pure ref else `(Noctium.Expr.cast $(← tyTerm ty) $ref)
            let aliasName ← defineAlias item ty value
            logicalOutputAliases := logicalOutputAliases ++ [(item.name, ty, aliasName)]
          | .unit => throwErrorAt stx "unexpected Unit circuit output"
        unless remaining.isEmpty do
          throwErrorAt stx "circuit output layout did not consume the compiled Native fields"
      pure (logicalOutputAliases, registeredAggregates, nominalBytes32Outputs)
    let signatureTerms ← witnesses.mapM quoteSignature
    let signatureTerms := signatureTerms.toArray
    let inputTerms ← inputs.mapM fun input => inputTerm input.name input.ty input.visibility input.span
    let inputTerms := inputTerms.toArray
    let aggregateInputTerms ← aggregateInputs.mapM fun input => do
      let visibility ← if input.visibility == .public then `(Noctium.Visibility.public)
        else `(Noctium.Visibility.private)
      `(Noctium.Helpers.AggregateInput.mk $(stringTerm input.name) $(← compositeTypeTerm input.type)
        $visibility $(← quoteSpan input.span))
    let aggregateInputTerms := aggregateInputTerms.toArray
    let libraryDeclarations := (library.map (·.declarations)).getD []
    let newDeclarations := program.declarations.filter fun declaration =>
      !libraryDeclarations.any (fun inherited => inherited.id == declaration.id)
    let declarationTerms ← newDeclarations.mapM fun declaration => do
      let parameterTerms ← declaration.parameters.mapM fun parameter => do
        `( ({ name := $(stringTerm parameter.name), ty := $(← tyTerm parameter.ty) } : Noctium.Helpers.Parameter))
      let parameterTerms := parameterTerms.toArray
      let compositeParameterTerms ← declaration.compositeParameters.mapM fun (name, type) => do
        `(($(stringTerm name), $(← compositeTypeTerm type)))
      let compositeParameterTerms := compositeParameterTerms.toArray
      let statementTerms ← declaration.body.mapM statementTerm
      let statementTerms := statementTerms.toArray
      let id ← `(Noctium.Helpers.DeclarationId.mk $(natTerm declaration.id.scope)
        $(natTerm declaration.id.ordinal))
      let result ← resultTypeTerm declaration.result
      let declaredPure ← if declaration.declaredPure then `(Bool.true) else `(Bool.false)
      `(Noctium.Helpers.Declaration.mk $id $(stringTerm declaration.name)
        [$parameterTerms,*] [$compositeParameterTerms,*] $result
        [$statementTerms,*] $declaredPure $(← quoteSpan declaration.span))
    let declarationTerms := declarationTerms.toArray
    let structureTerms ← program.composites.structures.mapM fun structDecl => do
      let fieldTerms ← structDecl.fields.mapM fun field => do
        let fieldType ← compositeTypeTerm field.type
        let fieldSpan ← quoteSpan field.span
        `(Noctium.Types.Field.mk $(stringTerm field.name) $fieldType $fieldSpan)
      let fieldTerms := fieldTerms.toArray
      `(Noctium.Types.StructDecl.mk $(stringTerm structDecl.id) [$fieldTerms,*]
        $(← quoteSpan structDecl.span))
    let structureTerms := structureTerms.toArray
    let enumerationTerms ← program.composites.enumerations.mapM fun enumeration => do
      let variantTerms ← enumeration.variants.mapM fun variant => do
        let fieldTerms ← variant.fields.mapM fun field => do
          `(Noctium.Types.Field.mk $(stringTerm field.name)
            $(← compositeTypeTerm field.type) $(← quoteSpan field.span))
        let fieldTerms := fieldTerms.toArray
        `(Noctium.Types.VariantDecl.mk $(stringTerm variant.name) [$fieldTerms,*]
          $(← quoteSpan variant.span))
      let variantTerms := variantTerms.toArray
      `(Noctium.Types.EnumDecl.mk $(stringTerm enumeration.id) [$variantTerms,*]
        $(← quoteSpan enumeration.span))
    let enumerationTerms := enumerationTerms.toArray
    let compositeEnvTerm ← `({
      structures := [$structureTerms,*]
      enumerations := [$enumerationTerms,*]
      : Noctium.Types.CompositeEnv })
    let exportSpanTerm ← quoteSpan entryExport.span
    let exportId ← `(Noctium.Helpers.DeclarationId.mk 0 $(natTerm ordinal))
    let exportTerm ← `(Noctium.Helpers.Export.mk $(stringTerm entryExport.name) $exportId
      [$inputTerms,*] [$aggregateInputTerms,*] $exportSpanTerm)
    let localDeclarations ← `([$declarationTerms,*])
    let programTerm ← match libraryName with
      | some source =>
        let library := mkIdent source
        `({
          scopes := $(library).scopes
          declarations := $(library).declarations ++ $localDeclarations
          exports := [$exportTerm]
          composites := $compositeEnvTerm
          witnesses := [$signatureTerms,*]
          ledger := $(library).ledger
          : Noctium.Helpers.Program })
      | none => `({
          scopes := [{id := 0}]
          declarations := $localDeclarations
          exports := [$exportTerm]
          composites := $compositeEnvTerm
          witnesses := [$signatureTerms,*]
          : Noctium.Helpers.Program })
    let programTerm ← if codecTerms.isEmpty || helperProgram.isSome then pure programTerm else
      `(match Noctium.Helpers.Wire.attach $programTerm [$codecTerms,*] with
        | .ok program => program
        | .error _ => {})
    let metadataTerm ← observationTerm observation
    let envBefore ← getEnv
    try
      elabCommand (← `(def $(mkIdent programSyntaxName) : Noctium.Helpers.Program := $programTerm))
      elabCommand (← `(def $(mkIdent observationSyntaxName) : Noctium.Authoring.ObservationMetadata := $metadataTerm))
      Noctium.registerWitnessCircuit name.raw programName exportName outputName
        (some observation.toJson.compress) describeOutputs
    catch error =>
      modifyEnv fun _ => envBefore
      throw error
  | _ => throwUnsupportedSyntax

end Noctium
