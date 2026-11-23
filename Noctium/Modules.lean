import Noctium.Helpers.Specialization
import Noctium.IR
import Lean

namespace Noctium.Modules

open Lean Noctium.Helpers.Specialization

local instance : Inhabited Diagnostic := ⟨{span := {}, message := ""}⟩

/-- Module members have stable source ordinals assigned by registration. -/
inductive MemberKind where
  | state
  | helper
  | circuit
  | witness
  | entrypoint
  | type
  | module
  deriving Repr, BEq, DecidableEq, Inhabited

inductive MemberVisibility where
  | «private»
  | «public»
  deriving Repr, BEq, DecidableEq, Inhabited

/-- Concrete module types are supplied after issue46 normalization. A source
module may forward one of its own parameters to a nested import. -/
inductive ModuleArgument where
  | typeValue (value : Types.CompositeType)
  | typeParameter (name : String)
  | naturalValue (value : Nat)
  | naturalParameter (name : String)
  deriving Repr, Inhabited

inductive ModuleNatural where
  | literal (value : Nat)
  | parameter (name : String)
  deriving Repr, Inhabited

/-- Ledger state accepts scalar types only. Type parameters must resolve to a
scalar at each module instance. -/
inductive ModuleScalarType where
  | native
  | bool
  | uint (maximum : ModuleNatural)
  | parameter (name : String)
  deriving Repr, Inhabited

inductive ModuleStateKind where
  | cell (value : ModuleScalarType)
  | map (key value : ModuleScalarType)
  deriving Repr, Inhabited

/-- An original generic helper source and export. The source constant remains
the compiler's recheck target through aliases and module views. -/
structure SourceExportRef where
  program : Name
  exportName : String
  arguments : List ModuleArgument := []
  span : SourceSpan := {}
  deriving Repr, Inhabited

/-- The same source export after module parameters have been resolved. -/
structure ResolvedSourceExport where
  program : Name
  exportName : String
  arguments : List SpecializationArgument := []
  span : SourceSpan := {}
  deriving Repr, BEq, Inhabited

/-- The generic source declaration for one module type member. `source` owns
the existing generic structure and alias templates. The concrete checked
type and environment are produced for each module specialization. -/
structure TypeTemplate where
  source : Noctium.Helpers.Specialization.Program
  value : GenericType
  nominalUInt? : Option NominalUIntType := none
  span : SourceSpan := {}
  deriving Repr

instance : Inhabited TypeTemplate := ⟨{source := {}, value := .unit}⟩

structure TypeInfo where
  value : Types.CompositeType
  environment : Types.CompositeEnv
  nominalUInt? : Option NominalUIntType := none
  deriving Repr, BEq, DecidableEq

instance : Inhabited TypeInfo := ⟨{value := .unit, environment := {}}⟩

structure Member where
  id : Nat
  name : String
  kind : MemberKind
  visibility : MemberVisibility := .«private»
  span : SourceSpan := {}
  sourceExport? : Option SourceExportRef := none
  stateKind? : Option StateKind := none
  stateSchema? : Option ModuleStateKind := none
  typeTemplate? : Option TypeTemplate := none
  typeInfo? : Option TypeInfo := none
  /-- A module member names a registered generic module definition. The
  importing module supplies specialization arguments when it selects this
  member as an import target. -/
  moduleTarget? : Option Name := none
  deriving Repr, Inhabited

inductive StateTarget where
  | localMember (member : Nat)
  | importedMember (viewName localName : String)
  deriving Repr, BEq, DecidableEq, Inhabited

inductive ModuleEffect where
  | readCell (state : StateTarget) (destination : String) (ty : Ty)
  | readMap (state : StateTarget) (destination : String) (keyTy valueTy : Ty)
      (key : Expr keyTy)
  | require (condition : Expr .bool)
  | writeCell (state : StateTarget) (ty : Ty) (value : Expr ty)
  | writeCellOutput (state : StateTarget) (outputName : String)
  | writeMap (state : StateTarget) (keyTy valueTy : Ty)
      (key : Expr keyTy) (value : Expr valueTy)
  | requireAbsent (state : StateTarget) (keyTy : Ty) (key : Expr keyTy)
  deriving Repr

structure ModuleEffectSpec where
  effect : ModuleEffect
  span : SourceSpan := {}
  deriving Repr

structure Selection where
  sourceName : String
  localName : String
  span : SourceSpan := {}
  deriving Repr, Inhabited

/-- Imports may name a registered module directly or select a module member
from an import view declared earlier in the same definition. -/
inductive ImportTarget where
  | registered (sourceName : Name)
  | moduleMember (viewName localName : String)
  deriving Repr, Inhabited

instance : Coe Name ImportTarget where
  coe := .registered

structure Import where
  viewName : String
  target : ImportTarget
  arguments : List ModuleArgument := []
  selections : List Selection := []
  span : SourceSpan := {}
  deriving Repr, Inhabited

inductive ExportTarget where
  | localMember (member : Nat)
  | importedMember (viewName localName : String)
  deriving Repr, BEq, DecidableEq, Inhabited

structure ModuleEntrypoint where
  member : Nat
  name : String
  circuit : ExportTarget
  effects : List ModuleEffectSpec := []
  span : SourceSpan := {}
  deriving Repr

structure Export where
  name : String
  target : ExportTarget
  span : SourceSpan := {}
  deriving Repr, Inhabited

/-- Pure source description. Registration supplies the exact Lean constant
identity separately, so display text and view aliases never become identity. -/
structure Definition where
  parameters : List TypeParameter := []
  members : List Member := []
  imports : List Import := []
  exports : List Export := []
  entrypoints : List ModuleEntrypoint := []
  span : SourceSpan := {}
  deriving Repr, Inhabited

structure Registered where
  sourceName : Name
  definition : Definition
  deriving Repr, Inhabited

structure Registry where
  modules : List Registered := []
  deriving Repr, Inhabited

/-- A registered root module and its already normalized specialization args. -/
structure Request where
  sourceName : Name
  arguments : List SpecializationArgument
  deriving Repr, Inhabited

/-- The canonical specialization identity. Arguments are ordered, normalized,
and structural. -/
structure ModuleKey where
  sourceName : Name
  arguments : List SpecializationArgument
  deriving Repr, BEq, Inhabited

structure MemberIdentity where
  module : ModuleKey
  member : Nat
  kind : MemberKind
  deriving Repr, BEq, Inhabited

structure ViewBinding where
  name : String
  identity : MemberIdentity
  kind : MemberKind
  span : SourceSpan := {}
  deriving Repr, Inhabited

structure ImportedView where
  name : String
  target : ModuleKey
  members : List ViewBinding := []
  span : SourceSpan := {}
  deriving Repr, Inhabited

structure ExportedMember where
  name : String
  identity : MemberIdentity
  kind : MemberKind
  span : SourceSpan := {}
  deriving Repr, Inhabited

structure ModuleInstance where
  key : ModuleKey
  digest : Nat
  members : List Member
  sourceExports : List (Nat × ResolvedSourceExport) := []
  entrypoints : List ModuleEntrypoint := []
  imports : List ImportedView := []
  exports : List ExportedMember := []
  span : SourceSpan := {}
  deriving Repr, Inhabited

structure Expansion where
  root : ModuleKey
  instances : List ModuleInstance := []
  deriving Repr, Inhabited

structure ResolvedEntrypoint where
  name : String
  identity : MemberIdentity
  circuit : MemberIdentity
  effects : List Effect
  stateIdentities : List MemberIdentity
  span : SourceSpan
  effectSpans : List SourceSpan
  deriving Repr

structure ModuleCircuitSource where
  identity : MemberIdentity
  outputName : String
  source : ResolvedSourceExport
  kind : MemberKind
  deriving Repr

structure ModuleContractPlan where
  root : ModuleKey
  state : List StateDecl
  entrypoints : List ResolvedEntrypoint
  circuits : List ModuleCircuitSource
  deriving Repr

structure ModuleSpecializationGroup where
  sourceProgram : Name
  requests : List ExportRequest
  deriving Repr, Inhabited

structure SpecializedModule where
  plan : ModuleContractPlan
  batches : List (Name × BatchResult)
  deriving Repr

def SpecializedModule.findBatch (module : SpecializedModule) (sourceProgram : Name) :
    Option BatchResult := (module.batches.find? (·.1 == sourceProgram)).map (·.2)

private def fail (span : SourceSpan) (message : String) : Except Diagnostic α :=
  .error {span, message}

private def resource (span : SourceSpan) (kind : String) : Except Diagnostic α :=
  fail span s!"Noctium module resource limit exceeded: {kind}"

private def validText (span : SourceSpan) (value : String) : Except Diagnostic Unit := do
  if value.isEmpty then fail span "empty module name"
  if value.utf8ByteSize > 1024 then resource span "module source text"

private def uniqueStrings (values : List String) : Bool :=
  values.eraseDups.length == values.length

private def natEncodingSize (value : Nat) : Nat := 2 + (toString value).length

private partial def nameEncodingSize (span : SourceSpan) (fuel : Nat) (name : Name) :
    Except Diagnostic Nat := do
  match fuel with
  | 0 => resource span "module identity depth"
  | fuel + 1 => match name with
    | .anonymous => pure 2
    | .str parent component => do
      validText span component
      let parentSize ← nameEncodingSize span fuel parent
      let textSize := 1 + natEncodingSize component.utf8ByteSize + 1 + component.utf8ByteSize
      pure (1 + parentSize + textSize)
    | .num parent value => do
      let parentSize ← nameEncodingSize span fuel parent
      pure (1 + parentSize + natEncodingSize value)

private def encodeNat (value : Nat) : String := "n" ++ toString value ++ ";"

private def encodeText (value : String) : String :=
  "s" ++ encodeNat value.utf8ByteSize ++ ":" ++ value

private partial def encodeName : Name → String
  | .anonymous => "A;"
  | .str parent component => "S" ++ encodeName parent ++ encodeText component
  | .num parent value => "N" ++ encodeName parent ++ encodeNat value

private partial def canonicalTypeSize (fuel : Nat) (value : Types.CompositeType) :
    Option Nat :=
  match fuel with
  | 0 => none
  | fuel + 1 =>
    let natSize := natEncodingSize
    match value with
    | .unit => some 2
    | .scalar .native => some 3
    | .scalar .bool => some 3
    | .scalar (.uint maximum) => some (2 + natSize maximum)
    | .scalar (.bytes length) => some (2 + natSize length)
    | .scalar .opaqueBytes => none
    | .scalar .opaqueString => none
    | .scalar .jubjubScalar => some 3
    | .scalar .jubjubPoint => some 3
    | .scalar (.foreign kind) =>
      some (2 + 1 + natSize kind.sourceName.utf8ByteSize + 1 + kind.sourceName.utf8ByteSize)
    | .tuple items => do
      let sizes ← items.mapM (canonicalTypeSize fuel)
      pure (3 + natSize items.length + sizes.foldl (· + ·) 0)
    | .structure id | .enumeration id =>
      some (1 + 1 + natSize id.utf8ByteSize + 1 + id.utf8ByteSize)
    | .vector length element => do
      let elementSize ← canonicalTypeSize fuel element
      pure (3 + natSize length + elementSize)
    | .bytes length => some (1 + natSize length)

private partial def consumeTypeNodes (span : SourceSpan) (remaining : Nat)
    (value : Types.CompositeType) : Except Diagnostic Nat := do
  if remaining == 0 then resource span "normalized type nodes"
  let remaining := remaining - 1
  match value with
  | .tuple items => items.foldlM (consumeTypeNodes span) remaining
  | .vector length element => do
    if length > Types.defaultLimits.maxVectorLength then resource span "module vector length"
    consumeTypeNodes span remaining element
  | .bytes length => do
    if length > Types.defaultLimits.maxVectorLength then resource span "module byte length"
    pure remaining
  | .structure id | .enumeration id => do
    validText span id
    unless Types.validDeclId id do fail span s!"invalid module type identity '{id}'"
    pure remaining
  | .scalar (.uint maximum) => do
    if maximum > ScalarPolicy.maxUint then resource span "module unsigned type bound"
    pure remaining
  | .scalar (.bytes _) => fail span "module byte types require a composite bytes layout"
  | .scalar .opaqueBytes => fail span "OpaqueBytes are not supported by module type parameters"
  | .scalar .opaqueString => fail span "OpaqueString is not supported by module type parameters"
  | .scalar .jubjubScalar | .scalar .jubjubPoint => pure remaining
  | .scalar (.foreign _) => pure remaining
  | .scalar .native | .scalar .bool | .unit => pure remaining

private def encodeType : Types.CompositeType → String
  | .unit => "u;"
  | .scalar .native => "sn;"
  | .scalar .bool => "sb;"
  | .scalar (.uint maximum) => "su" ++ encodeNat maximum
  | .scalar (.bytes length) => "sx" ++ encodeNat length
  | .scalar .opaqueBytes => "so;"
  | .scalar .opaqueString => "ss;"
  | .scalar .jubjubScalar => "sj;"
  | .scalar .jubjubPoint => "sp;"
  | .scalar (.foreign kind) => "sf" ++ encodeText kind.sourceName
  | .tuple items => "t" ++ encodeNat items.length ++ "[" ++ String.join (items.map encodeType) ++ "]"
  | .structure id => "r" ++ encodeText id
  | .enumeration id => "e" ++ encodeText id
  | .vector length element => "v" ++ encodeNat length ++ "[" ++ encodeType element ++ "]"
  | .bytes length => "b" ++ encodeNat length

private def encodeArgument : SpecializationArgument → String
  | .type value => "T" ++ encodeType value
  | .natural value => "N" ++ encodeNat value

private def encodeKey (key : ModuleKey) : String :=
  "K1" ++ encodeName key.sourceName ++ "L" ++ encodeNat key.arguments.length ++ "[" ++
    String.join (key.arguments.map encodeArgument) ++ "]"

/-- Fixed, non-cryptographic digest. Exact structural keys remain authoritative
and every digest collision is rejected before emission. -/
private def stableDigest (value : String) : Nat :=
  value.toList.foldl (fun state character =>
    (state * 1099511628211 + character.toNat + 1) % 18446744073709551557)
    14695981039346656037

private def sourceSpanName (name : Name) : String := toString name

private def memberKindName : MemberKind → String
  | .state => "state"
  | .helper => "helper"
  | .circuit => "circuit"
  | .witness => "witness"
  | .entrypoint => "entrypoint"
  | .type => "type"
  | .module => "module"

private def importViewNames (definition : Definition) : List String :=
  definition.imports.map (·.viewName)

private def lookupRegistered (registry : Registry) (name : Name) : Option Registered :=
  registry.modules.find? (·.sourceName == name)

/-- Registration receives the exact Lean constant name from the elaborator. -/
def registerDefinition (sourceName : Name) (definition : Definition) :
    Except Diagnostic Registered := do
  let _ ← nameEncodingSize definition.span 128 sourceName
  if sourceName == .anonymous then fail definition.span "anonymous module source identity"
  pure {sourceName, definition}

def Registry.register (registry : Registry) (sourceName : Name) (definition : Definition) :
    Except Diagnostic Registry := do
  let registered ← registerDefinition sourceName definition
  if (lookupRegistered registry sourceName).isSome then
    fail definition.span s!"duplicate module source identity '{sourceSpanName sourceName}'"
  pure {modules := registry.modules ++ [registered]}

structure Limits where
  maxModules : Nat := 256
  maxModuleInstances : Nat := 256
  maxSourceNodes : Nat := 16384
  maxSourceDepth : Nat := 128
  maxExpansionDepth : Nat := 64
  maxExpandedNodes : Nat := 65536
  maxArguments : Nat := 64
  maxNaturalValue : Nat := ScalarPolicy.maxUint
  maxCanonicalKeyBytes : Nat := 1048576
  maxCanonicalBytes : Nat := 4194304
  deriving Repr, Inhabited

private def validateLimits (limits : Limits) : Except Diagnostic Unit := do
  let hard : Limits := {}
  if limits.maxModules > hard.maxModules || limits.maxModuleInstances > hard.maxModuleInstances ||
      limits.maxSourceNodes > hard.maxSourceNodes || limits.maxSourceDepth > hard.maxSourceDepth ||
      limits.maxExpansionDepth > hard.maxExpansionDepth || limits.maxExpandedNodes > hard.maxExpandedNodes ||
      limits.maxArguments > hard.maxArguments || limits.maxNaturalValue > hard.maxNaturalValue ||
      limits.maxCanonicalKeyBytes > hard.maxCanonicalKeyBytes ||
      limits.maxCanonicalBytes > hard.maxCanonicalBytes then
    resource {} "requested limits exceed hard policy"

private def validateNominalUInt (span : SourceSpan) (value : Types.CompositeType)
    (nominalUInt? : Option NominalUIntType) : Except Diagnostic Unit := do
  if let some nominalUInt := nominalUInt? then
    validText span nominalUInt.name
    if nominalUInt.maximum > ScalarPolicy.maxUint then
      resource span "module nominal UInt bound"
    unless value == .scalar (.uint nominalUInt.maximum) do
      fail span "module nominal UInt identity does not match its scalar type"

private def validateDefinition (limits : Limits) (definition : Definition) :
    Except Diagnostic Nat := do
  if definition.parameters.length > limits.maxArguments then resource definition.span "module parameter count"
  if definition.members.length > limits.maxSourceNodes then resource definition.span "module members"
  if definition.imports.length > limits.maxSourceNodes then resource definition.span "module imports"
  if definition.exports.length > limits.maxSourceNodes then resource definition.span "module exports"
  unless uniqueStrings (definition.parameters.map (·.name)) do
    fail definition.span "duplicate Noctium module parameter"
  for parameter in definition.parameters do validText definition.span parameter.name
  let memberIds := definition.members.map (·.id)
  if memberIds.eraseDups.length != memberIds.length then
    fail definition.span "duplicate Noctium module member identity"
  let mut sourceExportTypeNodes := 0
  for sourceMember in definition.members do
    validText sourceMember.span sourceMember.name
    if sourceMember.id > 18446744073709551615 then resource sourceMember.span "module member identity"
    match sourceMember.kind, sourceMember.moduleTarget? with
    | .module, none =>
      fail sourceMember.span s!"module member '{sourceMember.name}' has no target module"
    | .module, some target =>
      let _ ← nameEncodingSize sourceMember.span limits.maxSourceDepth target
    | _, some _ =>
      fail sourceMember.span "module target is only valid on a module member"
    | _, none => pure ()
    if sourceMember.typeInfo?.isSome then
      fail sourceMember.span "module source cannot provide pre-resolved type metadata"
    if sourceMember.kind == .type && sourceMember.typeTemplate?.isNone then
      fail sourceMember.span s!"type member '{sourceMember.name}' has no checked type template"
    if sourceMember.typeTemplate?.isSome && sourceMember.kind != .type then
      fail sourceMember.span "type template is only valid on a type module member"
    if (sourceMember.stateKind?.isSome || sourceMember.stateSchema?.isSome) &&
        sourceMember.kind != .state then
      fail sourceMember.span "state kind is only valid on a state module member"
    if sourceMember.stateKind?.isSome && sourceMember.stateSchema?.isSome then
      fail sourceMember.span "state member has both concrete and generic type metadata"
    if let some schema := sourceMember.stateSchema? then
      let validateScalar (scalar : ModuleScalarType) : Except Diagnostic Unit := do
        match scalar with
        | .native | .bool => pure ()
        | .uint (.literal maximum) =>
          if maximum > limits.maxNaturalValue then resource sourceMember.span "module state unsigned bound"
        | .uint (.parameter name) =>
          validText sourceMember.span name
          unless definition.parameters.any (fun parameter =>
              parameter.name == name && parameter.kind == .natural) do
            fail sourceMember.span s!"module state width '{name}' is not a natural parameter"
        | .parameter name =>
          validText sourceMember.span name
          unless definition.parameters.any (fun parameter =>
              parameter.name == name && parameter.kind == .type) do
            fail sourceMember.span s!"module state type '{name}' is not a type parameter"
      match schema with
      | .cell value => validateScalar value
      | .map key value => validateScalar key *> validateScalar value
    if let some sourceExport := sourceMember.sourceExport? then
      unless sourceMember.kind == .circuit || sourceMember.kind == .witness do
        fail sourceMember.span "source helper export must belong to a circuit or witness member"
      let _ ← nameEncodingSize sourceExport.span limits.maxSourceDepth sourceExport.program
      validText sourceExport.span sourceExport.exportName
      if sourceExport.arguments.length > limits.maxArguments then
        resource sourceExport.span "source export argument count"
      for argument in sourceExport.arguments do
        match argument with
        | .typeValue value =>
          let nodeLimit := min limits.maxExpandedNodes Types.defaultLimits.maxLayoutNodes
          let remaining ← consumeTypeNodes sourceExport.span nodeLimit value
          sourceExportTypeNodes := sourceExportTypeNodes + (nodeLimit - remaining)
          if sourceExportTypeNodes > limits.maxSourceNodes then
            resource sourceExport.span "source export type arguments"
        | .typeParameter name | .naturalParameter name => validText sourceExport.span name
        | .naturalValue value =>
          if value > limits.maxNaturalValue then resource sourceExport.span "source export natural argument"
  let entrypointIds := definition.entrypoints.map (·.member)
  if entrypointIds.eraseDups.length != entrypointIds.length then
    fail definition.span "duplicate module entrypoint member identity"
  unless uniqueStrings (definition.entrypoints.map (·.name)) do
    fail definition.span "duplicate module entrypoint name"
  if definition.entrypoints.length > limits.maxSourceNodes then
    resource definition.span "module entrypoints"
  for entrypoint in definition.entrypoints do
    validText entrypoint.span entrypoint.name
    let some sourceMember := definition.members.find? (·.id == entrypoint.member)
      | fail entrypoint.span s!"unknown module entrypoint member '{entrypoint.member}'"
    unless sourceMember.kind == .entrypoint && sourceMember.name == entrypoint.name do
      fail entrypoint.span "module entrypoint metadata does not match its member declaration"
    if entrypoint.effects.length > limits.maxSourceNodes then
      resource entrypoint.span "module entrypoint effects"
    for effect in entrypoint.effects do
      if effect.span.file.utf8ByteSize > 4096 then resource effect.span "module source span"
      match effect.effect with
      | .writeCellOutput _ outputName => validText effect.span outputName
      | _ => pure ()
  for sourceMember in definition.members do
    if sourceMember.kind == .entrypoint && !entrypointIds.contains sourceMember.id then
      fail sourceMember.span s!"entrypoint member '{sourceMember.name}' has no entrypoint metadata"
  unless uniqueStrings (importViewNames definition) do
    fail definition.span "duplicate Noctium module import view"
  for item in definition.imports do
    validText item.span item.viewName
    match item.target with
    | .registered target =>
      let _ ← nameEncodingSize item.span limits.maxSourceDepth target
    | .moduleMember viewName localName =>
      validText item.span viewName
      validText item.span localName
    if item.arguments.length > limits.maxArguments then resource item.span "module import arguments"
    if item.selections.length > limits.maxSourceNodes then resource item.span "module import selections"
    let selectionKeys := item.selections.map fun selection =>
      (selection.sourceName, selection.localName)
    if selectionKeys.eraseDups.length != selectionKeys.length then
      fail item.span "duplicate Noctium module import selection"
    unless uniqueStrings (item.selections.map (·.localName)) do
      fail item.span "ambiguous local name in Noctium module import view"
    for selection in item.selections do
      validText selection.span selection.sourceName
      validText selection.span selection.localName
  unless uniqueStrings (definition.exports.map (·.name)) do
    fail definition.span "duplicate Noctium module export name"
  for item in definition.exports do
    validText item.span item.name
    match item.target with
    | .localMember id =>
      let some sourceMember := definition.members.find? (·.id == id)
        | fail item.span s!"unknown module member identity '{id}'"
      unless sourceMember.visibility == .«public» do
        fail item.span s!"private module member '{sourceMember.name}' cannot be exported"
    | .importedMember viewName localName => do
      validText item.span viewName
      validText item.span localName
  pure (definition.parameters.length + definition.members.length +
    definition.imports.length + definition.exports.length + definition.entrypoints.length +
    definition.entrypoints.foldl (fun count entry => count + entry.effects.length) 0 +
    definition.imports.foldl (fun count item => count + item.arguments.length + item.selections.length) 0 +
    definition.members.foldl (fun count member => count + match member.stateSchema? with
      | none => 0
      | some (.cell value) => 1 + (match value with | .uint _ => 2 | _ => 1)
      | some (.map key value) => 1 +
        (match key with | .uint _ => 2 | _ => 1) +
        (match value with | .uint _ => 2 | _ => 1)) 0 +
    definition.members.foldl (fun count item => count +
      (item.sourceExport?.map (fun sourceExport => 1 + sourceExport.arguments.length)).getD 0) 0 +
    sourceExportTypeNodes)

private def validateRegistry (limits : Limits) (registry : Registry) : Except Diagnostic Nat := do
  validateLimits limits
  if registry.modules.length > limits.maxModules then resource {} "registered module count"
  let names := registry.modules.map (·.sourceName)
  if names.eraseDups.length != names.length then fail {} "duplicate registered module source identity"
  let mut total := 0
  for module in registry.modules do
    let _ ← nameEncodingSize module.definition.span limits.maxSourceDepth module.sourceName
    total := total + (← validateDefinition limits module.definition)
    if total > limits.maxSourceNodes then resource module.definition.span "module source nodes"
  for module in registry.modules do
    for item in module.definition.imports do
      match item.target with
      | .registered target =>
        unless (lookupRegistered registry target).isSome do
          fail item.span s!"unknown imported module '{sourceSpanName target}'"
      | .moduleMember .. => pure ()
    for member in module.definition.members do
      if let some target := member.moduleTarget? then
        unless (lookupRegistered registry target).isSome do
          fail member.span s!"unknown target module '{sourceSpanName target}'"
  pure total

private abbrev TypeEnvironment := List (String × Types.CompositeType)
private abbrev NaturalEnvironment := List (String × Nat)

private def bindArguments (limits : Limits) (span : SourceSpan)
    (parameters : List TypeParameter) (arguments : List SpecializationArgument) :
    Except Diagnostic (TypeEnvironment × NaturalEnvironment) := do
  if parameters.length > limits.maxArguments || arguments.length > limits.maxArguments then
    resource span "module argument count"
  unless parameters.length == arguments.length do
    fail span "Noctium module specialization arity mismatch"
  let mut types : TypeEnvironment := []
  let mut naturals : NaturalEnvironment := []
  let mut remainingNodes := min limits.maxExpandedNodes Types.defaultLimits.maxLayoutNodes
  for (parameter, argument) in parameters.zip arguments do
    match parameter.kind, argument with
    | .type, .type value => do
      remainingNodes ← consumeTypeNodes span remainingNodes value
      types := (parameter.name, value) :: types
    | .natural, .natural value => do
      if value > limits.maxNaturalValue then resource span "module natural argument"
      naturals := (parameter.name, value) :: naturals
    | _, _ => fail span s!"Noctium module specialization kind mismatch for '{parameter.name}'"
  pure (types, naturals)

private def resolveArgument (limits : Limits) (span : SourceSpan)
    (types : TypeEnvironment) (naturals : NaturalEnvironment) :
    ModuleArgument → Except Diagnostic SpecializationArgument
  | .typeValue value => do
    let maxNodes := min limits.maxExpandedNodes Types.defaultLimits.maxLayoutNodes
    let _ ← consumeTypeNodes span maxNodes value
    pure (.type value)
  | .typeParameter name => do
    let some value := types.lookup name
      | fail span s!"unbound Noctium module type parameter '{name}'"
    pure (.type value)
  | .naturalValue value => do
    if value > limits.maxNaturalValue then resource span "module natural argument"
    pure (.natural value)
  | .naturalParameter name => do
    let some value := naturals.lookup name
      | fail span s!"unbound Noctium module natural parameter '{name}'"
    pure (.natural value)

private def resolveStateScalar (limits : Limits) (span : SourceSpan)
    (types : TypeEnvironment) (naturals : NaturalEnvironment) :
    ModuleScalarType → Except Diagnostic Ty
  | .native => pure .native
  | .bool => pure .bool
  | .uint (.literal maximum) => do
    if maximum > limits.maxNaturalValue then resource span "module state unsigned bound"
    match ScalarPolicy.validate (.uint maximum) with
    | .ok _ => pure (.uint maximum)
    | .error message => fail span message
  | .uint (.parameter name) => do
    let some maximum := naturals.lookup name
      | fail span s!"unbound Noctium module natural parameter '{name}'"
    if maximum > limits.maxNaturalValue then resource span "module state unsigned bound"
    match ScalarPolicy.validate (.uint maximum) with
    | .ok _ => pure (.uint maximum)
    | .error message => fail span message
  | .parameter name => do
    let some value := types.lookup name
      | fail span s!"unbound Noctium module type parameter '{name}'"
    match value with
    | .scalar ty =>
      match ty with
      | .native => pure .native
      | .bool => pure .bool
      | .uint maximum => do
        if maximum > limits.maxNaturalValue then resource span "module state unsigned bound"
        match ScalarPolicy.validate (.uint maximum) with
        | .ok _ => pure (.uint maximum)
        | .error message => fail span message
      | .bytes _ => fail span "module byte state parameters require a composite bytes type"
      | .opaqueBytes => fail span "OpaqueBytes state parameters are unsupported by module specialization"
      | .opaqueString => fail span "OpaqueString state parameters are unsupported by module specialization"
      | .jubjubScalar | .jubjubPoint =>
        fail span "Jubjub state parameters are not supported by module specialization"
      | .foreign _ => fail span "foreign state parameters are not supported by module specialization"
    | _ => fail span s!"Noctium ledger state parameter '{name}' must specialize to a scalar; aggregate ledger state is not supported"

private def resolveModuleStateKind (limits : Limits) (span : SourceSpan)
    (types : TypeEnvironment) (naturals : NaturalEnvironment) :
    ModuleStateKind → Except Diagnostic StateKind
  | .cell value => .cell <$> resolveStateScalar limits span types naturals value
  | .map key value => do
    let keyTy ← resolveStateScalar limits span types naturals key
    let valueTy ← resolveStateScalar limits span types naturals value
    pure (.map keyTy valueTy)

private def keyEncodingSize (limits : Limits) (span : SourceSpan) (key : ModuleKey) :
    Except Diagnostic Nat := do
  if key.arguments.length > limits.maxArguments then resource span "module argument count"
  let sourceSize ← nameEncodingSize span limits.maxSourceDepth key.sourceName
  let mut remainingNodes := min limits.maxExpandedNodes Types.defaultLimits.maxLayoutNodes
  let mut argumentBytes := 0
  for argument in key.arguments do
    match argument with
    | .type value => do
      remainingNodes ← consumeTypeNodes span remainingNodes value
      let nodeLimit := min limits.maxExpandedNodes Types.defaultLimits.maxLayoutNodes
      let used := nodeLimit - remainingNodes
      let some size := canonicalTypeSize (used + 1) value
        | resource span "canonical module type size"
      argumentBytes := argumentBytes + 1 + size
    | .natural value => do
      if value > limits.maxNaturalValue then resource span "module natural argument"
      argumentBytes := argumentBytes + 1 + natEncodingSize value
  pure (2 + sourceSize + 3 + natEncodingSize key.arguments.length + argumentBytes)

private def checkDigestCollision (span : SourceSpan) (digest : Nat) (key : ModuleKey)
    (known : List (Nat × ModuleKey)) : Except Diagnostic Unit := do
  if let some (_, prior) := known.find? (·.1 == digest) then
    unless prior == key do fail span "Noctium canonical module identity digest collision"

private structure ExpansionState where
  registry : Registry
  limits : Limits
  instances : List ModuleInstance := []
  active : List Name := []
  digests : List (Nat × ModuleKey) := []
  expandedNodes : Nat := 0
  canonicalBytes : Nat := 0
  deriving Inhabited

private abbrev ExpandM := StateT ExpansionState (Except Diagnostic)

private def liftE (value : Except Diagnostic α) : ExpandM α := do
  match value with
  | .ok result => pure result
  | .error diagnostic => throw diagnostic

private def memberIdentity (key : ModuleKey) (member : Member) : MemberIdentity :=
  ⟨key, member.id, member.kind⟩

private def lookupInstance (instances : List ModuleInstance) (key : ModuleKey) :
    Option ModuleInstance := instances.find? (·.key == key)

private def resolveTargetInModule (span : SourceSpan) (key : ModuleKey)
    (members : List Member) (views : List ImportedView) :
    ExportTarget → Except Diagnostic MemberIdentity
  | .localMember id => do
    let some sourceMember := members.find? (·.id == id)
      | fail span s!"unknown local module member '{id}'"
    pure (memberIdentity key sourceMember)
  | .importedMember viewName localName => do
    let some view := views.find? (·.name == viewName)
      | fail span s!"unknown module import view '{viewName}'"
    let some binding := view.members.find? (·.name == localName)
      | fail span s!"module view '{viewName}' does not expose '{localName}'"
    pure binding.identity

private def resolveStateTargetInModule (span : SourceSpan) (key : ModuleKey)
    (members : List Member) (views : List ImportedView) :
    StateTarget → Except Diagnostic MemberIdentity
  | .localMember id => resolveTargetInModule span key members views (.localMember id)
  | .importedMember viewName localName =>
    resolveTargetInModule span key members views (.importedMember viewName localName)

private def findIdentityMember (state : ExpansionState) (currentKey : ModuleKey)
    (currentMembers : List Member) (identity : MemberIdentity) : Option Member := do
  if identity.module == currentKey then
    currentMembers.find? fun sourceMember =>
      sourceMember.id == identity.member && sourceMember.kind == identity.kind
  else
    let moduleInstance ← lookupInstance state.instances identity.module
    moduleInstance.members.find? fun sourceMember =>
      sourceMember.id == identity.member && sourceMember.kind == identity.kind

private def resolveImportTarget (state : ExpansionState) (span : SourceSpan)
    (currentKey : ModuleKey) (currentMembers : List Member)
    (views : List ImportedView) : ImportTarget → ExpandM Name
  | .registered sourceName => pure sourceName
  | .moduleMember viewName localName => do
    let identity ← liftE <| resolveTargetInModule span currentKey currentMembers views
      (.importedMember viewName localName)
    unless identity.kind == .module do
      liftE <| fail span s!"module import target '{viewName}.{localName}' is not a module member"
    let some sourceMember := findIdentityMember state currentKey currentMembers identity
      | liftE <| fail span s!"module import target '{viewName}.{localName}' is unavailable"
    let some sourceName := sourceMember.moduleTarget?
      | liftE <| fail span s!"module member '{sourceMember.name}' has no target module"
    pure sourceName

private def validateModuleEntrypoints (state : ExpansionState)
    (key : ModuleKey) (members : List Member) (views : List ImportedView)
    (entrypoints : List ModuleEntrypoint) : Except Diagnostic Unit := do
  for entrypoint in entrypoints do
    let circuitIdentity ← resolveTargetInModule entrypoint.span key members views entrypoint.circuit
    unless circuitIdentity.kind == .circuit || circuitIdentity.kind == .witness do
      fail entrypoint.span "module entrypoint must use a circuit or witness member"
    let some _ := findIdentityMember state key members circuitIdentity
      | fail entrypoint.span "module entrypoint circuit identity is unavailable"
    for effectSpec in entrypoint.effects do
      let stateTarget? := match effectSpec.effect with
        | .readCell target _ _ | .readMap target _ _ _ _
        | .writeCell target _ _ | .writeCellOutput target _ | .writeMap target _ _ _ _
        | .requireAbsent target _ _ => some target
        | .require _ => none
      if let some stateTarget := stateTarget? then
        let identity ← resolveStateTargetInModule effectSpec.span key members views stateTarget
        unless identity.kind == .state do
          fail effectSpec.span "module state effect target is not a state member"
        let some stateMember := findIdentityMember state key members identity
          | fail effectSpec.span "module state declaration identity is unavailable"
        match effectSpec.effect, stateMember.stateKind? with
        | .readCell _ _ ty, some (.cell actual) | .writeCell _ ty _, some (.cell actual) =>
          unless ty == actual do
            fail effectSpec.span s!"module effect type does not match state member '{stateMember.name}'"
        | .writeCellOutput .., some (.cell _) => pure ()
        | .readMap _ _ keyTy valueTy _, some (.map actualKeyTy actualValueTy)
        | .writeMap _ keyTy valueTy _ _, some (.map actualKeyTy actualValueTy) =>
          unless keyTy == actualKeyTy && valueTy == actualValueTy do
            fail effectSpec.span s!"module effect type does not match state member '{stateMember.name}'"
        | .requireAbsent _ keyTy _, some (.map actualKeyTy _) =>
          unless keyTy == actualKeyTy do
            fail effectSpec.span s!"module effect key type does not match state member '{stateMember.name}'"
        | _, none => fail effectSpec.span s!"state member '{stateMember.name}' has no declared type"
        | .require _ , _ => pure ()
        | .readCell .., _ | .writeCell .., _ | .writeCellOutput .., _ |
            .readMap .., _ | .writeMap .., _ |
            .requireAbsent .., _ =>
          fail effectSpec.span s!"module effect type does not match state member '{stateMember.name}'"

mutual
  private partial def instantiate (span : SourceSpan) (sourceName : Name)
      (arguments : List SpecializationArgument) : ExpandM ModuleInstance := do
    let state ← get
    let some registered := lookupRegistered state.registry sourceName
      | liftE (fail span s!"unknown imported module '{sourceSpanName sourceName}'")
    let definition := registered.definition
    let key : ModuleKey := ⟨sourceName, arguments⟩
    let (_types, _naturals) ← liftE (bindArguments state.limits span definition.parameters arguments)
    if state.active.contains sourceName then
      liftE (fail span s!"Noctium module import cycle at '{sourceSpanName sourceName}'")
    if let some cachedInstance := lookupInstance state.instances key then return cachedInstance
    if state.instances.length + state.active.length >= state.limits.maxModuleInstances then
      liftE (resource span "module instance count before expansion")
    if state.active.length >= state.limits.maxExpansionDepth then
      liftE (resource span "module expansion depth")
    let nodeCost ← liftE (validateDefinition state.limits definition)
    if nodeCost > state.limits.maxExpandedNodes ||
        state.expandedNodes > state.limits.maxExpandedNodes - nodeCost then
      liftE (resource span "expanded module nodes before substitution")
    let keyBytes ← liftE (keyEncodingSize state.limits span key)
    if keyBytes > state.limits.maxCanonicalKeyBytes then
      liftE (resource span "canonical module identity key size")
    if keyBytes > state.limits.maxCanonicalBytes ||
        state.canonicalBytes > state.limits.maxCanonicalBytes - keyBytes then
      liftE (resource span "total canonical module identity bytes")
    let encoding := encodeKey key
    if encoding.utf8ByteSize != keyBytes then
      liftE (fail span "internal canonical module identity size mismatch")
    let digest := stableDigest encoding
    liftE (checkDigestCollision span digest key state.digests)
    set {state with
      active := sourceName :: state.active
      digests := (digest, key) :: state.digests
      canonicalBytes := state.canonicalBytes + keyBytes
      expandedNodes := state.expandedNodes + nodeCost}
    let (types, naturals) ← liftE (bindArguments state.limits span definition.parameters arguments)
    let mut resolvedMembers : List Member := []
    for sourceMember in definition.members do
      let mut resolvedMember := sourceMember
      if let some schema := sourceMember.stateSchema? then
        let kind ← liftE (resolveModuleStateKind state.limits sourceMember.span
          types naturals schema)
        resolvedMember := {resolvedMember with stateKind? := some kind}
      if let some template := sourceMember.typeTemplate? then
        let typeLimits : Noctium.Helpers.Specialization.Limits := {
          maxSourceNodes := state.limits.maxSourceNodes
          maxExpandedNodes := state.limits.maxExpandedNodes
          maxTypeArguments := state.limits.maxArguments
          maxNaturalValue := state.limits.maxNaturalValue}
        let specialized ← liftE (Noctium.Helpers.Specialization.specializeTypeWithEnvironment typeLimits
          template.source types naturals template.value)
        let info : TypeInfo := {
          value := specialized.value
          environment := specialized.environment
          nominalUInt? := template.nominalUInt?}
        liftE (validateNominalUInt template.span info.value info.nominalUInt?)
        resolvedMember := {resolvedMember with typeInfo? := some info}
      resolvedMembers := resolvedMembers ++ [resolvedMember]
    let mut sourceExports : List (Nat × ResolvedSourceExport) := []
    for sourceMember in definition.members do
      if let some sourceExport := sourceMember.sourceExport? then
        let sourceArguments ← sourceExport.arguments.mapM
          (fun argument => liftE (resolveArgument state.limits sourceExport.span types naturals argument))
        let sourceKey : ModuleKey := ⟨sourceExport.program, sourceArguments⟩
        let _ ← liftE (keyEncodingSize state.limits sourceExport.span sourceKey)
        sourceExports := sourceExports ++ [(sourceMember.id, {
          program := sourceExport.program
          exportName := sourceExport.exportName
          arguments := sourceArguments
          span := sourceExport.span})]
    let mut importedViews : List ImportedView := []
    for importSpec in definition.imports do
      let childArguments ← importSpec.arguments.mapM
        (fun argument => liftE (resolveArgument state.limits importSpec.span types naturals argument))
      let currentState ← get
      let targetName ← resolveImportTarget currentState importSpec.span key
        resolvedMembers importedViews importSpec.target
      let child ← instantiate importSpec.span targetName childArguments
      let mut bindings : List ViewBinding := []
      for selection in importSpec.selections do
        let selectedExports := child.exports.filter (·.name == selection.sourceName)
        if selectedExports.isEmpty then
          liftE (fail selection.span
            s!"module '{sourceSpanName targetName}' does not export '{selection.sourceName}'")
        for candidate in selectedExports do
          let binding : ViewBinding := {
            name := selection.localName
            identity := candidate.identity
            kind := candidate.kind
            span := selection.span}
          unless bindings.any (fun prior =>
              prior.name == binding.name && prior.identity == binding.identity) do
            bindings := bindings ++ [binding]
      importedViews := importedViews ++ [{
        name := importSpec.viewName
        target := child.key
        members := bindings
        span := importSpec.span}]
    let currentState ← get
    liftE (validateModuleEntrypoints currentState key resolvedMembers
      importedViews definition.entrypoints)
    let mut exports : List ExportedMember := []
    for exportSpec in definition.exports do
      let resolved ← match exportSpec.target with
        | .localMember id => do
          let some sourceMember := resolvedMembers.find? (·.id == id)
            | liftE (fail exportSpec.span s!"unknown module member identity '{id}'")
          if sourceMember.visibility != .«public» then
            liftE (fail exportSpec.span s!"private module member '{sourceMember.name}' cannot be exported")
          pure [{
            name := exportSpec.name
            identity := memberIdentity key sourceMember
            kind := sourceMember.kind
            span := exportSpec.span}]
        | .importedMember viewName localName => do
          let some view := importedViews.find? (·.name == viewName)
            | liftE (fail exportSpec.span s!"unknown module import view '{viewName}'")
          let members := view.members.filter (·.name == localName)
          if members.isEmpty then
            liftE (fail exportSpec.span s!"module view '{viewName}' does not expose '{localName}'")
          pure (members.map fun binding => {
            name := exportSpec.name
            identity := binding.identity
            kind := binding.kind
            span := exportSpec.span})
      for resolvedMember in resolved do
        if exports.any (fun prior => prior.name == resolvedMember.name &&
            prior.identity == resolvedMember.identity) then
          liftE (fail exportSpec.span s!"duplicate module export identity '{resolvedMember.name}'")
        exports := exports ++ [resolvedMember]
    let moduleInstance : ModuleInstance := {
      key
      digest
      members := resolvedMembers
      sourceExports
      entrypoints := definition.entrypoints
      imports := importedViews
      exports
      span := definition.span}
    modify fun current => {
      current with
      active := current.active.filter (· != sourceName)
      instances := current.instances ++ [moduleInstance]}
    pure moduleInstance
end

/-- Expand one root module, reusing exact module specialization keys across all
selected import views. The result contains one instance per source identity and
ordered normalized argument list. -/
def expandWithLimits (limits : Limits) (registry : Registry) (sourceName : Name)
    (arguments : List SpecializationArgument) : Except Diagnostic Expansion := do
  let _ ← validateRegistry limits registry
  let _ ← nameEncodingSize {} limits.maxSourceDepth sourceName
  let some rootSource := lookupRegistered registry sourceName
    | fail {} s!"unknown root module '{sourceSpanName sourceName}'"
  let initial : ExpansionState := {registry, limits}
  let (root, state) ← (instantiate rootSource.definition.span sourceName arguments).run initial
  pure {root := root.key, instances := state.instances}

def expand (registry : Registry) (sourceName : Name)
    (arguments : List SpecializationArgument) : Except Diagnostic Expansion :=
  expandWithLimits {} registry sourceName arguments

def Expansion.findInstance (expansion : Expansion) (key : ModuleKey) :
    Option ModuleInstance := lookupInstance expansion.instances key

def Expansion.moduleMemberName (expansion : Expansion) (identity : MemberIdentity) :
    Option String := do
  let moduleInstance ← expansion.findInstance identity.module
  if moduleInstance.members.any (fun sourceMember =>
      sourceMember.id == identity.member && sourceMember.kind == identity.kind) then
    pure s!"nlm_{moduleInstance.digest}_{memberKindName identity.kind}_{identity.member}"
  else none

def Expansion.findMember (expansion : Expansion) (identity : MemberIdentity) : Option Member := do
  let moduleInstance ← expansion.findInstance identity.module
  moduleInstance.members.find? fun sourceMember =>
    sourceMember.id == identity.member && sourceMember.kind == identity.kind

/-- Return the checked concrete type carried by the exact exported member.
Aliases and re-exports resolve through their retained `MemberIdentity`. -/
def Expansion.typeInfo (expansion : Expansion) (identity : MemberIdentity) : Option TypeInfo := do
  if identity.kind != .type then none
  let member ← expansion.findMember identity
  member.typeInfo?

/-- Resolve original source program metadata by declaration identity. Imported
and re-exported names point through this lookup without cloning the metadata. -/
def Expansion.sourceExport (expansion : Expansion) (identity : MemberIdentity) :
    Option ResolvedSourceExport := do
  let moduleInstance ← expansion.findInstance identity.module
  let _ ← expansion.findMember identity
  (moduleInstance.sourceExports.find? (·.1 == identity.member)).map (·.2)

def Expansion.stateFieldName (expansion : Expansion) (identity : MemberIdentity) :
    Option String :=
  if identity.kind == .state then expansion.moduleMemberName identity else none

private def resolveContractEffect (expansion : Expansion) (moduleInstance : ModuleInstance)
    (effectSpec : ModuleEffectSpec) : Except Diagnostic (Effect × List MemberIdentity) := do
  let resolveState (target : StateTarget) : Except Diagnostic (MemberIdentity × String × Member) := do
    let identity ← resolveStateTargetInModule effectSpec.span moduleInstance.key
      moduleInstance.members moduleInstance.imports target
    unless identity.kind == .state do
      fail effectSpec.span "module state effect target is not a state member"
    let some fieldName := expansion.stateFieldName identity
      | fail effectSpec.span "module state target has no canonical ledger field"
    let some member := expansion.findMember identity
      | fail effectSpec.span "module state declaration identity is missing"
    pure (identity, fieldName, member)
  match effectSpec.effect with
  | .readCell target destination ty => do
    let (identity, fieldName, _) ← resolveState target
    pure (.readCell fieldName destination ty, [identity])
  | .readMap target destination keyTy valueTy key => do
    let (identity, fieldName, _) ← resolveState target
    pure (.readMap fieldName destination keyTy valueTy key, [identity])
  | .require condition => pure (.require condition, [])
  | .writeCell target ty value => do
    let (identity, fieldName, _) ← resolveState target
    pure (.writeCell fieldName ty value, [identity])
  | .writeCellOutput target outputName => do
    let (identity, fieldName, member) ← resolveState target
    match member.stateKind? with
    | some (.cell ty) => pure (.writeCell fieldName ty (.ref outputName), [identity])
    | some (.map ..) => fail effectSpec.span "module output write requires a cell state"
    | some (.tree ..) | some (.merkleTree ..) | some (.historicMerkleTree ..) =>
      fail effectSpec.span "module output write requires a cell state"
    | some .opaqueString => fail effectSpec.span "module output write does not support opaque string state"
    | none => fail effectSpec.span s!"state member '{member.name}' has no declared type"
  | .writeMap target keyTy valueTy key value => do
    let (identity, fieldName, _) ← resolveState target
    pure (.writeMap fieldName keyTy valueTy key value, [identity])
  | .requireAbsent target keyTy key => do
    let (identity, fieldName, _) ← resolveState target
    pure (.requireAbsent fieldName keyTy key, [identity])

/-- Resolve a root-exported module entrypoint. Aliases affect only its visible
name. Circuit and state references retain their original member identities. -/
def Expansion.resolveEntrypoint (expansion : Expansion) (root : ModuleKey)
    (exportName : String) : Except Diagnostic ResolvedEntrypoint := do
  let some rootInstance := expansion.findInstance root
    | fail {} "unknown root module specialization"
  let some exported := rootInstance.exports.find? (·.name == exportName)
    | fail rootInstance.span s!"module root does not export '{exportName}'"
  unless exported.kind == .entrypoint do
    fail exported.span s!"module export '{exportName}' is not an entrypoint"
  let some origin := expansion.findInstance exported.identity.module
    | fail exported.span "module entrypoint origin is missing"
  let some entrypoint := origin.entrypoints.find? (·.member == exported.identity.member)
    | fail exported.span "module entrypoint metadata is missing"
  let circuit ← resolveTargetInModule entrypoint.span origin.key origin.members
    origin.imports entrypoint.circuit
  unless circuit.kind == .circuit || circuit.kind == .witness do
    fail entrypoint.span "module entrypoint must use a circuit or witness member"
  let resolvedEffects ← entrypoint.effects.mapM (resolveContractEffect expansion origin)
  pure {
    name := exportName
    identity := exported.identity
    circuit
    effects := resolvedEffects.map Prod.fst
    stateIdentities := (resolvedEffects.flatMap Prod.snd).eraseDups
    span := entrypoint.span
    effectSpans := entrypoint.effects.map (·.span)}

/-- Build canonical state declarations and entrypoint templates for one module
root. The frontend attaches checked monomorphic circuit values before creating
the ordinary `Contract` consumed by existing analysis and native lowering. -/
def Expansion.contractPlan (expansion : Expansion) (root : ModuleKey) :
    Except Diagnostic ModuleContractPlan := do
  let some rootInstance := expansion.findInstance root
    | fail {} "unknown root module specialization"
  let exportedEntrypoints := rootInstance.exports.filter (·.kind == .entrypoint)
  if exportedEntrypoints.isEmpty then
    fail rootInstance.span "module root exposes no entrypoints"
  let mut resolvedEntrypoints := []
  for exported in exportedEntrypoints do
    resolvedEntrypoints := resolvedEntrypoints ++
      [← expansion.resolveEntrypoint root exported.name]
  resolvedEntrypoints := resolvedEntrypoints.mergeSort fun left right =>
    decide (left.name < right.name)
  let exportedStates := rootInstance.exports.filter (·.kind == .state) |>.map (·.identity)
  let stateIdentities := (exportedStates ++
    resolvedEntrypoints.flatMap (·.stateIdentities)).eraseDups
  let stateIdentities := stateIdentities.mergeSort fun left right =>
    decide ((expansion.stateFieldName left).getD "" <
      (expansion.stateFieldName right).getD "")
  let mut states : List StateDecl := []
  for identity in stateIdentities do
    let some sourceMember := expansion.findMember identity
      | fail rootInstance.span "module state declaration identity is missing"
    let some kind := sourceMember.stateKind?
      | fail sourceMember.span s!"state member '{sourceMember.name}' has no declared type"
    let some fieldName := expansion.stateFieldName identity
      | fail sourceMember.span "module state declaration has no canonical field name"
    states := states ++ [{name := fieldName, kind, span := sourceMember.span}]
  let circuitIdentities := (resolvedEntrypoints.map (·.circuit)).eraseDups
  let circuitIdentities := circuitIdentities.mergeSort fun left right =>
    decide ((expansion.moduleMemberName left).getD "" <
      (expansion.moduleMemberName right).getD "")
  let mut circuits : List ModuleCircuitSource := []
  for identity in circuitIdentities do
    let some sourceMember := expansion.findMember identity
      | fail rootInstance.span "module circuit declaration identity is missing"
    unless identity.kind == .circuit || identity.kind == .witness do
      fail sourceMember.span "module entrypoint circuit has an invalid member kind"
    let some source := expansion.sourceExport identity
      | fail sourceMember.span s!"module circuit '{sourceMember.name}' has no source export"
    let some outputName := expansion.moduleMemberName identity
      | fail sourceMember.span "module circuit has no canonical generated name"
    circuits := circuits ++ [{identity, outputName, source, kind := identity.kind}]
  pure {root, state := states, entrypoints := resolvedEntrypoints, circuits}

private partial def genericTypeOfConcrete : Types.CompositeType → Except String GenericType
  | .unit => pure .unit
  | .scalar .native => pure .native
  | .scalar .bool => pure .bool
  | .scalar .jubjubScalar => pure .jubjubScalar
  | .scalar .jubjubPoint => pure .jubjubPoint
  | .scalar (.uint maximum) => pure (.uint (.literal maximum))
  | .scalar (.bytes _) => throw "scalar byte types cannot enter module specialization"
  | .scalar .opaqueBytes => throw "OpaqueBytes cannot enter module specialization"
  | .scalar .opaqueString => throw "OpaqueString cannot enter module specialization"
  | .scalar (.foreign kind) => pure (.foreign kind)
  | .tuple items => .tuple <$> items.mapM genericTypeOfConcrete
  | .structure id => pure (.structure id [])
  | .enumeration id => pure (.enumeration id)
  | .vector length element => do
    pure (.vector (.literal length) (← genericTypeOfConcrete element))
  | .bytes length => pure (.bytes (.literal length))

private def genericArgumentOfConcrete : SpecializationArgument → Except String Argument
  | .type value => .type <$> genericTypeOfConcrete value
  | .natural value => pure (.natural (.literal value))

/-- Group specialized circuit requests by exact source program identity. Each
member gets its canonical declaration-derived output name, never an import or
re-export alias. -/
def ModuleContractPlan.specializationGroups (plan : ModuleContractPlan) :
    Except Diagnostic (List ModuleSpecializationGroup) := do
  let mut groups : List ModuleSpecializationGroup := []
  for circuit in plan.circuits do
    let arguments ← (circuit.source.arguments.mapM genericArgumentOfConcrete).mapError fun message =>
      {span := circuit.source.span, message}
    let request : ExportRequest := {
      sourceExport := circuit.source.exportName
      outputName := circuit.outputName
      arguments
      span := circuit.source.span}
    if let some prior := groups.find? (·.sourceProgram == circuit.source.program) then
      if prior.requests.any (·.outputName == request.outputName) then
        fail request.span "duplicate canonical module circuit identity"
      groups := groups.map fun group =>
        if group.sourceProgram == circuit.source.program then
          {group with requests := group.requests ++ [request]}
        else group
    else
      groups := groups ++ [{sourceProgram := circuit.source.program, requests := [request]}]
  let orderedGroups := groups.map fun group => {
    group with
    requests := group.requests.mergeSort fun left right =>
      decide (left.outputName < right.outputName)}
  pure (orderedGroups.mergeSort fun left right => Name.lt left.sourceProgram right.sourceProgram)

/-- Specialize the exact grouped source requests from an already expanded
contract plan. Each source group shares the issue46 helper and type caches. -/
def ModuleContractPlan.specializeWithSources (plan : ModuleContractPlan)
    (specializationLimits : Noctium.Helpers.Specialization.Limits)
    (sources : List (Name × Noctium.Helpers.Specialization.Program)) :
    Except Diagnostic SpecializedModule := do
  if sources.length > 256 then resource {} "source program count"
  unless (sources.map (·.1)).eraseDups.length == sources.length do
    fail {} "duplicate source program identity in module request"
  let groups ← plan.specializationGroups
  let mut batches : List (Name × BatchResult) := []
  for group in groups do
    let some (_, source) := sources.find? (·.1 == group.sourceProgram)
      | fail {} s!"missing registered generic source program '{sourceSpanName group.sourceProgram}'"
    let batch ← Noctium.Helpers.Specialization.specializeRequestsWithLimits
      specializationLimits source group.requests
    batches := batches ++ [(group.sourceProgram, batch)]
  pure {plan, batches}

/-- Expand a root, collect its visible circuits, and specialize each exact
source program in one issue46 batch session. The caller supplies source values
looked up from registered Lean constants, not cached generated programs. -/
def specializeRequestWithSources (moduleLimits : Limits)
    (specializationLimits : Noctium.Helpers.Specialization.Limits)
    (registry : Registry) (request : Request)
    (sources : List (Name × Noctium.Helpers.Specialization.Program)) :
    Except Diagnostic SpecializedModule := do
  if sources.length > moduleLimits.maxModules then resource {} "source program count"
  unless (sources.map (·.1)).eraseDups.length == sources.length do
    fail {} "duplicate source program identity in module request"
  let expansion ← expandWithLimits moduleLimits registry request.sourceName request.arguments
  let plan ← expansion.contractPlan expansion.root
  plan.specializeWithSources specializationLimits sources

/-- Attach freshly compiled circuits to a checked module contract plan. -/
def ModuleContractPlan.assembleContract (plan : ModuleContractPlan) (name : String)
    (circuits : List Circuit) : Except Diagnostic Contract := do
  unless uniqueStrings (circuits.map (·.name)) do
    fail {} "duplicate compiled circuit name in module contract"
  let mut entrypoints : List Entrypoint := []
  for template in plan.entrypoints do
    let some source := plan.circuits.find? (·.identity == template.circuit)
      | fail template.span "module contract circuit source is missing"
    let some circuit := circuits.find? (·.name == source.outputName)
      | fail template.span s!"compiled module circuit '{source.outputName}' is missing"
    entrypoints := entrypoints ++ [{
      name := template.name
      circuit
      effects := template.effects
      span := template.span
      effectSpans := template.effectSpans}]
  pure {name, state := plan.state, entrypoints}

def Expansion.resolveImport (expansion : Expansion) (module : ModuleKey)
    (viewName localName : String) : List ViewBinding := Id.run do
  let some moduleInstance := expansion.findInstance module | return []
  let some view := moduleInstance.imports.find? (·.name == viewName) | return []
  return view.members.filter (·.name == localName)

/-- Resolve one selected public type import to its checked specialization data.
The returned type keeps the original member identity through any import alias
or re-export spelling. -/
def importedType (registry : Registry) (request : Request)
    (viewName localName : String) : Except Diagnostic TypeInfo := do
  let expansion ← expandWithLimits {} registry request.sourceName request.arguments
  let some root := expansion.findInstance expansion.root
    | fail {} "Noctium imported type root instance is unavailable"
  let some view := root.imports.find? (·.name == viewName)
    | fail root.span s!"unknown module import view '{viewName}'"
  let binding ← match view.members.filter (fun member =>
      member.name == localName && member.kind == .type) with
    | [binding] => pure binding
    | [] => fail view.span s!"module view '{viewName}' does not expose '{localName}' as a type"
    | _ => fail view.span s!"module view '{viewName}' exposes ambiguous type '{localName}'"
  let some info := expansion.typeInfo binding.identity
    | fail binding.span s!"module type member '{localName}' has no checked type data"
  pure info

def Expansion.resolveExport (expansion : Expansion) (module : ModuleKey)
    (exportName : String) : List ExportedMember := Id.run do
  let some moduleInstance := expansion.findInstance module | return []
  return moduleInstance.exports.filter (·.name == exportName)

end Noctium.Modules
