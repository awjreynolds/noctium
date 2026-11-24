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
  | checkedTypeValue (value : Types.CompositeType) (environment : Types.CompositeEnv)
  | typeParameter (name : String)
  | naturalValue (value : Nat)
  | naturalParameter (name : String)
  deriving Repr, Inhabited

inductive ModuleNatural where
  | literal (value : Nat)
  | parameter (name : String)
  deriving Repr, Inhabited

/-- Scalar ledger values and map keys. A map key parameter may also specialize
to a checked named record. -/
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
  typeEnvironments : List (Option Types.CompositeEnv) := []
  span : SourceSpan := {}
  deriving Repr, BEq, Inhabited

/-- The generic source declaration for one module type member. `source` owns
the existing generic structure and alias templates. The concrete checked
type and environment are produced for each module specialization. -/
structure TypeTemplate where
  source : Noctium.Helpers.Specialization.Program
  value : GenericType
  nominalUInt? : Option NominalUIntType := none
  /-- Checked nominal Field aliases attached to flat record fields. Paths name
  fields in the specialized record and identities use their canonical source
  names. -/
  nominalFieldPaths : List (List String × String) := []
  span : SourceSpan := {}
  deriving Repr

instance : Inhabited TypeTemplate := ⟨{source := {}, value := .unit}⟩

structure TypeInfo where
  value : Types.CompositeType
  environment : Types.CompositeEnv
  nominalUInt? : Option NominalUIntType := none
  nominalFieldPaths : List (List String × String) := []
  deriving Repr, BEq, DecidableEq

instance : Inhabited TypeInfo := ⟨{value := .unit, environment := {}}⟩

/-- A module type parameter's checked value and the declarations reachable from
that value. Module arguments keep this closure with the nominal type ID. -/
structure ModuleTypeValue where
  value : Types.CompositeType
  environment : Types.CompositeEnv := {}
  deriving Repr, BEq, DecidableEq

instance : Inhabited ModuleTypeValue := ⟨{value := .unit, environment := {}}⟩

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

structure ConstructorInputBinding where
  state : StateTarget
  parameterName : String := ""
  span : SourceSpan := {}
  /-- Checked record field names paired with constructor parameter names. -/
  recordFields : List (String × String) := []
  deriving Repr, Inhabited

structure OpaqueCellHashReturn where
  name : String
  state : StateTarget
  span : SourceSpan := {}
  deriving Repr, Inhabited

structure StateValueReturn where
  name : String
  state : StateTarget
  span : SourceSpan := {}
  deriving Repr, Inhabited

inductive ModuleMapKey where
  | mk (ty : Ty) (value : Expr ty)
  | argument (name : String) (disclosed : Bool := false)
  deriving Repr

private def moduleMapKeySourceNodes : ModuleMapKey → Nat
  | .mk .. => 0
  | .argument .. => 1

structure MapValueReturn extends StateValueReturn where
  key : ModuleMapKey
  deriving Repr

inductive ModuleEffect where
  | readCell (state : StateTarget) (destination : String) (ty : Ty)
  | readRecordCell (state : StateTarget) (destination : String)
  | readMap (state : StateTarget) (destination : String) (keyTy valueTy : Ty)
      (key : Expr keyTy)
  | require (condition : Expr .bool)
  | writeCell (state : StateTarget) (ty : Ty) (value : Expr ty)
  | writeCellOutput (state : StateTarget) (outputName : String)
  | writeRecordCell (state : StateTarget) (fields : List (String × LedgerFieldExpr))
  | writeCellInput (state : StateTarget) (inputName : String) (disclosed : Bool)
  | writeMapInput (state : StateTarget) (key : ModuleMapKey) (inputName : String) (disclosed : Bool)
  | writeMap (state : StateTarget) (keyTy valueTy : Ty)
      (key : Expr keyTy) (value : Expr valueTy)
  | requireAbsent (state : StateTarget) (keyTy : Ty) (key : Expr keyTy)
  deriving Repr

structure ModuleEffectSpec where
  effect : ModuleEffect
  span : SourceSpan := {}
  guard : Option (Expr .bool) := none
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
  opaqueCellHashReturns : List OpaqueCellHashReturn := []
  returns : List Output := []
  cellReturns : List StateValueReturn := []
  mapReturns : List MapValueReturn := []
  callInputs : List String := []
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
  constructorInputs : List ConstructorInputBinding := []
  deriving Repr, Inhabited

/-- The canonical specialization identity. Arguments are ordered, normalized,
and structural. -/
structure ModuleKey where
  sourceName : Name
  arguments : List SpecializationArgument
  /-- Checked reachable layouts for type arguments, aligned with `arguments`.
  Scalar and otherwise closed types use `none`. -/
  typeEnvironments : List (Option Types.CompositeEnv) := []
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

inductive StateInputCheck where
  | scalar (name : String) (type : Ty) (span : SourceSpan) (stateKind : String)
  | record (view : CallInputView) (layout : String) (span : SourceSpan) (stateKind : String)
  deriving Repr

private def StateInputCheck.name : StateInputCheck → String
  | .scalar name .. => name
  | .record view .. => view.name

structure ResolvedEntrypoint where
  name : String
  identity : MemberIdentity
  circuit : MemberIdentity
  effects : List Effect
  effectGuards : List (Option (Expr .bool)) := []
  returns : List Output := []
  returnViews : List ReturnView := []
  callInputs : List String := []
  callInputViews : List CallInputView := []
  stateInputChecks : List StateInputCheck := []
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
  constructor? : Option Constructor := none
  deriving Repr

structure ModuleSpecializationGroup where
  sourceProgram : Name
  requests : List ExportRequest
  /-- Checked external layouts needed to specialize this source's type arguments. -/
  typeEnvironment : Types.CompositeEnv := {}
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
    | .scalar .opaqueBytes | .scalar .opaqueString => some 3
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
  | .scalar .opaqueBytes | .scalar .opaqueString => pure remaining
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

private def encodeArgument (environment : Option Types.CompositeEnv) :
    SpecializationArgument → String
  | .type value =>
    let layout := match environment with
      | none => ""
      | some environment => "C" ++ encodeText (Types.CompositeType.fingerprint environment value)
    "T" ++ encodeType value ++ layout
  | .natural value => "N" ++ encodeNat value

private def encodeKey (key : ModuleKey) : String :=
  "K1" ++ encodeName key.sourceName ++ "L" ++ encodeNat key.arguments.length ++ "[" ++
    String.join (key.arguments.zipIdx.map fun (argument, index) =>
      encodeArgument (key.typeEnvironments[index]?.join) argument) ++ "]"

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

private def validateNominalFieldPaths (span : SourceSpan)
    (value : Types.CompositeType) (environment : Types.CompositeEnv)
    (fields : List (List String × String)) : Except Diagnostic Unit := do
  unless uniqueStrings (fields.map (fun (path, _) => String.intercalate "." path)) do
    fail span "duplicate module nominal Field path"
  for (path, identity) in fields do
    unless Types.validDeclId identity do
      fail span s!"invalid module nominal Field identity '{identity}'"
    let [name] := path | fail span "module nominal Field paths must name one flat record field"
    unless Types.validFieldName name do
      fail span s!"invalid module nominal Field path '{name}'"
    let .structure typeId := value
      | fail span "module nominal Field paths require a flat named record"
    let some declaration := environment.structures.find? (·.id == typeId)
      | fail span s!"module nominal Field record '{typeId}' is missing"
    let some field := declaration.fields.find? (·.name == name)
      | fail span s!"module nominal Field path '{name}' does not exist"
    unless field.type == .scalar .native do
      fail span s!"module nominal Field path '{name}' must have Native physical type"

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
        | .typeValue value | .checkedTypeValue value _ =>
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
  let mut recordEffectFields := 0
  for entrypoint in definition.entrypoints do
    validText entrypoint.span entrypoint.name
    let some sourceMember := definition.members.find? (·.id == entrypoint.member)
      | fail entrypoint.span s!"unknown module entrypoint member '{entrypoint.member}'"
    unless sourceMember.kind == .entrypoint && sourceMember.name == entrypoint.name do
      fail entrypoint.span "module entrypoint metadata does not match its member declaration"
    if entrypoint.effects.length > limits.maxSourceNodes then
      resource entrypoint.span "module entrypoint effects"
    if entrypoint.opaqueCellHashReturns.length + entrypoint.returns.length +
        entrypoint.cellReturns.length + entrypoint.mapReturns.length > limits.maxSourceNodes then
      resource entrypoint.span "module entrypoint returns"
    unless uniqueStrings (entrypoint.opaqueCellHashReturns.map (·.name) ++
        entrypoint.cellReturns.map (·.name) ++ entrypoint.mapReturns.map (·.name) ++
        entrypoint.returns.map (·.name)) do
      fail entrypoint.span "duplicate module entrypoint return name"
    if entrypoint.callInputs.length > limits.maxSourceNodes then
      resource entrypoint.span "module entrypoint call arguments"
    for name in entrypoint.callInputs do
      validText entrypoint.span name
    for returned in entrypoint.opaqueCellHashReturns do
      validText returned.span returned.name
      unless Types.validFieldName returned.name do
        fail returned.span s!"invalid module return name '{returned.name}'"
    for returned in entrypoint.returns do
      validText returned.span returned.name
      unless Types.validFieldName returned.name do
        fail returned.span s!"invalid module return name '{returned.name}'"
      match returned.ty.validate Capabilities.crypto with
      | .ok _ => pure ()
      | .error message => fail returned.span message
    for returned in entrypoint.cellReturns ++ entrypoint.mapReturns.map (·.toStateValueReturn) do
      validText returned.span returned.name
      unless Types.validFieldName returned.name do
        fail returned.span s!"invalid module return name '{returned.name}'"
    for returned in entrypoint.mapReturns do
      match returned.key with
      | .argument name _ => validText returned.span name
      | .mk .. => pure ()
    for effect in entrypoint.effects do
      if effect.span.file.utf8ByteSize > 4096 then resource effect.span "module source span"
      match effect.effect with
      | .writeCellOutput _ outputName => validText effect.span outputName
      | .readRecordCell _ destination => validText effect.span destination
      | .writeCellInput _ inputName _ => validText effect.span inputName
      | .writeMapInput _ key inputName _ => do
        validText effect.span inputName
        match key with
        | .argument name _ => validText effect.span name
        | .mk .. => pure ()
      | .writeRecordCell _ fields =>
        if fields.length > Noctium.maxEntrypointReturnFields then
          resource effect.span "record Cell fields"
        recordEffectFields := recordEffectFields + fields.length
        for (field, _) in fields do validText effect.span field
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
    definition.imports.length + definition.exports.length + definition.entrypoints.length + recordEffectFields +
    definition.entrypoints.foldl (fun count entry =>
      count + entry.effects.length + entry.returns.length + entry.opaqueCellHashReturns.length +
        entry.cellReturns.length + entry.mapReturns.length + entry.callInputs.length +
        entry.effects.foldl (fun nodes effect => nodes + match effect.effect with
          | .writeMapInput _ key _ _ => moduleMapKeySourceNodes key
          | _ => 0) 0 +
        entry.mapReturns.foldl (fun nodes returned =>
          nodes + moduleMapKeySourceNodes returned.key) 0) 0 +
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

private abbrev TypeEnvironment := List (String × ModuleTypeValue)
private abbrev NaturalEnvironment := List (String × Nat)

private def canonicalField (field : Types.Field) : Types.Field :=
  {field with span := {}}

private def canonicalVariant (variant : Types.VariantDecl) : Types.VariantDecl :=
  {variant with
    span := {}
    fields := variant.fields.map canonicalField}

private def canonicalCompositeEnvironment (environment : Types.CompositeEnv) : Types.CompositeEnv :=
  let structures := (environment.structures.map fun declaration =>
    {declaration with
      span := {}
      fields := declaration.fields.map canonicalField}).mergeSort fun left right => decide (left.id < right.id)
  let enumerations := (environment.enumerations.map fun declaration =>
    {declaration with
      span := {}
      variants := declaration.variants.map canonicalVariant}).mergeSort fun left right => decide (left.id < right.id)
  {structures, enumerations}

private def normalizeModuleTypeValue (limits : Limits) (span : SourceSpan)
    (value : Types.CompositeType) (environment : Option Types.CompositeEnv) :
    Except Diagnostic (ModuleTypeValue × Option Types.CompositeEnv) := do
  let _ ← consumeTypeNodes span
    (min limits.maxExpandedNodes Types.defaultLimits.maxLayoutNodes) value
  let reachable := canonicalCompositeEnvironment ((environment.getD {}).reachable value)
  unless value.referencedIds.isEmpty do
    match Types.checkedLayout Types.defaultLimits reachable value with
    | .ok _ => pure ()
    | .error diagnostic => fail span diagnostic.message
  let reachable? := if reachable.structures.isEmpty && reachable.enumerations.isEmpty then
      none else some reachable
  pure ({value, environment := reachable}, reachable?)

private def normalizeTypeEnvironments (limits : Limits) (span : SourceSpan)
    (arguments : List SpecializationArgument) (environments : List (Option Types.CompositeEnv)) :
    Except Diagnostic (List (Option Types.CompositeEnv)) := do
  let environments := if environments.isEmpty then
      List.replicate arguments.length none else environments
  unless environments.length == arguments.length do
    fail span "Noctium module type environment count does not match its arguments"
  (arguments.zip environments).mapM fun (argument, environment) =>
    match argument, environment with
    | .type value, environment => do
      let (_, environment) ← normalizeModuleTypeValue limits span value environment
      pure environment
    | .natural _, none => pure none
    | .natural _, some _ => fail span "Noctium natural arguments cannot carry a type environment"

private def mergeCompositeEnvironments (span : SourceSpan)
    (left right : Types.CompositeEnv) : Except Diagnostic Types.CompositeEnv := do
  let mut structures := left.structures
  let mut enumerations := left.enumerations
  for candidate in right.structures do
    if enumerations.any (·.id == candidate.id) then
      fail span s!"conflicting module composite declaration '{candidate.id}'"
    if let some prior := structures.find? (·.id == candidate.id) then
      let priorLayout := Types.CompositeType.fingerprint left (.structure prior.id)
      let candidateLayout := Types.CompositeType.fingerprint right (.structure candidate.id)
      unless priorLayout == candidateLayout do
        fail span s!"conflicting module structure layout '{candidate.id}'"
    else
      structures := structures ++ [candidate]
  for candidate in right.enumerations do
    if structures.any (·.id == candidate.id) then
      fail span s!"conflicting module composite declaration '{candidate.id}'"
    if let some prior := enumerations.find? (·.id == candidate.id) then
      let priorLayout := Types.CompositeType.fingerprint left (.enumeration prior.id)
      let candidateLayout := Types.CompositeType.fingerprint right (.enumeration candidate.id)
      unless priorLayout == candidateLayout do
        fail span s!"conflicting module enumeration layout '{candidate.id}'"
    else
      enumerations := enumerations ++ [candidate]
  pure (canonicalCompositeEnvironment {structures, enumerations})

private def mergeTypeEnvironments (span : SourceSpan)
    (environments : List (Option Types.CompositeEnv)) :
    Except Diagnostic Types.CompositeEnv := do
  environments.foldlM (fun accumulated environment =>
    mergeCompositeEnvironments span accumulated (environment.getD {})) {}

private def moduleTypesEnvironment (span : SourceSpan) (types : TypeEnvironment) :
    Except Diagnostic Types.CompositeEnv :=
  mergeTypeEnvironments span (types.map fun (_, value) =>
    if value.environment.structures.isEmpty && value.environment.enumerations.isEmpty then none
    else some value.environment)

private def bindArguments (limits : Limits) (span : SourceSpan)
    (parameters : List TypeParameter) (arguments : List SpecializationArgument)
    (typeEnvironments : List (Option Types.CompositeEnv) := []) :
    Except Diagnostic (TypeEnvironment × NaturalEnvironment × List (Option Types.CompositeEnv)) := do
  if parameters.length > limits.maxArguments || arguments.length > limits.maxArguments then
    resource span "module argument count"
  unless parameters.length == arguments.length do
    fail span "Noctium module specialization arity mismatch"
  let typeEnvironments ← normalizeTypeEnvironments limits span arguments typeEnvironments
  let mut types : TypeEnvironment := []
  let mut naturals : NaturalEnvironment := []
  let mut remainingNodes := min limits.maxExpandedNodes Types.defaultLimits.maxLayoutNodes
  let bindings := (parameters.zip arguments).zip typeEnvironments
  for ((parameter, argument), environment) in bindings do
    match parameter.kind, argument with
    | .type, .type value => do
      remainingNodes ← consumeTypeNodes span remainingNodes value
      let (moduleType, _) ← normalizeModuleTypeValue limits span value environment
      types := (parameter.name, moduleType) :: types
    | .natural, .natural value => do
      if value > limits.maxNaturalValue then resource span "module natural argument"
      naturals := (parameter.name, value) :: naturals
    | _, _ => fail span s!"Noctium module specialization kind mismatch for '{parameter.name}'"
  pure (types, naturals, typeEnvironments)

private def resolveArgument (limits : Limits) (span : SourceSpan)
    (types : TypeEnvironment) (naturals : NaturalEnvironment) :
    ModuleArgument → Except Diagnostic (SpecializationArgument × Option Types.CompositeEnv)
  | .typeValue value => do
    let (moduleType, environment) ← normalizeModuleTypeValue limits span value none
    pure (.type moduleType.value, environment)
  | .checkedTypeValue value environment => do
    let (moduleType, environment) ← normalizeModuleTypeValue limits span value (some environment)
    pure (.type moduleType.value, environment)
  | .typeParameter name => do
    let some moduleType := types.lookup name
      | fail span s!"unbound Noctium module type parameter '{name}'"
    let environment := if moduleType.environment.structures.isEmpty &&
        moduleType.environment.enumerations.isEmpty then none else some moduleType.environment
    pure (.type moduleType.value, environment)
  | .naturalValue value => do
    if value > limits.maxNaturalValue then resource span "module natural argument"
    pure (.natural value, none)
  | .naturalParameter name => do
    let some value := naturals.lookup name
      | fail span s!"unbound Noctium module natural parameter '{name}'"
    pure (.natural value, none)

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
    let some moduleType := types.lookup name
      | fail span s!"unbound Noctium module type parameter '{name}'"
    match moduleType.value with
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
      | .opaqueBytes | .opaqueString => pure ty
      | .jubjubScalar | .jubjubPoint =>
        fail span "Jubjub state parameters are not supported by module specialization"
      | .foreign _ => fail span "foreign state parameters are not supported by module specialization"
    | _ => fail span s!"Noctium ledger state parameter '{name}' must specialize to a scalar; aggregate ledger state is not supported"

private def resolveModuleMapKeyType (limits : Limits) (span : SourceSpan)
    (types : TypeEnvironment) (naturals : NaturalEnvironment)
    (value : ModuleScalarType) : Except Diagnostic Ty := do
  match value with
  | .parameter name => do
    let some moduleType := types.lookup name
      | fail span s!"unbound Noctium module type parameter '{name}'"
    match moduleType.value with
    | .bytes 32 => pure (.bytes 32)
    | .bytes _ => fail span "module Map byte keys only support Bytes32"
    | _ => resolveStateScalar limits span types naturals value
  | _ => resolveStateScalar limits span types naturals value

private def resolveModuleCellKind (limits : Limits) (span : SourceSpan)
    (types : TypeEnvironment) (naturals : NaturalEnvironment)
    (value : ModuleScalarType) : Except Diagnostic StateKind := do
  match value with
  | .parameter name =>
    let some moduleType := types.lookup name
      | fail span s!"unbound Noctium module type parameter '{name}'"
    match moduleType.value with
    | .structure _ => do
      match LedgerValueType.cellRecordFields moduleType.environment moduleType.value with
      | .ok _ => pure (.tree (.composite moduleType.environment moduleType.value))
      | .error message => fail span message
    | .scalar .jubjubScalar => pure (.cell .jubjubScalar)
    | _ => .cell <$> resolveStateScalar limits span types naturals value
  | _ => .cell <$> resolveStateScalar limits span types naturals value

private def moduleRecordType? (types : TypeEnvironment) : ModuleScalarType → Option ModuleTypeValue
  | .parameter name => do
    let type ← types.lookup name
    match type.value with
    | .structure _ => some type
    | _ => none
  | _ => none

private def resolveModuleStateKind (limits : Limits) (span : SourceSpan)
    (types : TypeEnvironment) (naturals : NaturalEnvironment) :
    ModuleStateKind → Except Diagnostic StateKind
  | .cell value => resolveModuleCellKind limits span types naturals value
  | .map key value => do
    let recordValue := moduleRecordType? types value
    if let some recordKey := moduleRecordType? types key then
      discard <| (LedgerValueType.ledgerRecordWriteFields
        recordKey.environment recordKey.value).mapError fun message => {span, message}
      if let some recordValue := recordValue then
        discard <| (LedgerValueType.ledgerRecordWriteFields
          recordValue.environment recordValue.value).mapError fun message => {span, message}
        return .tree (.recordMapComposite recordKey.environment recordKey.value
          recordValue.environment recordValue.value)
      let valueTy ← resolveStateScalar limits span types naturals value
      if valueTy.isOpaqueBytes || valueTy.isOpaqueString then
        fail span "opaque types are not supported by module Map state specialization"
      return .tree (.recordMapKey recordKey.environment recordKey.value valueTy)
    let keyTy ← resolveModuleMapKeyType limits span types naturals key
    if keyTy.isOpaqueBytes || keyTy.isOpaqueString then
      fail span "opaque types are not supported by module Map state specialization"
    if let some recordValue := recordValue then
      discard <| (LedgerValueType.ledgerRecordWriteFields
        recordValue.environment recordValue.value).mapError fun message => {span, message}
      return .tree (.map keyTy (.composite recordValue.environment recordValue.value))
    let valueTy ← resolveStateScalar limits span types naturals value
    if valueTy.isOpaqueBytes || valueTy.isOpaqueString then
      fail span "opaque types are not supported by module Map state specialization"
    pure (.map keyTy valueTy)

private def keyEncodingSize (limits : Limits) (span : SourceSpan) (key : ModuleKey) :
    Except Diagnostic Nat := do
  if key.arguments.length > limits.maxArguments then resource span "module argument count"
  let typeEnvironments ← normalizeTypeEnvironments limits span key.arguments key.typeEnvironments
  let sourceSize ← nameEncodingSize span limits.maxSourceDepth key.sourceName
  let mut remainingNodes := min limits.maxExpandedNodes Types.defaultLimits.maxLayoutNodes
  for (argument, environment) in key.arguments.zip typeEnvironments do
    match argument with
    | .type value => do
      remainingNodes ← consumeTypeNodes span remainingNodes value
      let _ ← normalizeModuleTypeValue limits span value environment
    | .natural value => do
      if value > limits.maxNaturalValue then resource span "module natural argument"
  let key := {key with typeEnvironments}
  let encodedArguments := String.join (key.arguments.zipIdx.map fun (argument, index) =>
    encodeArgument (key.typeEnvironments[index]?.join) argument)
  pure (2 + sourceSize + 3 + natEncodingSize key.arguments.length + encodedArguments.utf8ByteSize)

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
        | .readRecordCell target _ | .writeRecordCell target _ | .writeCellInput target _ _
        | .writeMapInput target _ _ _
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
        | .readRecordCell .., some (.tree (.composite ..))
        | .writeCellInput .., some (.cell _)
        | .writeCellInput .., some (.tree (.composite ..))
        | .writeRecordCell .., some (.tree (.composite ..))
        | .writeMapInput .., some (.map ..)
        | .writeMapInput .., some (.tree (.map _ (.composite ..)))
        | .writeMapInput .., some (.tree (.recordMapKey ..))
        | .writeMapInput .., some (.tree (.recordMapComposite ..)) => pure ()
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
            .readRecordCell .., _ | .writeRecordCell .., _ | .writeCellInput .., _ |
            .readMap .., _ | .writeMap .., _ | .writeMapInput .., _ |
            .requireAbsent .., _ =>
          fail effectSpec.span s!"module effect type does not match state member '{stateMember.name}'"
    for returned in entrypoint.opaqueCellHashReturns do
      let identity ← resolveStateTargetInModule returned.span key members views returned.state
      unless identity.kind == .state do
        fail returned.span "module hash return target is not a state member"
      let some stateMember := findIdentityMember state key members identity
        | fail returned.span "module hash return state declaration identity is unavailable"
      match stateMember.stateKind? with
      | some (.cell .opaqueBytes) | some (.cell .opaqueString) => pure ()
      | some (.cell _) => fail returned.span "module hash return requires an OpaqueBytes or OpaqueString root Cell"
      | some (.map ..) | some (.tree ..) | some (.merkleTree _) |
          some (.historicMerkleTree _) | some .opaqueString =>
        fail returned.span "module hash return requires an OpaqueBytes or OpaqueString root Cell"
      | none => fail returned.span "module hash return state has no declared type"

mutual
  private partial def instantiate (span : SourceSpan) (sourceName : Name)
      (arguments : List SpecializationArgument)
      (typeEnvironments : List (Option Types.CompositeEnv) := []) : ExpandM ModuleInstance := do
    let state ← get
    let some registered := lookupRegistered state.registry sourceName
      | liftE (fail span s!"unknown imported module '{sourceSpanName sourceName}'")
    let definition := registered.definition
    let (types, naturals, typeEnvironments) ← liftE (bindArguments state.limits span
      definition.parameters arguments typeEnvironments)
    let key : ModuleKey := {sourceName, arguments, typeEnvironments}
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
        let moduleEnvironment ← liftE (moduleTypesEnvironment template.span types)
        let composites ← liftE (mergeCompositeEnvironments template.span
          template.source.base.composites moduleEnvironment)
        let typeSource := {template.source with
          base := {template.source.base with composites}}
        let typeArguments := types.map fun (name, moduleType) => (name, moduleType.value)
        let specialized ← liftE (Noctium.Helpers.Specialization.specializeTypeWithEnvironment typeLimits
          typeSource typeArguments naturals template.value)
        let info : TypeInfo := {
          value := specialized.value
          environment := specialized.environment
          nominalUInt? := template.nominalUInt?
          nominalFieldPaths := template.nominalFieldPaths}
        liftE (validateNominalUInt template.span info.value info.nominalUInt?)
        liftE (validateNominalFieldPaths template.span info.value info.environment
          info.nominalFieldPaths)
        resolvedMember := {resolvedMember with typeInfo? := some info}
      resolvedMembers := resolvedMembers ++ [resolvedMember]
    let mut sourceExports : List (Nat × ResolvedSourceExport) := []
    for sourceMember in definition.members do
      if let some sourceExport := sourceMember.sourceExport? then
        let resolvedArguments ← sourceExport.arguments.mapM
          (fun argument => liftE (resolveArgument state.limits sourceExport.span types naturals argument))
        let sourceArguments := resolvedArguments.map Prod.fst
        let sourceTypeEnvironments := resolvedArguments.map Prod.snd
        let sourceKey : ModuleKey := {
          sourceName := sourceExport.program
          arguments := sourceArguments
          typeEnvironments := sourceTypeEnvironments}
        let _ ← liftE (keyEncodingSize state.limits sourceExport.span sourceKey)
        sourceExports := sourceExports ++ [(sourceMember.id, {
          program := sourceExport.program
          exportName := sourceExport.exportName
          arguments := sourceArguments
          typeEnvironments := sourceTypeEnvironments
          span := sourceExport.span})]
    let mut importedViews : List ImportedView := []
    for importSpec in definition.imports do
      let resolvedArguments ← importSpec.arguments.mapM
        (fun argument => liftE (resolveArgument state.limits importSpec.span types naturals argument))
      let childArguments := resolvedArguments.map Prod.fst
      let childTypeEnvironments := resolvedArguments.map Prod.snd
      let currentState ← get
      let targetName ← resolveImportTarget currentState importSpec.span key
        resolvedMembers importedViews importSpec.target
      let child ← instantiate importSpec.span targetName childArguments childTypeEnvironments
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

private def resolveContractState (expansion : Expansion) (moduleInstance : ModuleInstance)
    (span : SourceSpan) (target : StateTarget) :
    Except Diagnostic (MemberIdentity × String × StateKind) := do
  let identity ← resolveStateTargetInModule span moduleInstance.key
    moduleInstance.members moduleInstance.imports target
  unless identity.kind == .state do
    fail span "module target is not a state member"
  let some fieldName := expansion.stateFieldName identity
    | fail span "module state target has no canonical ledger field"
  let some member := expansion.findMember identity
    | fail span "module state declaration identity is missing"
  let some kind := member.stateKind?
    | fail span s!"state member '{member.name}' has no declared type"
  pure (identity, fieldName, kind)

private def validateConstructorParameter (span : SourceSpan) (name : String) :
    Except Diagnostic Unit := do
  validText span name
  unless Types.validFieldName name do
    fail span s!"invalid module constructor parameter '{name}'"

private def resolveScalarConstructorInput (span : SourceSpan) (fieldName parameterName : String)
    (ty : Ty) : Except Diagnostic (ConstructorParameter × ConstructorInitializer) := do
  validateConstructorParameter span parameterName
  let (parameterType, initializerValue) : ConstructorType × ConstructorValue := match ty with
    | .opaqueString => (.opaqueString, .opaqueStringParameter parameterName)
    | _ => (.scalar ty, .scalar (.ref parameterName : Expr ty))
  pure (
    {name := parameterName, type := parameterType},
    {state := fieldName, type := parameterType, value := initializerValue})

private def orderRecordFields (span : SourceSpan) (fields : List (String × Ty))
    (values : List (String × α)) : Except Diagnostic (List (Ty × α)) := do
  unless values.length == fields.length && uniqueStrings (values.map Prod.fst) do
    fail span "module record Cell requires exactly one value per field"
  fields.mapM fun (name, ty) => do
    let some value := values.lookup name
      | fail span s!"module record Cell is missing field '{name}'"
    pure (ty, value)

private def resolveConstructorInputs (expansion : Expansion) (root : ModuleInstance)
    (bindings : List ConstructorInputBinding) :
    Except Diagnostic (Option Constructor × List MemberIdentity) := do
  let mut parameters : List ConstructorParameter := []
  let mut initializers : List ConstructorInitializer := []
  let mut actions : List ConstructorAction := []
  let mut identities : List MemberIdentity := []
  for binding in bindings do
    let (identity, fieldName, kind) ← resolveContractState expansion root binding.span binding.state
    if identities.contains identity then
      fail binding.span s!"duplicate module constructor initializer for '{fieldName}'"
    let newParameters ← match kind with
      | .cell ty => do
        unless binding.recordFields.isEmpty do
          fail binding.span "scalar module constructor inputs use a single parameter"
        let (parameter, initializer) ←
          resolveScalarConstructorInput binding.span fieldName binding.parameterName ty
        initializers := initializers ++ [initializer]
        pure [parameter]
      | .tree (.composite environment type) => do
        unless binding.parameterName.isEmpty do
          fail binding.span "record module constructor inputs use named field parameters"
        let fields ← match LedgerValueType.cellWriteRecordFields environment type with
          | .ok fields => pure fields
          | .error message => fail binding.span message
        let ordered ← orderRecordFields binding.span fields binding.recordFields
        let params : List ConstructorParameter ← ordered.mapM fun (ty, name) => do
          validateConstructorParameter binding.span name
          pure {name, type := .scalar ty}
        let values := ordered.map fun (ty, name) => LedgerFieldExpr.mk ty (.ref name)
        actions := actions ++ [.initializeRecordCell fieldName values]
        pure params
      | _ => fail binding.span "module constructor inputs require a scalar or record root Cell"
    for parameter in newParameters do
      if let some previous := parameters.find? (·.name == parameter.name) then
        unless previous.type == parameter.type do
          fail binding.span s!"module constructor parameter '{parameter.name}' has conflicting cell types"
      else
        parameters := parameters ++ [parameter]
    identities := identities ++ [identity]
  let constructor? := if bindings.isEmpty then none else
    some {parameters, initializers, actions : Constructor}
  pure (constructor?, identities)

private def recordCellType (span : SourceSpan) (kind : StateKind) :
    Except Diagnostic (Types.CompositeEnv × Types.CompositeType) :=
  match kind with
  | .tree (.composite environment type) => pure (environment, type)
  | _ => fail span "module effect requires a checked root record Cell"

private def recordCellReadFields (span : SourceSpan) (environment : Types.CompositeEnv)
    (type : Types.CompositeType) : Except Diagnostic (List (String × Ty)) :=
  match LedgerValueType.cellRecordFields environment type with
  | .ok fields => pure fields
  | .error message => fail span message

private def recordCellDestinations (destination : String) (fields : List (String × Ty)) :
    List (String × Ty) :=
  fields.map fun (name, ty) => (s!"{destination}_{name}", ty)

private def decodeRecordInputField : (ty : Ty) → List (Expr .native) → Except String (Expr ty)
  | .native, [value] => pure value
  | .bool, [value] => pure (.cast .bool value)
  | .uint maximum, [value] => pure (.cast (.uint maximum) value)
  | .bytes length, octets => Helpers.fixedBytesFromOctets length octets
  | .jubjubPoint, [x, y] => pure (.jubjubFromCoordinates x y)
  | _, _ => throw "module record input field has an unsupported layout"

private def lowerRecordInput (span : SourceSpan) (environment : Types.CompositeEnv)
    (type : Types.CompositeType) (fields : List (String × Ty))
    (stateKind name : String) (disclosed : Bool) :
    Except Diagnostic (List LedgerFieldExpr × StateInputCheck) := do
  let checked ← (Types.checkedLayout Types.defaultLimits environment type span).mapError
    fun diagnostic => {span, message := diagnostic.message}
  let .structure _ members := checked.value
    | fail span s!"module record {stateKind} input requires a named structure"
  let names := Helpers.sourceLeafPaths checked.value name
  let leafTypes := Helpers.callViewLeafTypes checked.value
  let release (ty : Ty) (value : Expr ty) : LedgerFieldExpr :=
    .mk ty (if disclosed then .disclose span value else value)
  let values ← if fields.all (·.2 == .native) then do
    unless fields.length == names.length do fail span "module Native record input leaf count mismatch"
    pure (names.map fun leaf => release .native (.ref leaf))
  else do
    unless members.map Prod.fst == fields.map Prod.fst do
      fail span "module typed record layout does not match its ledger fields"
    (fields.zip members).mapM fun ((field, ty), (_, memberLayout)) => do
      let leaves := (Helpers.sourceLeafPaths memberLayout s!"{name}.{field}").map Expr.ref
      let value ← (decodeRecordInputField ty leaves).mapError fun message => {span, message}
      pure (release ty value)
  let view : CallInputView := {name, fields := names.zip leafTypes}
  pure (values, .record view (Types.CompositeType.fingerprint environment type) span stateKind)

private def resolveModuleRecordMapKey (span : SourceSpan)
    (environment : Types.CompositeEnv) (type : Types.CompositeType) (key : ModuleMapKey)
    (stateKind : String) : Except Diagnostic (List LedgerFieldExpr × List StateInputCheck) := do
  match key with
  | .argument name disclosed => do
    let fields ← (LedgerValueType.ledgerRecordWriteFields environment type).mapError fun message =>
      {span, message}
    let (values, check) ← lowerRecordInput span environment type fields stateKind name disclosed
    pure (values, [check])
  | .mk .. => fail span s!"module record {stateKind} keys require a named aggregate argument"

private def resolveModuleMapKey (span : SourceSpan) (keyType : Ty) (key : ModuleMapKey)
    (stateKind : String) : Except Diagnostic (PathKey × List StateInputCheck) := do
  match key with
  | .mk actualType value => do
    unless actualType == keyType do fail span "module Map key type mismatch"
    pure (.mk actualType value, [])
  | .argument name disclosed => do
    validText span name
    match keyType with
    | .bytes length => do
      unless length == 32 do fail span "module Map byte keys only support Bytes32"
      let environment : Types.CompositeEnv := {}
      let type : Types.CompositeType := .bytes length
      let checked ← (Types.checkedLayout Types.defaultLimits environment type span).mapError
        fun diagnostic => {span, message := diagnostic.message}
      let leafNames := Helpers.sourceLeafPaths checked.value name
      let octets : List (Expr .native) := leafNames.map Expr.ref
      let bytes ← (Helpers.fixedBytesFromOctets length octets).mapError fun message =>
        {span, message}
      let value : Expr (.bytes length) :=
        if disclosed then Expr.disclose span bytes else bytes
      let view : CallInputView := {
        name
        fields := leafNames.zip (Helpers.callViewLeafTypes checked.value)
      }
      pure (.mk (.bytes length) value, [
        .record view (Types.CompositeType.fingerprint environment type) span stateKind
      ])
    | _ => do
      let source : Expr keyType := .ref name
      let value : Expr keyType := if disclosed then Expr.disclose span source else source
      pure (.mk keyType value, [.scalar name keyType span stateKind])

private def resolveContractEffect (expansion : Expansion) (moduleInstance : ModuleInstance)
    (effectSpec : ModuleEffectSpec) :
    Except Diagnostic (Effect × List MemberIdentity × List StateInputCheck) := do
  let resolveState := resolveContractState expansion moduleInstance effectSpec.span
  match effectSpec.effect with
  | .readCell target destination ty => do
    let (identity, fieldName, _) ← resolveState target
    pure (.readCell fieldName destination ty, [identity], [])
  | .readRecordCell target destination => do
    let (identity, fieldName, kind) ← resolveState target
    let (environment, type) ← recordCellType effectSpec.span kind
    let fields ← recordCellReadFields effectSpec.span environment type
    pure (.readCompositePath fieldName destination [] type (recordCellDestinations destination fields),
      [identity], [])
  | .readMap target destination keyTy valueTy key => do
    let (identity, fieldName, _) ← resolveState target
    pure (.readMap fieldName destination keyTy valueTy key, [identity], [])
  | .require condition => pure (.require condition, [], [])
  | .writeCell target ty value => do
    let (identity, fieldName, _) ← resolveState target
    pure (.writeCell fieldName ty value, [identity], [])
  | .writeCellOutput target outputName => do
    let (identity, fieldName, kind) ← resolveState target
    match kind with
    | .cell ty => pure (.writeCell fieldName ty (.ref outputName), [identity], [])
    | .opaqueString => fail effectSpec.span "module output write does not support opaque string state"
    | _ => fail effectSpec.span "module output write requires a cell state"
  | .writeRecordCell target values => do
    let (identity, fieldName, kind) ← resolveState target
    let (environment, type) ← recordCellType effectSpec.span kind
    let fields ← match LedgerValueType.cellWriteRecordFields environment type with
      | .ok fields => pure fields
      | .error message => fail effectSpec.span message
    let ordered ← orderRecordFields effectSpec.span fields values
    for (ty, value) in ordered do
      unless ty == value.ty do fail effectSpec.span "module record Cell write field type mismatch"
    pure (.writeCompositePath fieldName [] type (ordered.map Prod.snd), [identity], [])
  | .writeCellInput target name disclosed => do
    let (identity, fieldName, kind) ← resolveState target
    match kind with
    | .cell .opaqueBytes | .cell .opaqueString =>
      fail effectSpec.span "opaque module Cell writes require an explicit typed effect"
    | .cell ty =>
      let source : Expr ty := .ref name
      let value := if disclosed then Expr.disclose effectSpec.span source else source
      pure (.writeCell fieldName ty value, [identity], [.scalar name ty effectSpec.span "Cell"])
    | .tree (.composite environment type) => do
      let fields ← (LedgerValueType.cellWriteRecordFields environment type).mapError fun message =>
        {span := effectSpec.span, message}
      let (values, layout) ← lowerRecordInput effectSpec.span environment type fields "Cell" name disclosed
      pure (.writeCompositePath fieldName [] type values, [identity], [layout])
    | _ => fail effectSpec.span "module input write requires a root Cell"
  | .writeMapInput target key name disclosed => do
    let (identity, fieldName, kind) ← resolveState target
    match kind with
    | .map expectedKeyTy valueTy => do
      let (pathKey, keyChecks) ← resolveModuleMapKey effectSpec.span expectedKeyTy key "Map key"
      let .mk keyTy keyValue := pathKey
      let source : Expr valueTy := .ref name
      let value := if disclosed then Expr.disclose effectSpec.span source else source
      pure (.writeMap fieldName keyTy valueTy keyValue value, [identity],
        keyChecks ++ [.scalar name valueTy effectSpec.span "Map"])
    | .tree (.map keyTy (.composite environment type)) => do
      let (pathKey, keyChecks) ← resolveModuleMapKey effectSpec.span keyTy key "Map key"
      let fields ← (LedgerValueType.ledgerRecordWriteFields environment type).mapError fun message =>
        {span := effectSpec.span, message}
      let (values, layout) ← lowerRecordInput effectSpec.span environment type fields "Map" name disclosed
      pure (.writeCompositePath fieldName [pathKey] type values, [identity], keyChecks ++ [layout])
    | .tree (.recordMapKey keyEnvironment keyType valueTy) => do
      let (keyValues, keyChecks) ← resolveModuleRecordMapKey effectSpec.span
        keyEnvironment keyType key "Map key"
      let source : Expr valueTy := .ref name
      let value := if disclosed then Expr.disclose effectSpec.span source else source
      pure (.writeRecordMap fieldName keyValues valueTy value [], [identity],
        keyChecks ++ [.scalar name valueTy effectSpec.span "Map"])
    | .tree (.recordMapComposite keyEnvironment keyType valueEnvironment valueType) => do
      let (keyValues, keyChecks) ← resolveModuleRecordMapKey effectSpec.span
        keyEnvironment keyType key "Map key"
      let fields ← (LedgerValueType.ledgerRecordWriteFields valueEnvironment valueType).mapError
        fun message => {span := effectSpec.span, message}
      let (valueValues, valueCheck) ← lowerRecordInput effectSpec.span valueEnvironment
        valueType fields "Map" name disclosed
      pure (.writeRecordMapComposite fieldName valueType keyValues valueValues [], [identity],
        keyChecks ++ [valueCheck])
    | _ => fail effectSpec.span "module input write requires a root Map"
  | .writeMap target keyTy valueTy key value => do
    let (identity, fieldName, _) ← resolveState target
    pure (.writeMap fieldName keyTy valueTy key value, [identity], [])
  | .requireAbsent target keyTy key => do
    let (identity, fieldName, _) ← resolveState target
    pure (.requireAbsent fieldName keyTy key, [identity], [])

private def resolveOpaqueCellHashReturn (expansion : Expansion)
    (moduleInstance : ModuleInstance) (returned : OpaqueCellHashReturn) :
    Except Diagnostic (Output × Effect × MemberIdentity) := do
  let identity ← resolveStateTargetInModule returned.span moduleInstance.key
    moduleInstance.members moduleInstance.imports returned.state
  unless identity.kind == .state do
    fail returned.span "module hash return target is not a state member"
  let some fieldName := expansion.stateFieldName identity
    | fail returned.span "module hash return target has no canonical ledger field"
  let some member := expansion.findMember identity
    | fail returned.span "module hash return state declaration identity is missing"
  let some (.cell ty) := member.stateKind?
    | fail returned.span "module hash return requires an opaque root Cell"
  let destination := s!"moduleHashValue_{returned.name}"
  let projection : Expr .native ← match ty with
    | .opaqueBytes => pure (.opaqueBytesProjection (.ref destination))
    | .opaqueString => pure (.opaqueStringProjection (.ref destination))
    | _ => fail returned.span "module hash return requires an OpaqueBytes or OpaqueString root Cell"
  let output : Output := {
    name := returned.name
    ty := .native
    value := .transientHash [projection]
    span := returned.span}
  pure (output, .readCell fieldName destination ty, identity)

private def scalarValueReturn (returned : StateValueReturn) (ty : Ty) (stateKind : String)
    (read : String → Effect) (identity : MemberIdentity) :
    List Output × Option ReturnView × Effect × MemberIdentity :=
  let destination := s!"module{stateKind}Value_{returned.name}"
  let output : Output := {name := returned.name, ty, value := .ref destination, span := returned.span}
  ([output], none, read destination, identity)

private def recordValueReturn (returned : StateValueReturn) (environment : Types.CompositeEnv)
    (type : Types.CompositeType) (fields : List (String × Ty))
    (readEffect : String → List (String × Ty) → Effect) (identity : MemberIdentity) :
    List Output × Option ReturnView × Effect × MemberIdentity := Id.run do
  let destination := s!"moduleRecordValue_{returned.name}"
  let destinations := recordCellDestinations destination fields
  let read := readEffect destination destinations
  let values := destinations.flatMap fun (name, ty) =>
    match ty with
    | .bytes length =>
      (List.range length).map fun index =>
        Expr.cast .native (Expr.bytesAt (Expr.ref name : Expr (.bytes length)) index)
    | _ => (Expr.ref name : Expr ty).nativeCallFields
  let outputs : List Output := values.zipIdx.map fun (value, index) =>
    {name := s!"moduleRecordReturn_{returned.name}_{index}", ty := .native,
      value, span := returned.span}
  return (outputs, some {name := returned.name, environment, type, fields := outputs.map (·.name)},
    read, identity)

private def resolveCellValueReturn (expansion : Expansion) (moduleInstance : ModuleInstance)
    (returned : StateValueReturn) :
    Except Diagnostic (List Output × Option ReturnView × Effect × MemberIdentity) := do
  let (identity, fieldName, kind) ←
    resolveContractState expansion moduleInstance returned.span returned.state
  match kind with
  | .cell .opaqueBytes | .cell .opaqueString =>
    fail returned.span "opaque module Cell returns require opaqueCellHashReturns"
  | .cell ty =>
    pure (scalarValueReturn returned ty "Cell" (fun destination => .readCell fieldName destination ty) identity)
  | .tree (.composite environment type) => do
    let fields ← recordCellReadFields returned.span environment type
    pure (recordValueReturn returned environment type fields
      (fun destination destinations =>
        .readCompositePath fieldName destination [] type destinations) identity)
  | _ => fail returned.span "module return requires a root Cell"

private def resolveMapValueReturn (expansion : Expansion) (moduleInstance : ModuleInstance)
    (returned : MapValueReturn) :
    Except Diagnostic (List Output × Option ReturnView × Effect × MemberIdentity ×
      List StateInputCheck) := do
  let (identity, fieldName, kind) ←
    resolveContractState expansion moduleInstance returned.span returned.state
  match kind with
  | .map expectedKeyTy valueTy => do
    let (pathKey, keyChecks) ← resolveModuleMapKey returned.span expectedKeyTy returned.key "Map key"
    let .mk keyTy key := pathKey
    let (outputs, view, read, state) := scalarValueReturn returned.toStateValueReturn valueTy "Map"
      (fun destination => .readMap fieldName destination keyTy valueTy key) identity
    pure (outputs, view, read, state, keyChecks)
  | .tree (.map keyTy (.composite environment type)) => do
    let (pathKey, keyChecks) ← resolveModuleMapKey returned.span keyTy returned.key "Map key"
    let fields ← (LedgerValueType.ledgerRecordFields environment type).mapError fun message =>
      {span := returned.span, message}
    let (outputs, view, read, state) := recordValueReturn returned.toStateValueReturn
      environment type fields (fun destination destinations =>
        .readCompositePath fieldName destination [pathKey] type destinations) identity
    pure (outputs, view, read, state, keyChecks)
  | .tree (.recordMapKey keyEnvironment keyType valueTy) => do
    let (keyValues, keyChecks) ← resolveModuleRecordMapKey returned.span
      keyEnvironment keyType returned.key "Map key"
    let (outputs, view, read, state) := scalarValueReturn returned.toStateValueReturn valueTy "Map"
      (fun destination => .readRecordMap fieldName destination valueTy keyValues []) identity
    pure (outputs, view, read, state, keyChecks)
  | .tree (.recordMapComposite keyEnvironment keyType valueEnvironment valueType) => do
    let (keyValues, keyChecks) ← resolveModuleRecordMapKey returned.span
      keyEnvironment keyType returned.key "Map key"
    let fields ← (LedgerValueType.ledgerRecordFields valueEnvironment valueType).mapError
      fun message => {span := returned.span, message}
    let (outputs, view, read, state) := recordValueReturn
      returned.toStateValueReturn valueEnvironment valueType fields
      (fun destination destinations =>
        .readRecordMapComposite fieldName destination valueType keyValues destinations []) identity
    pure (outputs, view, read, state, keyChecks)
  | _ => fail returned.span "module lookup return requires a root Map"

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
  let mapReturnsWithChecks ← entrypoint.mapReturns.mapM (resolveMapValueReturn expansion origin)
  let mapReturnChecks := mapReturnsWithChecks.flatMap fun (_, _, _, _, checks) => checks
  let mapReturns := mapReturnsWithChecks.map fun (outputs, view, effect, identity, _) =>
    (outputs, view, effect, identity)
  let stateInputChecks := resolvedEffects.flatMap (·.2.2) ++ mapReturnChecks
  let generatedInputs := stateInputChecks.foldl (fun inputs checked =>
    if inputs.any (·.name == checked.name) then inputs else inputs ++ [checked])
    ([] : List StateInputCheck)
  let callInputViews := generatedInputs.filterMap fun
    | .record view .. => some view
    | .scalar .. => none
  let generatedNames := generatedInputs.flatMap fun
    | .record view .. => view.fields.map Prod.fst
    | .scalar name .. => [name]
  let resolvedReturns ← entrypoint.opaqueCellHashReturns.mapM
    (resolveOpaqueCellHashReturn expansion origin)
  let cellReturns ← entrypoint.cellReturns.mapM
    (resolveCellValueReturn expansion origin)
  let valueReturns := cellReturns ++ mapReturns
  let returnStateIdentities := resolvedReturns.map (·.2.2) ++ valueReturns.map (·.2.2.2)
  let guards := entrypoint.effects.map (·.guard)
  pure {
    name := exportName
    identity := exported.identity
    circuit
    effects := resolvedEffects.map (·.1) ++ resolvedReturns.map (·.2.1) ++
      valueReturns.map (·.2.2.1)
    effectGuards := if guards.any Option.isSome then
      guards ++ List.replicate (resolvedReturns.length + valueReturns.length) none
      else []
    returns := entrypoint.returns ++ resolvedReturns.map (·.1) ++ valueReturns.flatMap (·.1)
    returnViews := valueReturns.filterMap (·.2.1)
    callInputs := entrypoint.callInputs ++ generatedNames
    callInputViews
    stateInputChecks
    stateIdentities := (resolvedEffects.flatMap (·.2.1) ++ returnStateIdentities).eraseDups
    span := entrypoint.span
    effectSpans := entrypoint.effects.map (·.span) ++
      entrypoint.opaqueCellHashReturns.map (·.span) ++ entrypoint.cellReturns.map (·.span) ++
      entrypoint.mapReturns.map (·.span)}

/-- Build canonical state declarations and entrypoint templates for one module
root. The frontend attaches checked monomorphic circuit values before creating
the ordinary `Contract` consumed by existing analysis and native lowering. -/
def Expansion.contractPlan (expansion : Expansion) (root : ModuleKey)
    (constructorInputs : List ConstructorInputBinding := []) :
    Except Diagnostic ModuleContractPlan := do
  if constructorInputs.length > 64 then resource {} "module constructor input count"
  let some rootInstance := expansion.findInstance root
    | fail {} "unknown root module specialization"
  let (constructor?, constructorStateIdentities) ←
    resolveConstructorInputs expansion rootInstance constructorInputs
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
    resolvedEntrypoints.flatMap (·.stateIdentities) ++ constructorStateIdentities).eraseDups
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
  pure {root, state := states, entrypoints := resolvedEntrypoints, circuits, constructor?}

private partial def genericTypeOfConcrete : Types.CompositeType → Except String GenericType
  | .unit => pure .unit
  | .scalar .native => pure .native
  | .scalar .bool => pure .bool
  | .scalar .opaqueBytes => pure .opaqueBytes
  | .scalar .opaqueString => pure .opaqueString
  | .scalar .jubjubScalar => pure .jubjubScalar
  | .scalar .jubjubPoint => pure .jubjubPoint
  | .scalar (.uint maximum) => pure (.uint (.literal maximum))
  | .scalar (.bytes _) => throw "scalar byte types cannot enter module specialization"
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
    let typeEnvironment ← mergeTypeEnvironments circuit.source.span
      circuit.source.typeEnvironments
    let request : ExportRequest := {
      sourceExport := circuit.source.exportName
      outputName := circuit.outputName
      arguments
      span := circuit.source.span}
    if let some prior := groups.find? (·.sourceProgram == circuit.source.program) then
      if prior.requests.any (·.outputName == request.outputName) then
        fail request.span "duplicate canonical module circuit identity"
      let mergedEnvironment ← mergeCompositeEnvironments circuit.source.span
        prior.typeEnvironment typeEnvironment
      groups := groups.map fun group =>
        if group.sourceProgram == circuit.source.program then
          {group with
            requests := group.requests ++ [request]
            typeEnvironment := mergedEnvironment}
        else group
    else
      groups := groups ++ [{sourceProgram := circuit.source.program, requests := [request], typeEnvironment}]
  let orderedGroups := groups.map fun group => {
    group with
    requests := group.requests.mergeSort fun left right =>
      decide (left.outputName < right.outputName)}
  pure (orderedGroups.mergeSort fun left right => Name.lt left.sourceProgram right.sourceProgram)

private def ModuleContractPlan.checkStateInputs (plan : ModuleContractPlan)
    (batches : List (Name × BatchResult)) : Except Diagnostic ModuleContractPlan := do
  let entrypoints ← plan.entrypoints.mapM fun operation => do
    if operation.stateInputChecks.isEmpty then return operation
    let some source := plan.circuits.find? (·.identity == operation.circuit)
      | fail operation.span "module state input circuit source is missing"
    let some batch := batches.lookup source.source.program
      | fail operation.span "module state input specialization is missing"
    let some signature := batch.program.exports.find? (·.name == source.outputName)
      | fail operation.span "module state input export is missing"
    for checked in operation.stateInputChecks do
      match checked with
      | .scalar name ty span stateKind =>
        let some input := signature.inputs.find? (·.name == name)
          | fail span s!"module scalar {stateKind} input '{name}' must be a scalar circuit input"
        unless input.visibility == .private do
          fail span s!"module scalar {stateKind} input '{name}' must be a private circuit input"
        unless input.ty == ty do
          fail span s!"module scalar {stateKind} input '{name}' does not match the checked {stateKind} type"
      | .record view layout span stateKind =>
        let name := view.name
        let some input := signature.compositeInputs.find? (·.name == name)
          | fail span s!"module record {stateKind} input '{name}' must be a checked aggregate argument"
        unless input.visibility == .private do
          fail span s!"module record {stateKind} input '{name}' must be a private circuit input"
        unless Types.CompositeType.fingerprint batch.program.composites input.type == layout do
          fail span s!"module record {stateKind} input '{name}' does not match the checked {stateKind} layout"
    pure {operation with stateInputChecks := []}
  pure {plan with entrypoints}

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
    let composites ← mergeCompositeEnvironments {} source.base.composites group.typeEnvironment
    let source := {source with base := {source.base with composites}}
    let batch ← Noctium.Helpers.Specialization.specializeRequestsWithLimits
      specializationLimits source group.requests
    batches := batches ++ [(group.sourceProgram, batch)]
  pure {plan := ← plan.checkStateInputs batches, batches}

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
  let plan ← expansion.contractPlan expansion.root request.constructorInputs
  plan.specializeWithSources specializationLimits sources

/-- Attach freshly compiled circuits to a checked module contract plan. -/
def ModuleContractPlan.assembleContract (plan : ModuleContractPlan) (name : String)
    (circuits : List Circuit) : Except Diagnostic Contract := do
  unless uniqueStrings (circuits.map (·.name)) do
    fail {} "duplicate compiled circuit name in module contract"
  let mut entrypoints : List Entrypoint := []
  for template in plan.entrypoints do
    unless template.stateInputChecks.isEmpty do
      fail template.span "module state inputs must be checked against the specialized source"
    let some source := plan.circuits.find? (·.identity == template.circuit)
      | fail template.span "module contract circuit source is missing"
    let some circuit := circuits.find? (·.name == source.outputName)
      | fail template.span s!"compiled module circuit '{source.outputName}' is missing"
    entrypoints := entrypoints ++ [{
      name := template.name
      circuit
      effects := template.effects
      effectGuards := template.effectGuards
      returns := template.returns
      returnViews := template.returnViews
      callInputs := template.callInputs
      callInputViews := template.callInputViews
      span := template.span
      effectSpans := template.effectSpans}]
  pure {name, state := plan.state, constructor := plan.constructor?, entrypoints}

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
