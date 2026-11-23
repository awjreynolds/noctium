import Noctium.Helpers
import Lean

namespace Noctium.Helpers.Specialization

open Noctium

local instance : Inhabited Diagnostic := ⟨{span := {}, message := ""}⟩

/-- The two compile-time generic argument kinds supported by source specialization. -/
inductive Kind where
  | type
  | natural
  deriving Repr, BEq, DecidableEq, Inhabited

structure TypeParameter where
  name : String
  kind : Kind
  deriving Repr, BEq, Inhabited

inductive Natural where
  | literal (value : Nat)
  | parameter (name : String)
  | add (left right : Natural)
  | multiply (left right : Natural)
  deriving Repr, BEq, Inhabited

mutual
  inductive GenericType where
    | unit
    | native
    | bool
    | jubjubScalar
    | jubjubPoint
    | uint (maximum : Natural)
    | parameter (name : String)
    | tuple (items : List GenericType)
    | structure (id : Types.DeclId) (arguments : List Argument)
    | enumeration (id : Types.DeclId)
    | vector (length : Natural) (element : GenericType)
    | bytes (length : Natural)
    | foreign (kind : Foreign.Kind)
    | alias (id : Types.DeclId) (arguments : List Argument)

  inductive Argument where
    | type (value : GenericType)
    | natural (value : Natural)
end

deriving instance Repr, BEq, Inhabited for GenericType, Argument

structure Structure where
  id : Types.DeclId
  parameters : List TypeParameter := []
  fields : List (String × GenericType) := []
  span : SourceSpan := {}
  deriving Repr, Inhabited

structure Alias where
  id : Types.DeclId
  parameters : List TypeParameter := []
  value : GenericType
  span : SourceSpan := {}
  deriving Repr, Inhabited

inductive Term where
  | unit
  | native (number : Nat)
  | bool (value : Bool)
  | uint (maximum : Natural) (number : Nat)
  | ref (name : String)
  | binary (op : ScalarPolicy.Binary) (left right : Term)
  | boolAnd (left right : Term)
  | boolOr (left right : Term)
  | boolXor (left right : Term)
  | foreignConstant (kind : Foreign.Kind) (encoding : List Nat)
  | curve (operation : Helpers.CurveOp) (arguments : List Term)
  | bytes (operation : Helpers.BytesOp) (arguments : List Term)
  | eq (left right : Term)
  | cast (target : GenericType) (value : Term)
  | disclose (span : SourceSpan) (value : Term)
  | select (condition yes no : Term)
  | ite (condition yes no : Term)
  | andThen (left right : Term)
  | orElse (left right : Term)
  | witness (name : String) (type : GenericType)
  | witnessCall (site name : String) (arguments : List Term)
  | poseidon2 (domain : Nat) (left right : Term)
  /-- Calls name a source declaration identity, so specialization never resolves
  a generated call through a runtime-signature overload group. -/
  | call (target : DeclarationId) (arguments : List Argument) (values : List Term)
  | composite (type : GenericType) (leaves : List Term)
  | project (value : Term) (projection : Types.Projection)
  | index (value index : Term)
  | effect (kind : EffectKind) (label : String) (result : Term)
  | at (span : SourceSpan) (value : Term)
  deriving Repr, Inhabited

inductive Statement where
  | bind (name : String) (type : GenericType) (value : Term)
  | evaluate (value : Term)
  | assert (condition : Term)
  | «return» (value : Option Term := none)
  | branch (condition : Term) (yes no : List Statement)
  | forRange (index : String) (start stop : Natural) (body : List Statement)
  | stage (capability key : String) (type : GenericType) (value : Term)
  | emitEvent (kind : EventKind) (payload : Term)
  | claimShielded (kind : ShieldedClaimKind) (digest : Term)
  deriving Repr, Inhabited

structure Declaration where
  id : DeclarationId
  name : String
  parameters : List TypeParameter := []
  values : List (String × GenericType) := []
  result : GenericType := .unit
  body : List Statement := []
  declaredPure : Bool := false
  span : SourceSpan := {}
  deriving Repr, Inhabited

structure ExportInput where
  name : String
  type : GenericType
  visibility : Visibility
  span : SourceSpan := {}
  deriving Repr, Inhabited

structure Export where
  name : String
  target : DeclarationId
  arguments : List Argument := []
  inputs : List ExportInput := []
  span : SourceSpan := {}
  deriving Repr, Inhabited

/-- `base` supplies concrete scopes and already checked, non-generic composite
declarations. All functions in this program live in `declarations`. -/
structure Program where
  base : Helpers.Program := {}
  structures : List Structure := []
  aliases : List Alias := []
  declarations : List Declaration := []
  exports : List Export := []
  deriving Repr

structure Limits where
  maxSpecializations : Nat := 256
  maxTypeSpecializations : Nat := 256
  maxSourceNodes : Nat := 16384
  maxSourceDepth : Nat := 128
  maxSpecializationDepth : Nat := 64
  maxExpandedNodes : Nat := 65536
  maxTypeArguments : Nat := 64
  maxNaturalValue : Nat := ScalarPolicy.maxUint
  deriving Repr, Inhabited

private def fail (span : SourceSpan) (message : String) : Except Diagnostic α :=
  .error {span, message := message}

private def resource (span : SourceSpan) (kind : String) : Except Diagnostic α :=
  fail span s!"Noctium specialization resource limit exceeded: {kind}"

inductive SpecializationArgument where
  | type (value : Types.CompositeType)
  | natural (value : Nat)
  deriving Repr, BEq, Inhabited

structure Key where
  declaration : DeclarationId
  arguments : List SpecializationArgument
  deriving Repr, BEq, Inhabited

structure Instance where
  key : Key
  target : DeclarationId
  name : String
  deriving Repr, BEq, Inhabited

structure Result where
  program : Helpers.Program
  exportName : String
  instances : List Instance
  deriving Repr

/-- One bounded specialization session for a selected set of source exports.
All roots share the declaration and type caches, and exports are processed by
name so caller order does not affect generated declaration identities. -/
structure BatchResult where
  program : Helpers.Program
  exportNames : List String
  sourceExports : List (String × String)
  instances : List Instance
  deriving Repr

/-- A requested monomorphic export may override its source export's generic
arguments and output name. Module expansion uses the source name and arguments
while keeping generated names tied to declaration identity. -/
structure ExportRequest where
  sourceExport : String
  outputName : String
  arguments : List Argument
  span : SourceSpan := {}
  deriving Repr, Inhabited

private abbrev TypeEnvironment := List (String × Types.CompositeType)
private abbrev NaturalEnvironment := List (String × Nat)

private structure State where
  source : Program := {}
  instances : List Instance := []
  activeDeclarations : List DeclarationId := []
  activeGeneratedNames : List String := []
  activeStructures : List Types.DeclId := []
  activeAliases : List Types.DeclId := []
  structureCache : List ((Types.DeclId × List SpecializationArgument) × Types.DeclId) := []
  aliasCache : List ((Types.DeclId × List SpecializationArgument) × Types.CompositeType) := []
  nominalIds : List (Types.DeclId × (Types.DeclId × List SpecializationArgument)) := []
  declarations : List Helpers.Declaration := []
  structures : List Types.StructDecl := []
  declarationCosts : List (DeclarationId × Nat) := []
  structureCosts : List (Types.DeclId × Nat) := []
  usedNames : List String := []
  nextOrdinal : Nat := 0
  expandedNodes : Nat := 0
  remainingSteps : Nat
  deriving Inhabited

private abbrev SpecializeM := StateT State (Except Diagnostic)

private def liftError (span : SourceSpan) (value : Except String α) : SpecializeM α := do
  match value with
  | .ok result => pure result
  | .error message => liftM (fail span message)

private def countOfKind (kind : Kind) : List TypeParameter → Nat
  | [] => 0
  | parameter :: rest => (if parameter.kind == kind then 1 else 0) + countOfKind kind rest

private def findDeclaration (program : Program) (id : DeclarationId) : Option Declaration :=
  program.declarations.find? (·.id == id)

private def findStructure (program : Program) (id : Types.DeclId) : Option Structure :=
  program.structures.find? (·.id == id)

private def findAlias (program : Program) (id : Types.DeclId) : Option Alias :=
  program.aliases.find? (·.id == id)

private def resultType (type : Types.CompositeType) : Helpers.ResultType :=
  match type with
  | .unit => .unit
  | .scalar ty => .scalar ty
  | other => .composite other

private def canonicalType : Types.CompositeType → String
  | .unit => "unit"
  | .scalar .native => "native"
  | .scalar .bool => "bool"
  | .scalar (.uint maximum) => s!"uint({maximum})"
  | .scalar (.bytes length) => s!"scalar-bytes({length})"
  | .scalar .opaqueBytes => "scalar-opaque-bytes"
  | .scalar .opaqueString => "scalar-opaque-string"
  | .scalar .jubjubScalar => "scalar-jubjub-scalar"
  | .scalar .jubjubPoint => "scalar-jubjub-point"
  | .scalar (.foreign kind) => s!"scalar-foreign({kind.sourceName})"
  | .tuple items => s!"tuple({String.intercalate "," (items.map canonicalType)})"
  | .structure id => s!"struct({id})"
  | .enumeration id => s!"enum({id})"
  | .vector length element => s!"vector({length},{canonicalType element})"
  | .bytes length => s!"bytes({length})"

private def canonicalTypeSize : Types.CompositeType → Nat
  | .unit => 4
  | .scalar .native => 6
  | .scalar .bool => 4
  | .scalar (.uint maximum) => 6 + (toString maximum).length
  | .scalar (.bytes length) => 14 + (toString length).length
  | .scalar .opaqueBytes => 19
  | .scalar .opaqueString => 20
  | .scalar .jubjubScalar => 20
  | .scalar .jubjubPoint => 19
  | .scalar (.foreign kind) => 16 + kind.sourceName.utf8ByteSize
  | .tuple items => 7 + (if items.isEmpty then 0 else items.length - 1) +
      items.foldl (fun size item => size + canonicalTypeSize item) 0
  | .structure id => 8 + id.utf8ByteSize
  | .enumeration id => 6 + id.utf8ByteSize
  | .vector length element => 9 + (toString length).length + canonicalTypeSize element
  | .bytes length => 7 + (toString length).length

private def canonicalArgumentSize : SpecializationArgument → Nat
  | .type value => 5 + canonicalTypeSize value
  | .natural value => 8 + (toString value).length

private def maxCanonicalKeyBytes := 1048576

private def canonicalArgument : SpecializationArgument → String
  | .type value => "type:" ++ canonicalType value
  | .natural value => "natural:" ++ toString value

private def canonicalKey (key : Key) : String :=
  s!"{key.declaration.scope}:{key.declaration.ordinal}[{String.intercalate ";" (key.arguments.map canonicalArgument)}]"

private def generatedTypeId (span : SourceSpan) (source : Types.DeclId)
    (arguments : List SpecializationArgument) : SpecializeM Types.DeclId := do
  let fullKeySize := source.utf8ByteSize + 2 +
    (if arguments.isEmpty then 0 else arguments.length - 1) +
    arguments.foldl (fun size argument => size + canonicalArgumentSize argument) 0
  if fullKeySize > maxCanonicalKeyBytes then
    liftM (resource span "canonical generic identity key size")
  let fullKey := source ++ "[" ++ String.intercalate ";" (arguments.map canonicalArgument) ++ "]"
  pure s!"NoctiumSpecialized.T{hash fullKey}"

private partial def consumeCompositeTypeNodes (span : SourceSpan) (remaining : Nat)
    (type : Types.CompositeType) : Except Diagnostic Nat := do
  if remaining == 0 then
    resource span "normalized type nodes"
  let remaining := remaining - 1
  match type with
  | .tuple items => items.foldlM (consumeCompositeTypeNodes span) remaining
  | .vector _ element => consumeCompositeTypeNodes span remaining element
  | _ => pure remaining

private def checkNormalizedTypeSize (limits : Limits) (span : SourceSpan)
    (type : Types.CompositeType) : SpecializeM Unit := do
  let maxNodes := min limits.maxExpandedNodes Types.defaultLimits.maxLayoutNodes
  let _ ← liftM (consumeCompositeTypeNodes span maxNodes type)

private def naturalBounded (limits : Limits) (span : SourceSpan) (value : Nat) : SpecializeM Nat := do
  if value > limits.maxNaturalValue then
    liftM (resource span "natural argument value")
  pure value

private def evalNatural (limits : Limits) (span : SourceSpan) (env : NaturalEnvironment)
    (value : Natural) : SpecializeM Nat := do
  let cap := limits.maxNaturalValue
  let rec go (fuel : Nat) (value : Natural) : SpecializeM Nat := do
    match fuel with
    | 0 => liftM (resource span "natural expression depth")
    | fuel + 1 => match value with
      | .literal value => naturalBounded limits span value
      | .parameter name =>
        match env.lookup name with
        | some value => naturalBounded limits span value
        | none => liftM (fail span s!"runtime generic argument '{name}' is not compile-time concrete")
      | .add left right => do
        let left ← go fuel left
        let right ← go fuel right
        if right > cap || left > cap - right then liftM (resource span "natural argument value")
        naturalBounded limits span (left + right)
      | .multiply left right => do
        let left ← go fuel left
        let right ← go fuel right
        if left != 0 && right > cap / left then liftM (resource span "natural argument value")
        naturalBounded limits span (left * right)
  go 128 value

mutual
  private partial def bindArguments (limits : Limits) (span : SourceSpan)
      (parameters : List TypeParameter) (arguments : List Argument)
      (types : TypeEnvironment) (naturals : NaturalEnvironment) :
      SpecializeM (List SpecializationArgument × TypeEnvironment × NaturalEnvironment) := do
    if parameters.length > limits.maxTypeArguments || arguments.length > limits.maxTypeArguments then
      liftM (resource span "generic argument count")
    unless parameters.length == arguments.length do
      liftM (fail span "Noctium specialization arity mismatch")
    let mut keyArguments := []
    -- Resolve actual arguments in the caller's lexical environment, then build
    -- a fresh environment for the declaration being instantiated. Carrying
    -- caller bindings into a zero-argument callee gives free generic names an
    -- accidental meaning and makes its structural cache key incomplete.
    let mut typeEnv : TypeEnvironment := []
    let mut naturalEnv : NaturalEnvironment := []
    for (parameter, argument) in parameters.zip arguments do
      match parameter.kind, argument with
      | .type, .type value => do
        let value ← normalizeType limits span types naturals value
        keyArguments := keyArguments ++ [.type value]
        typeEnv := (parameter.name, value) :: typeEnv
      | .natural, .natural value => do
        let value ← evalNatural limits span naturals value
        keyArguments := keyArguments ++ [.natural value]
        naturalEnv := (parameter.name, value) :: naturalEnv
      | _, _ => liftM (fail span s!"Noctium specialization kind mismatch for '{parameter.name}'")
    pure (keyArguments, typeEnv, naturalEnv)

  private partial def normalizeType (limits : Limits) (span : SourceSpan)
      (types : TypeEnvironment) (naturals : NaturalEnvironment)
      (value : GenericType) : SpecializeM Types.CompositeType := do
    let source := (← get).source
    let rec go (fuel : Nat) (value : GenericType) : SpecializeM Types.CompositeType := do
      match fuel with
      | 0 => liftM (resource span "type substitution depth")
      | fuel + 1 => match value with
        | .unit => pure .unit
        | .native => pure (.scalar .native)
        | .bool => pure (.scalar .bool)
        | .jubjubScalar => pure (.scalar .jubjubScalar)
        | .jubjubPoint => pure (.scalar .jubjubPoint)
        | .foreign kind => pure (.scalar (.foreign kind))
        | .uint maximum => do
          let maximum ← evalNatural limits span naturals maximum
          liftError span (ScalarPolicy.validate (.uint maximum))
          pure (.scalar (.uint maximum))
        | .parameter name =>
          match types.lookup name with
          | some value => pure value
          | none => liftM (fail span s!"runtime generic argument '{name}' is not compile-time concrete")
        | .tuple items => .tuple <$> items.mapM (go fuel)
        | .enumeration id => pure (.enumeration id)
        | .bytes length => .bytes <$> evalNatural limits span naturals length
        | .vector length element => do
          let length ← evalNatural limits span naturals length
          let element ← go fuel element
          pure (.vector length element)
        | .structure id arguments => do
          if let some declaration := findStructure source id then
            let (keyArguments, typeEnv, naturalEnv) ← bindArguments limits declaration.span
              declaration.parameters arguments types naturals
            instantiateStructure limits declaration keyArguments typeEnv naturalEnv
          else if arguments.isEmpty && source.base.composites.structures.any (·.id == id) then
            pure (.structure id)
          else
            liftM (fail span s!"unknown generic struct declaration '{id}'")
        | .alias id arguments => do
          let some declaration := findAlias source id
            | liftM (fail span s!"unknown generic type alias '{id}'")
          let (keyArguments, typeEnv, naturalEnv) ← bindArguments limits declaration.span
            declaration.parameters arguments types naturals
          let state ← get
          let cacheKey := (id, keyArguments)
          if let some value := state.aliasCache.lookup cacheKey then
            pure value
          else if state.activeAliases.contains id then
            liftM (fail declaration.span s!"Noctium specialization type-alias cycle at '{id}'")
          else
            let activeTypeSpecializations := state.aliasCache.length +
              state.structureCache.length + state.activeAliases.length
            if activeTypeSpecializations >= limits.maxTypeSpecializations then
              liftM (resource declaration.span "type-alias specialization count")
            if state.activeAliases.length + state.activeStructures.length >=
                limits.maxSpecializationDepth then
              liftM (resource declaration.span "generic type substitution depth")
            modify fun state => {state with activeAliases := id :: state.activeAliases}
            let value ← normalizeType limits declaration.span typeEnv naturalEnv declaration.value
            modify fun state => {state with
              activeAliases := state.activeAliases.filter (· != id)
              aliasCache := (cacheKey, value) :: state.aliasCache}
            pure value
    let result ← go 128 value
    checkNormalizedTypeSize limits span result
    pure result

  private partial def instantiateStructure (limits : Limits) (declaration : Structure)
      (arguments : List SpecializationArgument) (types : TypeEnvironment)
      (naturals : NaturalEnvironment) : SpecializeM Types.CompositeType := do
    let sourceKey := (declaration.id, arguments)
    let state ← get
    if state.activeStructures.contains declaration.id then
      liftM (fail declaration.span s!"Noctium specialization type cycle at struct '{declaration.id}'")
    if let some id := state.structureCache.lookup sourceKey then
      return .structure id
    let activeTypeSpecializations := state.structureCache.length +
      state.aliasCache.length + state.activeAliases.length
    if activeTypeSpecializations >= limits.maxTypeSpecializations then
      liftM (resource declaration.span "struct specialization count")
    if state.activeStructures.length + state.activeAliases.length >=
        limits.maxSpecializationDepth then
      liftM (resource declaration.span "generic type substitution depth")
    let retainedDeclarations := state.source.base.composites.structures.length +
      state.source.base.composites.enumerations.length + state.structures.length
    if retainedDeclarations >= Types.defaultLimits.maxDeclarations then
      liftM (resource declaration.span "retained composite declaration count")
    let baseLayoutNodes := state.source.base.composites.structures.foldl
        (fun count item => count + 1 + item.fields.length) 0 +
      state.source.base.composites.enumerations.foldl (fun count item =>
        count + 1 + item.variants.length +
          item.variants.foldl (fun fields variant => fields + variant.fields.length) 0) 0
    let generatedLayoutNodes := state.structures.foldl
      (fun count item => count + 1 + item.fields.length) 0
    let layoutCost := 1 + declaration.fields.length
    if baseLayoutNodes + generatedLayoutNodes > Types.defaultLimits.maxLayoutNodes - layoutCost then
      liftM (resource declaration.span "retained composite layout nodes")
    let source ← get
    let cloneCost := source.structureCosts.lookup declaration.id |>.getD declaration.fields.length
    if source.expandedNodes + cloneCost > limits.maxExpandedNodes then
      liftM (resource declaration.span "expanded nodes before struct specialization")
    if declaration.fields.length > limits.maxSourceNodes then
      liftM (resource declaration.span "struct fields")
    let id ← generatedTypeId declaration.span declaration.id arguments
    let state ← get
    if let some (_, priorKey) := state.nominalIds.find? (·.1 == id) then
      unless priorKey == sourceKey do
        liftM (fail declaration.span "Noctium generated nominal identity collision")
    if (state.source.base.composites.structures.any (·.id == id)) ||
        (state.source.base.composites.enumerations.any (·.id == id)) then
      liftM (fail declaration.span "Noctium generated nominal identity collides with a source declaration")
    modify fun state => {state with
      activeStructures := declaration.id :: state.activeStructures
      nominalIds := (id, sourceKey) :: state.nominalIds
      structureCache := (sourceKey, id) :: state.structureCache
      expandedNodes := state.expandedNodes + cloneCost}
    let mut fields := []
    for (name, fieldType) in declaration.fields do
      let type ← normalizeType limits declaration.span types naturals fieldType
      fields := fields ++ [{name, type, span := declaration.span : Types.Field}]
    modify fun state => {state with
      activeStructures := state.activeStructures.filter (· != declaration.id)
      structures := {id, fields, span := declaration.span : Types.StructDecl} :: state.structures}
    pure (.structure id)
end

private inductive SourceNode where
  | typeExpr (value : GenericType)
  | natural (value : Natural)
  | argument (value : Argument)
  | term (value : Term)
  | statement (value : Statement)

private def boundedChildren (span : SourceSpan) (limit : Nat) (values : List SourceNode) :
    Except Diagnostic (List SourceNode) := do
  if values.length > limit then resource span "source nodes"
  pure values

private def textLimit (span : SourceSpan) (value : String) : Except Diagnostic Unit := do
  if value.utf8ByteSize > 1024 then resource span "source text metadata"

private def spanLimit (span : SourceSpan) : Except Diagnostic Unit := do
  textLimit span span.file
  if span.line > 1000000000 || span.column > 1000000000 then
    resource span "source-span metadata"

private def sourceNodeMetadata (span : SourceSpan) : SourceNode → Except Diagnostic Unit
  | .natural (.parameter name) => textLimit span name
  | .typeExpr type => match type with
    | .parameter name | .enumeration name => textLimit span name
    | .structure id _ | .alias id _ => textLimit span id
    | _ => pure ()
  | .term term => match term with
    | .ref name | .witness name _ => textLimit span name
    | .witnessCall site name _ => do
      textLimit span site
      textLimit span name
      unless Helpers.validWitnessIdentifier site && Helpers.validWitnessIdentifier name do
        fail span "invalid typed witness site or provider identity"
    | .call target _ _ => do
      if target.scope > 18446744073709551615 || target.ordinal > 18446744073709551615 then
        resource span "declaration identity metadata"
    | .disclose sourceSpan _ | .at sourceSpan _ => spanLimit sourceSpan
    | .effect _ label _ => textLimit span label
    | .project _ (.field name) => textLimit span name
    | .project _ (.enumField variant field) => do
      textLimit span variant
      textLimit span field
    | _ => pure ()
  | .statement statement => match statement with
    | .bind name _ _ => textLimit span name
    | .forRange index _ _ _ => textLimit span index
    | .stage capability key _ _ => do
      textLimit span capability
      textLimit span key
    | _ => pure ()
  | .natural _ | .argument _ => pure ()

private def sourceChildren (limits : Limits) (span : SourceSpan) :
    SourceNode → Except Diagnostic (List SourceNode)
  | .natural (.literal _) | .natural (.parameter _) => pure []
  | .natural (.add left right) | .natural (.multiply left right) =>
    pure [.natural left, .natural right]
  | .argument (.type value) => pure [.typeExpr value]
  | .argument (.natural value) => pure [.natural value]
  | .typeExpr type => match type with
    | .unit | .native | .bool | .jubjubScalar | .jubjubPoint | .parameter _
    | .enumeration _ | .foreign _ => pure []
    | .uint maximum | .bytes maximum => pure [.natural maximum]
    | .tuple items => do
      if items.length > limits.maxSourceNodes then resource span "source nodes"
      pure (items.map SourceNode.typeExpr)
    | .structure _ arguments | .alias _ arguments => do
      if arguments.length > limits.maxTypeArguments then resource span "generic argument count"
      pure (arguments.map SourceNode.argument)
    | .vector length element => pure [.natural length, .typeExpr element]
  | .term term => match term with
    | .unit | .native _ | .bool _ | .ref _ | .foreignConstant .. => pure []
    | .uint maximum _ => pure [.natural maximum]
    | .binary _ left right | .boolAnd left right | .boolOr left right
    | .boolXor left right | .eq left right | .poseidon2 _ left right
    | .andThen left right | .orElse left right | .index left right =>
      pure [.term left, .term right]
    | .cast target value => pure [.typeExpr target, .term value]
    | .witness _ target => pure [.typeExpr target]
    | .disclose _ value | .project value _ | .effect _ _ value | .at _ value =>
      pure [.term value]
    | .curve _ arguments | .bytes _ arguments =>
      boundedChildren span limits.maxSourceNodes (arguments.map SourceNode.term)
    | .select condition yes no | .ite condition yes no => pure [.term condition, .term yes, .term no]
    | .call _ arguments values => do
      if arguments.length > limits.maxTypeArguments || values.length > limits.maxTypeArguments then
        resource span "call argument count"
      let argumentNodes := arguments.map SourceNode.argument
      let valueNodes := values.map SourceNode.term
      boundedChildren span limits.maxSourceNodes (argumentNodes ++ valueNodes)
    | .witnessCall _ _ arguments => do
      if arguments.length > limits.maxTypeArguments then resource span "call argument count"
      boundedChildren span limits.maxSourceNodes (arguments.map SourceNode.term)
    | .composite type leaves => do
      if leaves.length > limits.maxSourceNodes then resource span "source nodes"
      pure (SourceNode.typeExpr type :: leaves.map SourceNode.term)
  | .statement statement => match statement with
    | .bind _ type value => pure [.typeExpr type, .term value]
    | .evaluate value | .assert value => pure [.term value]
    | .return value => pure (value.toList.map SourceNode.term)
    | .branch condition yes no => do
      if yes.length + no.length > limits.maxSourceNodes then resource span "source nodes"
      let arms := (yes.map SourceNode.statement) ++ (no.map SourceNode.statement)
      pure (SourceNode.term condition :: arms)
    | .forRange _ start stop body => do
      if body.length + 2 > limits.maxSourceNodes then resource span "source nodes"
      pure ([SourceNode.natural start, SourceNode.natural stop] ++ body.map SourceNode.statement)
    | .stage _ _ type value => pure [.typeExpr type, .term value]
    | .emitEvent _ payload => pure [.term payload]
    | .claimShielded _ digest => pure [.term digest]

private def scanNodes (limits : Limits) (span : SourceSpan) (available : Nat)
    (initial : List SourceNode) : Except Diagnostic Nat := go available 0 (initial.map (·, 1))
where
  go : Nat → Nat → List (SourceNode × Nat) → Except Diagnostic Nat
    | _, used, [] => pure used
    | 0, _, _ :: _ => resource span "source nodes"
    | fuel + 1, used, (node, depth) :: rest => do
      if depth > limits.maxSourceDepth then resource span "source depth"
      sourceNodeMetadata span node
      let children ← sourceChildren limits span node
      if children.length > fuel then resource span "source nodes"
      go fuel (used + 1) (children.map (·, depth + 1) ++ rest)

private def validateParameters (limits : Limits) (span : SourceSpan)
    (parameters : List TypeParameter) : Except Diagnostic Unit := do
  if parameters.length > limits.maxTypeArguments then resource span "generic parameter count"
  unless uniqueNames (parameters.map (·.name)) do fail span "duplicate Noctium generic parameter"
  for parameter in parameters do textLimit span parameter.name

private def preflight (limits : Limits) (program : Program) :
    Except Diagnostic (List (DeclarationId × Nat) × List (Types.DeclId × Nat)) := do
  if limits.maxSpecializations > 256 || limits.maxTypeSpecializations > 256 ||
      limits.maxSourceNodes > 16384 ||
      limits.maxSourceDepth > 128 || limits.maxSpecializationDepth > 64 ||
      limits.maxExpandedNodes > 65536 || limits.maxTypeArguments > 64 ||
      limits.maxNaturalValue > ScalarPolicy.maxUint then
    resource {} "requested limits exceed hard policy"
  if program.declarations.length > 256 then resource {} "generic declarations"
  if program.structures.length + program.aliases.length > Types.defaultLimits.maxDeclarations then
    resource {} "generic type declarations"
  if program.exports.length > ({} : Helpers.Limits).maxExports then resource {} "generic exports"
  if !program.base.declarations.isEmpty || !program.base.exports.isEmpty then
    fail {} "specialization base must contain only scopes and concrete composite declarations"
  if program.base.scopes.length > ({} : Helpers.Limits).maxScopes then resource {} "base helper scopes"
  match program.base.composites.validate Types.defaultLimits with
  | .ok _ => pure ()
  | .error diagnostic => fail diagnostic.span diagnostic.message
  for scope in program.base.scopes do
    if scope.id > 18446744073709551615 then resource {} "scope identity metadata"
    if scope.parent.any (· > 18446744073709551615) then resource {} "scope identity metadata"
    if scope.values.length > ({} : Helpers.Limits).maxParameters then
      resource {} "base helper scope bindings"
    unless uniqueNames scope.values do fail {} "duplicate helper scope value name"
    for name in scope.values do textLimit {} name
  unless uniqueNames (program.base.scopes.map (toString ∘ Scope.id)) do
    fail {} "duplicate helper scope identity"
  unless uniqueNames ((program.declarations.map (fun declaration =>
      s!"{declaration.id.scope}:{declaration.id.ordinal}"))) do
    fail {} "duplicate generic declaration identity"
  let genericTypeIds := program.structures.map (·.id) ++ program.aliases.map (·.id)
  let baseTypeIds := program.base.composites.structures.map (·.id) ++
    program.base.composites.enumerations.map (·.id)
  unless uniqueNames (genericTypeIds ++ baseTypeIds) do
    fail {} "duplicate generic type declaration identity"
  unless uniqueNames (program.exports.map (·.name)) do fail {} "duplicate monomorphic helper entrypoint name"
  for declaration in program.declarations do
    spanLimit declaration.span
    textLimit declaration.span declaration.name
    if declaration.id.scope > 18446744073709551615 || declaration.id.ordinal > 18446744073709551615 then
      resource declaration.span "declaration identity metadata"
    if !program.base.scopes.any (·.id == declaration.id.scope) then
      fail declaration.span "unknown generic declaration scope"
    validateParameters limits declaration.span declaration.parameters
    if declaration.values.length > limits.maxTypeArguments then resource declaration.span "helper parameters"
    unless uniqueNames (declaration.values.map Prod.fst) do fail declaration.span "duplicate generic helper parameter"
    for (name, _) in declaration.values do textLimit declaration.span name
  let mut remaining := limits.maxSourceNodes
  let mut declarationCosts := []
  for declaration in program.declarations do
    if declaration.body.length > limits.maxSourceNodes then resource declaration.span "source nodes"
    let initial := (declaration.values.map fun (_, type) => SourceNode.typeExpr type) ++
      [SourceNode.typeExpr declaration.result] ++ declaration.body.map SourceNode.statement
    let used ← scanNodes limits declaration.span remaining initial
    remaining := remaining - used
    declarationCosts := (declaration.id, used) :: declarationCosts
  let mut structureCosts := []
  for declaration in program.structures do
    spanLimit declaration.span
    unless Types.validDeclId declaration.id do
      fail declaration.span s!"invalid generic struct identity '{declaration.id}'"
    textLimit declaration.span declaration.id
    validateParameters limits declaration.span declaration.parameters
    if declaration.fields.length > limits.maxSourceNodes then resource declaration.span "struct fields"
    unless uniqueNames (declaration.fields.map Prod.fst) do
      fail declaration.span "duplicate generic struct field"
    for (name, _) in declaration.fields do
      unless Types.validFieldName name do
        fail declaration.span s!"invalid generic struct field '{name}'"
      textLimit declaration.span name
    let initial := declaration.fields.map fun (_, type) => SourceNode.typeExpr type
    let used ← scanNodes limits declaration.span remaining initial
    remaining := remaining - used
    structureCosts := (declaration.id, used) :: structureCosts
  for declaration in program.aliases do
    spanLimit declaration.span
    unless Types.validDeclId declaration.id do
      fail declaration.span s!"invalid generic alias identity '{declaration.id}'"
    textLimit declaration.span declaration.id
    validateParameters limits declaration.span declaration.parameters
    let used ← scanNodes limits declaration.span remaining [.typeExpr declaration.value]
    remaining := remaining - used
  for entry in program.exports do
    spanLimit entry.span
    textLimit entry.span entry.name
    if entry.inputs.length > limits.maxTypeArguments || entry.arguments.length > limits.maxTypeArguments then
      resource entry.span "export inputs or generic arguments"
    let initial := (entry.arguments.map SourceNode.argument) ++
      (entry.inputs.map fun input => SourceNode.typeExpr input.type)
    let used ← scanNodes limits entry.span remaining initial
    remaining := remaining - used
    for input in entry.inputs do
      spanLimit input.span
      textLimit input.span input.name
  pure (declarationCosts, structureCosts)

private def spendStep (span : SourceSpan) : SpecializeM Unit := do
  let state ← get
  if state.remainingSteps == 0 then liftM (resource span "specialization steps")
  set {state with remainingSteps := state.remainingSteps - 1}

private def chargeExpanded (limits : Limits) (span : SourceSpan) (cost : Nat) : SpecializeM Unit := do
  let state ← get
  if cost > limits.maxExpandedNodes || state.expandedNodes > limits.maxExpandedNodes - cost then
    liftM (resource span "expanded nodes before substitution")
  set {state with expandedNodes := state.expandedNodes + cost}

private def helperParameter (_span : SourceSpan) (name : String)
    (type : Types.CompositeType) : SpecializeM (Helpers.Parameter × Option (String × Types.CompositeType)) := do
  match type with
  | .scalar ty => pure (⟨name, ty⟩, none)
  | composite => pure (⟨name, .native⟩, some (name, composite))

mutual
  private partial def specializeDeclaration (limits : Limits) (span : SourceSpan)
      (declaration : Declaration) (arguments : List Argument)
      (types : TypeEnvironment) (naturals : NaturalEnvironment) : SpecializeM Instance := do
    let (keyArguments, typeEnv, naturalEnv) ← bindArguments limits span
      declaration.parameters arguments types naturals
    specializeInstance limits span declaration keyArguments typeEnv naturalEnv

  private partial def specializeInstance (limits : Limits) (span : SourceSpan)
      (declaration : Declaration) (arguments : List SpecializationArgument)
      (types : TypeEnvironment) (naturals : NaturalEnvironment) : SpecializeM Instance := do
    let key : Key := ⟨declaration.id, arguments⟩
    let state ← get
    if state.activeDeclarations.contains declaration.id then
      liftM (fail span s!"Noctium specialization cycle at declaration {declaration.id.scope}:{declaration.id.ordinal}")
    if let some cached := state.instances.find? (·.key == key) then return cached
    -- Count pending instances as reservations. A parent clone remains active
    -- while its body specializes children, so completed-only counts would let
    -- a deeply nested graph exceed the configured limit before unwinding.
    if state.instances.length + state.activeDeclarations.length >= limits.maxSpecializations then
      liftM (resource span "specialization count")
    if state.activeDeclarations.length >= limits.maxSpecializationDepth then
      liftM (resource span "specialization call depth")
    let cloneCost := state.declarationCosts.lookup declaration.id |>.getD 1
    chargeExpanded limits span cloneCost
    spendStep span
    let state ← get
    let mut ordinal := state.nextOrdinal
    let mut generatedName := s!"__noctium_generated_{declaration.id.scope}_{ordinal}"
    while state.usedNames.contains generatedName do
      ordinal := ordinal + 1
      generatedName := s!"__noctium_generated_{declaration.id.scope}_{ordinal}"
    if ordinal > 18446744073709551615 then
      liftM (resource declaration.span "generated declaration identity")
    let target : DeclarationId := ⟨declaration.id.scope, ordinal⟩
    if state.declarations.any (·.id == target) ||
        state.source.declarations.any (·.id == target) then
      liftM (fail declaration.span "Noctium generated helper identity collision")
    let specialized : Instance := {key, target, name := generatedName}
    let callerGeneratedNames := state.activeGeneratedNames
    modify fun state => {state with
      activeDeclarations := declaration.id :: state.activeDeclarations
      activeGeneratedNames := generatedName :: state.activeGeneratedNames
      nextOrdinal := ordinal + 1
      usedNames := generatedName :: state.usedNames}
    let mut parameters := []
    let mut compositeParameters := []
    let mut valueEnvironment : List (String × Helpers.ResultType) := []
    for (name, type) in declaration.values do
      let concrete ← normalizeType limits declaration.span types naturals type
      valueEnvironment := (name, resultType concrete) :: valueEnvironment
      let (parameter, composite?) ← helperParameter declaration.span name concrete
      parameters := parameters ++ [parameter]
      if let some value := composite? then compositeParameters := compositeParameters ++ [value]
    let result ← resultType <$> normalizeType limits declaration.span types naturals declaration.result
    let body ← convertBody limits declaration types naturals valueEnvironment declaration.body
    let generated : Helpers.Declaration := {
      id := target
      name := generatedName
      parameters
      compositeParameters
      result
      body
      declaredPure := declaration.declaredPure
      span := declaration.span}
    modify fun state => {state with
      activeDeclarations := state.activeDeclarations.filter (· != declaration.id)
      activeGeneratedNames := callerGeneratedNames
      declarations := generated :: state.declarations
      instances := specialized :: state.instances}
    pure specialized

  private partial def convertBody (limits : Limits) (declaration : Declaration)
      (types : TypeEnvironment) (naturals : NaturalEnvironment)
      (outerValues : List (String × Helpers.ResultType))
      (body : List Statement) : SpecializeM (List Helpers.Statement) := do
    let mut values := outerValues
    let mut result : Array Helpers.Statement := #[]
    for statement in body do
      spendStep declaration.span
      match statement with
      | .bind name type value => do
        let type ← resultType <$> normalizeType limits declaration.span types naturals type
        let value ← convertTerm limits declaration types naturals values value
        if values.any (·.1 == name) then
          liftM (fail declaration.span s!"duplicate generic helper value '{name}'")
        values := (name, type) :: values
        result := result.push (.bind name type value)
      | .evaluate value => do
        result := result.push (.evaluate (← convertTerm limits declaration types naturals values value))
      | .assert condition => do
        result := result.push (.assert (← convertTerm limits declaration types naturals values condition))
      | .return value => do
        let value ← value.mapM (convertTerm limits declaration types naturals values)
        result := result.push (.return value)
      | .branch condition yes no => do
        let condition ← convertTerm limits declaration types naturals values condition
        let yes ← convertBody limits declaration types naturals values yes
        let no ← convertBody limits declaration types naturals values no
        result := result.push (.branch condition yes no)
      | .forRange index start stop body => do
        let start ← evalNatural limits declaration.span naturals start
        let stop ← evalNatural limits declaration.span naturals stop
        let body ← convertBody limits declaration types naturals
          ((index, .scalar .native) :: values) body
        result := result.push (.forRange index start stop body)
      | .stage capability key type value => do
        let concrete ← normalizeType limits declaration.span types naturals type
        let value ← convertTerm limits declaration types naturals values value
        result := result.push (.stage capability key (resultTypeOfComposite concrete) value)
      | .emitEvent kind payload => do
        let payload ← convertTerm limits declaration types naturals values payload
        result := result.push (.emitEvent kind payload)
      | .claimShielded kind digest => do
        let digest ← convertTerm limits declaration types naturals values digest
        result := result.push (.claimShielded kind digest)
    pure result.toList

  private partial def convertTerm (limits : Limits) (declaration : Declaration)
      (types : TypeEnvironment) (naturals : NaturalEnvironment)
      (values : List (String × Helpers.ResultType)) (term : Term) : SpecializeM Helpers.Term := do
    spendStep declaration.span
    match term with
    | .unit => pure .unit
    | .native value => pure (.native value)
    | .bool value => pure (.bool value)
    | .uint maximum value => do
      let maximum ← evalNatural limits declaration.span naturals maximum
      pure (.uint maximum value)
    | .ref name => pure (.ref name)
    | .binary op left right =>
      .binary op <$> convertTerm limits declaration types naturals values left <*>
        convertTerm limits declaration types naturals values right
    | .boolAnd left right =>
      .boolAnd <$> convertTerm limits declaration types naturals values left <*>
        convertTerm limits declaration types naturals values right
    | .boolOr left right =>
      .boolOr <$> convertTerm limits declaration types naturals values left <*>
        convertTerm limits declaration types naturals values right
    | .boolXor left right =>
      .boolXor <$> convertTerm limits declaration types naturals values left <*>
        convertTerm limits declaration types naturals values right
    | .foreignConstant kind encoding => pure (.foreignConstant kind encoding)
    | .curve operation arguments =>
      .curve operation <$> arguments.mapM (convertTerm limits declaration types naturals values)
    | .bytes operation arguments =>
      .bytes operation <$> arguments.mapM (convertTerm limits declaration types naturals values)
    | .eq left right =>
      .eq <$> convertTerm limits declaration types naturals values left <*>
        convertTerm limits declaration types naturals values right
    | .cast target value => do
      let target ← normalizeType limits declaration.span types naturals target
      let .scalar target := target | liftM (fail declaration.span "generic scalar cast target is composite")
      .cast target <$> convertTerm limits declaration types naturals values value
    | .disclose span value => .disclose span <$> convertTerm limits declaration types naturals values value
    | .select condition yes no =>
      .select <$> convertTerm limits declaration types naturals values condition <*>
        convertTerm limits declaration types naturals values yes <*>
        convertTerm limits declaration types naturals values no
    | .ite condition yes no =>
      .ite <$> convertTerm limits declaration types naturals values condition <*>
        convertTerm limits declaration types naturals values yes <*>
        convertTerm limits declaration types naturals values no
    | .andThen left right =>
      .andThen <$> convertTerm limits declaration types naturals values left <*>
        convertTerm limits declaration types naturals values right
    | .orElse left right =>
      .orElse <$> convertTerm limits declaration types naturals values left <*>
        convertTerm limits declaration types naturals values right
    | .witness name type => do
      let type ← normalizeType limits declaration.span types naturals type
      let .scalar type := type | liftM (fail declaration.span "generic witness signature requires a scalar type")
      pure (.witness name type)
    | .witnessCall sourceSite name arguments => do
      let state ← get
      let some generatedName := state.activeGeneratedNames.head?
        | liftM (fail declaration.span "typed witness call has no active specialization instance")
      let site := generatedName ++ "." ++ sourceSite
      if site.utf8ByteSize > 128 then
        liftM (resource declaration.span "typed witness site identity")
      unless Helpers.validWitnessIdentifier site do
        liftM (fail declaration.span "invalid specialized typed witness site identity")
      let arguments ← arguments.mapM (convertTerm limits declaration types naturals values)
      pure (.witnessCall site name arguments)
    | .poseidon2 domain left right =>
      .poseidon2 domain <$> convertTerm limits declaration types naturals values left <*>
        convertTerm limits declaration types naturals values right
    | .call target arguments callValues => do
      let values ← callValues.mapM (convertTerm limits declaration types naturals values)
      let some targetDeclaration := findDeclaration (← get).source target
        | liftM (fail declaration.span s!"unknown generic helper identity {target.scope}:{target.ordinal}")
      let specialized ← specializeDeclaration limits declaration.span targetDeclaration arguments types naturals
      pure (.call specialized.name values)
    | .composite type leaves => do
      let type ← normalizeType limits declaration.span types naturals type
      let leaves ← leaves.mapM (convertTerm limits declaration types naturals values)
      pure (.composite type leaves)
    | .project value projection =>
      .project <$> convertTerm limits declaration types naturals values value <*> pure projection
    | .index value index =>
      .index <$> convertTerm limits declaration types naturals values value <*>
        convertTerm limits declaration types naturals values index
    | .effect kind label value =>
      .effect kind label <$> convertTerm limits declaration types naturals values value
    | .at span value => .at span <$> convertTerm limits declaration types naturals values value
end

private def initialOrdinal (program : Program) : Nat :=
  ((program.declarations.map (·.id.ordinal) ++ program.base.declarations.map (·.id.ordinal)).foldl max 0).succ

private def sourceNames (program : Program) : List String :=
  program.declarations.map (·.name) ++ program.base.scopes.flatMap (·.values)

structure SpecializedType where
  value : Types.CompositeType
  environment : Types.CompositeEnv
  deriving Repr

instance : Inhabited SpecializedType := ⟨{value := .unit, environment := {}}⟩

/-- Resolve one generic type template with concrete surrounding arguments.
The result retains checked composite declarations produced while expanding
generic structures, so callers can use the type in a consuming signature. -/
def specializeTypeWithEnvironment (limits : Limits) (source : Program)
    (types : List (String × Types.CompositeType)) (naturals : List (String × Nat))
    (value : GenericType) : Except Diagnostic SpecializedType := do
  let (declarationCosts, structureCosts) ← preflight limits source
  let initial : State := {
    source
    declarationCosts
    structureCosts
    usedNames := sourceNames source
    nextOrdinal := initialOrdinal source
    remainingSteps := limits.maxExpandedNodes}
  let (value, state) ← (normalizeType limits {} types naturals value).run initial
  let expandedEnvironment : Types.CompositeEnv := {
    structures := source.base.composites.structures ++ state.structures
    enumerations := source.base.composites.enumerations}
  let environment := Types.CompositeEnv.reachable expandedEnvironment value
  match Types.checkedLayout Types.defaultLimits environment value with
  | .ok _ => pure {value, environment}
  | .error diagnostic => fail diagnostic.span diagnostic.message

/- Specialize requested exports in one bounded session. The declaration and
type caches are shared across roots. Output names are sorted before expansion,
so the same request set produces the same generated declaration IDs regardless
of caller order. -/
def specializeRequestsWithLimits (limits : Limits) (source : Program)
    (requests : List ExportRequest) : Except Diagnostic BatchResult := do
  if requests.isEmpty then fail {} "specialization batch requires at least one export"
  let (declarationCosts, structureCosts) ← preflight limits source
  if requests.length > limits.maxSpecializations then
    resource {} "specialization batch export count"
  unless uniqueNames (requests.map (·.outputName)) do
    fail {} "duplicate output name in specialization batch"
  let mut remainingNodes := limits.maxSourceNodes
  let mut entries : List (ExportRequest × Export) := []
  for request in requests do
    textLimit request.span request.outputName
    if request.arguments.length > limits.maxTypeArguments then
      resource request.span "generic argument count"
    let used ← scanNodes limits request.span remainingNodes
      (request.arguments.map SourceNode.argument)
    remainingNodes := remainingNodes - used
    let some sourceEntry := source.exports.find? (·.name == request.sourceExport)
      | fail request.span s!"unknown generic helper entrypoint '{request.sourceExport}'"
    let some _ := findDeclaration source sourceEntry.target
      | fail sourceEntry.span "unknown generic declaration identity"
    let entry : Export := {
      sourceEntry with
      name := request.outputName
      arguments := request.arguments
      span := request.span}
    entries := entries ++ [(request, entry)]
  let orderedEntries := entries.mergeSort fun left right =>
    decide (left.1.outputName < right.1.outputName)
  let initial : State := {
    source
    declarationCosts
    structureCosts
    usedNames := sourceNames source
    nextOrdinal := initialOrdinal source
    remainingSteps := limits.maxExpandedNodes}
  let action : SpecializeM (List Helpers.Export) := do
    let mut generatedExports : List Helpers.Export := []
    for (_, entry) in orderedEntries do
      let some targetDeclaration := findDeclaration source entry.target
        | liftM (fail entry.span "unknown generic declaration identity")
      let (keyArguments, typeEnv, naturalEnv) ← bindArguments limits entry.span
        targetDeclaration.parameters entry.arguments [] []
      let targetInstance ← specializeInstance limits entry.span targetDeclaration
        keyArguments typeEnv naturalEnv
      let mut scalarInputs : List Noctium.Input := []
      let mut compositeInputs : List Helpers.AggregateInput := []
      for input in entry.inputs do
        let type ← normalizeType limits input.span typeEnv naturalEnv input.type
        match type with
        | .scalar scalarTy => do
          let concreteInput : Noctium.Input := {
            name := input.name
            ty := scalarTy
            visibility := input.visibility
            span := input.span}
          scalarInputs := scalarInputs ++ [concreteInput]
        | compositeTy => do
          let concreteInput : Helpers.AggregateInput := {
            name := input.name
            type := compositeTy
            visibility := input.visibility
            span := input.span}
          compositeInputs := compositeInputs ++ [concreteInput]
      generatedExports := generatedExports ++ [
        ⟨entry.name, targetInstance.target, scalarInputs, compositeInputs, entry.span⟩]
    pure generatedExports
  let (generatedExports, state) ← action.run initial
  let concreteComposites : Types.CompositeEnv :=
    ⟨source.base.composites.structures ++ state.structures, source.base.composites.enumerations⟩
  let concrete : Helpers.Program := {
    source.base with
    declarations := state.declarations
    exports := generatedExports
    composites := concreteComposites}
  let analysisLimits : Helpers.Limits := {maxExpandedNodes := limits.maxExpandedNodes}
  match Helpers.analyzeWithLimits analysisLimits concrete with
  | .error diagnostic => .error diagnostic
  | .ok _ => pure {
      program := concrete
      exportNames := orderedEntries.map (·.1.outputName)
      sourceExports := orderedEntries.map fun (request, _) =>
        (request.outputName, request.sourceExport)
      instances := state.instances}

/-- Select source exports by name while sharing one bounded specialization
session. Use `specializeRequestsWithLimits` to supply module identities and
normalized module arguments explicitly. -/
def specializeBatchWithLimits (limits : Limits) (source : Program)
    (exportNames : List String) : Except Diagnostic BatchResult := do
  if exportNames.isEmpty then fail {} "specialization batch requires at least one export"
  unless uniqueNames exportNames do fail {} "duplicate source export in specialization batch"
  let mut requests : List ExportRequest := []
  for exportName in exportNames do
    let some entry := source.exports.find? (·.name == exportName)
      | fail {} s!"unknown generic helper entrypoint '{exportName}'"
    requests := requests ++ [{
      sourceExport := exportName
      outputName := exportName
      arguments := entry.arguments
      span := entry.span}]
  specializeRequestsWithLimits limits source requests

/-- Specialize one concrete export into the ordinary monomorphic
`Helpers.Program`. The single-export API shares the batch implementation. -/
def specializeWithLimits (limits : Limits) (source : Program) (exportName : String) :
    Except Diagnostic Result := do
  let batch ← specializeBatchWithLimits limits source [exportName]
  pure {program := batch.program, exportName, instances := batch.instances}

def specialize (source : Program) (exportName : String) : Except Diagnostic Result :=
  specializeWithLimits {} source exportName

def specializeBatch (source : Program) (exportNames : List String) :
    Except Diagnostic BatchResult :=
  specializeBatchWithLimits {} source exportNames

/-- A versioned signature type stored by the standalone specialization sidecar.
Natural values and nominal identities use strings to avoid JSON number loss. -/
inductive SignatureType where
  | unit
  | native
  | bool
  | uint (maximum : String)
  | opaqueBytes
  | opaqueString
  | tuple (items : List SignatureType)
  | structure (id : String)
  | enumeration (id : String)
  | vector (length : String) (element : SignatureType)
  | bytes (length : String)
  | jubjubScalar
  | jubjubPoint
  | foreign (sourceName : String)
  deriving Repr, BEq, Inhabited, Lean.FromJson, Lean.ToJson

inductive SignatureArgument where
  | type (value : SignatureType)
  | natural (value : String)
  deriving Repr, BEq, Inhabited, Lean.FromJson, Lean.ToJson

structure SignatureValue where
  name : String
  type : SignatureType
  deriving Repr, BEq, Inhabited, Lean.FromJson, Lean.ToJson

structure SpecializedSignature where
  sourceScope : String
  sourceOrdinal : String
  generatedScope : String
  generatedOrdinal : String
  generatedName : String
  arguments : List SignatureArgument
  parameters : List SignatureValue
  result : SignatureType
  witnesses : List SignatureValue
  deriving Repr, BEq, Inhabited, Lean.FromJson, Lean.ToJson

structure SignatureArtifact where
  schemaVersion : Nat := 1
  sourceExport : String
  declarations : List SpecializedSignature
  deriving Repr, BEq, Inhabited, Lean.FromJson, Lean.ToJson

private def signatureType : Types.CompositeType → SignatureType
  | .unit => .unit
  | .scalar .native => .native
  | .scalar .bool => .bool
  | .scalar (.uint maximum) => .uint (toString maximum)
  | .scalar (.bytes length) => .bytes (toString length)
  | .scalar .opaqueBytes => .opaqueBytes
  | .scalar .opaqueString => .opaqueString
  | .scalar .jubjubScalar => .jubjubScalar
  | .scalar .jubjubPoint => .jubjubPoint
  | .scalar (.foreign kind) => .foreign kind.sourceName
  | .tuple items => .tuple (items.map signatureType)
  | .structure id => .structure id
  | .enumeration id => .enumeration id
  | .vector length element => .vector (toString length) (signatureType element)
  | .bytes length => .bytes (toString length)

private def signatureResult : Helpers.ResultType → SignatureType
  | .unit => .unit
  | .scalar .native => .native
  | .scalar .bool => .bool
  | .scalar (.uint maximum) => .uint (toString maximum)
  | .scalar (.bytes length) => .bytes (toString length)
  | .scalar .opaqueBytes => .opaqueBytes
  | .scalar .opaqueString => .opaqueString
  | .scalar .jubjubScalar => .jubjubScalar
  | .scalar .jubjubPoint => .jubjubPoint
  | .scalar (.foreign kind) => .foreign kind.sourceName
  | .composite value => signatureType value

private def signatureArgument : SpecializationArgument → SignatureArgument
  | .type value => .type (signatureType value)
  | .natural value => .natural (toString value)

private partial def collectWitnessTerms (providers : List Helpers.WitnessSignature)
    (term : Helpers.Term) (result : Array SignatureValue) : Array SignatureValue :=
  match term with
  | .witness name type => result.push {name, type := signatureType (.scalar type)}
  | .binary _ left right | .boolAnd left right | .boolOr left right
  | .boolXor left right | .eq left right | .poseidon2 _ left right
  | .andThen left right | .orElse left right | .index left right =>
    collectWitnessTerms providers right (collectWitnessTerms providers left result)
  | .cast _ value | .castNominalUInt _ value | .disclose _ value | .effect _ _ value
  | .at _ value | .project value _ | .bytesAt value _ => collectWitnessTerms providers value result
  | .select condition yes no | .ite condition yes no =>
    collectWitnessTerms providers no
      (collectWitnessTerms providers yes (collectWitnessTerms providers condition result))
  | .witnessCall _ name values =>
    let result := values.foldl (fun acc value => collectWitnessTerms providers value acc) result
    match providers.find? (·.name == name) with
    | some provider => result.push {name, type := signatureResult provider.result}
    | none => result
  | .call _ values | .composite _ values | .curve _ values | .bytes _ values =>
    values.foldl (fun acc value => collectWitnessTerms providers value acc) result
  | .unit | .native _ | .bool _ | .uint _ _ | .ref _ | .bytes32Literal _
  | .foreignConstant .. => result

private partial def collectWitnessStatements (providers : List Helpers.WitnessSignature) :
    List Helpers.Statement → Array SignatureValue → Array SignatureValue
  | [], result => result
  | statement :: rest, result =>
    let result := match statement with
      | .bind _ _ value | .evaluate value | .assert value | .stage _ _ _ value =>
        collectWitnessTerms providers value result
      | .return value => value.toList.foldl (fun acc item => collectWitnessTerms providers item acc) result
      | .branch condition yes no =>
        let result := collectWitnessTerms providers condition result
        let result := collectWitnessStatements providers yes result
        collectWitnessStatements providers no result
      | .forRange _ _ _ body => collectWitnessStatements providers body result
      | .readCell .. => result
      | .writeCell _ _ value => collectWitnessTerms providers value result
      | .readMap _ _ _ _ key | .readMember _ _ _ _ key =>
        collectWitnessTerms providers key result
      | .writeMap _ _ _ key value =>
        collectWitnessTerms providers value (collectWitnessTerms providers key result)
      | .emitEvent _ payload => collectWitnessTerms providers payload result
      | .claimShielded _ digest => collectWitnessTerms providers digest result
    collectWitnessStatements providers rest result

private def witnessStatements (providers : List Helpers.WitnessSignature)
    (body : List Helpers.Statement) : List SignatureValue :=
  (collectWitnessStatements providers body #[]).toList.eraseDups

private def sourceIdParts (id : DeclarationId) : String × String :=
  (toString id.scope, toString id.ordinal)

def Result.signatureArtifact (result : Result) : SignatureArtifact :=
  let declarations := result.instances.reverse.filterMap fun item => do
    let declaration ← result.program.declarations.find? (·.id == item.target)
    let params := declaration.parameters.map fun parameter => {
      name := parameter.name
      type := signatureResult (declaration.parameterType parameter) : SignatureValue}
    let (sourceScope, sourceOrdinal) := sourceIdParts item.key.declaration
    let (generatedScope, generatedOrdinal) := sourceIdParts item.target
    some {
      sourceScope, sourceOrdinal, generatedScope, generatedOrdinal
      generatedName := item.name
      arguments := item.key.arguments.map signatureArgument
      parameters := params
      result := signatureResult declaration.result
      witnesses := witnessStatements result.program.witnesses declaration.body}
  {sourceExport := result.exportName, declarations}

/-- Sidecar for one output in a shared batch. The declaration list records the
full monomorphic program compiled by the batch, so shared helper instances
appear in each related output artifact without being specialized twice. -/
def BatchResult.signatureArtifactFor (result : BatchResult) (outputName : String) :
    Option SignatureArtifact := do
  let sourceExport ← (result.sourceExports.find? (·.1 == outputName)).map (·.2)
  let single : Result := {
    program := result.program
    exportName := sourceExport
    instances := result.instances}
  pure single.signatureArtifact

private def canonicalDecimal (text : String) : Except String Nat := do
  if text.length > (toString ScalarPolicy.maxUint).length then
    throw "decimal string exceeds the canonical integer limit"
  let some value := text.toNat?
    | throw "expected a canonical decimal string"
  unless toString value == text do throw "decimal string has a leading zero or invalid form"
  pure value

private partial def validateSignatureType (fuel : Nat) (value : SignatureType) : Except String Unit := do
  match fuel with
  | 0 => throw "signature type nesting exceeds the parser limit"
  | fuel + 1 => match value with
    | .unit | .native | .bool => pure ()
    | .jubjubScalar | .jubjubPoint => pure ()
    | .opaqueBytes =>
      throw "OpaqueBytes helper signatures are not supported by specialization"
    | .opaqueString =>
      throw "OpaqueString helper signatures are not supported by specialization"
    | .foreign sourceName => do
      unless Foreign.kinds.any (fun kind => kind.sourceName == sourceName) do
        throw "unsupported foreign helper signature type"
    | .uint maximum => do
      let maximum ← canonicalDecimal maximum
      unless maximum ≤ ScalarPolicy.maxUint do throw "unsigned signature exceeds target maximum"
    | .tuple items => do
      if items.length > Types.defaultLimits.maxLayoutNodes then throw "signature tuple exceeds the parser limit"
      for item in items do validateSignatureType fuel item
    | .structure id | .enumeration id =>
      unless Types.validDeclId id do throw "invalid nominal signature identity"
    | .vector length element => do
      let length ← canonicalDecimal length
      unless length ≤ Types.defaultLimits.maxVectorLength do throw "signature vector exceeds target maximum"
      validateSignatureType fuel element
    | .bytes length => do
      let length ← canonicalDecimal length
      unless length ≤ Types.defaultLimits.maxVectorLength do throw "signature byte array exceeds target maximum"

private def validateSignatureArgument (argument : SignatureArgument) : Except String Unit := do
  match argument with
  | .type value => validateSignatureType 128 value
  | .natural value =>
    let value ← canonicalDecimal value
    unless value ≤ ScalarPolicy.maxUint do throw "natural signature argument exceeds target maximum"

private def validateSignatureValue (value : SignatureValue) : Except String Unit := do
  if value.name.utf8ByteSize > 1024 then throw "signature value name exceeds parser limit"
  validateSignatureType 128 value.type

private def validateArtifact (artifact : SignatureArtifact) : Except String Unit := do
  unless artifact.schemaVersion == 1 do throw "unsupported specialization signature schema version"
  if artifact.sourceExport.utf8ByteSize > 1024 then throw "source export name exceeds parser limit"
  if artifact.declarations.length > 256 then throw "specialized declaration count exceeds parser limit"
  for declaration in artifact.declarations do
    if declaration.generatedName.utf8ByteSize > 1024 then throw "generated declaration name exceeds parser limit"
    for idPart in [declaration.sourceScope, declaration.sourceOrdinal,
        declaration.generatedScope, declaration.generatedOrdinal] do
      let idValue ← canonicalDecimal idPart
      unless idValue ≤ 18446744073709551615 do throw "declaration identity exceeds target maximum"
    if declaration.arguments.length > 64 || declaration.parameters.length > 64 ||
        declaration.witnesses.length > 16384 then
      throw "specialized signature list exceeds parser limit"
    for argument in declaration.arguments do validateSignatureArgument argument
    for parameter in declaration.parameters do validateSignatureValue parameter
    validateSignatureType 128 declaration.result
    for witness in declaration.witnesses do validateSignatureValue witness

/-- Parse and validate the additive standalone `.specialization.json` artifact. -/
def parseSignatureArtifact (json : Lean.Json) : Except String SignatureArtifact := do
  let artifact ← Lean.fromJson? json
  validateArtifact artifact
  pure artifact

private def validateJsonNesting (source : String) : Except String Unit := do
  let (depth, inString, escaped, malformed) := source.foldl (fun state character =>
    let (depth, inString, escaped, malformed) := state
    if malformed then state
    else if inString then
      if escaped then (depth, true, false, false)
      else if character == '\\' then (depth, true, true, false)
      else if character == '"' then (depth, false, false, false)
      else state
    else if character == '"' then (depth, true, false, false)
    else if character == '{' || character == '[' then
      if depth >= 512 then (depth, false, false, true)
      else (depth + 1, false, false, false)
    else if character == '}' || character == ']' then
      if depth == 0 then (depth, false, false, true)
      else (depth - 1, false, false, false)
    else state) (0, false, false, false)
  if malformed || inString || escaped || depth != 0 then
    throw "malformed or deeply nested specialization signature JSON"

def parseSignatureArtifactText (source : String) : Except String SignatureArtifact := do
  if source.utf8ByteSize > 134217728 then throw "specialization signature artifact exceeds parser limit"
  validateJsonNesting source
  parseSignatureArtifact (← Lean.Json.parse source)

end Noctium.Helpers.Specialization



