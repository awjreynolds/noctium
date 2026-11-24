import Noctium.Helpers
import Noctium.ComponentDisclosure
import Noctium.Types.ValueSchema
import Lean

namespace Noctium.Control
open Helpers Lean

private def fail (span : SourceSpan) (message : String) : Except Diagnostic α :=
  .error {span, message}

private def liftError (span : SourceSpan) : Except String α → Except Diagnostic α
  | .ok value => .ok value
  | .error message => fail span message

private def merge (a b : Disclosure.Origins) : Disclosure.Origins := (a ++ b).eraseDups

private def join (span : SourceSpan) (a b : ResultType) : Except Diagnostic ResultType :=
  match Helpers.commonType a b with
  | some common => pure common
  | none => fail span "conditional branches require a common type"

private def scalar (span : SourceSpan) : ResultType → Except Diagnostic Ty
  | .scalar ty => pure ty
  | .unit => fail span "unit is not a scalar control value"
  | .composite _ => fail span "aggregate control values are unavailable"

private def fromKind : ScalarPolicy.Kind → Ty
  | .native => .native | .bool => .bool | .uint m => .uint m | .bytes length => .bytes length
  | .opaqueBytes => .opaqueBytes
  | .jubjubScalar => .jubjubScalar | .jubjubPoint => .jubjubPoint
  | .foreign kind => .foreign kind

private def declaration (program : Program) (id : DeclarationId) (span : SourceSpan) : Except Diagnostic Helpers.Declaration :=
  match program.declarations.find? (·.id == id) with
  | some value => pure value
  | none => fail span "unknown control declaration"

private def portableResultLayout : Types.Layout → Bool
  | .structure _ fields => fields.all fun (_, item) =>
      match item with
      | .scalar .nativeField | .scalar .booleanField | .scalar (.boundedUnsignedField _) => true
      | _ => false
  | _ => false

structure Abstract where
  ty : ResultType
  origins : Disclosure.Origins := []
  control : Disclosure.Origins := []
  literal : Option ScalarPolicy.Value := none
  deriving Inhabited

private def constantBool (value : Abstract) : Option Bool := do
  let literal ← value.literal
  if literal.kind == .bool then some (literal.number != 0) else none

private def abstractCast (ty : ResultType) (value : Abstract) : Abstract :=
  {value with ty, literal := match ty, value.literal with
    | .scalar ty, some literal =>
      if ty.isBytes || ty.isOpaqueBytes || ty.isOpaqueString || ty.isJubjub || ty.isForeign then none
      else (ScalarPolicy.cast literal ty.scalarKind).toOption
    | _, _ => none}

private abbrev Environment := List (String × Abstract)
private abbrev CheckM := StateT Nat (Except Diagnostic)

private def spend (span : SourceSpan) : CheckM Unit := do
  let remaining ← get
  if remaining == 0 then liftM (fail span "control resource limit exceeded")
  set (remaining - 1)

private def liftD (value : Except Diagnostic α) : CheckM α := liftM value

private def combined (ty : ResultType) (values : List Abstract) : Abstract :=
  {ty, origins := (values.flatMap fun value => value.origins ++ value.control).eraseDups}

private structure Block where
  returns : List Abstract := []
  continues : Bool := true
  control : Disclosure.Origins := []
  deriving Inhabited

mutual
  private partial def expression (checked : Helpers.Prepared) (scope : Nat) (env : Environment)
      (span : SourceSpan) (term : Helpers.Term) : CheckM Abstract := do
    spend span
    match term with
    | .unit => pure {ty := .unit}
    | .native n => pure {ty := .scalar .native, literal := some ⟨.native, n⟩}
    | .bool b => pure {ty := .scalar .bool, literal := some ⟨.bool, if b then 1 else 0⟩}
    | .uint m n => pure {ty := .scalar (.uint m), literal := some ⟨.uint m, n⟩}
    | .foreignConstant kind _ => pure {ty := .scalar (.foreign kind)}
    | .ref name =>
      let some value := env.lookup name | liftD (fail span "unknown control origin reference")
      pure value
    | .binary op a b =>
      let a ← expression checked scope env span a
      let b ← expression checked scope env span b
      let leftType ← liftD (scalar span a.ty)
      let rightType ← liftD (scalar span b.ty)
      let result ← liftD (liftError span (ScalarPolicy.infer op leftType.scalarKind rightType.scalarKind))
      let literal := do ScalarPolicy.evaluate op (← a.literal) (← b.literal) |>.toOption
      pure {combined (.scalar (fromKind result)) [a, b] with literal}
    | .boolAnd left right | .boolOr left right | .boolXor left right => do
      let left ← expression checked scope env span left
      let right ← expression checked scope env span right
      let literal := do
        let left ← constantBool left
        let right ← constantBool right
        let value := match term with
          | .boolAnd .. => left && right
          | .boolOr .. => left || right
          | .boolXor .. => left != right
          | _ => false
        pure (⟨.bool, if value then 1 else 0⟩ : ScalarPolicy.Value)
      pure {combined (.scalar .bool) [left, right] with literal}
    | .eq a b =>
      let a ← expression checked scope env span a
      let b ← expression checked scope env span b
      let ty ← liftD (join span a.ty b.ty)
      let a := abstractCast ty a
      let b := abstractCast ty b
      let literal := do
        let a ← a.literal
        let b ← b.literal
        pure (⟨.bool, if a == b then 1 else 0⟩ : ScalarPolicy.Value)
      pure {combined (.scalar .bool) [a, b] with literal}
    | .cast ty value => abstractCast (.scalar ty) <$> expression checked scope env span value
    | .castNominalUInt target value =>
      abstractCast (.scalar (.uint target.maximum)) <$> expression checked scope env span value
    | .disclose _ value =>
      let value ← expression checked scope env span value
      pure {value with origins := [], control := []}
    | .select condition yes no =>
      let condition ← expression checked scope env span condition
      let yes ← expression checked scope env span yes
      let no ← expression checked scope env span no
      let ty ← liftD (join span yes.ty no.ty)
      pure {combined ty [condition, yes, no] with literal := do
        let flag ← constantBool condition
        (abstractCast ty (if flag then yes else no)).literal}
    | .ite condition yes no =>
      let condition ← expression checked scope env span condition
      match constantBool condition with
      | some flag =>
        let value ← expression checked scope env span (if flag then yes else no)
        let info ← liftD (checked.infer scope (env.map fun (name, value) => (name, value.ty)) span term)
        pure {abstractCast info.ty value with origins := merge condition.origins value.origins}
      | none =>
        let yes ← expression checked scope env span yes
        let no ← expression checked scope env span no
        pure (combined (← liftD (join span yes.ty no.ty)) [condition, yes, no])
    | .andThen left right | .orElse left right =>
      let isAnd := match term with | .andThen .. => true | _ => false
      let left ← expression checked scope env span left
      match constantBool left with
      | some value =>
        if value == !isAnd then pure left
        else
          let right ← expression checked scope env span right
          pure {combined (.scalar .bool) [left, right] with literal := right.literal}
      | none => pure (combined (.scalar .bool) [left, ← expression checked scope env span right])
    | .poseidon2 _ a b =>
      pure (combined (.scalar .native) [← expression checked scope env span a, ← expression checked scope env span b])
    | .curve _ arguments => do
      let values ← arguments.mapM (expression checked scope env span)
      let info ← liftD (checked.infer scope (env.map fun (name, value) => (name, value.ty)) span term)
      pure (combined info.ty values)
    | .bytes32Literal _ => pure {ty := .scalar (.bytes 32)}
    | .bytesAt value _ => do
      let value ← expression checked scope env span value
      let info ← liftD (checked.infer scope (env.map fun (name, value) => (name, value.ty)) span term)
      pure (combined info.ty [value])
    | .bytes _ arguments => do
      let values ← arguments.mapM (expression checked scope env span)
      let info ← liftD (checked.infer scope (env.map fun (name, value) => (name, value.ty)) span term)
      pure (combined info.ty values)
    | .witness name ty => pure {ty := .scalar ty, origins := [{name, kind := .provider, span}]}
    | .witnessCall _ name arguments => do
      let values ← arguments.mapM (expression checked scope env span)
      let signature ← liftD (Helpers.witnessSignature checked.program name span)
      let origins := merge [{name, kind := .provider, span}] (values.flatMap (·.origins))
      pure {combined signature.result values with origins}
    | .call name arguments =>
      let arguments ← arguments.mapM (expression checked scope env span)
      let target ← liftD (checked.resolve scope name (arguments.map (·.ty)) span)
      let result ← call checked target arguments
      pure {result with control := []}
    | .effect kind name result =>
      let value ← expression checked scope env span result
      let origins := if kind == .witness || kind == .privateState then
        [{name, kind := if kind == .witness then .provider else .privateState, span}] else []
      pure {value with origins := merge value.origins origins}
    | .composite type leaves => do
      let values ← leaves.mapM (expression checked scope env span)
      let info ← liftD (checked.infer scope (env.map fun (name, value) => (name, value.ty)) span term)
      unless info.ty == .composite type do liftD (fail span "aggregate control value type mismatch")
      pure (combined info.ty values)
    | .project .. | .index .. => liftD (fail span "aggregate control projections are unavailable")
    | .at span value => expression checked scope env span value

  private partial def call (checked : Helpers.Prepared) (target : Helpers.Declaration) (arguments : List Abstract) : CheckM Abstract := do
    spend target.span
    let env := (target.parameters.zip arguments).map fun (parameter, argument) =>
      (parameter.name, abstractCast (target.parameterType parameter) argument)
    let result ← body checked target env [] target.body
    let values := result.returns.map (abstractCast target.result)
    let candidate := values.head?.bind (·.literal)
    let literal := if values.all (fun value => value.literal == candidate) then candidate else none
    pure {ty := target.result, origins := (values.flatMap fun value => value.origins ++ value.control).eraseDups, literal}

  private partial def body (checked : Helpers.Prepared) (target : Helpers.Declaration) (env : Environment)
      (control : Disclosure.Origins) (statements : List Statement) : CheckM Block := do
    spend target.span
    match statements with
    | [] => pure {control}
    | .return value :: _ =>
      let value ← match value with
        | some value => expression checked target.id.scope env target.span value
        | none => pure {ty := .unit}
      pure {returns := [{value with control := merge value.control control}], continues := false, control}
    | .bind name ty value :: rest =>
      let value ← expression checked target.id.scope env target.span value
      body checked target ((name, abstractCast ty value) :: env) control rest
    | .evaluate value :: rest =>
      discard (expression checked target.id.scope env target.span value)
      body checked target env control rest
    | .assert value :: rest =>
      discard (expression checked target.id.scope env target.span value)
      body checked target env control rest
    | .stage _ _ _ value :: rest =>
      discard (expression checked target.id.scope env target.span value)
      body checked target env control rest
    | .readCell .. :: _ =>
      liftD (fail target.span "portable control capability unavailable: ledger reads")
    | .readMap .. :: _ | .readMember .. :: _ =>
      liftD (fail target.span "portable control capability unavailable: ledger reads")
    | .writeCell .. :: _ =>
      liftD (fail target.span "portable control capability unavailable: ledger writes")
    | .writeMap .. :: _ =>
      liftD (fail target.span "portable control capability unavailable: ledger writes")
    | .emitEvent .. :: _ =>
      liftD (fail target.span "portable control capability unavailable: ledger events")
    | .claimShielded .. :: _ =>
      liftD (fail target.span "portable control capability unavailable: shielded claims")
    | .forRange .. :: _ =>
      liftD (fail target.span "unexpanded finite loop reached portable control analysis")
    | .branch condition yes no :: rest =>
      let condition ← expression checked target.id.scope env target.span condition
      let guarded := merge control condition.origins
      match constantBool condition with
      | some flag =>
        let selected ← body checked target env guarded (if flag then yes else no)
        if !selected.continues then pure selected
        else
          let next ← body checked target env selected.control rest
          pure {next with returns := selected.returns ++ next.returns}
      | none =>
        let yes ← body checked target env guarded yes
        let no ← body checked target env guarded no
        let returns := yes.returns ++ no.returns
        if !yes.continues && !no.continues then pure {returns, continues := false, control := guarded}
        else
          let nextControl := if yes.continues && no.continues && returns.isEmpty then control
            else merge guarded (merge yes.control no.control)
          let next ← body checked target env nextControl rest
          pure {next with returns := returns ++ next.returns}
end

/-- Only successful exported scalar payloads are public sinks. Host scheduling
is visible to the controller. Callback arguments/traces/journals use private channels. -/
private def checkPreparedDisclosure (limits : Helpers.Limits) (checked : Helpers.Prepared) (entryName : String) : Except Diagnostic Unit := do
  let program := checked.program
  let some entry := program.exports.find? (·.name == entryName) | fail {} "unknown control entrypoint"
  if entry.compositeInputs.any (fun input => input.type != .unit) ||
      program.declarations.any fun declaration =>
        declaration.compositeParameters.any (fun (_, type) => type != .unit) then
    fail entry.span "aggregate inputs are not supported by the portable control plan"
  for declaration in program.declarations do
    if let .composite type := declaration.result then
      let compiled ← match Types.compileType program.composites type with
        | .ok value => pure value
        | .error diagnostic => fail declaration.span diagnostic.message
      unless portableResultLayout compiled.checked.value do
        fail declaration.span "portable control aggregate results require supported scalar-field layouts"
  let target ← declaration program entry.target entry.span
  let mut scalarInputs := entry.inputs
  let mut aggregateInputs := entry.compositeInputs
  let mut arguments : List Abstract := []
  for parameter in target.parameters do
    match target.parameterType parameter with
    | .scalar _ => do
      let some input := scalarInputs.head? | fail entry.span "control input signature mismatch"
      scalarInputs := scalarInputs.drop 1
      arguments := arguments ++ [({ty := .scalar input.ty, origins := if input.visibility == .private then
        [{name := input.name, kind := .parameter, span := input.span}] else []} : Abstract)]
    | .unit => do
      let some input := aggregateInputs.head? | fail entry.span "control input signature mismatch"
      aggregateInputs := aggregateInputs.drop 1
      unless input.type == .unit do fail input.span "control Unit input type mismatch"
      arguments := arguments ++ [({ty := .unit} : Abstract)]
    | .composite _ => fail entry.span "aggregate inputs are not supported by the portable control plan"
  unless scalarInputs.isEmpty && aggregateInputs.isEmpty do
    fail entry.span "control input signature mismatch"
  let env := (target.parameters.zip arguments).map fun (parameter, argument) =>
    (parameter.name, abstractCast (target.parameterType parameter) argument)
  let (result, _) ← (body checked target env [] target.body).run limits.maxExecutionSteps
  for value in result.returns do
    if value.ty != .unit then Disclosure.checkSink {description := "public control-plan return", span := entry.span} value.origins value.control

def checkDisclosureWithLimits (limits : Helpers.Limits) (program : Program) (entryName : String) : Except Diagnostic Unit := do
  let program ← Helpers.prepareProgramWithLimits limits program
  let checked ← Helpers.prepareWithLimits limits program
  checkPreparedDisclosure limits checked entryName

def checkDisclosure (program : Program) (entryName : String) : Except Diagnostic Unit :=
  checkDisclosureWithLimits {} program entryName

private def typeName : ResultType → String
  | .unit => "Unit"
  | .scalar .native => "Native"
  | .scalar .bool => "Bool"
  | .scalar (.uint maximum) => s!"UIntRange<{maximum + 1}>"
  | .scalar (.bytes length) => s!"Bytes<{length}>"
  | .scalar .opaqueBytes => "OpaqueBytes"
  | .scalar .opaqueString => "OpaqueString"
  | .scalar .jubjubScalar => "JubjubScalar"
  | .scalar .jubjubPoint => "JubjubPoint"
  | .scalar (.foreign kind) => kind.sourceName
  | .composite _ => "Aggregate"

private def idName (id : DeclarationId) : String := s!"s{id.scope}d{id.ordinal}"
private def spanJson (span : SourceSpan) : Json := Json.mkObj [
  ("file", toJson span.file), ("line", toJson span.line), ("column", toJson span.column)]

private def portableName (span : SourceSpan) (name : String) : Except Diagnostic Unit := do
  unless !name.isEmpty && name.utf8ByteSize ≤ 1024 && name.toList.all (fun c =>
    let n := c.toNat
    !(n < 32 || (127 ≤ n && n ≤ 159))) do fail span "invalid portable control name"

private def hostName (name : String) : Bool :=
  !name.isEmpty && name.utf8ByteSize ≤ 128 && name.toList.all (fun c =>
    ('a' ≤ c && c ≤ 'z') || ('A' ≤ c && c ≤ 'Z') || ('0' ≤ c && c ≤ '9') || "_-.:".contains c)

private def hostKey (name : String) : Bool :=
  !name.isEmpty && name.utf8ByteSize ≤ 128 && !name.startsWith "/" && !name.endsWith "/" &&
    name.toList.all (fun c => c == '/' || hostName (String.singleton c)) &&
    (name.splitOn "/").all (fun part => !part.isEmpty && part != "." && part != "..")

private def node (span : SourceSpan) (tag : String) (fields : List (String × Json) := []) : Json :=
  Json.mkObj (("tag", toJson tag) :: ("span", spanJson span) :: fields)

private structure EmitState where
  remaining : Nat
  witnesses : List (String × Ty) := []
  bytes : Nat := 1048576
  typed : Bool := false
  types : List (String × Types.CompiledType) := []
  assertionDiagnostics : List (SourceSpan × String) := []
  deriving Inhabited
private abbrev EmitM := StateT EmitState (Except Diagnostic)

private def chargeBytes (amount : Nat) : EmitM Unit := do
  let state ← get
  if amount > state.bytes then liftM (fail {} "control plan preflight byte limit exceeded")
  set {state with bytes := state.bytes - amount}

private def emitSpend (span : SourceSpan) : EmitM Unit := do
  let state ← get
  if state.remaining == 0 then liftM (fail span "control emission resource limit exceeded")
  set {state with remaining := state.remaining - 1}
  chargeBytes (512 + 6 * span.file.utf8ByteSize)

private def emitLift (value : Except Diagnostic α) : EmitM α := liftM value

private def emitType (checked : Helpers.Prepared) (span : SourceSpan) (type : ResultType) : EmitM String := do
  match type with
  | .unit | .scalar _ => pure (typeName type)
  | .composite type =>
    let compiled ← match Types.compileType checked.program.composites type with
      | .ok value => pure value
      | .error diagnostic => emitLift (fail span diagnostic.message)
    if let some (id, _) := (← get).types.find? (fun item => item.2.fingerprint == compiled.fingerprint) then
      pure ("Aggregate:" ++ id)
    else
      let state ← get
      if state.types.length >= 128 then emitLift (fail span "typed control schema limit exceeded")
      let schema ← emitLift (liftError span (Types.schemaJson compiled))
      chargeBytes (128 + schema.compress.utf8ByteSize)
      let id := s!"t{state.types.length}"
      modify fun state => {state with types := state.types ++ [(id, compiled)]}
      pure ("Aggregate:" ++ id)

private def projectionJson : Types.Projection → Json
  | .tupleIndex index => Json.mkObj [("kind", toJson ("tupleIndex" : String)), ("index", toJson (toString index))]
  | .field name => Json.mkObj [("kind", toJson ("field" : String)), ("name", toJson name)]
  | .vectorIndex index => Json.mkObj [("kind", toJson ("vectorIndex" : String)), ("index", toJson (toString index))]
  | .byteIndex index => Json.mkObj [("kind", toJson ("byteIndex" : String)), ("index", toJson (toString index))]
  | .enumTag => Json.mkObj [("kind", toJson ("enumTag" : String))]
  | .enumField variant name => Json.mkObj [("kind", toJson ("enumField" : String)),
      ("variant", toJson variant), ("name", toJson name)]

mutual
  private partial def emitCoercedExpression (checked : Helpers.Prepared) (scope : Nat)
      (env : Helpers.Environment) (span : SourceSpan) (target : ResultType)
      (value : Helpers.Term) : EmitM Json := do
    let info ← emitLift (checked.infer scope env span value)
    unless Helpers.subtype info.ty target do
      emitLift (fail span "control coercion does not match its checked target")
    let encoded ← emitExpression checked scope env span value
    match info.ty, target with
    | .scalar source, .scalar target =>
      if source == target then pure encoded
      else
        pure (node span "cast" [("type", toJson (typeName (.scalar target))),
          ("value", encoded)])
    | .composite source, .composite target =>
      if source == target then pure encoded
      else
        let targetName ← emitType checked span (.composite target)
        pure (node span "cast" [("type", toJson targetName), ("value", encoded)])
    | _, _ => pure encoded

  private partial def emitExpression (checked : Helpers.Prepared) (scope : Nat) (env : Helpers.Environment)
      (span : SourceSpan) (value : Helpers.Term) : EmitM Json := do
    emitSpend span
    match value with
    | .unit => pure (node span "unit")
    | .native n => pure (node span "constant" [("value", toJson (toString n))])
    | .bool value => pure (node span "bool" [("value", toJson value)])
    | .uint maximum value => pure (node span "uint" [("maximum", toJson (toString maximum)), ("value", toJson (toString value))])
    | .ref name => do
      emitLift (portableName span name)
      chargeBytes (6 * name.utf8ByteSize)
      pure (node span "reference" [("name", toJson name)])
    | .binary op a b =>
      let op := match op with | .add => "add" | .sub => "sub" | .mul => "mul"
      pure (node span "binary" [("operation", toJson op), ("left", ← emitExpression checked scope env span a), ("right", ← emitExpression checked scope env span b)])
    | .boolAnd left right | .boolOr left right | .boolXor left right => do
      let tag := match value with
        | .boolAnd .. => "boolAnd"
        | .boolOr .. => "boolOr"
        | .boolXor .. => "boolXor"
        | _ => "boolAnd"
      pure (node span tag [
        ("left", ← emitExpression checked scope env span left),
        ("right", ← emitExpression checked scope env span right)])
    | .eq a b => do
      let leftInfo ← emitLift (checked.infer scope env span a)
      let rightInfo ← emitLift (checked.infer scope env span b)
      let (left, right) ← match leftInfo.ty, rightInfo.ty with
        | .composite leftType, .composite rightType => do
          let common ← emitLift (Helpers.checkedAggregateEquality checked.program span leftType rightType)
          let target : ResultType := .composite common.type
          pure (← emitCoercedExpression checked scope env span target a,
            ← emitCoercedExpression checked scope env span target b)
        | _, _ => pure (← emitExpression checked scope env span a,
            ← emitExpression checked scope env span b)
      pure (node span "eq" [("left", left), ("right", right)])
    | .andThen a b | .orElse a b =>
      let tag := match value with | .andThen .. => "and" | _ => "or"
      pure (node span tag [("left", ← emitExpression checked scope env span a), ("right", ← emitExpression checked scope env span b)])
    | .select c a b | .ite c a b => do
      let tag := match value with | .select .. => "select" | _ => "if"
      let (yes, no) ← if let .ite .. := value then do
        let info ← emitLift (checked.infer scope env span value)
        pure (← emitCoercedExpression checked scope env span info.ty a,
          ← emitCoercedExpression checked scope env span info.ty b)
      else pure (← emitExpression checked scope env span a, ← emitExpression checked scope env span b)
      pure (node span tag [("condition", ← emitExpression checked scope env span c),
        ("yes", yes), ("no", no)])
    | .cast ty value => pure (node span "cast" [("type", toJson (typeName (.scalar ty))), ("value", ← emitExpression checked scope env span value)])
    | .castNominalUInt target value => pure (node span "cast" [
        ("type", toJson (typeName (.scalar (.uint target.maximum)))),
        ("value", ← emitExpression checked scope env span value)])
    | .disclose _ value => pure (node span "disclose" [("value", ← emitExpression checked scope env span value)])
    | .poseidon2 domain a b => pure (node span "poseidon2" [("domain", toJson (toString domain)),
        ("left", ← emitExpression checked scope env span a), ("right", ← emitExpression checked scope env span b)])
    | .curve (.foreignEncodedField _ index) [value] => do
      unless (← get).typed do emitLift (fail span "foreign values require control schema version 2")
      pure (node span "foreignEncodedField" [
        ("value", ← emitExpression checked scope env span value),
        ("index", toJson index)])
    | .curve operation arguments => do
      unless (← get).typed do emitLift (fail span "curve operations require control schema version 2")
      pure (node span "curve" [("operation", toJson operation.operationName),
        ("arguments", toJson (← arguments.mapM (emitExpression checked scope env span)))])
    | .bytes32Literal values => pure (node span "bytes32" [("values", toJson values)])
    | .bytes (.bytesLiteral length values) [] => do
      unless (← get).typed do emitLift (fail span "byte literals require control schema version 2")
      pure (node span "bytesLiteral" [("length", toJson length), ("values", toJson values)])
    | .foreignConstant kind encoding => do
      unless (← get).typed do emitLift (fail span "foreign values require control schema version 2")
      pure (node span "foreignConstant" [
        ("type", toJson kind.sourceName),
        ("encoding", toJson (encoding.map toString))])
    | .bytesAt value index => do
      unless (← get).typed do emitLift (fail span "Bytes32 operations require control schema version 2")
      pure (node span "byteAt" [("value", ← emitExpression checked scope env span value),
        ("index", toJson index)])
    | .bytes (.fabDigest algorithm type _) arguments => do
      unless (← get).typed do emitLift (fail span "FAB digests require control schema version 2")
      pure (node span "fabDigest" [
        ("operation", toJson algorithm.name),
        ("type", toJson (← emitType checked span (.composite type))),
        ("arguments", toJson (← arguments.mapM (emitExpression checked scope env span)))])
    | .bytes operation arguments => do
      unless (← get).typed do emitLift (fail span "Bytes32 operations require control schema version 2")
      pure (node span "bytes" [("operation", toJson operation.operationName),
        ("arguments", toJson (← arguments.mapM (emitExpression checked scope env span)))])
    | .call name arguments =>
      let types ← emitLift (arguments.mapM fun argument => do pure (← checked.infer scope env span argument).ty)
      let target ← emitLift (checked.resolve scope name types span)
      let encodedArguments ← (arguments.zip target.parameters).mapM fun (argument, parameter) =>
        emitCoercedExpression checked scope env span (target.parameterType parameter) argument
      pure (node span "call" [("function", toJson (idName target.id)),
        ("arguments", toJson encodedArguments)])
    | .witness name ty =>
      if (← get).typed then emitLift (fail span "typed control plans require declared witnessCall providers")
      unless hostName name do emitLift (fail span "invalid control witness provider name")
      chargeBytes (6 * name.utf8ByteSize)
      let state ← get
      if let some prior := state.witnesses.lookup name then
        unless prior == ty do emitLift (fail span "witness name has inconsistent result types")
      else
        if state.witnesses.length >= 32 then emitLift (fail span "control witness limit exceeded")
        chargeBytes (512 + 6 * name.utf8ByteSize)
        modify fun state => {state with witnesses := state.witnesses ++ [(name, ty)]}
      pure (node span "witness" [("name", toJson name), ("type", toJson (typeName (.scalar ty)))])
    | .witnessCall site name arguments =>
      unless (← get).typed do emitLift (fail span "typed witness calls require control schema version 2")
      chargeBytes (6 * (site.utf8ByteSize + name.utf8ByteSize))
      let signature ← emitLift (Helpers.witnessSignature checked.program name span)
      let encodedArguments ← (arguments.zip signature.parameters).mapM fun (argument, parameter) =>
        emitCoercedExpression checked scope env span parameter.type argument
      pure (node span "witnessCall" [("site", toJson site), ("name", toJson name),
        ("arguments", toJson encodedArguments)])
    | .effect .. => emitLift (fail span "portable control capability unavailable: labelled effect fixture")
    | .composite type leaves =>
      unless (← get).typed do emitLift (fail span "aggregate control values require schema version 2")
      let compiled ← match Types.compileType checked.program.composites type with
        | .ok compiled => pure compiled
        | .error diagnostic => emitLift (fail span diagnostic.message)
      let expected := Helpers.sourceLeafTypes compiled.checked.value
      unless leaves.length == expected.length do
        emitLift (fail span "aggregate control leaf count mismatch")
      let encodedLeaves ← (leaves.zip expected).mapM fun (leaf, leafType) =>
        emitCoercedExpression checked scope env span (.scalar leafType) leaf
      pure (node span "composite" [("type", toJson (← emitType checked span (.composite type))),
        ("leaves", toJson encodedLeaves)])
    | .project value projection =>
      unless (← get).typed do emitLift (fail span "aggregate control values require schema version 2")
      let info ← emitLift (checked.infer scope env span (.project value projection))
      pure (node span "project" [("value", ← emitExpression checked scope env span value),
        ("projection", projectionJson projection), ("type", toJson (← emitType checked span info.ty))])
    | .index value index =>
      unless (← get).typed do emitLift (fail span "aggregate control values require schema version 2")
      let info ← emitLift (checked.infer scope env span (.index value index))
      pure (node span "index" [("value", ← emitExpression checked scope env span value),
        ("index", ← emitExpression checked scope env span index), ("type", toJson (← emitType checked span info.ty))])
    | .at span value => emitExpression checked scope env span value

  private partial def emitBody (checked : Helpers.Prepared) (target : Helpers.Declaration) (env : Helpers.Environment)
      (statements : List Statement) : EmitM (List Json) := do
    let mut env := env
    let mut result := []
    for statement in statements do
      emitSpend target.span
      let item ← match statement with
        | .bind name ty value => do
          emitLift (portableName target.span name)
          chargeBytes (6 * name.utf8ByteSize)
          let value ← emitCoercedExpression checked target.id.scope env target.span ty value
          env := (name, ty) :: env
          pure (node target.span "bind" [("name", toJson name), ("type", toJson (← emitType checked target.span ty)), ("value", value)])
        | .evaluate value => pure (node target.span "evaluate" [("value", ← emitExpression checked target.id.scope env target.span value)])
        | .assert condition => do
          let conditionSpan := match condition with
            | .at span _ => span
            | _ => target.span
          let message := (← get).assertionDiagnostics.find? (·.1 == conditionSpan)
          let fields := [("condition", ← emitExpression checked target.id.scope env target.span condition)]
          let fields := match message with
            | none => fields
            | some (_, value) => fields ++ [("message", toJson value)]
          pure (node target.span "assert" fields)
        | .return value => pure (node target.span "return" [("value", ← match value with
          | none => pure Json.null
          | some value => emitCoercedExpression checked target.id.scope env target.span target.result value)])
        | .branch condition yes no => pure (node target.span "if" [
          ("condition", ← emitExpression checked target.id.scope env target.span condition),
          ("yes", toJson (← emitBody checked target env yes)), ("no", toJson (← emitBody checked target env no))])
        | .stage capability key type value => do
          unless hostName capability && hostKey key do emitLift (fail target.span "invalid private stage capability/key")
          pure (node target.span "stage" [
          ("capability", toJson capability), ("key", toJson key), ("type", toJson (← emitType checked target.span type)),
          ("value", ← emitExpression checked target.id.scope env target.span value)])
        | .readCell .. => emitLift (fail target.span "portable control capability unavailable: ledger reads")
        | .readMap .. | .readMember .. =>
          emitLift (fail target.span "portable control capability unavailable: ledger reads")
        | .writeCell .. => emitLift (fail target.span "portable control capability unavailable: ledger writes")
        | .writeMap .. =>
          emitLift (fail target.span "portable control capability unavailable: ledger writes")
        | .emitEvent .. =>
          emitLift (fail target.span "portable control capability unavailable: ledger events")
        | .claimShielded .. =>
          emitLift (fail target.span "portable control capability unavailable: shielded claims")
        | .forRange .. => emitLift (fail target.span "unexpanded finite loop reached portable control emission")
      result := result ++ [item]
    pure result
end

/-- Portable host-only plan. Named calls reference a function table and never
copy callee subtrees. Native guarded lowering remains gated until CF-02. -/
private def compileScalarWithLimits (limits : Helpers.Limits) (program : Program) (entryName : String)
    (maxPlanBytes : Nat := 1048576) : Except Diagnostic Json := do
  if maxPlanBytes > 1048576 then fail {} "control byte limit exceeds hard policy"
  let program ← Helpers.prepareProgramWithLimits limits program
  let checked ← Helpers.prepareWithLimits limits program
  checkPreparedDisclosure limits checked entryName
  let summaries := checked.summaries
  let some entry := program.exports.find? (·.name == entryName) | fail {} "unknown control entrypoint"
  let functions : List Helpers.Declaration := program.declarations.filter fun value => summaries.any (·.id == value.id)
  let emit : EmitM (List Json) := do
    chargeBytes (512 + 6 * entry.name.utf8ByteSize)
    for input in entry.inputs do chargeBytes (512 + 6 * input.name.utf8ByteSize)
    let mut values := []
    for target in functions do
      emitLift (portableName target.span target.name)
      chargeBytes (512 + 6 * target.name.utf8ByteSize)
      for parameter in target.parameters do
        emitLift (portableName target.span parameter.name)
        chargeBytes (512 + 6 * parameter.name.utf8ByteSize)
      let env := target.parameters.map fun parameter => (parameter.name, ResultType.scalar parameter.ty)
      let body ← emitBody checked target env target.body
      values := values ++ [Json.mkObj [
        ("id", toJson (idName target.id)), ("name", toJson target.name),
        ("parameters", toJson (target.parameters.map fun parameter => Json.mkObj [
          ("name", toJson parameter.name), ("type", toJson (typeName (.scalar parameter.ty)))])),
        ("resultType", toJson (typeName target.result)), ("body", toJson body)]]
    pure values
  let (functions, state) ← emit.run {remaining := limits.maxExecutionSteps, bytes := maxPlanBytes}
  portableName entry.span entry.name
  for input in entry.inputs do portableName input.span input.name
  let plan := Json.mkObj [
    ("schemaVersion", toJson (1 : Nat)), ("kind", toJson ("host-control" : String)), ("name", toJson entry.name),
    ("inputs", toJson (entry.inputs.map fun (input : Noctium.Input) => Json.mkObj [
      ("name", toJson input.name), ("type", toJson (typeName (.scalar input.ty))),
      ("visibility", toJson (if input.visibility == .public then "public" else "private"))])),
    ("witnesses", toJson (state.witnesses.map fun (name, ty) => Json.mkObj [
      ("name", toJson name), ("type", toJson (typeName (.scalar ty)))])),
    ("functions", toJson functions), ("entry", toJson (idName entry.target)),
    ("limits", Json.mkObj [("maxSteps", toJson limits.maxExecutionSteps)])]
  if plan.compress.utf8ByteSize > maxPlanBytes then fail entry.span "control plan byte limit exceeded"
  pure plan

/-- Typed private execution shares helper checking and component disclosure.
Native circuit binding is supplied only by Witness.compile after actual lowering. -/
def compileTypedWithLimits (limits : Helpers.Limits) (program : Program) (entryName : String)
    (maxPlanBytes : Nat := 1048576)
    (assertionDiagnostics : List (SourceSpan × String) := []) : Except Diagnostic Json := do
  if maxPlanBytes > 1048576 then fail {} "control byte limit exceeds hard policy"
  let program ← Helpers.prepareProgramWithLimits limits program
  let checked ← Helpers.prepareWithLimits limits program
  ComponentDisclosure.checkProgram program entryName
  let some entry := program.exports.find? (·.name == entryName) | fail {} "unknown control entrypoint"
  let target ← declaration program entry.target entry.span
  let functions := program.declarations.filter fun value => checked.summaries.any (·.id == value.id)
  let emit : EmitM (List Json × List Json × List Json) := do
    chargeBytes (1024 + 6 * entry.name.utf8ByteSize)
    let mut inputValues := []
    let mut scalarInputs := entry.inputs
    let mut aggregateInputs := entry.compositeInputs
    for parameter in target.parameters do
      let (name, type, visibility, span) ← match target.parameterType parameter with
        | .scalar _ => do
          let some input := scalarInputs.head? | emitLift (fail entry.span "typed input signature mismatch")
          scalarInputs := scalarInputs.drop 1
          pure (input.name, ResultType.scalar input.ty, input.visibility, input.span)
        | .composite _ => do
          let some input := aggregateInputs.head? | emitLift (fail entry.span "typed input signature mismatch")
          aggregateInputs := aggregateInputs.drop 1
          pure (input.name, ResultType.composite input.type, input.visibility, input.span)
        | .unit => do
          let some input := aggregateInputs.head? | emitLift (fail entry.span "typed input signature mismatch")
          aggregateInputs := aggregateInputs.drop 1
          unless input.type == .unit do emitLift (fail input.span "typed Unit input type mismatch")
          pure (input.name, .unit, input.visibility, input.span)
      emitLift (portableName span name)
      chargeBytes (512 + 6 * name.utf8ByteSize)
      inputValues := inputValues ++ [Json.mkObj [("name", toJson name),
        ("type", toJson (← emitType checked span type)),
        ("visibility", toJson (if visibility == .public then "public" else "private"))]]
    unless scalarInputs.isEmpty && aggregateInputs.isEmpty do emitLift (fail entry.span "typed input signature mismatch")
    let mut signatures := []
    for signature in program.witnesses do
      chargeBytes (512 + 6 * (signature.name.utf8ByteSize + signature.operation.utf8ByteSize + signature.capability.utf8ByteSize))
      let mut parameters := []
      for parameter in signature.parameters do
        chargeBytes (128 + 6 * parameter.name.utf8ByteSize)
        parameters := parameters ++ [Json.mkObj [("name", toJson parameter.name),
          ("type", toJson (← emitType checked signature.span parameter.type))]]
      signatures := signatures ++ [Json.mkObj [("name", toJson signature.name),
        ("operation", toJson signature.operation), ("capability", toJson signature.capability),
        ("privateKey", toJson signature.privateKey),
        ("parameters", toJson parameters), ("resultType", toJson (← emitType checked signature.span signature.result))]]
    let mut values := []
    for function in functions do
      emitLift (portableName function.span function.name)
      chargeBytes (512 + 6 * function.name.utf8ByteSize)
      let mut parameters := []
      for parameter in function.parameters do
        emitLift (portableName function.span parameter.name)
        chargeBytes (128 + 6 * parameter.name.utf8ByteSize)
        parameters := parameters ++ [Json.mkObj [("name", toJson parameter.name),
          ("type", toJson (← emitType checked function.span (function.parameterType parameter)))]]
      let resultType ← emitType checked function.span function.result
      let env := function.parameters.map fun parameter => (parameter.name, function.parameterType parameter)
      let body ← emitBody checked function env function.body
      values := values ++ [Json.mkObj [("id", toJson (idName function.id)), ("name", toJson function.name),
        ("parameters", toJson parameters), ("resultType", toJson resultType), ("body", toJson body)]]
    pure (inputValues, signatures, values)
  let ((inputs, signatures, functions), state) ← emit.run
    {remaining := limits.maxExecutionSteps, bytes := maxPlanBytes, typed := true,
      assertionDiagnostics}
  let types ← state.types.mapM fun (id, compiled) => do
    pure (Json.mkObj [("id", toJson id), ("schema", ← liftError entry.span (Types.schemaJson compiled))])
  let plan := Json.mkObj [("schemaVersion", toJson (2 : Nat)), ("kind", toJson ("host-control" : String)),
    ("mode", toJson ("host" : String)), ("binding", Json.null), ("name", toJson entry.name),
    ("inputs", toJson inputs), ("witnesses", toJson signatures), ("types", toJson types),
    ("functions", toJson functions), ("entry", toJson (idName entry.target)),
    ("limits", Json.mkObj [("maxSteps", toJson limits.maxExecutionSteps)])]
  if plan.compress.utf8ByteSize > maxPlanBytes then fail entry.span "control plan byte limit exceeded"
  pure plan

private partial def hasCompositeStage : List Statement → Bool
  | [] => false
  | .stage _ _ (.composite _) _ :: _ => true
  | .branch _ yes no :: rest => hasCompositeStage yes || hasCompositeStage no || hasCompositeStage rest
  | .forRange _ _ _ body :: rest => hasCompositeStage body || hasCompositeStage rest
  | _ :: rest => hasCompositeStage rest

def compileWithLimits (limits : Helpers.Limits) (program : Program) (entryName : String)
    (maxPlanBytes : Nat := 1048576) : Except Diagnostic Json :=
  let hasUnitParameters := program.declarations.any fun declaration =>
    declaration.compositeParameters.any (fun (_, type) => type == .unit)
  let hasUnitInputs := program.exports.any fun entry =>
    entry.compositeInputs.any (fun input => input.type == .unit)
  if program.witnesses.isEmpty && !hasUnitParameters && !hasUnitInputs &&
      !program.declarations.any (hasCompositeStage ∘ (·.body)) then
    compileScalarWithLimits limits program entryName maxPlanBytes
  else compileTypedWithLimits limits program entryName maxPlanBytes

def compile (program : Program) (entryName : String) : Except Diagnostic Json :=
  compileWithLimits {} program entryName

end Noctium.Control
