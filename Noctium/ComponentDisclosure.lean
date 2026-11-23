import Noctium.Helpers

namespace Noctium.ComponentDisclosure
open Noctium Noctium.Helpers

structure FlowOrigin where
  origin : Disclosure.Origin
  via : List String := []
  deriving Repr, BEq

abbrev Origins := List FlowOrigin

structure Value where
  type : ResultType
  components : List Origins
  indexOrigins : Origins := []
  tagOrigins : Origins := []
  controlOrigins : Origins := []
  deriving Repr, Inhabited

private def merge (left right : Origins) : Origins := (left ++ right).eraseDups
private def mergeMany (values : List Origins) : Origins := values.foldl merge []

private def addVia (label : String) (origins : Origins) : Origins :=
  origins.map fun item => {item with via := item.via ++ [label]}

private def allOrigins (value : Value) : Origins :=
  mergeMany (value.components ++ [value.indexOrigins, value.tagOrigins, value.controlOrigins])

private def payloadOrigins (value : Value) : Origins := mergeMany value.components

private def compileType (program : Program) (span : SourceSpan) (type : Types.CompositeType) :
    Except Diagnostic Types.CompiledType :=
  match Types.compileType program.composites type with
  | .ok value => pure value
  | .error diagnostic =>
    let sourceSpan := if diagnostic.span.file.isEmpty then span else diagnostic.span
    .error {span := sourceSpan, message := diagnostic.message}

private partial def paths (layout : Types.Layout) (pathPrefix : String := "") : List String :=
  match layout with
  | .unit => []
  | .scalar _ => [pathPrefix]
  | .curve type => List.replicate type.nativeCallFieldCount pathPrefix
  | .tuple items => items.zipIdx.flatMap fun (item, index) => paths item (pathPrefix ++ s!".{index}")
  | .structure _ fields => fields.flatMap fun (name, item) => paths item (pathPrefix ++ s!".{name}")
  | .vector length element => (List.range length).flatMap fun index => paths element (pathPrefix ++ s!".{index}")
  | .bytes length _ => (List.range length).map fun index => pathPrefix ++ s!".{index}"
  | .enumeration _ _ _ payloadLeaves _ _ =>
      (pathPrefix ++ ".$tag") :: ((List.range payloadLeaves).map fun index => pathPrefix ++ s!".$payload{index}")

private def inputComponentName (root path : String) : String :=
  if path.isEmpty then root else root ++ path

private def projectionSlice (layout : Types.Layout) (projection : Types.Projection) :
    Except Diagnostic (Nat × Nat) := do
  match layout, projection with
  | .tuple items, .tupleIndex index =>
    let some selected := items[index]? | throw {span := {}, message := "aggregate tuple projection out of bounds"}
    pure ((items.take index).map Types.Layout.leafCount |>.sum, selected.leafCount)
  | .structure _ fields, .field name =>
    let some index := fields.findIdx? (·.1 == name) | throw {span := {}, message := "unknown aggregate field"}
    let some selected := fields[index]? | throw {span := {}, message := "aggregate field layout mismatch"}
    pure ((fields.take index).map (fun field => field.2.leafCount) |>.sum, selected.2.leafCount)
  | .vector length element, .vectorIndex index =>
    unless index < length do throw {span := {}, message := "aggregate vector projection out of bounds"}
    pure (index * element.leafCount, element.leafCount)
  | .bytes length _, .byteIndex index =>
    unless index < length do throw {span := {}, message := "aggregate byte projection out of bounds"}
    pure (index, 1)
  | .enumeration _ _ _ _ _ variants, .enumField variant name =>
    let some selected := variants.find? (·.1 == variant) | throw {span := {}, message := "unknown aggregate enum variant"}
    let some index := selected.2.1.findIdx? (·.1 == name) | throw {span := {}, message := "unknown aggregate enum field"}
    let some field := selected.2.1[index]? | throw {span := {}, message := "aggregate enum layout mismatch"}
    pure (1 + ((selected.2.1.take index).map (fun item => item.2.leafCount)).sum, field.2.leafCount)
  | .enumeration .., .enumTag => pure (0, 1)
  | _, _ => throw {span := {}, message := "aggregate projection kind/type mismatch"}

private def scalarInfo (prepared : Prepared) (scope : Nat) (env : Environment)
    (span : SourceSpan) (term : Term) : Except Diagnostic TermInfo :=
  prepared.infer scope env span term

private def zeroValue (type : ResultType) : Value :=
  {type, components := []}

private def scalarValue (type : ResultType) (origins : Origins := []) : Value :=
  {type, components := [origins]}

private def makeValue (type : ResultType) (components : List Origins)
    (indexOrigins tagOrigins controlOrigins : Origins) : Value :=
  ⟨type, components, indexOrigins, tagOrigins, controlOrigins⟩

private def mapValueOrigins (label : String) (value : Value) : Value :=
  {value with
    components := value.components.map (addVia label)
    indexOrigins := addVia label value.indexOrigins
    tagOrigins := addVia label value.tagOrigins
    controlOrigins := addVia label value.controlOrigins}

private def sourceInputValue (input : AggregateInput) (program : Program) :
    Except Diagnostic Value := do
  let compiled ← compileType program input.span input.type
  let leafPaths := paths compiled.checked.value
  unless leafPaths.length == compiled.checked.expandedLeaves do
    throw {span := input.span, message := "aggregate source input path count mismatch"}
  let leaves : List Origins := leafPaths.map fun path =>
    if input.visibility == .private then
      let origin : Disclosure.Origin := {
        name := inputComponentName input.name path
        kind := .parameter
        span := input.span}
      [{origin}]
    else []
  pure {type := .composite input.type, components := leaves}

private def scalarInputValue (input : Input) : Value :=
  let origins := if input.visibility == .private then
    [[{origin := {name := input.name, kind := .parameter, span := input.span}}]]
    else [[]]
  {type := .scalar input.ty, components := origins}

private def normalizeValue (span : SourceSpan) (target : ResultType) (value : Value) :
    Except Diagnostic Value := do
  unless Helpers.subtype value.type target do
    throw {span, message := "component analysis value type is incompatible with its declared type"}
  pure {value with type := target}

private def knownBoolean : Term → Option Bool
  | .bool value => some value
  | .at _ value => knownBoolean value
  | .disclose _ value => knownBoolean value
  | _ => none

private def checkBoolean (prepared : Prepared) (scope : Nat) (env : Environment)
    (span : SourceSpan) (term : Term) : Except Diagnostic Unit := do
  let info ← scalarInfo prepared scope env span term
  unless info.ty == .scalar .bool do throw {span, message := "helper condition requires Bool"}

private def callPath (declaration : Declaration) (value : Value) : Value :=
  mapValueOrigins s!"helper {declaration.name}" value

private structure BodyFlow where
  returns : List Value := []
  continues : Bool := true
  deriving Inhabited

private def addControl (value : Value) (origins : Origins) : Value :=
  {value with controlOrigins := merge value.controlOrigins origins}

private def mergeReturns (span : SourceSpan) (type : ResultType) (values : List Value) :
    Except Diagnostic Value := do
  let values ← values.mapM (normalizeValue span type)
  match values with
  | [] =>
    if type == .unit then pure (zeroValue .unit)
    else throw {span, message := "component analysis found a non-unit fall-through path"}
  | first :: rest => do
    let mut result := first
    for value in rest do
      unless result.components.length == value.components.length do
        throw {span, message := "component analysis return shape mismatch"}
      result := {
        type
        components := result.components.zipWith merge value.components
        indexOrigins := merge result.indexOrigins value.indexOrigins
        tagOrigins := merge result.tagOrigins value.tagOrigins
        controlOrigins := merge result.controlOrigins value.controlOrigins}
    pure result

mutual
private partial def analyzeTerm (fuel : Nat) (program : Program) (prepared : Prepared)
    (scope : Nat) (env : List (String × Value)) (span : SourceSpan) (term : Term) :
    Except Diagnostic Value := do
  if fuel == 0 then throw {span, message := "component disclosure call depth exceeded"}
  let typeEnv := env.map fun (name, value) => (name, value.type)
  let info ← scalarInfo prepared scope typeEnv span term
  match term with
  | .unit => pure (zeroValue .unit)
  | .native _ | .bool _ | .uint _ _ | .bytes32Literal _ | .foreignConstant .. =>
    pure (scalarValue info.ty)
  | .ref name =>
    match env.lookup name with
    | some value => pure value
    | none =>
      let message := "missing component origin rule for reference '" ++ name ++ "'"
      throw {span := span, message := message}
  | .binary _ left right | .boolAnd left right | .boolOr left right
  | .boolXor left right | .eq left right | .poseidon2 _ left right => do
    let left ← analyzeTerm fuel program prepared scope env span left
    let right ← analyzeTerm fuel program prepared scope env span right
    pure (makeValue info.ty [merge (payloadOrigins left) (payloadOrigins right)]
      (merge left.indexOrigins right.indexOrigins) (merge left.tagOrigins right.tagOrigins)
      (merge left.controlOrigins right.controlOrigins))
  | .curve _ arguments | .bytes _ arguments => do
    let values ← arguments.mapM (analyzeTerm fuel program prepared scope env span)
    pure (makeValue info.ty [values.foldl (fun result value => merge result (payloadOrigins value)) []]
      (values.foldl (fun result value => merge result value.indexOrigins) [])
      (values.foldl (fun result value => merge result value.tagOrigins) [])
      (values.foldl (fun result value => merge result value.controlOrigins) []))
  | .cast _ value | .bytesAt value _ => do
    let value ← analyzeTerm fuel program prepared scope env span value
    pure (makeValue info.ty [payloadOrigins value] value.indexOrigins value.tagOrigins value.controlOrigins)
  | .disclose _ value => do
    let value ← analyzeTerm fuel program prepared scope env span value
    pure {value with type := info.ty, components := value.components.map fun _ => []}
  | .select condition yes no => do
    let condition ← analyzeTerm fuel program prepared scope env span condition
    let yes ← analyzeTerm fuel program prepared scope env span yes
    let no ← analyzeTerm fuel program prepared scope env span no
    pure (makeValue info.ty [merge (payloadOrigins yes) (payloadOrigins no)]
      (mergeMany [yes.indexOrigins, no.indexOrigins, condition.indexOrigins])
      (merge yes.tagOrigins no.tagOrigins)
      (mergeMany [yes.controlOrigins, no.controlOrigins, allOrigins condition]))
  | .ite condition yes no => do
    let _ ← checkBoolean prepared scope typeEnv span condition
    match knownBoolean condition with
    | some selected =>
      let value ← analyzeTerm fuel program prepared scope env span (if selected then yes else no)
      pure {value with type := info.ty}
    | none => do
      let condition ← analyzeTerm fuel program prepared scope env span condition
      let yes ← analyzeTerm fuel program prepared scope env span yes
      let no ← analyzeTerm fuel program prepared scope env span no
      unless yes.components.length == no.components.length do
        throw {span, message := "conditional source origin count mismatch"}
      pure (makeValue info.ty (List.zipWith merge yes.components no.components)
        (mergeMany [yes.indexOrigins, no.indexOrigins, condition.indexOrigins])
        (merge yes.tagOrigins no.tagOrigins)
        (mergeMany [yes.controlOrigins, no.controlOrigins, allOrigins condition]))
  | .andThen left right | .orElse left right => do
    let leftValue ← analyzeTerm fuel program prepared scope env span left
    match knownBoolean left with
    | some false =>
      if let .andThen .. := term then pure {leftValue with type := info.ty}
      else
        let rightValue ← analyzeTerm fuel program prepared scope env span right
        pure (makeValue info.ty [merge (payloadOrigins leftValue) (payloadOrigins rightValue)]
          (merge leftValue.indexOrigins rightValue.indexOrigins)
          (merge leftValue.tagOrigins rightValue.tagOrigins)
          (mergeMany [leftValue.controlOrigins, rightValue.controlOrigins, allOrigins leftValue]))
    | some true =>
      if let .orElse .. := term then pure {leftValue with type := info.ty}
      else analyzeTerm fuel program prepared scope env span right
    | none => do
      let rightValue ← analyzeTerm fuel program prepared scope env span right
      pure (makeValue info.ty [merge (payloadOrigins leftValue) (payloadOrigins rightValue)]
        (merge leftValue.indexOrigins rightValue.indexOrigins)
        (merge leftValue.tagOrigins rightValue.tagOrigins)
        (mergeMany [leftValue.controlOrigins, rightValue.controlOrigins, allOrigins leftValue]))
  | .witness name _ =>
    pure (scalarValue info.ty [{origin := {name, kind := .provider, span}, via := ["provider witness"]}])
  | .witnessCall _ name arguments => do
    let arguments ← arguments.mapM (analyzeTerm fuel program prepared scope env span)
    let signature ← Helpers.witnessSignature program name span
    let kind := if signature.operation == "private_state.read.v1" then PrivateOriginKind.privateState else .provider
    let origins := mergeMany (([{origin := {name, kind, span}, via := ["typed provider witness"]}] : Origins) ::
      arguments.map allOrigins)
    let width ← match info.ty with
      | .unit => pure 0
      | .scalar _ => pure 1
      | .composite type => pure (← compileType program span type).checked.expandedLeaves
    pure {
      type := info.ty
      components := List.replicate width origins
      controlOrigins := if width == 0 then origins else []}
  | .call name arguments => do
    let values ← arguments.mapM (analyzeTerm fuel program prepared scope env span)
    let declaration ← prepared.resolve scope name (values.map (·.type)) span
    analyzeCall (fuel - 1) program prepared declaration values
  | .composite type leaves => do
    let values ← leaves.mapM (analyzeTerm fuel program prepared scope env span)
    let compiled ← compileType program span type
    let components := values.flatMap fun value =>
      match value.type with
      | .scalar type =>
        if type.isJubjub || type.isForeign then
          List.replicate type.nativeCallFieldCount (payloadOrigins value)
        else value.components
      | _ => value.components
    unless components.length == compiled.checked.expandedLeaves do
      throw {span, message := "aggregate source origin count mismatch"}
    pure (makeValue info.ty components (mergeMany (values.map (·.indexOrigins)))
      (mergeMany (values.map (·.tagOrigins))) (mergeMany (values.map (·.controlOrigins))))
  | .project value projection => do
    let parent ← analyzeTerm fuel program prepared scope env span value
    let .composite parentType := parent.type
      | throw {span, message := "aggregate projection origin rule requires composite"}
    let compiled ← compileType program span parentType
    let (offset, width) ← projectionSlice compiled.checked.value projection
    let selected := (parent.components.drop offset).take width
    let tagOrigins := match projection with
      | .enumField _ _ => merge parent.tagOrigins (parent.components.headD [])
      | _ => parent.tagOrigins
    let components := match info.ty with
      | .scalar _ => [mergeMany selected]
      | _ => selected
    pure (makeValue info.ty components parent.indexOrigins tagOrigins parent.controlOrigins)
  | .index value index => do
    let parent ← analyzeTerm fuel program prepared scope env span value
    let indexValue ← analyzeTerm fuel program prepared scope env span index
    let .composite (.vector length element) := parent.type
      | throw {span, message := "dynamic aggregate index origin rule requires a vector"}
    let childType ← compileType program span element
    let width := childType.checked.expandedLeaves
    let components := (List.range width).map fun offset =>
      mergeMany ((List.range length).map fun position =>
        (parent.components[position * width + offset]?).getD [])
    let components := match info.ty with
      | .scalar _ => [mergeMany components]
      | _ => components
    pure (makeValue info.ty components
      (mergeMany [parent.indexOrigins, payloadOrigins indexValue, indexValue.indexOrigins])
      (merge parent.tagOrigins indexValue.tagOrigins)
      (mergeMany [parent.controlOrigins, indexValue.controlOrigins]))
  | .effect kind label result => do
    let value ← analyzeTerm fuel program prepared scope env span result
    if kind == .privateState then
      let origin := {origin := {name := label, kind := .privateState, span}}
      pure {value with components := value.components.map fun origins => merge origins [origin]}
    else pure value
  | .at nested value => analyzeTerm fuel program prepared scope env nested value

private partial def analyzeCall (fuel : Nat) (program : Program) (prepared : Prepared)
    (declaration : Declaration) (values : List Value) : Except Diagnostic Value := do
  if fuel == 0 then throw {span := declaration.span, message := "component disclosure call depth exceeded"}
  let mut env := []
  for (parameter, value) in declaration.parameters.zip values do
    let value ← normalizeValue declaration.span (declaration.parameterType parameter) value
    env := (parameter.name, callPath declaration value) :: env
  let flow ← analyzeBody fuel program prepared declaration env declaration.body
  let result ← mergeReturns declaration.span declaration.result flow.returns
  normalizeValue declaration.span declaration.result result

private partial def analyzeBody (fuel : Nat) (program : Program) (prepared : Prepared)
    (declaration : Declaration) (env : List (String × Value)) (body : List Statement) :
    Except Diagnostic BodyFlow := do
  let span := declaration.span
  match body with
  | [] => pure {}
  | .return none :: _ => do
    let value ← normalizeValue span declaration.result (zeroValue .unit)
    pure {returns := [value], continues := false}
  | .return (some value) :: _ => do
    let value ← analyzeTerm fuel program prepared declaration.id.scope env span value
    let value ← normalizeValue span declaration.result value
    pure {returns := [value], continues := false}
  | .bind name type value :: rest => do
    let value ← analyzeTerm fuel program prepared declaration.id.scope env span value
    let value ← normalizeValue span type value
    analyzeBody fuel program prepared declaration ((name, value) :: env) rest
  | .evaluate value :: rest => do
    discard (analyzeTerm fuel program prepared declaration.id.scope env span value)
    analyzeBody fuel program prepared declaration env rest
  | .assert condition :: rest => do
    discard (analyzeTerm fuel program prepared declaration.id.scope env span condition)
    analyzeBody fuel program prepared declaration env rest
  | .branch condition yes no :: rest => do
    let _ ← checkBoolean prepared declaration.id.scope (env.map fun (name, value) => (name, value.type)) span condition
    match knownBoolean condition with
    | some flag => do
      let branch := if flag then yes else no
      let branchFlow ← analyzeBody fuel program prepared declaration env branch
      if !branchFlow.continues then pure branchFlow
      else do
        let restFlow ← analyzeBody fuel program prepared declaration env rest
        pure {returns := branchFlow.returns ++ restFlow.returns, continues := restFlow.continues}
    | none => do
      let conditionValue ← analyzeTerm fuel program prepared declaration.id.scope env span condition
      let yesFlow ← analyzeBody fuel program prepared declaration env yes
      let noFlow ← analyzeBody fuel program prepared declaration env no
      let branchReturns := (yesFlow.returns ++ noFlow.returns).map
        fun value => addControl value (allOrigins conditionValue)
      if !yesFlow.continues && !noFlow.continues then
        pure {returns := branchReturns, continues := false}
      else do
        -- Branch-local bindings leave scope here. The continuation sees the original environment.
        let restFlow ← analyzeBody fuel program prepared declaration env rest
        let restReturns := if branchReturns.isEmpty then restFlow.returns else
          restFlow.returns.map fun value => addControl value (allOrigins conditionValue)
        pure {returns := branchReturns ++ restReturns, continues := restFlow.continues}
  | .stage _ _ _ value :: rest => do
    discard (analyzeTerm fuel program prepared declaration.id.scope env span value)
    analyzeBody fuel program prepared declaration env rest
  | .readCell _ destination ty :: rest =>
    analyzeBody fuel program prepared declaration
      ((destination, scalarValue (.scalar ty)) :: env) rest
  | .writeCell _ _ value :: rest => do
    discard (analyzeTerm fuel program prepared declaration.id.scope env span value)
    analyzeBody fuel program prepared declaration env rest
  | .readMap _ destination _ valueTy key :: rest => do
    discard (analyzeTerm fuel program prepared declaration.id.scope env span key)
    analyzeBody fuel program prepared declaration
      ((destination, scalarValue (.scalar valueTy)) :: env) rest
  | .readMember _ destination _ _ key :: rest => do
    discard (analyzeTerm fuel program prepared declaration.id.scope env span key)
    analyzeBody fuel program prepared declaration
      ((destination, scalarValue (.scalar .bool)) :: env) rest
  | .writeMap _ _ _ key value :: rest => do
    discard (analyzeTerm fuel program prepared declaration.id.scope env span key)
    discard (analyzeTerm fuel program prepared declaration.id.scope env span value)
    analyzeBody fuel program prepared declaration env rest
  | .emitEvent _ payload :: rest => do
    discard (analyzeTerm fuel program prepared declaration.id.scope env span payload)
    analyzeBody fuel program prepared declaration env rest
  | .claimShielded _ digest :: rest => do
    discard (analyzeTerm fuel program prepared declaration.id.scope env span digest)
    analyzeBody fuel program prepared declaration env rest
  | .forRange .. :: _ =>
    throw {span, message := "unexpanded finite loop reached component disclosure analysis"}
end

private def outputName (program : Program) (entry : Export) : String := Id.run do
  let scalarNames := entry.inputs.map (·.name)
  let aggregateNames := entry.compositeInputs.flatMap fun input =>
    match Types.compileType program.composites input.type with
    | .ok compiled => (paths compiled.checked.value).map (inputComponentName input.name)
    | .error _ => []
  let names := scalarNames ++ aggregateNames
  return ((List.range (names.length + 1)).map fun index =>
    if index == 0 then "result" else s!"result{index}").find?
      (fun name => !names.contains name) |>.getD "result"

private def kindName : PrivateOriginKind → String
  | .parameter => "parameter"
  | .provider => "provider result"
  | .privateState => "private-state read"

private def location (span : SourceSpan) : String :=
  s!"{if span.file.isEmpty then "<typed source>" else span.file}:{span.line}:{span.column}"

private def diagnostic (sink : String) (sinkSpan : SourceSpan) (control : Bool)
    (item : FlowOrigin) : Diagnostic :=
  let category := if control then "control from " else ""
  let release := if control then "disclose the controlling value explicitly" else "use disclose(...) for the released value"
  let path := if item.via.isEmpty then "" else s!"; source path: {String.intercalate " -> " item.via}"
  {span := sinkSpan, message := s!"undisclosed private {category}{kindName item.origin.kind} '{item.origin.name}' at {location item.origin.span} reaches {sink}{path}; {release}"}

private def checkOutput (sink : String) (sinkSpan : SourceSpan) (value : Value) : Except Diagnostic Unit := do
  let control := mergeMany [value.indexOrigins, value.tagOrigins, value.controlOrigins]
  if let some item := control.head? then throw (diagnostic sink sinkSpan true item)
  if let some item := (payloadOrigins value).head? then throw (diagnostic sink sinkSpan false item)

/-- Analyze an exported source entry from its declaration, inputs and helper bodies. -/
def analyzeEntry (program : Program) (entryName : String) : Except Diagnostic (Export × Value) := do
  let program ← Helpers.prepareProgramWithLimits {} program
  let prepared ← Helpers.prepareWithLimits {} program
  let some entry := program.exports.find? (·.name == entryName)
    | throw {span := {}, message := "unknown helper entrypoint"}
  let declaration ← match program.declarations.find? (·.id == entry.target) with
    | some declaration => pure declaration
    | none => throw {span := entry.span, message := "unknown helper declaration identity"}
  let mut arguments := []
  let mut scalarInputs := entry.inputs
  let mut aggregateInputs := entry.compositeInputs
  for parameter in declaration.parameters do
    let inputValue ← match declaration.parameterType parameter with
      | .scalar _ =>
        let some input := scalarInputs.head?
          | throw {span := entry.span, message := "helper entrypoint input signature mismatch"}
        scalarInputs := scalarInputs.drop 1
        pure (scalarInputValue input)
      | .composite _ =>
        let some input := aggregateInputs.head?
          | throw {span := entry.span, message := "helper entrypoint input signature mismatch"}
        aggregateInputs := aggregateInputs.drop 1
        sourceInputValue input program
      | .unit => do
        let some input := aggregateInputs.head?
          | throw {span := entry.span, message := "helper entrypoint input signature mismatch"}
        aggregateInputs := aggregateInputs.drop 1
        unless input.type == .unit do
          throw {span := input.span, message := "helper Unit input type mismatch"}
        pure (zeroValue .unit)
    let value ← normalizeValue entry.span (declaration.parameterType parameter) inputValue
    arguments := arguments ++ [value]
  unless scalarInputs.isEmpty && aggregateInputs.isEmpty do
    throw {span := entry.span, message := "helper entrypoint input signature mismatch"}
  let value ← analyzeCall 64 program prepared declaration arguments
  pure (entry, value)

/-- Recompute private component origins from source declarations and helper bodies.
No visibility or release summary is accepted from the caller. -/
def checkProgram (program : Program) (entryName : String) : Except Diagnostic Unit := do
  let (entry, value) ← analyzeEntry program entryName
  let root := outputName program entry
  match value.type with
  | .unit => pure ()
  | .scalar _ => checkOutput s!"public output '{root}'" entry.span value
  | .composite type => do
    let compiled ← compileType program entry.span type
    let names := (paths compiled.checked.value).map (inputComponentName root)
    unless names.length == value.components.length do
      throw {span := entry.span, message := "aggregate helper output origin count mismatch"}
    for (name, origins) in names.zip value.components do
      let projected : Value := {value with components := [origins]}
      checkOutput s!"public output '{name}'" entry.span projected

end Noctium.ComponentDisclosure
