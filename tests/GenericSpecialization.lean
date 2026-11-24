import Noctium.Helpers.Specialization
import Noctium.ComponentDisclosure
import Noctium.Backend.Zkir

namespace Noctium.GenericSpecializationTests
open Noctium
open Noctium.Helpers
open Noctium.Helpers.Specialization

private abbrev GType := Noctium.Helpers.Specialization.GenericType
private abbrev GArg := Noctium.Helpers.Specialization.Argument
private abbrev GTerm := Noctium.Helpers.Specialization.Term
private abbrev GStmt := Noctium.Helpers.Specialization.Statement
private abbrev GDecl := Noctium.Helpers.Specialization.Declaration
private abbrev GInput := Noctium.Helpers.Specialization.ExportInput
private abbrev GExport := Noctium.Helpers.Specialization.Export
private abbrev GProgram := Noctium.Helpers.Specialization.Program

private def messageContains (value : Except Diagnostic α) (text : String) : Bool :=
  match value with
  | .error diagnostic => (diagnostic.message.splitOn text).length > 1
  | .ok _ => false

private def genericInput (name : String) (type : GType)
    (visibility : Visibility := .public) : GInput :=
  ⟨name, type, visibility, {}⟩

private def genericExport (name : String) (target : DeclarationId)
    (arguments : List GArg) (inputs : List GInput := []) : GExport :=
  {name, target, arguments, inputs}

private def identityDeclarationAt (id : DeclarationId) (release : Bool := false) : GDecl := {
  id := id
  name := "identity"
  parameters := [⟨"T", .type⟩]
  values := [("value", .parameter "T")]
  result := .parameter "T"
  body := [.return (some (if release then .disclose {} (.ref "value") else .ref "value"))]
}

private def identityDeclaration (release : Bool := false) : GDecl :=
  identityDeclarationAt ⟨0, 0⟩ release

private def identityProgram (type : GType) (visibility : Visibility := .public)
    (release := false) : GProgram := {
  declarations := [identityDeclaration release]
  exports := [genericExport "entry" ⟨0, 0⟩ [.type type]
    [genericInput "value" type visibility]]
}

-- GEN-ARITY, GEN-KINDS, and runtime-provided generic values fail before cloning.
private def arityProgram : GProgram := {
  declarations := [identityDeclaration]
  exports := [genericExport "entry" ⟨0, 0⟩ [] [genericInput "value" .native]]
}

private def kindProgram : GProgram := {
  declarations := [{
    id := ⟨0, 0⟩
    name := "natural"
    parameters := [⟨"N", .natural⟩]
    values := [("value", .uint (.parameter "N"))]
    result := .uint (.parameter "N")
    body := [.return (some (.ref "value"))]
  }]
  exports := [genericExport "entry" ⟨0, 0⟩ [.type .native]
    [genericInput "value" .native]]
}

private def runtimeArgumentProgram : GProgram := {
  declarations := [identityDeclaration]
  exports := [genericExport "entry" ⟨0, 0⟩ [.type (.parameter "runtime")]
    [genericInput "value" .native]]
}

#guard messageContains (specialize (identityProgram .native) "missing") "unknown generic helper entrypoint"
#guard messageContains (specialize arityProgram "entry") "arity mismatch"
#guard messageContains (specialize kindProgram "entry") "kind mismatch"
#guard messageContains (specialize runtimeArgumentProgram "entry") "runtime generic argument"

private def genericRangeProgram : GProgram := {
  declarations := [{
    id := ⟨0, 0⟩
    name := "range"
    parameters := [⟨"N", .natural⟩]
    result := .unit
    body := [
      .forRange "index" (.literal 1) (.parameter "N") [.evaluate (.ref "index")],
      .return none]
  }]
  exports := [
    genericExport "short" ⟨0, 0⟩ [.natural (.literal 3)],
    genericExport "long" ⟨0, 0⟩ [.natural (.literal 6)]
  ]
}

private def hasGenericRange (program : Helpers.Program) (exportName : String) (stop : Nat) : Bool :=
  match program.exports.find? (·.name == exportName) with
  | some entry => match program.declarations.find? (·.id == entry.target) with
    | some declaration => match declaration.body with
      | [.forRange "index" 1 actualStop _, .return none] => actualStop == stop
      | _ => false
    | none => false
  | none => false

-- Generic Nat endpoints specialize into the existing bounded Helpers loop form.
#guard match specialize genericRangeProgram "short" with
  | .ok result => hasGenericRange result.program "short" 3 &&
      (Helpers.compile result.program result.exportName).isOk
  | .error _ => false

private def genericShieldedClaimProgram : GProgram := {
  declarations := [{
    id := ⟨0, 0⟩
    name := "claim"
    parameters := [⟨"T", .type⟩]
    values := [("digest", .bytes (.literal 32))]
    result := .unit
    body := [
      .claimShielded .receive (.disclose {} (.ref "digest")),
      .return none]
  }]
  exports := [genericExport "claim" ⟨0, 0⟩ [.type .native] [
    genericInput "digest" (.bytes (.literal 32)) .private]]
}

#guard match specialize genericShieldedClaimProgram "claim" with
  | .ok result => (Helpers.compileEntrypointFor result.program result.exportName []).isOk
  | .error _ => false

#guard messageContains
  (specialize {genericRangeProgram with exports :=
    [genericExport "reverse" ⟨0, 0⟩ [.natural (.literal 0)]]} "reverse")
  "finite range start exceeds its stop"

-- Different Nat specializations in one batch retain distinct endpoint values.
#guard match specializeBatch genericRangeProgram ["long", "short"] with
  | .ok result => hasGenericRange result.program "short" 3 &&
      hasGenericRange result.program "long" 6
  | .error _ => false

private def missingRangeNaturalProgram : GProgram := {
  declarations := [{
    id := ⟨0, 0⟩
    name := "range"
    result := .unit
    body := [.forRange "index" (.literal 0) (.parameter "N") [], .return none]
  }]
  exports := [genericExport "entry" ⟨0, 0⟩ []]
}

#guard messageContains (specialize missingRangeNaturalProgram "entry")
  "runtime generic argument 'N'"

private def excessiveRangeProgram : GProgram := {
  declarations := [{
    id := ⟨0, 0⟩
    name := "range"
    parameters := [⟨"N", .natural⟩]
    result := .unit
    body := [.forRange "index" (.literal 0) (.parameter "N") [], .return none]
  }]
  exports := [genericExport "entry" ⟨0, 0⟩ [.natural (.literal 1025)]]
}

#guard messageContains (specialize excessiveRangeProgram "entry") "finite range length"

private def genericRangeIndexEscapeProgram : GProgram := {
  declarations := [{
    id := ⟨0, 0⟩
    name := "range"
    result := .native
    body := [
      .forRange "index" (.literal 0) (.literal 1) [],
      .return (some (.ref "index"))]
  }]
  exports := [genericExport "entry" ⟨0, 0⟩ []]
}

#guard messageContains (specialize genericRangeIndexEscapeProgram "entry")
  "unknown helper value 'index'"

-- GEN-MONOMORPHIC-ENTRY: exports lower to concrete Helpers signatures.
#guard match specialize (identityProgram (.uint (.literal 255))) "entry" with
  | .ok result => result.program.declarations.any fun declaration =>
      declaration.parameters.length == 1 &&
      declaration.parameterType declaration.parameters.head! == .scalar (.uint 255) &&
      declaration.result == .scalar (.uint 255) &&
      result.program.exports.length == 1
  | .error _ => false

private def opaqueIdentityCompiles (type : GType) (ty : Ty) : Bool :=
  match specialize (identityProgram type) "entry" with
  | .error _ => false
  | .ok result =>
    match Helpers.compile result.program result.exportName with
    | .error _ => false
    | .ok circuit =>
      let inputOk := circuit.inputs.any fun input =>
        input.name == "value" && input.ty == ty && input.visibility == .public
      let outputOk := match circuit.outputs with
        | [output] => output.name == "result" && output.ty == ty &&
            output.nativeReturnFieldCount == 1 &&
            (match output.nativeReturnFields with
            | .ok fields => fields.length == 1
            | .error _ => false)
        | _ => false
      let signatureOk := parseSignatureArtifact (Lean.toJson result.signatureArtifact) |>.isOk
      inputOk && outputOk && signatureOk

-- Opaque types specialize only as root scalar helper inputs and outputs.
#guard opaqueIdentityCompiles .opaqueBytes .opaqueBytes
#guard opaqueIdentityCompiles .opaqueString .opaqueString

private def opaqueAggregateProgram : GProgram :=
  identityProgram (.tuple [.opaqueBytes])

#guard match specialize opaqueAggregateProgram "entry" with
  | .error diagnostic => diagnostic.message.contains "opaque byte strings are not scalar values"
  | .ok result => messageContains (Helpers.compile result.program result.exportName)
      "opaque byte strings are not scalar values"

private def genericBox (id : String) : Structure :=
  ⟨id, [⟨"T", .type⟩], [("value", .parameter "T")], {}⟩

private def genericVectorBox : Structure :=
  ⟨"Demo.VectorBox", [⟨"T", .type⟩, ⟨"N", .natural⟩],
    [("items", .vector (.parameter "N") (.parameter "T"))], {}⟩

private def nominalProgram : GProgram := {
  structures := [genericBox "Demo.Box", genericBox "Demo.Twin", genericVectorBox]
  aliases := [⟨"Demo.Value", [⟨"T", .type⟩],
    .structure "Demo.Box" [.type (.parameter "T")], {}⟩]
  declarations := [identityDeclaration]
  exports := [
    genericExport "alias" ⟨0, 0⟩ [.type (.alias "Demo.Value" [.type .native])]
      [genericInput "value" (.alias "Demo.Value" [.type .native])],
    genericExport "direct" ⟨0, 0⟩ [.type (.structure "Demo.Box" [.type .native])]
      [genericInput "value" (.structure "Demo.Box" [.type .native])],
    genericExport "twin" ⟨0, 0⟩ [.type (.structure "Demo.Twin" [.type .native])]
      [genericInput "value" (.structure "Demo.Twin" [.type .native])],
    genericExport "vector" ⟨0, 0⟩
      [.type (.structure "Demo.VectorBox" [.type .native, .natural (.literal 2)])]
      [genericInput "value" (.structure "Demo.VectorBox" [.type .native, .natural (.literal 2)])]
  ]
}

private def resultTypeAtEntry (result : Result) : Option Helpers.ResultType := do
  let entry ← result.program.exports.head?
  let declaration ← result.program.declarations.find? (·.id == entry.target)
  pure declaration.result

-- Alias-to-struct normalization reuses nominal identity. Twins and vector sizes stay distinct.
#guard match specialize nominalProgram "alias", specialize nominalProgram "direct",
    specialize nominalProgram "twin", specialize nominalProgram "vector" with
  | .ok aliasResult, .ok directResult, .ok twinResult, .ok vectorResult =>
    match resultTypeAtEntry aliasResult, resultTypeAtEntry directResult,
        resultTypeAtEntry twinResult, resultTypeAtEntry vectorResult with
    | some (.composite (.structure aliasId)), some (.composite (.structure directId)),
      some (.composite (.structure twinId)), some (.composite (.structure vectorId)) =>
      aliasId == directId && aliasId != twinId && vectorId != aliasId &&
        ((specialize nominalProgram "alias").toOption.bind resultTypeAtEntry ==
          some (.composite (.structure aliasId))) &&
        vectorResult.program.composites.structures.any fun declaration =>
          declaration.id == vectorId && declaration.fields.any fun field =>
            field.type == .vector 2 (.scalar .native)
    | _, _, _, _ => false
  | _, _, _, _ => false

private def nestedProgram : GProgram := {
  declarations := [
    {
      id := ⟨0, 0⟩
      name := "outer"
      parameters := [⟨"T", .type⟩, ⟨"N", .natural⟩]
      values := [("value", .parameter "T"), ("limit", .uint (.parameter "N"))]
      result := .parameter "T"
      body := [.return (some (.call ⟨0, 1⟩
        [.type (.parameter "T"), .natural (.parameter "N")]
        [.ref "value", .ref "limit"]))]
    },
    {
      id := ⟨0, 1⟩
      name := "inner"
      parameters := [⟨"U", .type⟩, ⟨"M", .natural⟩]
      values := [("value", .parameter "U"), ("limit", .uint (.parameter "M"))]
      result := .parameter "U"
      body := [.return (some (.ref "value"))]
    }
  ]
  exports := [genericExport "entry" ⟨0, 0⟩ [.type .native, .natural (.literal 7)] [
    genericInput "value" .native,
    genericInput "limit" (.uint (.literal 7))
  ]]
}

-- GEN-NESTED: outer type and natural environments flow into nested call arguments.
#guard match specialize nestedProgram "entry" with
  | .ok result => result.instances.length == 2 && result.program.declarations.length == 2 &&
    result.program.declarations.any fun declaration =>
      declaration.parameters.any (fun parameter => parameter.ty == .uint 7)
  | .error _ => false

private def lexicalScopeProgram : GProgram := {
  structures := [⟨"Demo.FreeStruct", [], [("value", .parameter "T")], {}⟩]
  aliases := [⟨"Demo.FreeAlias", [], .parameter "T", {}⟩]
  declarations := [
    {
      id := ⟨0, 0⟩
      name := "outerType"
      parameters := [⟨"T", .type⟩]
      result := .unit
      body := [.evaluate (.call ⟨0, 1⟩ [] []), .return none]
    },
    {
      id := ⟨0, 1⟩
      name := "innerType"
      result := .unit
      body := [.evaluate (.cast (.parameter "T") (.native 0)), .return none]
    },
    {
      id := ⟨0, 2⟩
      name := "outerNatural"
      parameters := [⟨"N", .natural⟩]
      result := .unit
      body := [.evaluate (.call ⟨0, 3⟩ [] []), .return none]
    },
    {
      id := ⟨0, 3⟩
      name := "innerNatural"
      result := .unit
      body := [.evaluate (.uint (.parameter "N") 0), .return none]
    },
    {
      id := ⟨0, 4⟩
      name := "outerAlias"
      parameters := [⟨"T", .type⟩]
      result := .unit
      body := [.evaluate (.call ⟨0, 5⟩ [] []), .return none]
    },
    {
      id := ⟨0, 5⟩
      name := "innerAlias"
      result := .unit
      body := [.evaluate (.cast (.alias "Demo.FreeAlias" []) (.native 0)), .return none]
    },
    {
      id := ⟨0, 6⟩
      name := "outerStruct"
      parameters := [⟨"T", .type⟩]
      result := .unit
      body := [.evaluate (.call ⟨0, 7⟩ [] []), .return none]
    },
    {
      id := ⟨0, 7⟩
      name := "innerStruct"
      result := .unit
      body := [.evaluate (.composite (.structure "Demo.FreeStruct" []) [.native 0]), .return none]
    }
  ]
  exports := [
    genericExport "type" ⟨0, 0⟩ [.type .native],
    genericExport "natural" ⟨0, 2⟩ [.natural (.literal 7)],
    genericExport "alias" ⟨0, 4⟩ [.type .native],
    genericExport "struct" ⟨0, 6⟩ [.type .native]
  ]
}

-- Callee, alias, and struct declarations use only their own generic parameters.
-- Caller bindings still resolve the explicit arguments in nestedProgram above.
#guard messageContains (specialize lexicalScopeProgram "type") "runtime generic argument 'T'"
#guard messageContains (specialize lexicalScopeProgram "natural") "runtime generic argument 'N'"
#guard messageContains (specialize lexicalScopeProgram "alias") "runtime generic argument 'T'"
#guard messageContains (specialize lexicalScopeProgram "struct") "runtime generic argument 'T'"

-- Pending helper/type clones count toward limits before child expansion.
#guard messageContains
  (specializeWithLimits {maxSpecializations := 1} nestedProgram "entry")
  "specialization count"

private def nestedAliasProgram : GProgram := {
  aliases := [
    ⟨"Demo.AliasA", [], .alias "Demo.AliasB" [], {}⟩,
    ⟨"Demo.AliasB", [], .native, {}⟩
  ]
  declarations := [identityDeclaration]
  exports := [genericExport "entry" ⟨0, 0⟩
    [.type (.alias "Demo.AliasA" [])] [genericInput "value" (.alias "Demo.AliasA" [])]]
}
#guard messageContains
  (specializeWithLimits {maxTypeSpecializations := 1} nestedAliasProgram "entry")
  "type-alias specialization count"

private def nestedStructureProgram : GProgram := {
  structures := [
    ⟨"Demo.DepthA", [], [("next", .structure "Demo.DepthB" [])], {}⟩,
    ⟨"Demo.DepthB", [], [("value", .native)], {}⟩
  ]
  declarations := [identityDeclaration]
  exports := [genericExport "entry" ⟨0, 0⟩
    [.type (.structure "Demo.DepthA" [])] [genericInput "value" (.structure "Demo.DepthA" [])]]
}
#guard messageContains
  (specializeWithLimits {maxSpecializationDepth := 1} nestedStructureProgram "entry")
  "generic type substitution depth"

private def repeatedDouble (depth : Nat) : GType :=
  match depth with
  | 0 => .native
  | depth + 1 => .alias "Demo.Double" [.type (repeatedDouble depth)]

private def exponentialTypeProgram : GProgram := {
  structures := [⟨"Demo.Ignore", [⟨"T", .type⟩], [], {}⟩]
  aliases := [⟨"Demo.Double", [⟨"T", .type⟩],
    .tuple [.parameter "T", .parameter "T"], {}⟩]
  declarations := [identityDeclaration]
  exports := [genericExport "entry" ⟨0, 0⟩
    [.type (.structure "Demo.Ignore" [.type (repeatedDouble 14)])]
    [genericInput "value" (.structure "Demo.Ignore" [.type (repeatedDouble 14)])]]
}

-- Reject a compact alias chain before traversing its exponentially expanded tuple key.
#guard messageContains (specialize exponentialTypeProgram "entry") "normalized type nodes"

private def canonicalKeyBudgetProgram : GProgram := Id.run do
  let longId := String.ofList (List.replicate 1024 'A')
  let wideTuple := .tuple (List.replicate 1100 (.structure longId []))
  return {
    base := {composites := {structures := [{id := longId, fields := []}]}}
    structures := [⟨"Demo.WideIgnore", [⟨"T", .type⟩], [], {}⟩]
    declarations := [identityDeclaration]
    exports := [genericExport "entry" ⟨0, 0⟩
      [.type (.structure "Demo.WideIgnore" [.type wideTuple])]
      [genericInput "value" (.structure "Demo.WideIgnore" [.type wideTuple])]]
  }

-- Bound encoded key bytes even when the normalized node count is within limits.
#guard messageContains
  (specialize canonicalKeyBudgetProgram "entry") "canonical generic identity key size"

private def effectfulGenericProgram : GProgram := {
  declarations := [{
    id := ⟨0, 0⟩
    name := "effectful"
    parameters := [⟨"T", .type⟩]
    values := [("value", .parameter "T")]
    result := .parameter "T"
    body := [.return (some (.effect .event "audit" (.ref "value")))]
    span := {file := "tests/generics/effects.lean", line := 12, column := 4}
  }]
  exports := [genericExport "entry" ⟨0, 0⟩ [.type .native] [genericInput "value" .native]]
}

-- Effects and declaration source spans survive generic conversion and analysis.
#guard match specialize effectfulGenericProgram "entry" with
  | .ok result => match result.program.declarations with
    | [declaration] => declaration.span == {file := "tests/generics/effects.lean", line := 12, column := 4} &&
      match declaration.body with
      | [.return (some (.effect .event "audit" (.ref "value")))] =>
        match Helpers.analyze result.program with
        | .ok summaries => summaries.any (fun summary => summary.effects.contains .event)
        | .error _ => false
      | _ => false
    | _ => false
  | .error _ => false

private def repeatedProgram : GProgram := {
  declarations := [
    {
      id := ⟨0, 0⟩
      name := "twice"
      parameters := [⟨"T", .type⟩]
      values := [("value", .parameter "T")]
      result := .parameter "T"
      body := [.return (some (.binary .add
        (.call ⟨0, 1⟩ [.type (.parameter "T")] [.ref "value"])
        (.call ⟨0, 1⟩ [.type (.parameter "T")] [.ref "value"])))]
    },
    identityDeclarationAt ⟨0, 1⟩
  ]
  exports := [genericExport "entry" ⟨0, 0⟩ [.type .native] [genericInput "value" .native]]
}

-- Repeated instantiations share a cache entry and exact generated call target.
#guard match specialize repeatedProgram "entry" with
  | .ok result => result.instances.length == 2 &&
    match result.program.exports, result.program.declarations with
    | [entry], declarations => match declarations.find? (·.id == entry.target) with
      | some declaration => match declaration.body with
        | [.return (some (.binary .add (.call leftName _) (.call rightName _)))] => leftName == rightName
        | _ => false
      | none => false
    | _, _ => false
  | .error _ => false

private def identityTwinsProgram : GProgram := {
  structures := [
    ⟨"Demo.EmptyA", [], [("value", .native)], {}⟩,
    ⟨"Demo.EmptyB", [], [("value", .native)], {}⟩
  ]
  declarations := [
    {
      id := ⟨0, 0⟩
      name := "useTwins"
      values := [
        ("left", .structure "Demo.EmptyA" []),
        ("right", .structure "Demo.EmptyB" [])
      ]
      result := .unit
      body := [
        .evaluate (.call ⟨0, 1⟩ [.type (.structure "Demo.EmptyA" [])] [.ref "left"]),
        .evaluate (.call ⟨0, 1⟩ [.type (.structure "Demo.EmptyB" [])] [.ref "right"]),
        .return none
      ]
    },
    identityDeclarationAt ⟨0, 1⟩
  ]
  exports := [genericExport "entry" ⟨0, 0⟩ [] [
    genericInput "left" (.structure "Demo.EmptyA" []),
    genericInput "right" (.structure "Demo.EmptyB" [])
  ]]
}

-- Distinct nominal arguments with identical layouts keep distinct exact targets.
#guard match specialize identityTwinsProgram "entry" with
  | .ok result => match result.instances.filter (·.key.declaration == ⟨0, 1⟩) with
    | [left, right] => left.key.arguments != right.key.arguments &&
        left.target != right.target && left.name != right.name &&
        match result.program.exports, result.program.declarations with
        | [entry], declarations => match declarations.find? (·.id == entry.target) with
          | some declaration => match declaration.body with
            | [.evaluate (.call leftName _), .evaluate (.call rightName _), .return none] =>
              leftName != rightName && [leftName, rightName].all fun name =>
                result.instances.any (fun item =>
                  item.key.declaration == ⟨0, 1⟩ && item.name == name)
            | _ => false
          | none => false
        | _, _ => false
    | _ => false
  | .error _ => false

private def zeroLayoutProgram : GProgram := {
  structures := [⟨"Demo.ZeroA", [], [], {}⟩, ⟨"Demo.ZeroB", [], [], {}⟩]
  declarations := [
    {
      id := ⟨0, 0⟩
      name := "instantiateZeroTypes"
      result := .unit
      body := [
        .evaluate (.call ⟨0, 1⟩ [.type (.structure "Demo.ZeroA" [])] []),
        .evaluate (.call ⟨0, 1⟩ [.type (.structure "Demo.ZeroB" [])] []),
        .return none
      ]
    },
    {
      id := ⟨0, 1⟩
      name := "ignoreType"
      parameters := [⟨"T", .type⟩]
      result := .unit
      body := [.return none]
    }
  ]
  exports := [genericExport "entry" ⟨0, 0⟩ []]
}

-- Empty layouts still retain separate nominal identity and exact call targets.
#guard match specialize zeroLayoutProgram "entry" with
  | .ok result => match result.instances.filter (·.key.declaration == ⟨0, 1⟩),
      result.program.composites.structures with
    | [left, right], [first, second] =>
      left.key.arguments != right.key.arguments && left.target != right.target &&
        left.name != right.name && first.id != second.id
    | _, _ => false
  | .error _ => false

private def recursiveProgram : GProgram := {
  declarations := [{
    id := ⟨0, 0⟩
    name := "growing"
    parameters := [⟨"T", .type⟩]
    values := [("value", .parameter "T")]
    result := .parameter "T"
    body := [.return (some (.call ⟨0, 0⟩
      [.type (.tuple [.parameter "T"])] [.ref "value"]))]
  }]
  exports := [genericExport "entry" ⟨0, 0⟩ [.type .native] [genericInput "value" .native]]
}
#guard messageContains (specialize recursiveProgram "entry") "specialization cycle"

private def recursiveAliasProgram : GProgram := {
  aliases := [⟨"Demo.Loop", [], .alias "Demo.Loop" [], {}⟩]
  declarations := [identityDeclaration]
  exports := [genericExport "entry" ⟨0, 0⟩ [.type (.alias "Demo.Loop" [])]
    [genericInput "value" (.alias "Demo.Loop" [])]]
}
#guard messageContains (specialize recursiveAliasProgram "entry") "type-alias cycle"

private def recursiveStructureProgram : GProgram := {
  structures := [⟨"Demo.Loop", [], [("next", .structure "Demo.Loop" [])], {}⟩]
  declarations := [identityDeclaration]
  exports := [genericExport "entry" ⟨0, 0⟩ [.type (.structure "Demo.Loop" [])]
    [genericInput "value" (.structure "Demo.Loop" [])]]
}
#guard messageContains (specialize recursiveStructureProgram "entry") "type cycle"

private def largeCloneProgram : GProgram := {
  declarations := [{
    id := ⟨0, 0⟩
    name := "large"
    parameters := []
    values := []
    result := .unit
    body := (List.replicate 16 (.evaluate (.native 0)) : List GStmt) ++ [.return none]
  }]
  exports := [genericExport "entry" ⟨0, 0⟩ []]
}

-- GEN-RESOURCE: fail before body substitution when the budget is too small.
#guard messageContains (specializeWithLimits {maxExpandedNodes := 8} largeCloneProgram "entry")
  "expanded nodes before substitution"

private def multipleStructProgram : GProgram := {
  structures := [
    ⟨"Demo.First", [], [("value", .native)], {}⟩,
    ⟨"Demo.Second", [], [("value", .native)], {}⟩
  ]
  declarations := [identityDeclaration]
  exports := [genericExport "entry" ⟨0, 0⟩
    [.type (.tuple [.structure "Demo.First" [], .structure "Demo.Second" []])]
    [genericInput "value" (.tuple [.structure "Demo.First" [], .structure "Demo.Second" []])]]
}
#guard messageContains
  (specializeWithLimits {maxTypeSpecializations := 1} multipleStructProgram "entry")
  "struct specialization count"

private def privateIdentity (release : Bool) : GProgram :=
  identityProgram .native .private release

-- Private generic inputs still require disclosure on the public result.
#guard match specialize (privateIdentity false) "entry" with
  | .ok result => messageContains (ComponentDisclosure.checkProgram result.program result.exportName)
      "undisclosed private"
  | .error _ => false
#guard match specialize (privateIdentity true) "entry" with
  | .ok result => ComponentDisclosure.checkProgram result.program result.exportName |>.isOk
  | .error _ => false

private def privateOpaqueIdentity (release : Bool) : GProgram :=
  identityProgram .opaqueBytes .private release

#guard match specialize (privateOpaqueIdentity false) "entry" with
  | .ok result => messageContains (Helpers.compile result.program result.exportName)
      "undisclosed private parameter 'value'"
  | .error _ => false
#guard match specialize (privateOpaqueIdentity true) "entry" with
  | .ok result => (Helpers.compile result.program result.exportName).isOk
  | .error _ => false

private def providerProgram (release : Bool) (type : GType := .native) : GProgram := {
  declarations := [{
    id := ⟨0, 0⟩
    name := "provider"
    parameters := [⟨"T", .type⟩]
    values := []
    result := .parameter "T"
    body := [.return (some (
      let witness : GTerm := .witness "attestation" (.parameter "T")
      if release then .disclose {} witness else witness))]
  }]
  exports := [genericExport "entry" ⟨0, 0⟩ [.type type]]
}

-- Provider witnesses remain private through generic specialization.
#guard match specialize (providerProgram false) "entry" with
  | .ok result => messageContains (ComponentDisclosure.checkProgram result.program result.exportName)
      "undisclosed private provider result"
  | .error _ => false
#guard match specialize (providerProgram true) "entry" with
  | .ok result => match Helpers.compile result.program result.exportName with
    | .ok circuit => match circuit.privateOrigins, circuit.inputs with
      | [(_, origin)], inputs => origin == PrivateOriginKind.provider &&
          inputs.any (·.visibility == .private)
      | _, _ => false
    | .error _ => false
  | .error _ => false

#guard match specialize (providerProgram true (.uint (.literal 255))) "entry" with
  | .ok result => result.signatureArtifact.declarations.any (fun declaration =>
      declaration.witnesses == [{name := "attestation", type := .uint "255"}])
  | .error _ => false

-- Typed witness signatures survive the standalone versioned JSON roundtrip.
#guard match specialize (providerProgram true) "entry" with
  | .ok result =>
    let artifact := result.signatureArtifact
    match parseSignatureArtifact (Lean.toJson artifact) with
    | .ok parsed => parsed == artifact && parsed.declarations.any (fun declaration =>
        declaration.witnesses == [{name := "attestation", type := .native}])
    | .error _ => false
  | .error _ => false

#guard match specialize {
    base := {scopes := [{id := 9007199254740993}]},
    declarations := [{
      id := ⟨9007199254740993, 0⟩, name := "natural", parameters := [⟨"N", .natural⟩],
      values := [("value", .uint (.parameter "N"))],
      result := .uint (.parameter "N"), body := [.return (some (.ref "value"))]
    }],
    exports := [genericExport "entry" ⟨9007199254740993, 0⟩
      [.natural (.literal 1606938044258990275541962092341162602522202993782792835301376)]
      [genericInput "value"
        (.uint (.literal 1606938044258990275541962092341162602522202993782792835301376))]]
  } "entry" with
  | .ok result =>
    let json := (Lean.toJson result.signatureArtifact).compress
    (json.splitOn "\"sourceScope\":\"9007199254740993\"").length > 1 &&
      (json.splitOn "\"sourceOrdinal\":\"0\"").length > 1 &&
      (json.splitOn "\"value\":\"1606938044258990275541962092341162602522202993782792835301376\"").length > 1
  | .error _ => false
#guard match parseSignatureArtifact (Lean.Json.mkObj [
    ("schemaVersion", Lean.toJson (2 : Nat)), ("sourceExport", Lean.toJson ("entry" : String)),
    ("declarations", Lean.toJson ([] : List SpecializedSignature))]) with
  | .error _ => true
  | .ok _ => false
#guard match parseSignatureArtifactText (String.ofList
    (List.replicate 513 '[' ++ List.replicate 513 ']')) with
  | .error _ => true
  | .ok _ => false

-- A Unit specialization retains one logical argument and no physical fields.
#guard match specialize (identityProgram .unit .private) "entry" with
  | .ok result =>
    match Helpers.compile result.program result.exportName with
    | .ok circuit => circuit.inputs.isEmpty && circuit.outputs.isEmpty &&
      result.program.exports.any (fun entry =>
        entry.compositeInputs.any (fun input => input.type == .unit))
    | .error _ => false
  | .error _ => false

end Noctium.GenericSpecializationTests
