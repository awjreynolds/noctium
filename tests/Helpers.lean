import Noctium.Helpers
import Noctium.Backend.Zkir
open Noctium Noctium.Helpers

private def accepted (value : Except α β) : Bool := match value with | .ok _ => true | _ => false
private def rejected (value : Except α β) : Bool := !accepted value
private def errorContains (value : Except Diagnostic α) (text : String) : Bool :=
  match value with | .error d => (d.message.splitOn text).length > 1 | _ => false
private def ctx : EvalContext := {modulus := Field.modulus, poseidon2 := fun _ _ _ => .error "hash unavailable"}
private def exported (declarations : List Declaration) (target : DeclarationId := ⟨0, 0⟩) : Program :=
  {declarations, exports := [{name := "main", target}]}

-- FN-RETURN-UNIT: explicit unit and fall-through agree. Invalid return types fail.
#guard accepted (compile (exported [{id := ⟨0, 0⟩, name := "unit"}]) "main")
#guard accepted (compile (exported [{id := ⟨0, 0⟩, name := "unit", body := [.return none]}]) "main")
#guard errorContains (analyze (exported [{id := ⟨0, 0⟩, name := "missing", result := .scalar .native}])) "fall-through"
#guard errorContains (analyze (exported [{id := ⟨0, 0⟩, name := "wrong", result := .scalar .native, body := [.return (some (.bool true))]}])) "return type mismatch"
#guard errorContains (analyze (exported [{id := ⟨0, 0⟩, name := "wrong", result := .scalar .native, body := [.return none]}])) "return type mismatch"

private def overloadProgram : Program := {
  scopes := [{id := 0}, {id := 1, parent := some 0}]
  declarations := [
    {id := ⟨0, 0⟩, name := "f", parameters := [⟨"x", .native⟩]},
    {id := ⟨1, 0⟩, name := "f", parameters := [⟨"x", .bool⟩]}]
}
private def selected (value : Except Diagnostic Declaration) : Option DeclarationId :=
  value.toOption.map (·.id)
-- FN-OVERLOAD-INNER, FN-OVERLOAD-FALLBACK, FN-OVERLOAD-AMBIGUOUS.
#guard selected (resolve overloadProgram 1 "f" [.scalar .bool]) == some ⟨1, 0⟩
#guard selected (resolve overloadProgram 1 "f" [.scalar (.uint 3)]) == some ⟨0, 0⟩
#guard errorContains (resolve {overloadProgram with declarations := overloadProgram.declarations ++ [
  {id := ⟨1, 1⟩, name := "f", parameters := [⟨"x", .bool⟩]}]} 1 "f" [.scalar .bool]) "ambiguous"
#guard errorContains (resolve {overloadProgram with scopes := [{id := 0}, {id := 1, parent := some 0, values := ["f"]}]} 1 "f" [.scalar .native]) "hidden"
#guard errorContains (resolve {overloadProgram with declarations := [
  {id := ⟨0, 0⟩, name := "f", parameters := [⟨"x", .uint 7⟩]},
  {id := ⟨0, 1⟩, name := "f", parameters := [⟨"x", .uint 3⟩]}]} 0 "f" [.scalar (.uint 1)]) "ambiguous"

-- FN-RECURSION-DIRECT and FN-RECURSION-MUTUAL include syntax after return.
#guard errorContains (analyze (exported [{id := ⟨0, 0⟩, name := "f", body := [.evaluate (.call "f" [])]}])) "recursive"
#guard errorContains (analyze (exported [
  {id := ⟨0, 0⟩, name := "f", body := [.evaluate (.call "g" [])]},
  {id := ⟨0, 1⟩, name := "g", body := [.return none, .evaluate (.call "f" [])]}])) "recursive"
#guard accepted (analyze (exported [
  {id := ⟨0, 0⟩, name := "used"},
  {id := ⟨0, 1⟩, name := "unused", body := [.evaluate (.call "unused" [])]}]))

private def effectProgram (kind : EffectKind) (declaredPure := false) : Program := exported [
  {id := ⟨0, 0⟩, name := "outer", declaredPure, body := [.evaluate (.call "inner" [])]},
  {id := ⟨0, 1⟩, name := "inner", body := [.evaluate (.effect kind "effect" .unit)]}]
-- FN-PURE-INDIRECT. Each external category survives transitive summarization.
#guard ([EffectKind.witness, .privateState, .ledgerRead, .ledgerWrite, .event, .asset, .crossCall]).all fun kind =>
  errorContains (analyze (effectProgram kind true)) "transitive effects"
#guard ([EffectKind.witness, .privateState, .ledgerRead, .ledgerWrite, .event, .asset, .crossCall]).all fun kind =>
  match analyze (effectProgram kind) with
  | .ok summaries => summaries.any (fun s => s.id == ⟨0, 0⟩ && s.effects.contains kind)
  | _ => false
#guard errorContains (compile (effectProgram .ledgerRead) "main") "capability unavailable"
#guard errorContains (analyze (exported [{id := ⟨0, 0⟩, name := "syntaxPure", declaredPure := true, body := [.return none, .evaluate (.effect .event "after-return" .unit)]}])) "transitive effects"
-- FN-PURE-INACTIVE is registered for CF-01, which introduces branch syntax.

private def traceProgram : Program := exported [
  {id := ⟨0, 0⟩, name := "main", result := .scalar .native, body := [.return (some (.call "combine" [
    .effect .witness "left" (.native 2), .effect .privateState "right" (.native 7)]))]},
  {id := ⟨0, 1⟩, name := "combine", parameters := [⟨"a", .native⟩, ⟨"unused", .native⟩],
   result := .scalar .native, body := [.evaluate (.effect .event "body" .unit),
     .return (some (.binary .add (.ref "a") (.ref "a")))]}]
-- FN-ARGS-ORDER: left to right, unused right argument still executes, a used twice runs once.
#guard match trace traceProgram ctx "main" [] with
  | .ok (some value, events) => value.number == 4 && events == ["left", "right", "body"]
  | _ => false
#guard errorContains (compile traceProgram "main") "capability unavailable"

private def identity (release := false) : Declaration := {
  id := ⟨0, 0⟩, name := "id", parameters := [⟨"x", .native⟩], result := .scalar .native
  body := [.return (some (if release then .disclose {} (.ref "x") else .ref "x"))]
}
private def privateProgram (release := false) : Program := {
  declarations := [identity release]
  exports := [{name := "private", target := ⟨0, 0⟩, inputs := [{name := "secret", ty := .native, visibility := .private}]}]
}
-- DISC-HELPER: mandatory DF-00 sees the actual private argument through a bound parameter.
#guard errorContains (compile (privateProgram false) "private") "undisclosed private"
#guard accepted (compile (privateProgram true) "private")
#guard accepted ((compile (privateProgram true) "private").bind Backend.Zkir.lowerCircuit)

private def unusedFailure : Program := exported [
  {id := ⟨0, 0⟩, name := "main", result := .scalar .native, body := [.return (some (.call "ignore" [.cast (.uint 0) (.native 1)]))]},
  {id := ⟨0, 1⟩, name := "ignore", parameters := [⟨"unused", .uint 0⟩], result := .scalar .native, body := [.return (some (.native 9))]}]
#guard match compile unusedFailure "main" with
  | .ok circuit => rejected (circuit.run ctx [])
  | _ => false
#guard rejected ((compile unusedFailure "main").bind Backend.Zkir.lowerCircuit)

private def noCapture : Program := {
  declarations := [{id := ⟨0, 0⟩, name := "add", parameters := [⟨"a", .native⟩, ⟨"b", .native⟩], result := .scalar .native, body := [.return (some (.binary .add (.ref "a") (.ref "b")))]}]
  exports := [{name := "capture", target := ⟨0, 0⟩, inputs := [
    {name := "first", ty := .native, visibility := .public},
    {name := "$helper0", ty := .native, visibility := .public}]}]
}
#guard match compile noCapture "capture" with
  | .ok circuit => match circuit.run ctx [("first", .native 2), ("$helper0", .native 7)] with
    | .ok values => values.lookup "result" == some (.native 9)
    | _ => false
  | _ => false
#guard accepted ((compile noCapture "capture").bind Backend.Zkir.lowerCircuit)

#guard errorContains (analyze {noCapture with exports := noCapture.exports ++ noCapture.exports}) "duplicate monomorphic"
#guard errorContains (analyze {noCapture with declarations := noCapture.declarations ++ noCapture.declarations}) "duplicate helper declaration"
#guard errorContains (analyze {noCapture with exports := [{name := "bad", target := ⟨0, 0⟩}]}) "signature mismatch"

-- Assertions and bound casts remain separately visible in the transitive summary.
#guard match analyze (exported [{id := ⟨0, 0⟩, name := "fallible", body := [
  .assert (.bool true), .evaluate (.cast (.uint 3) (.native 2))]}]) with
  | .ok [summary] => summary.effects.contains .assertion && summary.effects.contains .fallibleCast
  | _ => false

private def asserted : Circuit := {
  name := "nestedAssertion"
  inputs := [{name := "value", ty := .native, visibility := .public}]
  outputs := [{name := "result", ty := .native, value := .assertE (.eq (.ref "value") (.native 9)) (.ref "value")}]
}
private def removeAssertions (program : Lean.Json) : Except String Lean.Json := do
  let instructions ← (← program.getObjVal? "instructions").getArr?
  let fields ← program.getObj?
  pure (Lean.Json.mkObj (fields.toList.map fun (key, value) =>
    (key, if key == "instructions" then Lean.Json.arr (instructions.filter fun instruction =>
      ((instruction.getObjVal? "op").bind Lean.Json.getStr?).toOption != some "assert") else value)))
#guard accepted (Backend.Zkir.lowerCircuit asserted)
#guard match Backend.Zkir.lowerCircuit asserted, Backend.Native.expectedCircuit asserted with
  | .ok program, .ok expected => match removeAssertions program with
    | .ok changed => rejected (Backend.Native.validate expected changed)
    | _ => false
  | _, _ => false

-- A compatible inner declaration wins even when an outer declaration also matches.
#guard selected (resolve {overloadProgram with declarations := [
  {id := ⟨0, 0⟩, name := "f", parameters := [⟨"x", .uint 3⟩]},
  {id := ⟨1, 0⟩, name := "f", parameters := [⟨"x", .uint 7⟩]}]} 1 "f" [.scalar (.uint 1)]) == some ⟨1, 0⟩

private def unitCall : Program := exported [
  {id := ⟨0, 0⟩, name := "main", result := .scalar .native, body := [
    .evaluate (.call "noop" []), .return (some (.binary .add (.call "two" []) (.native 1)))]},
  {id := ⟨0, 1⟩, name := "noop", body := [.assert (.bool true)]},
  {id := ⟨0, 2⟩, name := "two", result := .scalar .native, body := [
    .return (some (.native 2)), .evaluate (.cast (.uint 0) (.native 1))]}]
#guard match compile unitCall "main" with
  | .ok circuit => match circuit.run ctx [] with
    | .ok values => values.lookup "result" == some (.native 3)
    | _ => false
  | _ => false
#guard accepted ((compile unitCall "main").bind Backend.Zkir.lowerCircuit)

private def emptyAggregateType : Types.CompositeType := .vector 0 (.scalar .native)
private def emptyAggregateReturn : Program := {
  declarations := [{
    id := ⟨0, 0⟩
    name := "empty"
    result := .composite emptyAggregateType
    body := [.return (some (.composite emptyAggregateType []))]
  }]
  exports := [{name := "empty", target := ⟨0, 0⟩}]
}

-- Logical empty aggregates retain a return view without physical Native fields.
#guard match Helpers.compileEntrypoint emptyAggregateReturn "empty" with
  | .ok entry => entry.returns.isEmpty && match entry.returnViews with
    | [view] => view.type == .vector 0 (.scalar .native) && view.fields.isEmpty
    | _ => false
  | .error _ => false

private def oversizedAggregateType : Types.CompositeType := .vector 257 (.scalar .native)
private def oversizedAggregateReturn : Program := {
  declarations := [{
    id := ⟨0, 0⟩
    name := "oversized"
    result := .composite oversizedAggregateType
    body := [.return (some (.composite oversizedAggregateType (List.replicate 257 (.native 0))))]
  }]
  exports := [{name := "oversized", target := ⟨0, 0⟩}]
}

#guard errorContains (Helpers.compileEntrypoint oversizedAggregateReturn "oversized")
  "entrypoint return field limit"

-- Exported inputs named result do not collide with the generated public return.
#guard accepted (compile {noCapture with exports := [{name := "capture", target := ⟨0, 0⟩, inputs := [
  {name := "result", ty := .native, visibility := .public},
  {name := "other", ty := .native, visibility := .public}]}]} "capture")

private def doubling (depth : Nat) : Program := {
  declarations := (List.range (depth + 1)).map fun n => {
    id := ⟨0, n⟩
    name := s!"f{n}"
    body := if n == 0 then [] else [
      .evaluate (.call s!"f{n - 1}" []), .evaluate (.call s!"f{n - 1}" [])]
  }
  exports := [{name := "doubling", target := ⟨0, depth⟩}]
}

private def boundaryLimits : Limits := {
  maxDeclarations := 2, maxScopes := 1, maxExports := 1, maxSourceNodes := 4
  maxCallDepth := 2, maxAnalysisSteps := 3, maxExpandedNodes := 30
  maxExpandedDepth := 21, maxExecutionSteps := 10
}

-- These exact boundaries include both call sites, even though they share a callee.
#guard accepted (compileWithLimits boundaryLimits (doubling 1) "doubling")
#guard accepted (traceWithLimits boundaryLimits (doubling 1) ctx "doubling" [])
#guard errorContains (compileWithLimits {boundaryLimits with maxExpandedNodes := 29} (doubling 1) "doubling") "expanded nodes"
#guard errorContains (compileWithLimits {boundaryLimits with maxExpandedDepth := 20} (doubling 1) "doubling") "expanded depth"
#guard errorContains (compileWithLimits {boundaryLimits with maxExecutionSteps := 9} (doubling 1) "doubling") "lowering steps"
#guard errorContains (traceWithLimits {boundaryLimits with maxExecutionSteps := 9} (doubling 1) ctx "doubling" []) "evaluation steps"
#guard errorContains (analyzeWithLimits {boundaryLimits with maxSourceNodes := 3} (doubling 1)) "source nodes"
#guard errorContains (analyzeWithLimits {boundaryLimits with maxDeclarations := 1} (doubling 1)) "declarations"
#guard errorContains (analyzeWithLimits {boundaryLimits with maxScopes := 0} (doubling 1)) "scopes"
#guard errorContains (analyzeWithLimits {boundaryLimits with maxCallDepth := 1} (doubling 1)) "call depth"
#guard errorContains (analyzeWithLimits {boundaryLimits with maxAnalysisSteps := 2} (doubling 1)) "call analysis steps"

-- A compact 13-declaration DAG is rejected before constructing its exponential AST.
#guard errorContains (compile (doubling 12) "doubling") "expanded nodes"
#guard errorContains (trace (doubling 12) ctx "doubling" []) "expanded nodes"
-- Memoization needs one root visit and two edge visits per level, rather than 2^n visits.
#guard accepted (analyzeWithLimits {maxAnalysisSteps := 21} (doubling 10))
#guard errorContains (analyzeWithLimits {maxAnalysisSteps := 20} (doubling 10)) "call analysis steps"

private def nestedCasts (depth : Nat) : Term :=
  Nat.rec (.native 1) (fun _ term => .cast .native term) depth
#guard accepted (inferWithLimits {maxSourceDepth := 8} {} 0 [] {} (nestedCasts 7))
#guard errorContains (inferWithLimits {maxSourceDepth := 8} {} 0 [] {} (nestedCasts 8)) "source depth"
#guard errorContains (inferWithLimits {maxSourceNodes := 7} {} 0 [] {} (nestedCasts 7)) "source nodes"
#guard errorContains (resolve {scopes := [{id := 0, parent := some 0}]} 0 "missing" []) "scope cycle"

private def raisedPolicies : List Limits := [
  {maxDeclarations := 257}, {maxScopes := 257}, {maxExports := 257},
  {maxParameters := 65}, {maxSourceNodes := 16385}, {maxSourceDepth := 129},
  {maxCallDepth := 65}, {maxAnalysisSteps := 65537}, {maxExpandedNodes := 65537},
  {maxExpandedDepth := 257}, {maxExecutionSteps := 131073}]
-- Budget APIs permit tightening only. Every field is checked even for empty source.
#guard raisedPolicies.all fun limits => errorContains (analyzeWithLimits limits {}) "hard policy"
#guard errorContains (compileWithLimits {maxExpandedNodes := 200000} (doubling 12) "doubling") "hard policy"
#guard errorContains (inferWithLimits {maxExpandedNodes := 65537} {} 0 [] {} (.native 1)) "hard policy"
#guard errorContains (resolveWithLimits {maxExpandedNodes := 65537} {} 0 "missing" []) "hard policy"
#guard errorContains (checkDeclarationWithLimits {maxExpandedNodes := 65537} {} {id := ⟨0, 0⟩, name := "empty"}) "hard policy"
#guard errorContains (traceWithLimits {maxExpandedNodes := 65537} (doubling 0) ctx "doubling" []) "hard policy"
