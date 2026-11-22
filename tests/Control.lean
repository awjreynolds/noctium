import Noctium.Control
open Noctium Noctium.Helpers

private def accepted (value : Except α β) : Bool := match value with | .ok _ => true | _ => false
private def errorContains (value : Except Diagnostic α) (text : String) : Bool :=
  match value with | .error d => (d.message.splitOn text).length > 1 | _ => false
private def program (body : List Statement) (result : ResultType := .scalar .native) : Program := {
  declarations := [{id := ⟨0, 0⟩, name := "main", result, body}]
  exports := [{name := "main", target := ⟨0, 0⟩}]
}
private def ctx : EvalContext := {modulus := Field.modulus, poseidon2 := fun _ _ _ => .error "hash unavailable"}
private def returned (value : Term) : List Statement := [.return (some value)]

-- CF-TYPE-BOTH: inactive branches are still checked, including after returns.
#guard errorContains (analyze (program [.branch (.bool false) [.assert (.native 1)] [], .return (some (.native 0))])) "assertion requires Bool"
#guard errorContains (analyze (program (returned (.ite (.bool true) (.native 1) (.ref "missing"))))) "unknown helper value"
#guard errorContains (analyze (program [.branch (.native 0) [] [], .return (some (.native 0))])) "condition requires Bool"
-- CF-TYPE-JOIN requires a common type, including unit/scalar incompatibility.
#guard errorContains (analyze (program (returned (.ite (.bool true) (.native 1) (.bool false))))) "common type"
#guard errorContains (analyze (program (returned (.ite (.bool true) .unit (.native 1))))) "common type"
#guard accepted (analyze (program (returned (.ite (.bool false) (.uint 3 2) (.uint 7 4))) (.scalar (.uint 7))))

-- CF-ASSERT-INACTIVE and CF-CAST-INACTIVE preserve type checks but skip execution.
private def inactive := program [.branch (.bool false) [
  .assert (.bool false), .evaluate (.cast (.uint 0) (.native 1))] [], .return (some (.native 9))]
#guard match trace inactive ctx "main" [] with
  | .ok (some value, events) => value.number == 9 && events.isEmpty
  | _ => false
#guard accepted (Control.compile inactive "main")
#guard accepted (Helpers.compile inactive "main")

-- CF-SHORT-AND / CF-SHORT-OR, with effect fixtures solely for reference order.
#guard match trace (program (returned (.andThen (.bool false) (.effect .witness "inactive" (.bool true)))) (.scalar .bool)) ctx "main" [] with
  | .ok (some value, events) => value.number == 0 && events.isEmpty
  | _ => false
#guard match trace (program (returned (.orElse (.bool true) (.effect .witness "inactive" (.bool false)))) (.scalar .bool)) ctx "main" [] with
  | .ok (some value, events) => value.number == 1 && events.isEmpty
  | _ => false
#guard match trace (program (returned (.ite (.bool true) (.effect .witness "yes" (.native 2)) (.effect .witness "no" (.native 3))))) ctx "main" [] with
  | .ok (some value, events) => value.number == 2 && events == ["yes"]
  | _ => false
-- Eager select retains its separate behavior.
#guard match trace (program (returned (.select (.bool true) (.effect .witness "yes" (.native 2)) (.effect .witness "no" (.native 3))))) ctx "main" [] with
  | .ok (_, events) => events == ["yes", "no"]
  | _ => false

-- FN-PURE-INACTIVE includes calls to an impure helper inside a literal-false branch.
private def inactiveImpure : Program := {
  declarations := [
    {id := ⟨0, 0⟩, name := "main", declaredPure := true, body := [.branch (.bool false) [.evaluate (.call "impure" [])] []]},
    {id := ⟨0, 1⟩, name := "impure", body := [.evaluate (.witness "registered" .native)]}]
  exports := [{name := "main", target := ⟨0, 0⟩}]
}
#guard errorContains (analyze inactiveImpure) "transitive effects"

private def guarded (condition : Term) (yes no : Term) : Program := {
  declarations := [{id := ⟨0, 0⟩, name := "main", parameters := [⟨"secret", .bool⟩], result := .scalar .native, body := [.branch condition (returned yes) (returned no)]}]
  exports := [{name := "main", target := ⟨0, 0⟩, inputs := [{name := "secret", ty := .bool, visibility := .private}]}]
}
-- NL-DISC-GUARD-CONSTANT selects only the active path for disclosure.
#guard accepted (Control.compile (guarded (.bool false) (.witness "inactive" .native) (.native 3)) "main")
-- NL-DISC-GUARD-OUTPUT and DISC-PAYLOAD-ONLY reject private control even for disclosed payloads.
#guard errorContains (Control.compile (guarded (.ref "secret") (.native 1) (.native 2)) "main") "private control"
#guard errorContains (Control.compile (guarded (.ref "secret") (.disclose {} (.native 1)) (.disclose {} (.native 2))) "main") "private control"
-- DISC-GUARD explicitly releases the condition before branching.
#guard accepted (Control.compile (guarded (.disclose {} (.ref "secret")) (.native 1) (.native 2)) "main")
-- NL-DISC-NESTED retains accumulated outer guards through nested branches.
#guard errorContains (Control.compile {declarations := [{id := ⟨0, 0⟩, name := "main", parameters := [⟨"secret", .bool⟩], result := .scalar .native, body := [.branch (.ref "secret") [.branch (.bool true) (returned (.native 1)) (returned (.native 2))] (returned (.native 3))]}], exports := [{name := "main", target := ⟨0, 0⟩, inputs := [{name := "secret", ty := .bool, visibility := .private}]}]} "main") "private control"
-- A private early return also controls whether the later return executes.
#guard errorContains (Control.compile {declarations := [{id := ⟨0, 0⟩, name := "main", parameters := [⟨"secret", .bool⟩], result := .scalar .native, body := [.branch (.ref "secret") (returned (.native 1)) [], .return (some (.native 2))]}], exports := [{name := "main", target := ⟨0, 0⟩, inputs := [{name := "secret", ty := .bool, visibility := .private}]}]} "main") "private control"
#guard errorContains (Control.compileWithLimits {maxExecutionSteps := 131073} inactive "main") "hard policy"

#guard errorContains (analyze (program (returned (.andThen (.bool false) (.native 1))) (.scalar .bool))) "operands require Bool"
#guard errorContains (analyze (program (returned (.orElse (.bool true) (.native 1))) (.scalar .bool))) "operands require Bool"
#guard errorContains (analyze (program [.branch (.bool false) [.evaluate (.cast (.uint (ScalarPolicy.maxUint + 1)) (.native 0))] [], .return (some (.native 0))])) "unsigned type exceeds"
#guard accepted (Control.compile (program (returned (.ite (.bool true) (.uint 3 2) (.uint 7 4))) (.scalar (.uint 7))) "main")
#guard errorContains (Control.compile (program (returned (.witness "privateResult" .native))) "main") "undisclosed private"
#guard accepted (Control.compile (program (returned (.disclose {} (.witness "privateResult" .native)))) "main")
#guard errorContains (Control.compile (program [.branch (.bool false) [.evaluate (.witness "bad name" .native)] [], .return (some (.native 0))]) "main") "invalid control witness"
#guard errorContains (Control.compile (program [.branch (.bool false) [.stage "store" "../bad" (.scalar .native) (.native 1)] [], .return (some (.native 0))]) "main") "invalid private stage"

-- Constant-aware disclosure must retain the static wider conditional type for overloads.
#guard accepted (Control.compile {
  declarations := [
    {id := ⟨0, 0⟩, name := "main", result := .scalar .native, body := [.return (some (.call "f" [.ite (.bool true) (.uint 3 2) (.uint 7 4)]))]},
    {id := ⟨0, 1⟩, name := "f", parameters := [⟨"x", .uint 3⟩], result := .scalar .native, body := [.return (some (.native 3))]},
    {id := ⟨0, 2⟩, name := "f", parameters := [⟨"x", .uint 7⟩], result := .scalar .native, body := [.return (some (.native 7))]}]
  exports := [{name := "main", target := ⟨0, 0⟩}]
} "main")

#guard accepted (Control.compile (program [.evaluate (.ite (.bool true) .unit .unit)] .unit) "main")
#guard accepted (Control.compile (guarded (.andThen (.bool true) (.bool false)) (.witness "inactive" .native) (.native 3)) "main")
#guard errorContains (Control.compile {
  declarations := [{id := ⟨0, 0⟩, name := "main", parameters := [⟨"public", .bool⟩, ⟨"secret", .bool⟩], result := .scalar .native, body := [
    .branch (.ref "public") [.branch (.ref "secret") (returned (.native 1)) []] [], .return (some (.native 2))]}]
  exports := [{name := "main", target := ⟨0, 0⟩, inputs := [
    {name := "public", ty := .bool, visibility := .public}, {name := "secret", ty := .bool, visibility := .private}]}]
} "main") "private control"

-- Unit has no public payload slot. Its identical successful returns reveal no scalar value.
#guard accepted (Control.compile {
  declarations := [{id := ⟨0, 0⟩, name := "main", parameters := [⟨"secret", .bool⟩], body := [
    .branch (.ref "secret") [.return none] [.return none]]}]
  exports := [{name := "main", target := ⟨0, 0⟩, inputs := [{name := "secret", ty := .bool, visibility := .private}]}]
} "main")

#guard accepted (Control.compile {
  declarations := [{id := ⟨0, 0⟩, name := "main", parameters := [⟨"secret", .bool⟩], result := .scalar .native, body := [
    .branch (.ref "secret") [.branch (.eq (.native 0) (.native 1)) (returned (.native 1)) []] [], .return (some (.native 2))]}]
  exports := [{name := "main", target := ⟨0, 0⟩, inputs := [{name := "secret", ty := .bool, visibility := .private}]}]
} "main")

-- Metadata never amplifies unbounded spans/identities before serialization.
private def hugeMetadata := String.ofList (List.replicate 1025 'x')
#guard errorContains (Control.compile {program [] .unit with declarations := [
  {id := ⟨0, 0⟩, name := "main", span := {file := hugeMetadata}}]} "main") "source-span metadata"
#guard errorContains (Control.compile {program [] .unit with scopes := [{id := 18446744073709551616}]} "main") "identity metadata"
#guard errorContains (Control.compile {program [] .unit with declarations := [
  {id := ⟨0, 18446744073709551616⟩, name := "main"}]} "main") "identity metadata"
#guard match Control.compile {program [] .unit with declarations := [
  {id := ⟨0, 0⟩, name := "main", span := {file := hugeMetadata}}]} "main" with
  | .error diagnostic => diagnostic.span.file.isEmpty && diagnostic.message.length < 128
  | _ => false
-- Empty unit plan: two 512-byte records plus escaped-name allowance 6*(4+4).
#guard accepted (Control.compileWithLimits {} (program [] .unit) "main" 1072)
#guard errorContains (Control.compileWithLimits {} (program [] .unit) "main" 1071) "preflight byte"
#guard errorContains (Control.compileWithLimits {} (program [] .unit) "main" 1048577) "hard policy"
#guard errorContains (Helpers.resolve {} 0 hugeMetadata []) "metadata text"
#guard errorContains (Helpers.infer {} 0 [] {file := hugeMetadata} (.native 0)) "source-span metadata"
#guard match Helpers.prepareWithLimits {} {} with
  | .ok prepared => errorContains (prepared.resolve 0 hugeMetadata [] {}) "metadata text"
  | _ => false
