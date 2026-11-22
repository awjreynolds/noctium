import Noctium.Frontend

open scoped Noctium
open Noctium Noctium.Helpers

def finiteRangeProgram : Program := {
  ledger := [{name := "total", kind := .cell .native}]
  witnesses := [{
    name := "step"
    operation := "noctium.range-step.v1"
    capability := "step"
    parameters := [
      {name := "index", type := .scalar .native},
      {name := "before", type := .scalar .native}]
    result := .scalar .native}]
  declarations := [{
    id := ⟨0, 0⟩
    name := "update"
    parameters := [⟨"enabled", .bool⟩, ⟨"expected", .native⟩]
    result := .scalar .native
    body := [
      .branch (.disclose {} (.ref "enabled")) [
        .forRange "index" 1 4 [
          .readCell "total" "before" .native,
          .bind "delta" (.scalar .native)
            (.witnessCall "range-step" "step" [.ref "index", .ref "before"]),
          .writeCell "total" .native
            (.disclose {} (.binary .add (.ref "before") (.ref "delta"))),
          .stage "private" "loop/last" (.scalar .native) (.ref "delta")]] [],
      .readCell "total" "after" .native,
      .assert (.eq (.ref "after") (.ref "expected")),
      .return (some (.ref "after"))]}]
  exports := [{name := "update", target := ⟨0, 0⟩, inputs := [
    {name := "enabled", ty := .bool, visibility := .private},
    {name := "expected", ty := .native, visibility := .public}]}]
}

noctium_contract FiniteRangeWitness where
  cell total : Native
  entry update from finiteRangeProgram entry "update" end
end

private def loopProgram (start stop : Nat) (body : List Statement) : Program := {
  declarations := [{
    id := ⟨0, 0⟩, name := "main", result := .unit,
    body := [.forRange "index" start stop body, .return none]}]
  exports := [{name := "main", target := ⟨0, 0⟩}]
}

#guard (Helpers.compile (loopProgram 0 0 [.assert (.bool Bool.false)]) "main").isOk
#guard (Helpers.compileWithLimits {maxExecutionSteps := 128}
  (loopProgram 0 8 []) "main").isOk
#guard (Helpers.compile (loopProgram (2^248-2) (2^248-1) []) "main").isOk
#guard !(Helpers.compile (loopProgram 0 (2^248) []) "main").isOk
#guard !(Helpers.compile (loopProgram 2 1 []) "main").isOk
#guard (Helpers.prepareProgramWithLimits {} (loopProgram 0 1024 [])).isOk
#guard !(Helpers.compile (loopProgram 0 1025 []) "main").isOk
#guard !(Helpers.compile (loopProgram 0 0 [.return none]) "main").isOk
#guard !(Helpers.compile (loopProgram 0 0 [.assert (.ref "missing")]) "main").isOk
#guard !(Helpers.compile (loopProgram 0 1024
  [.forRange "inner" 0 1024 [.assert (.bool Bool.true)]]) "main").isOk

private def indexDoesNotEscape : Program := {
  declarations := [{
    id := ⟨0, 0⟩, name := "main", result := .scalar .native,
    body := [.forRange "index" 0 1 [], .return (some (.ref "index"))]}]
  exports := [{name := "main", target := ⟨0, 0⟩}]
}

#guard !(Helpers.compile indexDoesNotEscape "main").isOk
