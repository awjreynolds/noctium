import Noctium.Frontend
open Noctium.Helpers

private def controlSpan : Noctium.SourceSpan := {file := "tests/ControlSource.lean", line := 7}

def branchWitnessProgram : Program := {
  declarations := [{
    id := ⟨0, 0⟩, name := "branchWitness", parameters := [⟨"active", .bool⟩]
    result := .scalar .native, span := controlSpan, body := [.branch (.ref "active") [
      .stage "store" "counter/value" (.scalar .native) (.native 1),
      .return (some (.disclose controlSpan (.witness "chosen" .native)))]
      [.return (some (.native 7))]]
  }]
  exports := [{name := "branchWitness", target := ⟨0, 0⟩, inputs := [
    {name := "active", ty := .bool, visibility := .public}]}]
}

def witnessOrderProgram : Program := {
  declarations := [{id := ⟨0, 0⟩, name := "order", result := .scalar .native, body := [.return (some (.disclose controlSpan
      (.binary .add (.witness "left" .native) (.witness "right" .native))))]}]
  exports := [{name := "order", target := ⟨0, 0⟩}]
}

def inactiveFailureProgram : Program := {
  declarations := [{id := ⟨0, 0⟩, name := "inactive", result := .scalar .native, body := [.branch (.bool false) [
      .assert (.bool false), .evaluate (.cast (.uint 0) (.native 1))] [],
      .return (some (.native 9))]}]
  exports := [{name := "inactive", target := ⟨0, 0⟩}]
}

def shortCircuitProgram : Program := {
  declarations := [{id := ⟨0, 0⟩, name := "shortCircuit", result := .scalar .bool, body := [.evaluate (.andThen (.bool false) (.eq (.witness "andSkipped" .native) (.native 0))),
      .return (some (.orElse (.bool true) (.eq (.witness "orSkipped" .native) (.native 0))))]}]
  exports := [{name := "shortCircuit", target := ⟨0, 0⟩}]
}

def lazyReturnProgram : Program := {
  declarations := [
    {id := ⟨0, 0⟩, name := "outer", result := .scalar .native, body := [.return (some (.binary .add (.call "inner" []) (.native 1)))]},
    {id := ⟨0, 1⟩, name := "inner", result := .scalar .native, body := [.branch (.bool true) [.return (some (.native 4))] [],
       .assert (.bool false), .return (some (.native 0))]}]
  exports := [{name := "lazyReturn", target := ⟨0, 0⟩}]
}

def lazyExpressionProgram : Program := {
  declarations := [{id := ⟨0, 0⟩, name := "lazyExpression", result := .scalar (.uint 7), body := [.return (some (.ite (.bool true) (.uint 3 2) (.cast (.uint 7) (.native 99))))]}]
  exports := [{name := "lazyExpression", target := ⟨0, 0⟩}]
}

def conditionalProvidersProgram : Program := {
  declarations := [{
    id := ⟨0, 0⟩, name := "conditionalProviders", parameters := [⟨"active", .bool⟩]
    result := .scalar .native, span := controlSpan, body := [.branch (.andThen (.ref "active") (.disclose controlSpan (.witness "flag" .bool))) [
      .evaluate (.witness "left" .native),
      .stage "store" "counter/value" (.scalar .native) (.native 1),
      .return (some (.disclose controlSpan (.witness "right" .native)))]
      [.return (some (.native 7))]]
  }]
  exports := [{name := "conditionalProviders", target := ⟨0, 0⟩, inputs := [
    {name := "active", ty := .bool, visibility := .public}]}]
}

def activeFailureProgram : Program := {
  declarations := [{id := ⟨0, 0⟩, name := "activeFailure", result := .scalar .native, body := [.assert (.bool false), .return (some (.native 0))]}]
  exports := [{name := "activeFailure", target := ⟨0, 0⟩}]
}

def unitConditionalProgram : Program := {
  declarations := [{id := ⟨0, 0⟩, name := "unitConditional", body := [.evaluate (.ite (.bool true) .unit .unit)]}]
  exports := [{name := "unitConditional", target := ⟨0, 0⟩}]
}

def unitPrivateBranchesProgram : Program := {
  declarations := [{id := ⟨0, 0⟩, name := "unitPrivateBranches", parameters := [⟨"flag", .bool⟩], body := [.branch (.ref "flag") [.return none] [.return none]]}]
  exports := [{name := "unitPrivateBranches", target := ⟨0, 0⟩, inputs := [
    {name := "flag", ty := .bool, visibility := .private}]}]
}

def constantInactiveReturnProgram : Program := {
  declarations := [{id := ⟨0, 0⟩, name := "constantInactiveReturn", parameters := [⟨"flag", .bool⟩], result := .scalar .native, body := [
      .branch (.ref "flag") [.branch (.eq (.native 0) (.native 1)) [.return (some (.native 1))] []] [],
      .return (some (.native 2))]}]
  exports := [{name := "constantInactiveReturn", target := ⟨0, 0⟩, inputs := [
    {name := "flag", ty := .bool, visibility := .private}]}]
}

open scoped Noctium
noctium_control branchWitness from branchWitnessProgram entry "branchWitness"
noctium_control witnessOrder from witnessOrderProgram entry "order"
noctium_control inactiveFailure from inactiveFailureProgram entry "inactive"
noctium_control shortCircuit from shortCircuitProgram entry "shortCircuit"
noctium_control lazyReturn from lazyReturnProgram entry "lazyReturn"
noctium_control lazyExpression from lazyExpressionProgram entry "lazyExpression"

noctium_control conditionalProviders from conditionalProvidersProgram entry "conditionalProviders"

noctium_control activeFailure from activeFailureProgram entry "activeFailure"

noctium_control unitConditional from unitConditionalProgram entry "unitConditional"

noctium_control unitPrivateBranches from unitPrivateBranchesProgram entry "unitPrivateBranches"

noctium_control constantInactiveReturn from constantInactiveReturnProgram entry "constantInactiveReturn"
