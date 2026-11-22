import Noctium.Frontend

open Noctium Noctium.Helpers
open scoped Noctium

private def blockTimeWitnessProgram : Program := {
  witnesses := [{
    name := "lookup"
    operation := "noctium.lookup.v1"
    capability := "lookup"
    parameters := [{name := "seed", type := .scalar (.uint 255)}]
    result := .scalar (.uint 255)
  }]
  declarations := [{
    id := ⟨0, 0⟩
    name := "checkTime"
    parameters := [
      {name := "expected", ty := .uint 255},
      {name := "seed", ty := .uint 255},
      {name := "cutoff", ty := .uint (2 ^ 64 - 1)},
      {name := "enabled", ty := .bool}
    ]
    result := .scalar (.uint 255)
    body := [
      .bind "actual" (.scalar (.uint 255))
        (.witnessCall "lookup-value" "lookup" [.ref "seed"]),
      .assert (.eq (.ref "actual") (.ref "expected")),
      .return (some (.ref "expected"))
    ]
  }]
  exports := [{
    name := "checkTime"
    target := ⟨0, 0⟩
    inputs := [
      {name := "expected", ty := .uint 255, visibility := .public},
      {name := "seed", ty := .uint 255, visibility := .private},
      {name := "cutoff", ty := .uint (2 ^ 64 - 1), visibility := .public},
      {name := "enabled", ty := .bool, visibility := .public}
    ]
  }]
}

noctium_witness_circuit blockTimeRelation from blockTimeWitnessProgram entry "checkTime"

noctium_contract TypedWitnessBlockTime where
  cell total : UInt 8
  entry checkTime uses blockTimeRelation where
    when enabled blockTimeBefore(cutoff) as beforeDeadline
    require beforeDeadline
    write total := cast(UInt 8, result)
    return total : UInt 8 := cast(UInt 8, result)
  end
end
