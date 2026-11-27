import Noctium.Frontend

open scoped Noctium
open Noctium.Helpers

private def unitIdentityHelperProgram : Program := {
  declarations := [{
    id := ⟨0, 0⟩
    name := "identityUnit"
    parameters := [{name := "value", ty := .native}]
    compositeParameters := [("value", .unit)]
    result := .unit
    body := [.return (some (.ref "value"))]
  }]
  exports := [{name := "identityUnit", target := ⟨0, 0⟩}]
}

noctium_witness_circuit namedProofUnit where
  public allowed : Bool
  prove allowed as checked
  let unitAlias := checked
end

noctium_witness_circuit nestedUnitAssertion where
  public enabled : Bool
  public allowed : Bool
  public secondAllowed : Bool
  if enabled then
    let checked := assertUnit(allowed, "first gate denied")
    let unitAlias := checked
    let secondChecked := assertUnit(secondAllowed, "second gate denied")
    let secondAlias := secondChecked
  end
  let result : Native := if enabled then 7 else 9
  output value : Native := disclose(result)
end

noctium_witness_circuit conditionalUnitAssertion where
  public choice : Bool
  public first : Bool
  public second : Bool
  let checked := if choice then
    assertUnit(first, "positive arm denied")
  else
    assertUnit(second, "negative arm denied")
  let result : Native := 7
  output value : Native := disclose(result)
end

noctium_witness_circuit unitHelperArgument with unitIdentityHelperProgram where
  public allowed : Bool
  let checked := invoke(identityUnit, [assertUnit(allowed, "helper argument denied")])
  let result : Native := 11
  output value : Native := disclose(result)
end

noctium_contract NamedProofUnit where
  entry checkGate uses namedProofUnit where
  end
  entry checkNestedGate uses nestedUnitAssertion where
    return result : Native := value
  end
  entry checkConditionalUnit uses conditionalUnitAssertion where
    return result : Native := value
  end
  entry checkUnitHelperArgument uses unitHelperArgument where
    return result : Native := value
  end
end

/-- error: duplicate readable witness value 'allowed' -/
#guard_msgs in
noctium_witness_circuit duplicateProofName where
  public allowed : Bool
  prove allowed as allowed
end
