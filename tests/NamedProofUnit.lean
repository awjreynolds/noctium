import Noctium.Frontend

open scoped Noctium

noctium_witness_circuit namedProofUnit where
  public allowed : Bool
  prove allowed as checked
  let unitAlias := checked
end

noctium_witness_circuit nestedUnitAssertion where
  public enabled : Bool
  public allowed : Bool
  if enabled then
    let checked := assertUnit(allowed)
    let unitAlias := checked
  end
  let result : Native := if enabled then 7 else 9
  output value : Native := disclose(result)
end

noctium_contract NamedProofUnit where
  entry checkGate uses namedProofUnit where
  end
  entry checkNestedGate uses nestedUnitAssertion where
    return result : Native := value
  end
end

/-- error: duplicate readable witness value 'allowed' -/
#guard_msgs in
noctium_witness_circuit duplicateProofName where
  public allowed : Bool
  prove allowed as allowed
end
