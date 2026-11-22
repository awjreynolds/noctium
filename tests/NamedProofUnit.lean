import Noctium.Frontend

open scoped Noctium

noctium_witness_circuit namedProofUnit where
  public allowed : Bool
  prove allowed as checked
  let unitAlias := checked
end

noctium_contract NamedProofUnit where
  entry checkGate uses namedProofUnit where
  end
end

/-- error: duplicate readable witness value 'allowed' -/
#guard_msgs in
noctium_witness_circuit duplicateProofName where
  public allowed : Bool
  prove allowed as allowed
end
