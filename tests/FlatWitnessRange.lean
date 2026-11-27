import Noctium.Frontend

open scoped Noctium

noctium_witness visit(index : Native) : Unit

noctium_witness_circuit shortVisits where
  for index in 0 ..< 3 do
    witness visit(index)
  end
  output checked : Native := 0
end

noctium_witness_circuit longVisits where
  for index in 0 ..< 1025 do
    witness visit(index)
  end
  output checked : Native := 0
end

noctium_witness_circuit aliasVisits where
  for index in 0 ..< 1200 do
    let localIndex : Native := index
    witness visit(localIndex)
  end
  output checked : Native := 0
end

/- error: helper resource limit exceeded: finite range length -/
#guard_msgs (substring := true) in
noctium_witness_circuit rejectsCalculatedAliasVisits where
  for index in 0 ..< 1200 do
    let localIndex : Native := add(index, 1)
    witness visit(localIndex)
  end
  output checked : Native := 0
end

noctium_contract FlatWitnessRange where
  entry shortRange uses shortVisits where
    return result : Native := checked
  end
  entry longRange uses longVisits where
    return result : Native := checked
  end
  entry aliasRange uses aliasVisits where
    return result : Native := checked
  end
end
