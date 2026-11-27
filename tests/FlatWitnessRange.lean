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

noctium_contract FlatWitnessRange where
  entry shortRange uses shortVisits where
    return result : Native := checked
  end
  entry longRange uses longVisits where
    return result : Native := checked
  end
end
