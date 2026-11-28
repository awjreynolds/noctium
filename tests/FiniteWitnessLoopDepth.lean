import Noctium.Frontend

open scoped Noctium

noctium_witness visitValue(index : UInt 8) : Native
noctium_witness visitValue16(index : UInt 16) : Native

noctium_witness_circuit witnessLoop16 where
  for index in 0 ..< 16 do
    let value : Native := witness visitValue(cast(UInt 8, index))
    prove eq(value, 0)
  end
  output checked : Native := 0
end

noctium_witness_circuit witnessLoop32 where
  for index in 0 ..< 32 do
    let value : Native := witness visitValue(cast(UInt 8, index))
    prove eq(value, 0)
  end
  output checked : Native := 0
end

noctium_witness_circuit witnessLoop1025 where
  for index in 0 ..< 1025 do
    let value : Native := witness visitValue16(cast(UInt 16, index))
    prove eq(value, 0)
  end
  output checked : Native := 0
end

noctium_contract FiniteWitnessLoopDepth where
  entry witnessLoop16 uses witnessLoop16 where
    return result : Native := checked
  end
  entry witnessLoop32 uses witnessLoop32 where
    return result : Native := checked
  end
  entry witnessLoop1025 uses witnessLoop1025 where
    return result : Native := checked
  end
end
