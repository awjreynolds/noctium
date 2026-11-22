import Noctium.Frontend

open scoped Noctium

noctium_circuit supplyProbeNoInputs where
end

noctium_contract UInt128BoundProbe where
  cell totalSupply : UInt 128 alignedBytes
  entry readSupply uses supplyProbeNoInputs where
    read totalSupply as current
    return amount : UInt 128 := current
  end
end
