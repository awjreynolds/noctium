import Noctium.Frontend

open scoped Noctium

noctium_circuit alignedByteConcatInputs where
  public front : Bytes 31
  public sourceBytes : Bytes 2
  output joined : Bytes 32 := concatBytes(front, sliceBytes(sourceBytes, 1, 2))
end

noctium_contract AlignedByteConcat where
  entry joinTail uses alignedByteConcatInputs where
    return joinedResult : Bytes 32 := joined
  end
end
