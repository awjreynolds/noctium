import Noctium.Frontend

open scoped Noctium

noctium_witness_circuit readableTokenColors where
  public domain : Bytes32
  public contractAddress : Bytes32
  output nativeColor : Bytes32 := disclose(nativeToken())
  output derivedColor : Bytes32 := disclose(tokenType(domain, contractAddress))
end

#guard
  let compiled := Noctium.Witness.compile readableTokenColors.__program
    "noctium.witness-circuit.readableTokenColors.v1"
  compiled.isOk

noctium_circuit tokenColorInputs where
  public domain : Bytes32
end

noctium_circuit explicitTokenColorInputs where
  public domain : Bytes32
  public contractAddress : Bytes32
end

noctium_contract NativeTokenColors where
  entry derive uses tokenColorInputs where
    readSelf as own
    return nativeColor : Bytes32 := disclose(nativeToken())
    return derivedColor : Bytes32 := disclose(tokenType(domain, own))
  end

  entry deriveFor uses explicitTokenColorInputs where
    return nativeColor : Bytes32 := disclose(nativeToken())
    return derivedColor : Bytes32 := disclose(tokenType(domain, contractAddress))
  end
end
