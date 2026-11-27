import Noctium.Frontend

open scoped Noctium

noctium_circuit widePublicInput where
  public payload : Bytes 1025
end

noctium_contract WidePublicBytes where
  entry roundTrip uses widePublicInput where
    return result : Bytes 1025 := payload
  end
end
