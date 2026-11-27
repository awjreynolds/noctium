import Noctium.Frontend

open scoped Noctium

noctium_circuit widePublicInput where
  public payload : Bytes 1025
end

noctium_circuit widePublicInput1055 where
  public payload : Bytes 1055
end

noctium_circuit widePublicInput4096 where
  public payload : Bytes 4096
end

noctium_contract WidePublicBytes where
  entry roundTrip uses widePublicInput where
    return result : Bytes 1025 := payload
  end

  entry roundTrip1055 uses widePublicInput1055 where
    return result : Bytes 1055 := payload
  end

  entry roundTrip4096 uses widePublicInput4096 where
    return result : Bytes 4096 := payload
  end
end

/-- byte string length exceeds the maximum of 4096 -/
#guard_msgs (substring := true) in
noctium_circuit oversizedPublicInput where
  public payload : Bytes 4097
end

#guard !(Noctium.Circuit.validate Noctium.Capabilities.source {
  name := "widePrivateInput"
  inputs := [{name := "payload", ty := .bytes 1055, visibility := .private}]
}).isOk
