import Noctium.Frontend

open scoped Noctium
open Noctium

noctium_circuit nativeMapResetSeedInputs where
  private key : Native
  private amount : Native
end

noctium_circuit nativeMapResetInputs where
  private key : Native
end

noctium_contract NativeMapReset where
  map values : Native => Native

  entry seed uses nativeMapResetSeedInputs where
    insert values[disclose(key)] := disclose(amount)
  end

  entry clearMap uses nativeMapResetInputs where
    reset values
    member values[disclose(key)] as present
    size values as count
    return hasEntry : Bool := present
    return entries : UInt 64 := count
  end
end
