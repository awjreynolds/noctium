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

noctium_circuit nativeNestedMapResetSeedInputs where
  private owner : Native
  private targetA : Native
  private amountA : Native
  private targetB : Native
  private amountB : Native
  private siblingOwner : Native
  private siblingKey : Native
  private siblingAmount : Native
end

noctium_circuit nativeNestedMapResetInputs where
  private owner : Native
  public active : Bool
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

noctium_contract NativeNestedMapReset where
  tree nestedValues : Native => Native => Native

  entry seedNested uses nativeNestedMapResetSeedInputs where
    insert nestedValues[disclose(owner)] := emptyMap
    insert nestedValues[disclose(owner)][disclose(targetA)] := disclose(amountA)
    insert nestedValues[disclose(owner)][disclose(targetB)] := disclose(amountB)
    insert nestedValues[disclose(siblingOwner)] := emptyMap
    insert nestedValues[disclose(siblingOwner)][disclose(siblingKey)] :=
      disclose(siblingAmount)
  end

  entry clearInner uses nativeNestedMapResetInputs where
    when active reset nestedValues[disclose(owner)]
  end
end
