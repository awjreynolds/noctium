import Noctium.Frontend

open scoped Noctium
open Noctium

noctium_circuit constructorPreflightInputs where
  public allowCall : Bool
  assert eq(allowCall, true)
end

noctium_contract ConstructorPreflight where
  sealed cell initialAmount : UInt 16
  cell spent : Bool

  constructor(seedValue : UInt 16) where
    initialize initialAmount := disclose(seedValue)
    initialize spent := false
  end

  entry inspect uses constructorPreflightInputs where
    read initialAmount as observedAmount
    read spent as wasSpent
    require eq(wasSpent, false)
    write spent := true
    return amountResult : UInt 16 := observedAmount
  end
end
