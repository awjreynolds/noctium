import Noctium.Frontend

open scoped Noctium
open Noctium

noctium_circuit fixedByteMaybePushInputs where
  private byte1 : Bytes 1
  private byte32 : Bytes 32
  private byte128 : Bytes 128
end

noctium_circuit fixedByteMaybeNoInputs where
end

noctium_contract FixedByteListMaybe where
  list bytes1 : Bytes 1
  list bytes32 : Bytes 32
  list bytes128 : Bytes 128

  entry push uses fixedByteMaybePushInputs where
    pushFront bytes1 := disclose(byte1)
    pushFront bytes32 := disclose(byte32)
    pushFront bytes128 := disclose(byte128)
  end

  entry head uses fixedByteMaybeNoInputs where
    headOrDefault bytes1 as (present1, value1)
    headOrDefault bytes32 as (present32, value32)
    headOrDefault bytes128 as (present128, value128)
    returnMaybe maybe1 as (present1, value1)
    returnMaybe maybe32 as (present32, value32)
    returnMaybe maybe128 as (present128, value128)
  end
end
