import Noctium.Disclosure
import Noctium.Frontend

open scoped Noctium

noctium_circuit fourteenParentsInputs where
  public owner : Bytes32
  public group : Bytes32
  public key : Bytes32
  private nonce : Bytes32
  private color : Bytes32
  private amount : UInt 128
  private isContract : Bool
  private recipient : Bytes32
end

noctium_contract DeepBookedCoinMapBoundary where
  tree coins : Bytes32 => Bytes32 => Bytes32 => Bytes32 => Bytes32 =>
    Bytes32 => Bytes32 => Bytes32 => Bytes32 => Bytes32 =>
    Bytes32 => Bytes32 => Bytes32 => Bytes32 => Bytes32 => struct Coin {
      nonce : Bytes32
      color : Bytes32
      value : UInt 128
      mtIndex : UInt 64
    }

  entry store uses fourteenParentsInputs where
    insertShieldedCoinMap(
      coins[owner][group][group][group][group][group][group][group][group][group][group][group][group][group],
      key,
      disclose(nonce),
      disclose(color),
      disclose(amount),
      disclose(isContract),
      disclose(recipient))
  end
end
