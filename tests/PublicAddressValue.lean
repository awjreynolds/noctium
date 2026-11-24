import Noctium.Frontend
import Noctium.Midnight.PublicAddress

open scoped Noctium
open Noctium

namespace PublicAddressValue

open Noctium.Midnight

noctium_witness_circuit echo using PublicAddress.codec where
  private address : Payload PublicAddress.codec
  output returned := disclose(address)
end

noctium_witness_circuit asContract using ContractAddress.codec, PublicAddress.codec, UserAddress.codec where
  private address : Payload ContractAddress.codec
  output returned := disclose(record(Payload PublicAddress.codec, {
    is_left := true,
    left := address,
    right := default(Payload UserAddress.codec)
  }))
end

noctium_witness_circuit asUser using UserAddress.codec, PublicAddress.codec, ContractAddress.codec where
  private address : Payload UserAddress.codec
  output returned := disclose(record(Payload PublicAddress.codec, {
    is_left := false,
    left := default(Payload ContractAddress.codec),
    right := address
  }))
end

/- error: record field 'left' has the wrong Payload type -/
#guard_msgs (substring := true) in
noctium_witness_circuit rejectsUserInContractArm using UserAddress.codec, PublicAddress.codec where
  public address : Payload UserAddress.codec
  output returned := record(Payload PublicAddress.codec, {
    is_left := true,
    left := address,
    right := address
  })
end

private def context : EvalContext := {
  modulus := Field.modulus
  poseidon2 := fun _ _ _ => .error "unused by public address fixture"
}

private def addressBytes (name : String) (byte : Nat) : List (String × Value) :=
  (List.range 32).map fun index => (s!"{name}.bytes.{index}", .native byte)

private def publicAddress (name : String) (tag leftByte rightByte : Nat) : List (String × Value) :=
  (s!"{name}.is_left", .native tag) ::
    addressBytes (name ++ ".left") leftByte ++ addressBytes (name ++ ".right") rightByte

#guard PublicAddress.codec.frameBytes == 65
#guard (echo.run context (publicAddress "address" 1 1 2)).toOption == some (publicAddress "result" 1 1 2)
#guard (echo.run context (publicAddress "address" 0 1 2)).toOption == some (publicAddress "result" 0 1 2)
#guard (asContract.run context (addressBytes "address" 1)).toOption == some (publicAddress "result" 1 1 0)
#guard (asUser.run context (addressBytes "address" 2)).toOption == some (publicAddress "result" 0 0 2)
#guard !(echo.run context (publicAddress "address" 2 1 2)).isOk
#guard !(echo.run context (publicAddress "address" 1 256 2)).isOk

noctium_contract Transport where
  entry echo uses echo arguments [address] where
    return returned
  end
  entry asContract uses asContract arguments [address] where
    return returned
  end
  entry asUser uses asUser arguments [address] where
    return returned
  end
end

end PublicAddressValue
