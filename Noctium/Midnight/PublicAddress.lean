import Noctium.Helpers.Wire

namespace Noctium.Midnight

private def addressCodec (id : Types.DeclId) : Helpers.Wire.Codec := {
  payload := .structure id
  frameBytes := 32
  composites := {structures := [{
    id
    fields := [{name := "bytes", type := .bytes 32}]
  }]}
}

/-- The address record used for deployed contracts. -/
def ContractAddress.codec : Helpers.Wire.Codec :=
  addressCodec "Noctium.Midnight.ContractAddress"

/-- The address record used for public user recipients. -/
def UserAddress.codec : Helpers.Wire.Codec :=
  addressCodec "Noctium.Midnight.UserAddress"

/-- The checked `Either<ContractAddress, UserAddress>` layout used by public recipients. -/
def PublicAddress.codec : Helpers.Wire.Codec :=
  Helpers.Wire.either "Noctium.Midnight.PublicAddress" ContractAddress.codec UserAddress.codec

end Noctium.Midnight
