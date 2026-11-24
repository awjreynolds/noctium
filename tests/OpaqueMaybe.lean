import Noctium.Frontend
import Noctium.Backend.Zkir

open scoped Noctium
open Noctium

noctium_witness_circuit opaqueMaybeResults where
  public textValue : OpaqueString
  public bytesValue : OpaqueBytes
  output stringSome := some(textValue)
  output stringNone := none(OpaqueString)
  output bytesSome := some(bytesValue)
  output bytesNone := none(OpaqueBytes)
end

noctium_contract OpaqueMaybe where
  entry inspect uses opaqueMaybeResults where
    return stringSome
    return stringNone
    return bytesSome
    return bytesNone
  end
end

#guard OpaqueMaybe.entrypoints.all fun operation =>
  (Backend.Zkir.lowerEntrypoint OpaqueMaybe.state operation).isOk

/-- undisclosed private parameter 'textValue' -/
#guard_msgs (substring := true) in
noctium_witness_circuit hiddenOpaqueMaybe where
  private textValue : OpaqueString
  output hiddenValue := some(textValue)
end
