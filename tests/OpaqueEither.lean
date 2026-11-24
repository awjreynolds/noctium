import Noctium.Frontend
import Noctium.Backend.Zkir

open scoped Noctium
open Noctium

noctium_witness_circuit opaqueEitherChoices where
  public isLeft : Bool
  public textValue : OpaqueString
  public bytesValue : OpaqueBytes
  public boolValue : Bool
  output stringChoice := either(isLeft, textValue, boolValue)
  output bytesChoice := either(isLeft, boolValue, bytesValue)
end

noctium_contract OpaqueEither where
  entry inspect uses opaqueEitherChoices where
    return stringChoice
    return bytesChoice
  end
end

#guard OpaqueEither.entrypoints.all fun operation =>
  (Backend.Zkir.lowerEntrypoint OpaqueEither.state operation).isOk

#guard OpaqueEither.state.composites.structures.any fun declaration =>
  declaration.id.startsWith "OpaqueEither.opaqueEitherChoices.EitherComposite" &&
  declaration.fields.map (fun field => (field.name, field.type)) == [
    ("is_left", .scalar .bool),
    ("left", .scalar .opaqueString),
    ("right", .scalar .bool)]

#guard OpaqueEither.state.composites.structures.any fun declaration =>
  declaration.id.startsWith "OpaqueEither.opaqueEitherChoices.EitherComposite" &&
  declaration.fields.map (fun field => (field.name, field.type)) == [
    ("is_left", .scalar .bool),
    ("left", .scalar .bool),
    ("right", .scalar .opaqueBytes)]
