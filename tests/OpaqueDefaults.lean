import Noctium.Frontend
import Noctium.Backend.Zkir

open scoped Noctium
open Noctium

noctium_circuit opaqueDefaultsInputs where
end

noctium_contract OpaqueDefaults where
  entry defaults uses opaqueDefaultsInputs where
    return textValue : OpaqueString := default(OpaqueString)
    return bytesValue : OpaqueBytes := default(OpaqueBytes)
  end
end

#guard match OpaqueDefaults.entrypoints with
  | [defaults] =>
    defaults.name == "defaults" && defaults.circuit.inputs.isEmpty &&
      (match defaults.returns with
       | [{name := "textValue", ty := .opaqueString, value := .opaqueStringEmpty, ..},
          {name := "bytesValue", ty := .opaqueBytes, value := .opaqueBytesEmpty, ..}] => Bool.true
       | _ => Bool.false) &&
      (Backend.Zkir.lowerEntrypoint OpaqueDefaults.state defaults).isOk
  | _ => Bool.false

noctium_witness_circuit readableOpaqueDefaults where
  output textValue : OpaqueString := default(OpaqueString)
  output bytesValue : OpaqueBytes := default(OpaqueBytes)
end

noctium_contract ReadableOpaqueDefaults where
  entry defaults uses readableOpaqueDefaults where
    return textValue : OpaqueString := textValue
    return bytesValue : OpaqueBytes := bytesValue
  end
end

#guard ReadableOpaqueDefaults.entrypoints.all fun operation =>
  (Backend.Zkir.lowerEntrypoint ReadableOpaqueDefaults.state operation).isOk
