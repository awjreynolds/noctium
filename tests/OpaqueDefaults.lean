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
