import Noctium.Frontend
import Noctium.Backend.Zkir

open scoped Noctium
open Noctium

noctium_circuit fixedBytesDefaultsInputs where
end

noctium_contract FixedBytesDefaults where
  entry defaults uses fixedBytesDefaultsInputs where
    return emptyValue : Bytes 0 := default(Bytes 0)
    return shortValue : Bytes 4 := default(Bytes 4)
    return wordValue : Bytes 32 := default(Bytes 32)
  end
end

#guard match FixedBytesDefaults.entrypoints with
  | [defaults] =>
    FixedBytesDefaults.state.isEmpty && defaults.name == "defaults" &&
      defaults.circuit.inputs.isEmpty &&
      (match defaults.returns with
       | [{name := "emptyValue", ty := .bytes 0,
            value := .bytesLiteral 0 [], ..},
          {name := "shortValue", ty := .bytes 4,
            value := .bytesLiteral 4 [0, 0, 0, 0], ..},
          {name := "wordValue", ty := .bytes 32,
            value := .bytes32Literal values, ..}] =>
              values == List.replicate 32 0
       | _ => Bool.false) &&
      (Backend.Zkir.lowerEntrypoint FixedBytesDefaults.state defaults).isOk
  | _ => Bool.false
