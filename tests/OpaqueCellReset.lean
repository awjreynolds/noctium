import Noctium.Frontend

open scoped Noctium
open Noctium

noctium_circuit opaqueResetSeedInputs where
  public nextText : OpaqueString
  public nextBytes : OpaqueBytes
end

noctium_circuit opaqueResetInputs where
  public enabled : Bool
end

noctium_contract OpaqueCellReset where
  cell text : OpaqueString
  cell bytes : OpaqueBytes
  entry seed uses opaqueResetSeedInputs where
    write text := disclose(nextText)
    write bytes := disclose(nextBytes)
  end
  entry clear uses opaqueResetInputs where
    when enabled reset text
    when enabled reset bytes
    read text as currentText
    read bytes as currentBytes
    return textAfter : OpaqueString := disclose(currentText)
    return bytesAfter : OpaqueBytes := disclose(currentBytes)
  end
end

#guard match OpaqueCellReset.entrypoints with
  | [_, clear] =>
    match clear.effects, clear.effectGuards with
    | [.writeCell "text" .opaqueString .opaqueStringEmpty,
       .writeCell "bytes" .opaqueBytes .opaqueBytesEmpty,
       .readCell "text" "currentText" .opaqueString,
       .readCell "bytes" "currentBytes" .opaqueBytes],
      [some (.ref "enabled"), some (.ref "enabled"), none, none] => Bool.true
    | _, _ => Bool.false
  | _ => Bool.false

#guard match OpaqueCellReset.entrypoints with
  | [_, clear] =>
    let state := OpaqueCellReset.state.map fun field =>
      if field.name == "text" then {field with «sealed» := Bool.true} else field
    match clear.validate Capabilities.source state with
    | .error diagnostic => diagnostic.message == "sealed state 'text' cannot be written by an entrypoint"
    | .ok _ => Bool.false
  | _ => Bool.false
