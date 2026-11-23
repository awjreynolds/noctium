import Noctium.Frontend

open scoped Noctium
open Noctium

noctium_circuit fieldKeccakInput where
  private value : Native
  output sourceDigest : Bytes32 := disclose(keccak256(value))
end

noctium_witness_circuit fieldKeccakReadableInput where
  private value : Native
  output sourceDigest : Bytes32 := disclose(keccak256(value))
end

noctium_contract FieldKeccak where
  entry hash uses fieldKeccakInput where
    return digest : Bytes32 := sourceDigest
  end
  entry hashReadable uses fieldKeccakReadableInput where
    return digest : Bytes32 := sourceDigest
  end
end

private def fieldKeccakEntry (name : String) : Entrypoint :=
  (FieldKeccak.entrypoints.find? (·.name == name)).getD
    {name := "missing", circuit := {name := "missing"}}

#guard ((fieldKeccakEntry "hash").validate
  Capabilities.source FieldKeccak.state).isOk
#guard ((fieldKeccakEntry "hashReadable").validate
  Capabilities.source FieldKeccak.state).isOk
