import Noctium.Frontend

open scoped Noctium
open Noctium

noctium_witness_circuit typedOptions where
  public memo : Bytes 3
  public jubjub : JubjubPoint
  public secp : Secp256k1Point
  output presentMemo := some(memo)
  output absentMemo := none(Bytes 3)
  output presentJubjub := some(jubjub)
  output absentJubjub := none(JubjubPoint)
  output presentSecp := some(secp)
  output absentSecp := none(Secp256k1Point)
  output presentEmpty := some(default(Bytes 0))
  output absentEmpty := none(Bytes 0)
end

noctium_contract MaybeBytesCurves where
  entry inspect uses typedOptions where
    return presentMemo
    return absentMemo
    return presentJubjub
    return absentJubjub
    return presentSecp
    return absentSecp
    return presentEmpty
    return absentEmpty
  end
end
