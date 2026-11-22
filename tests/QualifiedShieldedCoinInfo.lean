import Noctium.Backend.Impact
import Noctium.Compiler
import Noctium.Frontend
import Noctium.Midnight.QualifiedShieldedCoinInfo

open scoped Noctium
open Noctium

private def qualifiedShieldedCoinInfoWire : Helpers.Wire.Codec :=
  Noctium.Midnight.QualifiedShieldedCoinInfo.codec

noctium_witness_circuit qualifiedShieldedCoinInfoEcho using qualifiedShieldedCoinInfoWire where
  public coin : Payload qualifiedShieldedCoinInfoWire
  output echoed := coin
end

noctium_contract QualifiedShieldedCoinInfoWireFixture where
  entry echo uses qualifiedShieldedCoinInfoEcho where
    return echoed
  end
end

private def qualifiedShieldedCoinInfoType := Noctium.Midnight.QualifiedShieldedCoinInfo.type
private def qualifiedShieldedCoinInfoEnvironment :=
  Noctium.Midnight.QualifiedShieldedCoinInfo.environment
private def qualifiedShieldedCoinInfoMaximum := 2 ^ 128 - 1
private def qualifiedShieldedCoinInfoIndexMaximum := 2 ^ 64 - 1

#guard Noctium.Midnight.QualifiedShieldedCoinInfo.id ==
  "Noctium.Midnight.QualifiedShieldedCoinInfo"
#guard Noctium.Midnight.QualifiedShieldedCoinInfo.frameBytes == 88

#guard match Types.compileType qualifiedShieldedCoinInfoEnvironment
    qualifiedShieldedCoinInfoType with
  | .ok compiled =>
      match Helpers.Wire.declarations compiled "QualifiedShieldedCoinInfo"
          Noctium.Midnight.QualifiedShieldedCoinInfo.frameBytes ⟨0, 1⟩ ⟨0, 2⟩ with
      | .ok [_, _] => Bool.true
      | _ => Bool.false
  | .error _ => Bool.false

#guard match QualifiedShieldedCoinInfoWireFixture.entrypoints with
  | [compiledEntry] =>
      compiledEntry.name == "echo" &&
        (compiledEntry.validate Capabilities.source
          QualifiedShieldedCoinInfoWireFixture.state).isOk &&
        (Backend.Impact.lower QualifiedShieldedCoinInfoWireFixture.state compiledEntry).isOk
  | _ => Bool.false

private def qualifiedCoinFields (value index : Nat) : List (String × Types.AggregateValue) := [
  ("nonce", .bytes (List.range 32)),
  ("color", .bytes (List.replicate 32 255)),
  ("value", .scalar (.uint qualifiedShieldedCoinInfoMaximum) value),
  ("mt_index", .scalar (.uint qualifiedShieldedCoinInfoIndexMaximum) index)
]

private def validQualifiedCoinFields
    (fields : List (String × Types.AggregateValue)) : _root_.Bool :=
  match Types.compileType qualifiedShieldedCoinInfoEnvironment qualifiedShieldedCoinInfoType with
  | .ok compiled =>
      (Types.checkValue compiled
        (.structure Noctium.Midnight.QualifiedShieldedCoinInfo.id fields)).isOk
  | .error _ => Bool.false

#guard validQualifiedCoinFields (qualifiedCoinFields 0 0)
#guard validQualifiedCoinFields
  (qualifiedCoinFields qualifiedShieldedCoinInfoMaximum qualifiedShieldedCoinInfoIndexMaximum)
#guard !validQualifiedCoinFields
  (qualifiedCoinFields (qualifiedShieldedCoinInfoMaximum + 1) 0)
#guard !validQualifiedCoinFields
  (qualifiedCoinFields 0 (qualifiedShieldedCoinInfoIndexMaximum + 1))
#guard !validQualifiedCoinFields (qualifiedCoinFields 0 0).reverse
