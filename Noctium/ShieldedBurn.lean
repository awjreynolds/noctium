import Noctium.Helpers

namespace Noctium

/-- Lean's scoped representation of Compact's `shieldedBurnAddress()` result.

Compact returns the left `Either` arm, which is the default
`ZswapCoinPublicKey`. The nominal marker keeps the recipient in Noctium's
existing wallet-key family, and the default key is the zero Bytes32 value.
This helper covers the canonical wallet burn address only. -/
inductive ShieldedBurnAddress where
  | wallet
  deriving Repr, BEq, DecidableEq

namespace ShieldedBurnAddress

/-- Compact's wallet arm is the left side of the returned Either. -/
def walletBranch (_ : ShieldedBurnAddress) : _root_.Bool := _root_.Bool.true

/-- The default `ZswapCoinPublicKey` payload is a zero Bytes32 value. -/
def recipient (_ : ShieldedBurnAddress) : Expr (.bytes 32) :=
  .bytes32Literal (List.replicate 32 0)

/-- Compact's `shieldedBurnAddress()` return schema, including both nominal
address arms and the inactive zero-valued default arm. -/
def logicalType : Types.CompositeType := .structure "Noctium.Midnight.ShieldedBurnAddressResult"

def composites : Types.CompositeEnv := {
  structures := [
    {id := "Noctium.Midnight.ZswapCoinPublicKey", fields := [
      {name := "bytes", type := .bytes 32}]},
    {id := "Noctium.Midnight.ContractAddress", fields := [
      {name := "bytes", type := .bytes 32}]},
    {id := "Noctium.Midnight.ShieldedBurnAddressResult", fields := [
      {name := "is_left", type := .scalar .bool},
      {name := "left", type := .structure "Noctium.Midnight.ZswapCoinPublicKey"},
      {name := "right", type := .structure "Noctium.Midnight.ContractAddress"}]}
  ]
}

/-- A pure helper program exposing the complete logical return value. The
composite helper ABI flattens each nested Bytes32 into 32 checked byte leaves. -/
def program : Helpers.Program := {
  composites := ShieldedBurnAddress.composites
  declarations := [{
    id := ⟨0, 0⟩
    name := "shieldedBurnAddress"
    result := .composite logicalType
    body := [.return (some (.composite logicalType
      ([.bool (walletBranch .wallet)] ++ List.replicate 64 (.native 0))))]
  }]
  exports := [{name := "shieldedBurnAddress", target := ⟨0, 0⟩}]
}

end ShieldedBurnAddress

/-- Canonical wallet recipient used by Compact's shielded burn helper. -/
def shieldedBurnAddress : ShieldedBurnAddress := .wallet

end Noctium
