import Noctium.Midnight.ShieldedCoinInfo

namespace Noctium.Midnight.QualifiedShieldedCoinInfo

open Noctium

/-- Compact's qualified coin keeps the shielded coin fields and appends its
Merkle tree index. -/
def id : Types.DeclId := "Noctium.Midnight.QualifiedShieldedCoinInfo"

def fields : List (String × Ty) :=
  Noctium.Midnight.ShieldedCoinInfo.fields ++
    [("mt_index", .uint (2 ^ 64 - 1))]

def type : Types.CompositeType := .structure id

def environment : Types.CompositeEnv := {
  structures := [{
    id
    fields := fields.map fun (name, fieldTy) => {
      name
      type := match fieldTy with
        | .bytes length => .bytes length
        | _ => .scalar fieldTy
    }
  }]
}

/-- Two 32-byte fields, a 16-byte value, and an 8-byte tree index. -/
def frameBytes : Nat := Noctium.Midnight.ShieldedCoinInfo.frameBytes + 8

/-- Checked encoder/decoder shape for qualified ShieldedCoinInfo values. -/
def codec : Helpers.Wire.Codec := {
  payload := type
  frameBytes
  composites := environment
}

end Noctium.Midnight.QualifiedShieldedCoinInfo
