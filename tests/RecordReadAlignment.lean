import Noctium.Backend.Impact

open Lean
open Noctium
open Noctium.Backend.Impact

private def readTypes : List Ty :=
  [.bytes 32, .bytes 32, .uint (2 ^ 128 - 1), .uint (2 ^ 64 - 1)]

private def readValues : List LedgerFieldExpr := [
  .mk (.bytes 32) (.bytesLiteral 32 (List.replicate 32 0)),
  .mk (.bytes 32) (.bytesLiteral 32 (List.replicate 32 1)),
  .mk (.uint (2 ^ 128 - 1)) (.uint (2 ^ 128 - 1) 7),
  .mk (.uint (2 ^ 64 - 1)) (.uint (2 ^ 64 - 1) 9)]

private def recordSchema (identifier : String) (names : List String) : Json :=
  Json.mkObj [
    ("id", toJson identifier),
    ("fields", toJson (names.zip readTypes |>.map fun (name, ty) => Json.mkObj [
      ("name", toJson name),
      ("type", toJson (NativeExpression.typeName ty))]))]

private def tags (fields : List Scalar) (start : Nat) : List Nat :=
  ((fields.drop start).take 4).filterMap fun
    | .native value => some value
    | _ => none

private def ordinarySchema :=
  recordSchema "Noctium.Tests.Journal" ["one", "two", "budget", "index"]

private def qualifiedCoinSchema :=
  recordSchema "Noctium.Midnight.QualifiedShieldedCoinInfo"
    ["nonce", "color", "value", "mtIndex"]

private def ordinaryReadTags :=
  tags (Op.fields (.popeqFields ordinarySchema readValues)) 2

private def ordinaryWriteTags :=
  tags (Op.fields (.pushFields ordinarySchema readValues false)) 3

private def qualifiedCoinReadTags :=
  tags (Op.fields (.popeqFields qualifiedCoinSchema readValues)) 2

private def qualifiedCoinWriteTags :=
  tags (Op.fields (.pushFields qualifiedCoinSchema readValues false)) 3

private def ordinaryTags : List Nat :=
  [32, 32, Field.modulus - 2, Field.modulus - 2]

private def qualifiedCoinTags : List Nat :=
  [32, 32, 16, 8]

#guard ordinaryReadTags == ordinaryTags
#guard ordinaryWriteTags == ordinaryTags
#guard ordinaryReadTags == ordinaryWriteTags
#guard qualifiedCoinReadTags == qualifiedCoinTags
#guard qualifiedCoinWriteTags == qualifiedCoinTags
