import Noctium.Frontend

open scoped Noctium
open Noctium Helpers

namespace NominalFieldMapHelpers

noctium_field_type Key := Field
noctium_field_type OtherKey := Field

private def keyIdentity := "NominalFieldMapHelpers.Key"

private def mapProgram : Program := {
  ledger := [{name := "balances", kind := .map .native .native}]
  declarations := [
    {id := ⟨0, 0⟩, name := "get", parameters := [⟨"key", .native⟩],
      nominalFieldParameters := [("key", keyIdentity)], result := .scalar .native,
      body := [
        .readMember "balances" "present" .native .native (.disclose {} (.ref "key")),
        .assert (.ref "present"),
        .readMap "balances" "stored" .native .native (.disclose {} (.ref "key")),
        .return (some (.ref "stored"))]},
    {id := ⟨0, 1⟩, name := "set", parameters := [⟨"key", .native⟩, ⟨"amount", .native⟩],
      nominalFieldParameters := [("key", keyIdentity)],
      body := [
        .writeMap "balances" .native .native (.disclose {} (.ref "key")) (.disclose {} (.ref "amount")),
        .return none]}]
  exports := [
    {name := "get", target := ⟨0, 0⟩, inputs := [
      {name := "key", ty := .native, visibility := .private}]},
    {name := "set", target := ⟨0, 1⟩, inputs := [
      {name := "key", ty := .native, visibility := .private},
      {name := "amount", ty := .native, visibility := .private}]}]
}

noctium_contract BalanceBook where
  map balances : Key => Native

  entry lookup from mapProgram entry "get" end
  entry store from mapProgram entry "set" end
end

private def roundTrip : Except String _root_.Bool := do
  let [lookup, store] := BalanceBook.entrypoints | throw "expected two compiled helpers"
  let context : EvalContext := {
    modulus := Field.modulus
    poseidon2 := fun _ _ _ => .error "unused by nominal Field Map helpers"
  }
  let key : Value := .native 17
  let initial : LedgerState := {maps := [("balances", [])]}
  let (_, stored) ← store.run context [("key", key), ("amount", .native 42)] initial
  let (result, final) ← lookup.run context [("key", key)] stored
  pure (result.any (fun (_, value) => value == .native 42) &&
    stored.maps.lookup "balances" == some [(key, .native 42)] && final == stored)

#guard roundTrip.toOption == some _root_.Bool.true

#guard match Witness.Ledger.transform (mapProgram.withNominalFieldMapKeys [("balances", keyIdentity)]) with
  | .ok transformed =>
      (transformed.host.witnesses.map fun signature =>
        signature.parameters.map (·.sourceNominalField)) ==
      [[some keyIdentity], [some keyIdentity], [some keyIdentity, none]]
  | .error _ => _root_.Bool.false

private def wrongKeyProgram : Program := {
  mapProgram with declarations := mapProgram.declarations.map fun declaration =>
    {declaration with nominalFieldParameters := [("key", "NominalFieldMapHelpers.OtherKey")]}
}

/-- error: :1:1: nominal Field values require an explicit cast and must match the target type -/
#guard_msgs (substring := true) in
noctium_contract RejectWrongMapHelperKey where
  map balances : Key => Native
  entry lookup from wrongKeyProgram entry "get" end
end

end NominalFieldMapHelpers
