import Noctium.Frontend

open scoped Noctium
open Noctium

namespace NominalFieldScalarSet

noctium_field_type Amount := Field
noctium_field_type Count := Field

noctium_circuit inputs where
  private amount : Amount
  private raw : Native
  public adding : Bool
  public removing : Bool
end

noctium_circuit wrongAliasInputs where
  private amount : Count
end

noctium_contract ScalarSet where
  set members : Amount
  set plain : Amount

  entry update uses inputs where
    member plain[disclose(amount)] as plainBefore
    insert plain[disclose(amount)]
    member plain[disclose(amount)] as plainAfterInsert
    remove plain[disclose(amount)]
    member plain[disclose(amount)] as plainAfterRemove
    member members[disclose(amount)] as before
    when adding insert members[disclose(amount)]
    member members[disclose(amount)] as afterInsert
    when adding insert members[cast(Amount, disclose(raw))]
    member members[cast(Amount, disclose(raw))] as casted
    when removing remove members[disclose(amount)]
    member members[disclose(amount)] as afterRemove
    when removing remove members[cast(Amount, disclose(raw))]
    member members[cast(Amount, disclose(raw))] as castedAfterRemove
    return plainWasPresent : Bool := plainBefore
    return plainWasInserted : Bool := plainAfterInsert
    return plainRemains : Bool := plainAfterRemove
    return wasPresent : Bool := before
    return wasPresentAfterInsert : Bool := afterInsert
    return wasCastedPresent : Bool := casted
    return wasPresentAfterRemove : Bool := afterRemove
    return wasCastedPresentAfterRemove : Bool := castedAfterRemove
  end
end

noctium_contract ConstructorScalarSet where
  set members : Amount

  constructor(seed : Amount, raw : Native, enabled : Bool) where
    insert members[seed]
    when enabled insert members[cast(Amount, raw)]
  end
end

private def scalarSetEntry : Entrypoint :=
  (ScalarSet.entrypoints.find? (·.name == "update")).getD
    {name := "missing", circuit := {name := "missing"}}

private def context : EvalContext := {
  modulus := Field.modulus
  poseidon2 := fun _ _ _ => .error "unused by nominal Field scalar Set fixture"
}

private def initialState : LedgerState := {trees := [("members", .map []), ("plain", .map [])]}

private def run (amount raw : Nat) (adding removing : _root_.Bool) (state : LedgerState) :=
  scalarSetEntry.run context [
    ("amount", .native amount), ("raw", .native raw),
    ("adding", .bool adding), ("removing", .bool removing)] state

#guard (ScalarSet.validate Capabilities.source).isOk
#guard (scalarSetEntry.validate Capabilities.source ScalarSet.state).isOk
#guard (ConstructorScalarSet.validate Capabilities.source).isOk

#guard match run 17 19 _root_.Bool.true _root_.Bool.false initialState with
  | .ok (outputs, state) =>
      outputs.lookup "plainWasPresent" == some (.bool _root_.Bool.false) &&
      outputs.lookup "plainWasInserted" == some (.bool _root_.Bool.true) &&
      outputs.lookup "plainRemains" == some (.bool _root_.Bool.false) &&
      outputs.lookup "wasPresent" == some (.bool _root_.Bool.false) &&
      outputs.lookup "wasPresentAfterInsert" == some (.bool _root_.Bool.true) &&
      outputs.lookup "wasCastedPresent" == some (.bool _root_.Bool.true) &&
      outputs.lookup "wasPresentAfterRemove" == some (.bool _root_.Bool.true) &&
      outputs.lookup "wasCastedPresentAfterRemove" == some (.bool _root_.Bool.true) &&
      state.trees.lookup "members" == some (.map [(.native 19, .null), (.native 17, .null)]) &&
      state.trees.lookup "plain" == some (.map [])
  | .error _ => _root_.Bool.false

#guard match run 17 19 _root_.Bool.false _root_.Bool.true
    (match run 17 19 _root_.Bool.true _root_.Bool.false initialState with
      | .ok (_, state) => state
      | .error _ => initialState) with
  | .ok (outputs, state) =>
      outputs.lookup "plainWasPresent" == some (.bool _root_.Bool.false) &&
      outputs.lookup "plainWasInserted" == some (.bool _root_.Bool.true) &&
      outputs.lookup "plainRemains" == some (.bool _root_.Bool.false) &&
      outputs.lookup "wasPresent" == some (.bool _root_.Bool.true) &&
      outputs.lookup "wasPresentAfterInsert" == some (.bool _root_.Bool.true) &&
      outputs.lookup "wasCastedPresent" == some (.bool _root_.Bool.true) &&
      outputs.lookup "wasPresentAfterRemove" == some (.bool _root_.Bool.false) &&
      outputs.lookup "wasCastedPresentAfterRemove" == some (.bool _root_.Bool.false) &&
      state.trees.lookup "members" == some (.map []) &&
      state.trees.lookup "plain" == some (.map [])
  | .error _ => _root_.Bool.false

/- error: nominal Field values require an explicit cast and must match the target type -/
#guard_msgs (substring := true) in
noctium_contract RejectRawKey where
  set members : Amount

  entry update uses inputs where
    member members[raw] as present
  end
end

/- error: nominal Field values require an explicit cast and must match the target type -/
#guard_msgs (substring := true) in
noctium_contract RejectWrongConstructorAlias where
  set members : Amount

  constructor(seed : Count) where
    insert members[seed]
  end
end

/- error: nominal Field values require an explicit cast and must match the target type -/
#guard_msgs (substring := true) in
noctium_contract RejectRawConstructorKey where
  set members : Amount

  constructor(seed : Native, enabled : Bool) where
    when enabled insert members[seed]
  end
end

/- error: nominal Field values require an explicit cast and must match the target type -/
#guard_msgs (substring := true) in
noctium_contract RejectWrongAlias where
  set members : Amount

  entry update uses wrongAliasInputs where
    member members[amount] as present
  end
end

/- error: nominal Field effects require a direct scalar Cell write -/
#guard_msgs (substring := true) in
noctium_contract RejectNominalGuard where
  set members : Amount

  entry update uses inputs where
    when eq(amount, amount) insert members[amount]
  end
end

end NominalFieldScalarSet
