import Noctium.Backend.Zkir
import Noctium.Frontend

open scoped Noctium
open Noctium

namespace NestedNominalFieldScalarMap

noctium_field_type OwnerId := Field
noctium_field_type AssetId := Field
noctium_field_type OtherId := Field

noctium_circuit nestedInputs where
  private owner : OwnerId
  private asset : AssetId
  private amount : Native
  public enabled : Bool
end

noctium_circuit wrongOuterAliasInputs where
  private owner : AssetId
  private asset : AssetId
  private amount : Native
  public enabled : Bool
end

noctium_circuit wrongInnerAliasInputs where
  private owner : OwnerId
  private asset : OtherId
  private amount : Native
  public enabled : Bool
end

noctium_circuit mixedKeyInputs where
  private owner : OwnerId
  private slot : Native
  private amount : Native
end

noctium_contract NestedScalarMap where
  tree holdings : OwnerId => AssetId => Native

  entry update uses nestedInputs where
    insertDefault holdings[disclose(owner)]
    insert holdings[disclose(owner)][disclose(asset)] := disclose(amount)
    when enabled read holdings[disclose(owner)][disclose(asset)] as stored
    when enabled member holdings[disclose(owner)][disclose(asset)] as present
    when enabled remove holdings[disclose(owner)][disclose(asset)]
    return value : Native := stored
    return found : Bool := present
  end
end

noctium_contract MixedNestedScalarMap where
  tree holdings : OwnerId => Native => Native

  entry update uses mixedKeyInputs where
    insertDefault holdings[disclose(owner)]
    insert holdings[disclose(owner)][disclose(slot)] := disclose(amount)
    read holdings[disclose(owner)][disclose(slot)] as stored
    return value : Native := stored
  end
end

private def updateEntry : Entrypoint :=
  (NestedScalarMap.entrypoints.find? (·.name == "update")).getD
    {name := "missing", circuit := {name := "missing"}}

private def updateContext : EvalContext := {
  modulus := Field.modulus
  poseidon2 := fun _ _ _ => .error "unused by nested nominal Field scalar Map fixture"
}

#guard (NestedScalarMap.validate Capabilities.source).isOk
#guard (updateEntry.validate Capabilities.source NestedScalarMap.state).isOk
#guard match Backend.Zkir.lowerEntrypoint NestedScalarMap.state updateEntry with
  | .ok _ => _root_.Bool.true
  | .error _ => _root_.Bool.false

#guard match updateEntry.run updateContext [
    ("owner", .native 11), ("asset", .native 29), ("amount", .native 73),
    ("enabled", .bool _root_.Bool.true)]
    {trees := [("holdings", .map [])]} with
  | .ok (outputs, state) =>
      outputs.lookup "value" == some (.native 73) &&
      outputs.lookup "found" == some (.bool _root_.Bool.true) &&
      state.trees.lookup "holdings" == some (.map [(.native 11, .map [])])
  | .error _ => _root_.Bool.false

#guard match MixedNestedScalarMap.validate Capabilities.source with
  | .ok _ => _root_.Bool.true
  | .error _ => _root_.Bool.false


/- error: nominal Field values require an explicit cast and must match the target type -/
#guard_msgs (substring := true) in
noctium_contract RejectWrongOuterAlias where
  tree holdings : OwnerId => AssetId => Native

  entry update uses wrongOuterAliasInputs where
    read holdings[disclose(owner)][disclose(asset)] as stored
  end
end

/- error: nominal Field values require an explicit cast and must match the target type -/
#guard_msgs (substring := true) in
noctium_contract RejectWrongInnerAlias where
  tree holdings : OwnerId => AssetId => Native

  entry update uses wrongInnerAliasInputs where
    read holdings[disclose(owner)][disclose(asset)] as stored
  end
end

end NestedNominalFieldScalarMap
