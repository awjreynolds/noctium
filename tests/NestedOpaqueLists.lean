import Noctium.Backend.Impact
import Noctium.Backend.Zkir
import Noctium.Frontend

open scoped Noctium
open Noctium

noctium_circuit nestedOpaqueStringPath where
  public owner : Bytes32
end

noctium_circuit nestedOpaqueStringWrite where
  public owner : Bytes32
  public text : OpaqueString
end

noctium_circuit nestedOpaqueDeepStringPath where
  public owner : Bytes32
  public group : Bytes32
end

noctium_circuit nestedOpaqueDeepStringWrite where
  public owner : Bytes32
  public group : Bytes32
  public text : OpaqueString
end

noctium_contract NestedOpaqueLists where
  tree texts : Bytes32 => List OpaqueString
  tree deepTexts : Bytes32 => Bytes32 => List OpaqueString

  entry clear uses nestedOpaqueStringPath where
    reset texts[disclose(owner)]
  end

  entry push uses nestedOpaqueStringWrite where
    pushFront texts[disclose(owner)] := disclose(text)
  end

  entry inspect uses nestedOpaqueStringPath where
    headOrDefault texts[disclose(owner)] as (present, currentText)
    returnMaybe textHead as (present, currentText)
  end

  entry pop uses nestedOpaqueStringPath where
    popFront texts[disclose(owner)]
  end

  entry clearDeep uses nestedOpaqueDeepStringPath where
    member deepTexts[disclose(owner)] as ownerPresent
    if eq(ownerPresent, false) then {
      insert deepTexts[disclose(owner)] := emptyMap
    } else {
    }
    reset deepTexts[disclose(owner)][disclose(group)]
  end

  entry pushDeep uses nestedOpaqueDeepStringWrite where
    pushFront deepTexts[disclose(owner)][disclose(group)] := disclose(text)
  end

  entry inspectDeep uses nestedOpaqueDeepStringPath where
    headOrDefault deepTexts[disclose(owner)][disclose(group)] as (present, currentText)
    returnMaybe textHead as (present, currentText)
  end

  entry popDeep uses nestedOpaqueDeepStringPath where
    popFront deepTexts[disclose(owner)][disclose(group)]
  end
end

private def nestedOpaqueStringEntry (name : String) : Entrypoint :=
  (NestedOpaqueLists.entrypoints.find? (·.name == name)).getD
    {name := "missing", circuit := {name := "missing"}}

#guard match NestedOpaqueLists.state with
  | [{name := "texts", kind := .tree (.map (.bytes 32) (.list _ (.scalar .opaqueString))), ..},
     {name := "deepTexts", kind := .tree (.map (.bytes 32)
       (.map (.bytes 32) (.list _ (.scalar .opaqueString)))), ..}] => Bool.true
  | _ => Bool.false

#guard match LedgerValueType.validate Capabilities.source
    (.map (.bytes 32) (.list {} (.scalar .opaqueString))) with
  | .ok _ => Bool.true
  | .error _ => Bool.false

#guard match LedgerValueType.validate Capabilities.source
    (.map (.bytes 32) (.map (.bytes 32) (.list {} (.scalar .opaqueString)))) with
  | .ok _ => Bool.true
  | .error _ => Bool.false

#guard match LedgerValueType.validate Capabilities.source
    (.map (.bytes 32) (.map (.bytes 32)
      (.map (.bytes 32) (.list {} (.scalar .opaqueString))))) with
  | .error _ => Bool.true
  | .ok _ => Bool.false

#guard match NestedOpaqueLists.validate Capabilities.source with
  | .ok _ => Bool.true
  | .error _ => Bool.false

#guard match Backend.Impact.lower NestedOpaqueLists.state (nestedOpaqueStringEntry "push") with
  | .ok _ => Bool.true
  | .error _ => Bool.false

#guard match Backend.Impact.lower NestedOpaqueLists.state (nestedOpaqueStringEntry "inspect") with
  | .ok _ => Bool.true
  | .error _ => Bool.false

#guard match Backend.Impact.lower NestedOpaqueLists.state (nestedOpaqueStringEntry "pop") with
  | .ok _ => Bool.true
  | .error _ => Bool.false

#guard match Backend.Zkir.lowerPrunedEntrypoint NestedOpaqueLists.state
    (nestedOpaqueStringEntry "push") with
  | .ok _ => Bool.true
  | .error _ => Bool.false

#guard match Backend.Zkir.lowerPrunedEntrypoint NestedOpaqueLists.state
    (nestedOpaqueStringEntry "inspect") with
  | .ok _ => Bool.true
  | .error _ => Bool.false

#guard match Backend.Zkir.lowerPrunedEntrypoint NestedOpaqueLists.state
    (nestedOpaqueStringEntry "pop") with
  | .ok _ => Bool.true
  | .error _ => Bool.false

#guard ["clearDeep", "pushDeep", "inspectDeep", "popDeep"].all fun name =>
  match Backend.Impact.lower NestedOpaqueLists.state (nestedOpaqueStringEntry name) with
  | .ok _ => Bool.true
  | .error _ => Bool.false

#guard ["clearDeep", "pushDeep", "inspectDeep", "popDeep"].all fun name =>
  match Backend.Zkir.lowerPrunedEntrypoint NestedOpaqueLists.state
      (nestedOpaqueStringEntry name) with
  | .ok _ => Bool.true
  | .error _ => Bool.false
