import Noctium.Frontend
import Noctium.Backend.Impact
import Noctium.Backend.Zkir

open scoped Noctium
open Noctium

noctium_circuit mapListInputs where
  private owner : Native
  private value : Native
end

noctium_contract NativeMapList where
  tree buckets : Native => List Native

  entry push uses mapListInputs where
    member buckets[disclose(owner)] as bucketPresent
    if eq(bucketPresent, false) then {
      insertDefault buckets[disclose(owner)]
    } else {
    }
    pushFront buckets[disclose(owner)] := disclose(value)
  end

  entry inspect uses mapListInputs where
    headOrDefault buckets[disclose(owner)] as (present, first)
    length buckets[disclose(owner)] as listLength
    return headPresent : Bool := present
    return head : Native := first
    return length : UInt 64 := listLength
  end

  entry pop uses mapListInputs where
    popFront buckets[disclose(owner)]
  end
end

private def mapListEntry (name : String) : Entrypoint :=
  (NativeMapList.entrypoints.find? (·.name == name)).getD
    {name := "missing", circuit := {name := "missing"}}

private def mapListInputsFor (owner value : Nat) : List (String × Value) :=
  [("owner", .native owner), ("value", .native value)]

private def mapListState (aValues bValues : List Nat) : LedgerState := {
  trees := [
    ("buckets", .map [
      (.native 1, .list (aValues.map fun value => [.native value])),
      (.native 2, .list (bValues.map fun value => [.native value]))
    ])
  ]
}

private def mapListContext : EvalContext := {
  modulus := Field.modulus
  poseidon2 := fun _ _ _ => .error "unused by Map/List fixture"
}

private def runMapList (name : String) (owner value : Nat) (state : LedgerState) :=
  (mapListEntry name).run mapListContext (mapListInputsFor owner value) state

#guard match Backend.Impact.lower NativeMapList.state (mapListEntry "push") with
  | .ok _ => Bool.true
  | .error _ => Bool.false

#guard match Backend.Impact.lower NativeMapList.state (mapListEntry "inspect") with
  | .ok _ => Bool.true
  | .error _ => Bool.false

#guard match Backend.Impact.lower NativeMapList.state (mapListEntry "pop") with
  | .ok _ => Bool.true
  | .error _ => Bool.false

#guard match Backend.Zkir.lowerEntrypoint NativeMapList.state (mapListEntry "push") with
  | .ok _ => Bool.true
  | .error _ => Bool.false

#guard match Backend.Zkir.lowerEntrypoint NativeMapList.state (mapListEntry "inspect") with
  | .ok _ => Bool.true
  | .error _ => Bool.false

#guard match Backend.Zkir.lowerEntrypoint NativeMapList.state (mapListEntry "pop") with
  | .ok _ => Bool.true
  | .error _ => Bool.false

#guard match runMapList "push" 1 11 (mapListState [5] [99]) with
  | .ok (_, state) =>
      match state.trees.lookup "buckets" with
      | some (.map entries) =>
          entries == [
            (.native 1, .list [[.native 11], [.native 5]]),
            (.native 2, .list [[.native 99]])
          ]
      | _ => Bool.false
  | .error _ => Bool.false

#guard match runMapList "push" 1 22 (mapListState [11, 5] [99]) with
  | .ok (_, state) =>
      match state.trees.lookup "buckets" with
      | some (.map entries) =>
          entries == [
            (.native 1, .list [[.native 22], [.native 11], [.native 5]]),
            (.native 2, .list [[.native 99]])
          ]
      | _ => Bool.false
  | .error _ => Bool.false

#guard match runMapList "pop" 1 0 (mapListState [22, 11, 5] [99]) with
  | .ok (_, state) =>
      match state.trees.lookup "buckets" with
      | some (.map entries) =>
          entries == [
            (.native 1, .list [[.native 11], [.native 5]]),
            (.native 2, .list [[.native 99]])
          ]
      | _ => Bool.false
  | .error _ => Bool.false

#guard match runMapList "inspect" 1 0 (mapListState [11, 5] [99]) with
  | .ok (outputs, _) =>
      outputs.lookup "headPresent" == some (.bool Bool.true) &&
      outputs.lookup "head" == some (.native 11) &&
      outputs.lookup "length" == some (.uint (2 ^ 64 - 1) 2)
  | .error _ => Bool.false

#guard match runMapList "inspect" 2 0 (mapListState [11, 5] [99]) with
  | .ok (outputs, _) =>
      outputs.lookup "headPresent" == some (.bool Bool.true) &&
      outputs.lookup "head" == some (.native 99) &&
      outputs.lookup "length" == some (.uint (2 ^ 64 - 1) 1)
  | .error _ => Bool.false

