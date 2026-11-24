import Noctium.Frontend
import Noctium.Backend.Impact
import Noctium.Backend.Zkir

open scoped Noctium
open Noctium

noctium_circuit zeroWidthListMaybeNoInputs where
end

noctium_contract NativeZeroWidthListMaybe where
  list inbox : Bytes 0

  entry push uses zeroWidthListMaybeNoInputs where
    pushFront inbox := bytes(0, "")
  end

  entry pop uses zeroWidthListMaybeNoInputs where
    popFront inbox
  end

  entry peek uses zeroWidthListMaybeNoInputs where
    headOrDefault inbox as (present, payload)
    returnMaybe item as (present, payload)
  end
end

private def zeroWidthListMaybeEntry (name : String) : Entrypoint :=
  (NativeZeroWidthListMaybe.entrypoints.find? (·.name == name)).getD
    {name := "missing", circuit := {name := "missing"}}

private def zeroWidthListMaybeContext : EvalContext := {
  modulus := Field.modulus
  poseidon2 := fun _ _ _ => .error "unused by zero-width List Maybe fixture"
}

private def zeroWidthListMaybeState (values : List (List Value)) : LedgerState := {
  trees := [("inbox", .list values)]
}

#guard match Backend.Impact.lower NativeZeroWidthListMaybe.state
    (zeroWidthListMaybeEntry "peek") with
  | .ok _ => Bool.true
  | .error _ => Bool.false

#guard match Backend.Zkir.lowerEntrypoint NativeZeroWidthListMaybe.state
    (zeroWidthListMaybeEntry "peek") with
  | .ok _ => Bool.true
  | .error _ => Bool.false

#guard match zeroWidthListMaybeEntry "peek" with
  | {returns := [tag, payload], returnViews := [view], ..} =>
      tag.name == "item_is_some" && tag.ty == .native &&
      payload.name == "item_value" && payload.ty == .bytes 0 &&
      payload.nativeReturnFieldCount == 0 &&
      view.fields == ["item_is_some"] && view.packedBytesFields.isEmpty &&
      match Types.compileType view.environment view.type with
      | .ok compiled => compiled.checked.expandedLeaves == 1 &&
          view.physicalFieldCount compiled.checked.expandedLeaves == 1
      | .error _ => Bool.false
  | _ => Bool.false

#guard match (zeroWidthListMaybeEntry "peek").run zeroWidthListMaybeContext []
    (zeroWidthListMaybeState []) with
  | .ok (outputs, _) =>
      outputs.lookup "item_is_some" == some (.native 0) &&
      outputs.lookup "item_value" == some (.bytes 0 [])
  | .error _ => Bool.false

#guard match (zeroWidthListMaybeEntry "push").run zeroWidthListMaybeContext []
    (zeroWidthListMaybeState []) with
  | .ok (outputs, state) =>
      outputs.isEmpty &&
      state.trees.lookup "inbox" == some (.list [[.bytes 0 []]]) &&
      match (zeroWidthListMaybeEntry "peek").run zeroWidthListMaybeContext [] state with
      | .ok (peekOutputs, _) =>
          peekOutputs.lookup "item_is_some" == some (.native 1) &&
          peekOutputs.lookup "item_value" == some (.bytes 0 [])
      | .error _ => Bool.false
  | .error _ => Bool.false

#guard match (zeroWidthListMaybeEntry "push").run zeroWidthListMaybeContext []
    (zeroWidthListMaybeState []) with
  | .ok (_, populated) =>
      match (zeroWidthListMaybeEntry "pop").run zeroWidthListMaybeContext [] populated with
      | .ok (_, emptied) =>
          match (zeroWidthListMaybeEntry "peek").run zeroWidthListMaybeContext [] emptied with
          | .ok (outputs, _) =>
              outputs.lookup "item_is_some" == some (.native 0) &&
              outputs.lookup "item_value" == some (.bytes 0 [])
          | .error _ => Bool.false
      | .error _ => Bool.false
  | .error _ => Bool.false
