import Noctium.Frontend

open scoped Noctium

noctium_circuit setInputs where
  public bucket : Native
  public tag : Bytes32
  public adding : Bool
  public removing : Bool
  public clearing : Bool
end

noctium_circuit setInspection where
  private bucket : Native
  public enabled : Bool
end

noctium_contract NativeSet where
  set registered : Bytes32
  tree groups : Native => Set Bytes32
  entry update uses setInputs where
    member groups[bucket] as initialized
    when eq(initialized, false) reset groups[bucket]
    when adding insert registered[tag]
    when adding insert groups[bucket][tag]
    when removing remove registered[tag]
    when removing remove groups[bucket][tag]
    when clearing reset registered
    when clearing reset groups[bucket]
    member registered[tag] as present
    member groups[bucket][tag] as inGroup
    size registered as total
    size groups[bucket] as groupSize
    return containsTag : Bool := present
    return groupContainsTag : Bool := inGroup
    return totalTags : UInt 64 := total
    return groupTags : UInt 64 := groupSize
    return isEmpty : Bool := eq(total, uint(0))
  end
  entry inspect uses setInspection where
    isEmpty registered as noTags
    isEmpty groups as noGroups
    when enabled isEmpty groups[disclose(bucket)] as groupEmpty
    return registeredEmpty : Bool := noTags
    return groupsEmpty : Bool := noGroups
    return selectedEmpty : Bool := groupEmpty
  end
end

open Noctium

#guard
  let tag : Value := .bytes 32 (List.replicate 32 7)
  let ctx : EvalContext := {modulus := Field.modulus, poseidon2 := fun _ _ _ => .error "unused"}
  match NativeSet.entrypoints.find? (·.name == "update") with
  | some ep =>
    match ep.run ctx [
        ("bucket", .native 1), ("tag", tag), ("adding", .bool Bool.true),
        ("removing", .bool Bool.false), ("clearing", .bool Bool.false)]
        {trees := [("registered", .map []), ("groups", .map [])]} with
    | .ok (outputs, state) =>
      outputs.lookup "containsTag" == some (.bool Bool.true) &&
      outputs.lookup "groupContainsTag" == some (.bool Bool.true) &&
      outputs.lookup "totalTags" == some (.uint (2 ^ 64 - 1) 1) &&
      outputs.lookup "groupTags" == some (.uint (2 ^ 64 - 1) 1) &&
      outputs.lookup "isEmpty" == some (.bool Bool.false) &&
      state.trees.lookup "registered" == some (.map [(tag, .null)]) &&
      state.trees.lookup "groups" == some (.map [(.native 1, .map [(tag, .null)])])
    | .error _ => Bool.false
  | none => Bool.false

#guard
  let tag : Value := .bytes 32 (List.replicate 32 7)
  let ctx : EvalContext := {modulus := Field.modulus, poseidon2 := fun _ _ _ => .error "unused"}
  let initial : LedgerState := {trees := [("registered", .map []), ("groups", .map [])]}
  match NativeSet.entrypoints.find? (·.name == "update") with
  | some ep =>
    match ep.run ctx [
        ("bucket", .native 1), ("tag", tag), ("adding", .bool Bool.true),
        ("removing", .bool Bool.false), ("clearing", .bool Bool.false)] initial with
    | .ok (_, inserted) =>
      match ep.run ctx [
          ("bucket", .native 1), ("tag", tag), ("adding", .bool Bool.false),
          ("removing", .bool Bool.true), ("clearing", .bool Bool.false)] inserted with
      | .ok (outputs, removed) =>
        outputs.lookup "containsTag" == some (.bool Bool.false) &&
        outputs.lookup "groupContainsTag" == some (.bool Bool.false) &&
        outputs.lookup "totalTags" == some (.uint (2 ^ 64 - 1) 0) &&
        outputs.lookup "groupTags" == some (.uint (2 ^ 64 - 1) 0) &&
        outputs.lookup "isEmpty" == some (.bool Bool.true) &&
        removed.trees.lookup "registered" == some (.map [])
      | .error _ => Bool.false
    | .error _ => Bool.false
  | none => Bool.false

#guard
  let ctx : EvalContext := {modulus := Field.modulus, poseidon2 := fun _ _ _ => .error "unused"}
  let initial : LedgerState := {trees := [("registered", .map []), ("groups", .map [])]}
  match NativeSet.entrypoints.find? (·.name == "inspect") with
  | some ep =>
    match ep.run ctx [("bucket", .native 1), ("enabled", .bool Bool.false)] initial with
    | .ok (outputs, after) =>
      outputs.lookup "registeredEmpty" == some (.bool Bool.true) &&
      outputs.lookup "groupsEmpty" == some (.bool Bool.true) &&
      outputs.lookup "selectedEmpty" == some (.bool Bool.false) && after == initial
    | .error _ => Bool.false
  | none => Bool.false

#guard
  let subject : Entrypoint := {
    name := "privateTag"
    circuit := {name := "privateTag", inputs := [{name := "tag", ty := .bytes 32, visibility := .private}]}
    effects := [.setInsert "registered" [.mk (.bytes 32) (.ref "tag")]]
  }
  match Disclosure.entrypoint subject with
  | .error diagnostic => diagnostic.message.contains "undisclosed private parameter 'tag'"
  | .ok _ => Bool.false

#guard
  let subject : Entrypoint := {
    name := "privateGroup"
    circuit := {name := "privateGroup", inputs := [{name := "bucket", ty := .native, visibility := .private}]}
    effects := [.mapIsEmpty "groups" "empty" [.mk .native (.ref "bucket")]]
  }
  match Disclosure.entrypoint subject with
  | .error diagnostic => diagnostic.message.contains "undisclosed private parameter 'bucket'"
  | .ok _ => Bool.false

#guard match (LedgerValueType.set (.bytes 31)).validate Capabilities.source with
  | .ok _ => Bool.true
  | .error _ => Bool.false
