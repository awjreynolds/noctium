import Noctium.Frontend
import Noctium.Backend.Impact
import Noctium.Backend.Zkir

open scoped Noctium
open Noctium

noctium_circuit scalarListInputs where
  private owner : Bytes32
  private amount : Native
  private payload : Bytes 128
  private empty : Bytes 0
  public enabled : Bool
end

noctium_contract NativeScalarList where
  list values : Native
  list zeroBytes : Bytes 0
  tree memos : Bytes32 => List Bytes 128

  entry append uses scalarListInputs where
    pushFront values := disclose(amount)
    pushFront zeroBytes := disclose(empty)
    pushFront memos[disclose(owner)] := disclose(payload)
    head values as strictNative
    head zeroBytes as strictEmpty
    head memos[disclose(owner)] as strictPayload
    headOrDefault values as (nativePresent, optionalNative)
    headOrDefault zeroBytes as (emptyPresent, optionalEmpty)
    headOrDefault memos[disclose(owner)] as (payloadPresent, optionalPayload)
    length values as nativeLength
    length zeroBytes as emptyLength
    length memos[disclose(owner)] as payloadLength
    isEmpty values as nativeEmpty
    isEmpty zeroBytes as emptyList
    isEmpty memos[disclose(owner)] as payloadEmpty
    return headValue : Native := strictNative
    return headZeroBytes : Bytes 0 := strictEmpty
    return headPayload : Bytes 128 := strictPayload
    return nativePresentResult : Bool := nativePresent
    return nativeOptional : Native := optionalNative
    return emptyPresentResult : Bool := emptyPresent
    return emptyOptional : Bytes 0 := optionalEmpty
    return payloadPresentResult : Bool := payloadPresent
    return payloadOptional : Bytes 128 := optionalPayload
    return nativeCount : UInt 64 := nativeLength
    return emptyCount : UInt 64 := emptyLength
    return payloadCount : UInt 64 := payloadLength
    return nativeIsEmpty : Bool := nativeEmpty
    return zeroBytesIsEmpty : Bool := emptyList
    return payloadIsEmpty : Bool := payloadEmpty
  end

  entry inspect uses scalarListInputs where
    headOrDefault values as (nativePresent, nativeValue)
    headOrDefault zeroBytes as (emptyPresent, emptyValue)
    headOrDefault memos[disclose(owner)] as (payloadPresent, payloadValue)
    length values as nativeLength
    length zeroBytes as emptyLength
    length memos[disclose(owner)] as payloadLength
    isEmpty values as nativeEmpty
    isEmpty zeroBytes as emptyList
    isEmpty memos[disclose(owner)] as payloadEmpty
    return nativePresentResult : Bool := nativePresent
    return nativeDefault : Native := nativeValue
    return emptyPresentResult : Bool := emptyPresent
    return emptyDefault : Bytes 0 := emptyValue
    return payloadPresentResult : Bool := payloadPresent
    return payloadDefault : Bytes 128 := payloadValue
    return nativeCount : UInt 64 := nativeLength
    return emptyCount : UInt 64 := emptyLength
    return payloadCount : UInt 64 := payloadLength
    return nativeIsEmpty : Bool := nativeEmpty
    return zeroBytesIsEmpty : Bool := emptyList
    return payloadIsEmpty : Bool := payloadEmpty
  end

  entry guardMissing uses scalarListInputs where
    when enabled headOrDefault memos[disclose(owner)] as (payloadPresent, payloadValue)
    when enabled isEmpty memos[disclose(owner)] as skippedEmpty
    return hasPayload : Bool := payloadPresent
    return optionalPayload : Bytes 128 := payloadValue
    return pathEmpty : Bool := skippedEmpty
  end

  entry pop uses scalarListInputs where
    popFront values
    popFront zeroBytes
    popFront memos[disclose(owner)]
    headOrDefault values as (nativePresent, nativeValue)
    headOrDefault zeroBytes as (emptyPresent, emptyValue)
    headOrDefault memos[disclose(owner)] as (payloadPresent, payloadValue)
    length values as nativeLength
    length zeroBytes as emptyLength
    length memos[disclose(owner)] as payloadLength
    isEmpty values as nativeEmpty
    isEmpty zeroBytes as emptyList
    isEmpty memos[disclose(owner)] as payloadEmpty
    return nativePresentResult : Bool := nativePresent
    return nativeDefault : Native := nativeValue
    return emptyPresentResult : Bool := emptyPresent
    return emptyDefault : Bytes 0 := emptyValue
    return payloadPresentResult : Bool := payloadPresent
    return payloadDefault : Bytes 128 := payloadValue
    return nativeCount : UInt 64 := nativeLength
    return emptyCount : UInt 64 := emptyLength
    return payloadCount : UInt 64 := payloadLength
    return nativeIsEmpty : Bool := nativeEmpty
    return zeroBytesIsEmpty : Bool := emptyList
    return payloadIsEmpty : Bool := payloadEmpty
  end

  entry popRoot uses scalarListInputs where
    popFront values
  end

  entry popNested uses scalarListInputs where
    popFront memos[disclose(owner)]
  end

  entry guardedPop uses scalarListInputs where
    when enabled popFront values
    when enabled popFront memos[disclose(owner)]
  end

  entry clear uses scalarListInputs where
    reset values
    reset zeroBytes
    reset memos[disclose(owner)]
    headOrDefault values as (nativePresent, nativeValue)
    headOrDefault zeroBytes as (emptyPresent, emptyValue)
    headOrDefault memos[disclose(owner)] as (payloadPresent, payloadValue)
    length values as nativeLength
    length zeroBytes as emptyLength
    length memos[disclose(owner)] as payloadLength
    isEmpty values as nativeEmpty
    isEmpty zeroBytes as emptyList
    isEmpty memos[disclose(owner)] as payloadEmpty
    return nativePresentResult : Bool := nativePresent
    return nativeDefault : Native := nativeValue
    return emptyPresentResult : Bool := emptyPresent
    return emptyDefault : Bytes 0 := emptyValue
    return payloadPresentResult : Bool := payloadPresent
    return payloadDefault : Bytes 128 := payloadValue
    return nativeCount : UInt 64 := nativeLength
    return emptyCount : UInt 64 := emptyLength
    return payloadCount : UInt 64 := payloadLength
    return nativeIsEmpty : Bool := nativeEmpty
    return zeroBytesIsEmpty : Bool := emptyList
    return payloadIsEmpty : Bool := payloadEmpty
  end
end

private def nativeScalarListEntry (name : String) : Entrypoint :=
  match NativeScalarList.entrypoints.find? (·.name == name) with
  | some found => found
  | none => {name := "missing", circuit := {name := "missing"}}

private def scalarListOwner : Value := .bytes 32 (List.replicate 32 7)

private def scalarListInputValues (amount : Nat) (payload : List Nat) : List (String × Value) :=
  [ ("owner", scalarListOwner)
  , ("amount", .native amount)
  , ("payload", .bytes 128 payload)
  , ("empty", .bytes 0 [])
  , ("enabled", .bool Bool.true)
  ]

private def scalarListDisabledInputValues (amount : Nat) (payload : List Nat) :
    List (String × Value) :=
  [ ("owner", scalarListOwner)
  , ("amount", .native amount)
  , ("payload", .bytes 128 payload)
  , ("empty", .bytes 0 [])
  , ("enabled", .bool Bool.false)
  ]

private def scalarListState : LedgerState := {
  trees := [
    ("values", .list []),
    ("zeroBytes", .list []),
    ("memos", .map [(scalarListOwner, .list [])])
  ]
}

private def scalarListAbsentParentState : LedgerState := {
  trees := [
    ("values", .list []),
    ("zeroBytes", .list []),
    ("memos", .map [])
  ]
}

private def scalarListContext : EvalContext := {
  modulus := Field.modulus
  poseidon2 := fun _ _ _ => .error "unused by this fixture"
}

#guard match Backend.Impact.lower NativeScalarList.state (nativeScalarListEntry "append") with
  | .ok _ => Bool.true
  | .error _ => Bool.false

#guard match Backend.Zkir.lowerEntrypoint NativeScalarList.state
    (nativeScalarListEntry "inspect") with
  | .ok _ => Bool.true
  | .error _ => Bool.false

#guard match Backend.Zkir.lowerEntrypoint NativeScalarList.state
    (nativeScalarListEntry "guardMissing") with
  | .ok _ => Bool.true
  | .error _ => Bool.false

#guard match Backend.Zkir.lowerEntrypoint NativeScalarList.state
    (nativeScalarListEntry "pop") with
  | .ok _ => Bool.true
  | .error _ => Bool.false

#guard match Backend.Zkir.lowerEntrypoint NativeScalarList.state
    (nativeScalarListEntry "popRoot") with
  | .ok _ => Bool.true
  | .error _ => Bool.false

#guard match Backend.Zkir.lowerEntrypoint NativeScalarList.state
    (nativeScalarListEntry "popNested") with
  | .ok _ => Bool.true
  | .error _ => Bool.false

#guard match Backend.Zkir.lowerEntrypoint NativeScalarList.state
    (nativeScalarListEntry "guardedPop") with
  | .ok _ => Bool.true
  | .error _ => Bool.false

#guard match Entrypoint.run scalarListContext (nativeScalarListEntry "popRoot")
    (scalarListInputValues 0 (List.replicate 128 0)) scalarListState with
  | .error _ => Bool.true
  | .ok _ => Bool.false

#guard match Entrypoint.run scalarListContext (nativeScalarListEntry "popNested")
    (scalarListInputValues 0 (List.replicate 128 0)) scalarListState with
  | .error _ => Bool.true
  | .ok _ => Bool.false

#guard match Entrypoint.run scalarListContext (nativeScalarListEntry "popNested")
    (scalarListInputValues 0 (List.replicate 128 0)) scalarListAbsentParentState with
  | .error _ => Bool.true
  | .ok _ => Bool.false

#guard match Entrypoint.run scalarListContext (nativeScalarListEntry "guardedPop")
    (scalarListDisabledInputValues 0 (List.replicate 128 0))
    scalarListAbsentParentState with
  | .ok (outputs, state) => outputs.isEmpty && state == scalarListAbsentParentState
  | .error _ => Bool.false

#guard match Entrypoint.run scalarListContext (nativeScalarListEntry "inspect")
    (scalarListInputValues 0 (List.replicate 128 0)) scalarListState with
  | .ok (outputs, _) =>
      outputs.lookup "nativePresentResult" == some (.bool Bool.false) &&
      outputs.lookup "nativeDefault" == some (.native 0) &&
      outputs.lookup "emptyPresentResult" == some (.bool Bool.false) &&
      outputs.lookup "emptyDefault" == some (.bytes 0 []) &&
      outputs.lookup "payloadPresentResult" == some (.bool Bool.false) &&
      outputs.lookup "payloadDefault" == some (.bytes 128 (List.replicate 128 0)) &&
      outputs.lookup "nativeCount" == some (.uint (2 ^ 64 - 1) 0) &&
      outputs.lookup "emptyCount" == some (.uint (2 ^ 64 - 1) 0) &&
      outputs.lookup "payloadCount" == some (.uint (2 ^ 64 - 1) 0) &&
      outputs.lookup "nativeIsEmpty" == some (.bool Bool.true) &&
      outputs.lookup "zeroBytesIsEmpty" == some (.bool Bool.true) &&
      outputs.lookup "payloadIsEmpty" == some (.bool Bool.true)
  | .error _ => Bool.false

#guard match Entrypoint.run scalarListContext (nativeScalarListEntry "append")
    (scalarListInputValues 5 (List.range 128)) scalarListState with
  | .ok (outputs, _) =>
      outputs.lookup "headValue" == some (.native 5) &&
      outputs.lookup "headZeroBytes" == some (.bytes 0 []) &&
      outputs.lookup "headPayload" == some (.bytes 128 (List.range 128)) &&
      outputs.lookup "nativeCount" == some (.uint (2 ^ 64 - 1) 1) &&
      outputs.lookup "payloadCount" == some (.uint (2 ^ 64 - 1) 1)
  | .error _ => Bool.false
