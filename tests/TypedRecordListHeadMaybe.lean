import Noctium.Frontend
import Noctium.Backend.Impact
import Noctium.Backend.Zkir

open scoped Noctium
open Noctium

noctium_circuit typedRecordListSeedInputs where
  private active : Bool
  private amount : UInt 16
end

noctium_circuit typedRecordListNoInputs where
end

noctium_contract TypedRecordListHeadMaybe where
  list inbox : struct Memo {
    active : Bool
    amount : UInt 16
  }

  entry seed uses typedRecordListSeedInputs arguments [active, amount] where
    pushFront inbox := fields(disclose(active), disclose(amount))
  end

  entry peek uses typedRecordListNoInputs where
    headOrDefault inbox as (present, payload)
    returnMaybe head as (present, payload)
  end
end

private def typedMaybeContext : EvalContext := {
  modulus := Field.modulus
  poseidon2 := fun _ _ _ => .error "unused by typed List Maybe fixture"
}

private def typedMaybeEntry (name : String) : Entrypoint :=
  (TypedRecordListHeadMaybe.entrypoints.find? (·.name == name)).getD
    {name := "missing", circuit := {name := "missing"}}

private def emptyTypedMaybeState : LedgerState :=
  {trees := [("inbox", .list [])]}

#guard match Backend.Impact.lower TypedRecordListHeadMaybe.state (typedMaybeEntry "seed") with
  | .ok _ => _root_.Bool.true
  | .error _ => _root_.Bool.false

#guard match Backend.Impact.lower TypedRecordListHeadMaybe.state (typedMaybeEntry "peek") with
  | .ok _ => _root_.Bool.true
  | .error _ => _root_.Bool.false

#guard match Backend.Zkir.lowerEntrypoint TypedRecordListHeadMaybe.state (typedMaybeEntry "peek") with
  | .ok _ => _root_.Bool.true
  | .error _ => _root_.Bool.false

#guard match (typedMaybeEntry "peek").run typedMaybeContext [] emptyTypedMaybeState with
  | .ok (outputs, _) =>
      outputs.lookup "head_is_some" == some (.native 0) &&
      outputs.lookup "head_value_active" == some (.native 0) &&
      outputs.lookup "head_value_amount" == some (.native 0)
  | .error _ => _root_.Bool.false

#guard match (typedMaybeEntry "seed").run typedMaybeContext
    [("active", .bool _root_.Bool.true), ("amount", .uint 65535 513)] emptyTypedMaybeState with
  | .ok (_, populated) =>
    match (typedMaybeEntry "peek").run typedMaybeContext [] populated with
    | .ok (outputs, _) =>
        outputs.lookup "head_is_some" == some (.native 1) &&
        outputs.lookup "head_value_active" == some (.native 1) &&
        outputs.lookup "head_value_amount" == some (.native 513)
    | .error _ => _root_.Bool.false
  | .error _ => _root_.Bool.false

private def overwideUIntListEnvironment : Types.CompositeEnv := {
  structures := [{
    id := "OverwideUIntMemo"
    fields := [{name := "amount", type := .scalar (.uint (ScalarPolicy.maxUint + 1))}]
  }]
}

#guard match LedgerValueType.listElementFields overwideUIntListEnvironment
    (.structure "OverwideUIntMemo") with
  | .error _ => _root_.Bool.true
  | .ok _ => _root_.Bool.false
