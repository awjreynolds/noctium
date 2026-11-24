import Noctium.Frontend
import Noctium.Backend.Impact
import Noctium.Backend.Zkir
import Noctium.Compiler
import Noctium.Types.ValueSchema

open scoped Noctium
open Lean
open Noctium
open Noctium.Types

noctium_circuit foreignScalarListPushInputs where
  private value : Secp256k1Scalar
end

noctium_circuit foreignScalarListMaybeNoInputs where
end

noctium_contract ForeignScalarListMaybe where
  list values : Secp256k1Scalar

  entry push uses foreignScalarListPushInputs arguments [value] where
    pushFront values := disclose(value)
    headOrDefault values as (present, payload)
    returnMaybe maybeHead as (present, payload)
  end

  entry head uses foreignScalarListMaybeNoInputs where
    headOrDefault values as (present, payload)
    returnMaybe maybeHead as (present, payload)
  end

  entry pop uses foreignScalarListMaybeNoInputs where
    popFront values
  end
end

private def foreignScalarListMaybeEntry (name : String) : Entrypoint :=
  (ForeignScalarListMaybe.entrypoints.find? (·.name == name)).getD
    {name := "missing", circuit := {name := "missing"}}

private def foreignScalarListMaybeContext : EvalContext := {
  modulus := Field.modulus
  poseidon2 := fun _ _ _ => .error "unused by the foreign scalar List Maybe fixture"
}

private def foreignScalarListMaybeEmpty : LedgerState := {
  trees := [("values", .list [])]
}

private def foreignScalarListMaybeEncode (value : Nat) : List Nat :=
  (Foreign.encodeValue (.scalar .secp256k1) value).toOption.getD []

private def foreignScalarListMaybeRun (name : String) (inputs : EvalEnv)
    (state : LedgerState) :=
  (foreignScalarListMaybeEntry name).run foreignScalarListMaybeContext inputs state

#guard match Backend.Impact.lower ForeignScalarListMaybe.state
    (foreignScalarListMaybeEntry "push") with
  | .ok _ => Bool.true
  | .error _ => Bool.false

#guard match Backend.Impact.lower ForeignScalarListMaybe.state
    (foreignScalarListMaybeEntry "head") with
  | .ok _ => Bool.true
  | .error _ => Bool.false

#guard match Backend.Impact.lower ForeignScalarListMaybe.state
    (foreignScalarListMaybeEntry "pop") with
  | .ok _ => Bool.true
  | .error _ => Bool.false

#guard match Backend.Zkir.lowerEntrypoint ForeignScalarListMaybe.state
    (foreignScalarListMaybeEntry "head") with
  | .ok _ => Bool.true
  | .error _ => Bool.false

#guard match Backend.Zkir.lowerEntrypoint ForeignScalarListMaybe.state
    (foreignScalarListMaybeEntry "push") with
  | .ok _ => Bool.true
  | .error _ => Bool.false

#guard match Backend.Zkir.lowerEntrypoint ForeignScalarListMaybe.state
    (foreignScalarListMaybeEntry "pop") with
  | .ok _ => Bool.true
  | .error _ => Bool.false

-- `None` keeps the canonical two-limb foreign encoding of scalar zero.
#guard match foreignScalarListMaybeRun "head" [] foreignScalarListMaybeEmpty with
  | .ok (outputs, _) =>
    let zero := foreignScalarListMaybeEncode 0
    outputs.lookup "maybeHead_is_some" == some (.native 0) &&
    outputs.lookup "maybeHead_value_low" == some (.native (zero[0]?.getD 0)) &&
    outputs.lookup "maybeHead_value_high" == some (.native (zero[1]?.getD 0))
  | .error _ => Bool.false

#guard match foreignScalarListMaybeRun "push"
    [("value", .foreignScalar .secp256k1 7)] foreignScalarListMaybeEmpty with
  | .ok (outputs, state) =>
    let encoded := foreignScalarListMaybeEncode 7
    outputs.lookup "maybeHead_is_some" == some (.native 1) &&
    outputs.lookup "maybeHead_value_low" == some (.native (encoded[0]?.getD 0)) &&
    outputs.lookup "maybeHead_value_high" == some (.native (encoded[1]?.getD 0)) &&
    state.trees.lookup "values" == some (.list [[.foreignScalar .secp256k1 7]])
  | .error _ => Bool.false

#guard match foreignScalarListMaybeRun "pop" []
    {trees := [("values", .list [[.foreignScalar .secp256k1 7]])]} with
  | .ok (_, state) => state.trees.lookup "values" == some (.list [])
  | .error _ => Bool.false
