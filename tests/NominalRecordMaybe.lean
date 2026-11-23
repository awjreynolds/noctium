import Noctium.Frontend
import Noctium.Backend.Impact
import Noctium.Compiler

open scoped Noctium
open Lean
open Noctium

namespace NominalRecordMaybeFixture

noctium_uint_type Amount := UInt 8
noctium_uint_type Count := UInt 8

noctium_circuit noInputs where
end

noctium_circuit recordInputs where
  private amount : Amount
  private count : Count
end

noctium_contract NominalRecordMaybe where
  list history : struct Position {
    amount : Amount
    count : Count
    active : Bool
  }

  entry remember uses recordInputs arguments [amount, count] where
    pushFront history := fields(disclose(amount), disclose(count), true)
  end

  entry inspect uses noInputs where
    headOrDefault history as (present, latest)
    returnMaybe latestPosition as (present, latest)
  end
end

private def maybeEntry : Entrypoint :=
  (NominalRecordMaybe.entrypoints.find? (·.name == "inspect")).getD
    {name := "missing", circuit := {name := "missing"}}

private def maybePlanJson : Except String Json := do
  let entrypoint := maybeEntry
  let plan ← (Backend.Impact.lower NominalRecordMaybe.state entrypoint).mapError (·.message)
  pure (Compiler.nativePlanJson TargetProfile.selected321 `NominalRecordMaybe
    NominalRecordMaybe.state none entrypoint plan)

#guard maybeEntry.returns.map (·.ty) == [.native, .native, .native, .native]

#guard maybeEntry.returnViews.any fun view =>
  view.nominalUIntFields == [
    {path := ["value", "amount"], nominalUInt := Amount.nominalType},
    {path := ["value", "count"], nominalUInt := Count.nominalType}]

private def keepsUnderlyingWireTypes (view : Lean.Json) : _root_.Bool :=
  let schema := view.getObjValD "schema"
  let layout := schema.getObjValD "layout"
  let fields := ((layout.getObjVal? "fields").toOption.getD Json.null).getArr?.toOption.getD #[]
  let valueLayout := (fields[1]?.getD Json.null).getObjValD "layout"
  let valueFields := ((valueLayout.getObjVal? "fields").toOption.getD Json.null).getArr?.toOption.getD #[]
  let expectedUIntLeaf := Json.mkObj [
    ("kind", toJson ("uint" : String)),
    ("maximum", toJson ("255" : String))]
  let expectedBoolLeaf := Json.mkObj [("kind", toJson ("bool" : String))]
  fields.size == 2 && valueFields.size == 3 &&
    ((valueFields[0]?.getD Json.null).getObjValD "layout").getObjValD "leaf" == expectedUIntLeaf &&
    ((valueFields[1]?.getD Json.null).getObjValD "layout").getObjValD "leaf" == expectedUIntLeaf &&
    ((valueFields[2]?.getD Json.null).getObjValD "layout").getObjValD "leaf" == expectedBoolLeaf

#guard match maybePlanJson with
  | .ok plan =>
      match (plan.getObjVal? "returnViews").toOption with
      | some (.arr #[view]) =>
          view.getObjValD "name" == toJson ("latestPosition" : String) &&
          view.getObjValD "fields" ==
            toJson (["latestPosition_is_some", "latestPosition_value_amount",
              "latestPosition_value_count", "latestPosition_value_active"] : List String) &&
          view.getObjValD "nominalUIntFields" == Json.arr #[
            Json.mkObj [
              ("path", toJson (["value", "amount"] : List String)),
              ("name", toJson Amount.nominalType.name),
              ("maximum", toJson (toString Amount.nominalType.maximum))],
            Json.mkObj [
              ("path", toJson (["value", "count"] : List String)),
              ("name", toJson Count.nominalType.name),
              ("maximum", toJson (toString Count.nominalType.maximum))]] &&
          keepsUnderlyingWireTypes view
      | _ => Bool.false
  | .error _ => Bool.false

end NominalRecordMaybeFixture
