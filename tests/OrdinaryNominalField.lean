import Noctium.Frontend
import Noctium.Authoring
import Noctium.Semantics

open scoped Noctium
open Noctium

namespace OrdinaryNominalField

noctium_field_type Amount := Field
noctium_field_type Count := Field

noctium_circuit addAmount where
  private left : Amount
  private right : Amount
  let total : Amount := add(left, right)
  output result : Amount := disclose(total)
  output difference : Amount := disclose(sub(left, right))
  output product : Amount := disclose(mul(left, right))
end

noctium_circuit castField where
  private raw : Native
  let amount : Amount := cast(Amount, raw)
  output result : Native := disclose(cast(Native, amount))
end

/- error: nominal Field arithmetic requires matching nominal operands -/
#guard_msgs (substring := true) in
noctium_circuit rejectsMixedAliases where
  private amount : Amount
  private count : Count
  output result : Amount := disclose(add(amount, count))
end

/- error: nominal Field values require an explicit cast and must match the target type -/
#guard_msgs (substring := true) in
noctium_circuit rejectsImplicitOutputCast where
  private amount : Amount
  output result : Native := disclose(amount)
end

/- error: nominal Field arithmetic requires matching nominal operands -/
#guard_msgs (substring := true) in
noctium_circuit rejectsMixedAliasBinding where
  private amount : Amount
  private count : Count
  let total : Amount := add(amount, count)
  output result : Amount := disclose(total)
end

#guard addAmount.inputs.map (·.ty) == [.native, .native]
#guard addAmount.outputs.map (·.ty) == [.native, .native, .native]

private def fieldModulus := Field.modulus
private def fieldContext : EvalContext := {
  modulus := fieldModulus
  poseidon2 := fun _ _ _ => .error "unused by this fixture"
}

#guard match addAmount.run fieldContext [
    ("left", .native (fieldModulus - 1)), ("right", .native 2)] with
  | .ok values => values == [
      ("result", .native 1),
      ("difference", .native (fieldModulus - 3)),
      ("product", .native (fieldModulus - 2))]
  | _ => Bool.false

#guard match castField.run fieldContext [("raw", .native 37)] with
  | .ok values => values == [("result", .native 37)]
  | _ => Bool.false

end OrdinaryNominalField
