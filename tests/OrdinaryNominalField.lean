import Noctium.Frontend
import Noctium.Authoring
import Noctium.Semantics

open scoped Noctium
open Noctium

namespace OrdinaryNominalField

noctium_field_type Amount := Field
noctium_field_type Count := Field
noctium_uint_type Small := UInt 8
noctium_uint_type OtherSmall := UInt 8

/- error: nominal Field aliases are only supported in ordinary circuit declarations -/
#guard_msgs (substring := true) in
noctium_interface FieldAliasInterface where
  entry takeAmount accepts [amount : Amount] yields [result : Amount]
end

noctium_circuit addAmount where
  private left : Amount
  private right : Amount
  let total : Amount := add(left, right)
  output result : Amount := disclose(total)
  output difference : Amount := disclose(sub(left, right))
  output product : Amount := disclose(mul(left, right))
end

noctium_contract FieldContractAlias where
  entry echo uses addAmount where
    return returned : Amount := result
  end
  entry echoAsNative uses addAmount where
    return returned : Native := cast(Native, result)
  end
end

/- error: nominal Field values require an explicit cast and must match the target type -/
#guard_msgs (substring := true) in
noctium_contract RejectImplicitFieldErasure where
  entry echo uses addAmount where
    return returned : Native := result
  end
end

/- error: nominal Field values require an explicit cast and must match the target type -/
#guard_msgs (substring := true) in
noctium_contract RejectForeignFieldErasure where
  entry echo uses addAmount where
    return returned : Count := result
  end
end

noctium_interface NativeFieldEcho where
  entry echo accepts [] yields [returned : Native]
end

/- error: entry 'echo' does not match interface -/
#guard_msgs (substring := true) in
noctium_implements FieldContractAlias implements NativeFieldEcho

/- error: nominal Field interface values are unsupported in callCommitment -/
#guard_msgs (substring := true) in
noctium_circuit rejectsNominalFieldCommitment where
  output commitment : Native := callCommitment(FieldContractAlias, "echo", 1, [], [1])
end

noctium_circuit castField where
  private raw : Native
  let amount : Amount := cast(Amount, raw)
  output result : Native := disclose(cast(Native, amount))
end

noctium_circuit inlineFieldCasts where
  private left : Native
  private right : Native
  let total : Amount := add(cast(Amount, left), cast(Amount, right))
  output result : Amount := disclose(total)
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

/- error: nominal Field arithmetic requires matching nominal operands -/
#guard_msgs (substring := true) in
noctium_circuit rejectsFieldAndNominalUIntMix where
  private amount : Amount
  private count : Small
  output result : Amount := disclose(add(amount, count))
end

/- error: nominal UInt arithmetic requires matching nominal operands -/
#guard_msgs (substring := true) in
noctium_circuit retainsNominalUIntChecksInsideFieldExpression where
  private amount : Amount
  private first : Small
  private second : OtherSmall
  output result : Amount := disclose(add(amount, add(first, second)))
end

#guard addAmount.inputs.map (·.ty) == [.native, .native]
#guard addAmount.outputs.map (·.ty) == [.native, .native, .native]

private def attachedEcho : Entrypoint :=
  (FieldContractAlias.entrypoints.find? (·.name == "echo")).getD
    {name := "", circuit := {name := ""}}
private def attachedNativeEcho : Entrypoint :=
  (FieldContractAlias.entrypoints.find? (·.name == "echoAsNative")).getD
    {name := "", circuit := {name := ""}}

#guard attachedEcho.returns.map (·.ty) == [.native]
#guard attachedNativeEcho.returns.map (·.ty) == [.native]

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

#guard match inlineFieldCasts.run fieldContext [
    ("left", .native (fieldModulus - 1)), ("right", .native 2)] with
  | .ok values => values == [("result", .native 1)]
  | _ => Bool.false

end OrdinaryNominalField
