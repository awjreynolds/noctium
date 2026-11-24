import Noctium.Frontend

open scoped Noctium
open Noctium
open Noctium.Helpers

namespace NominalField

noctium_field_type Amount := Field
noctium_field_type Count := Field

private def echoNativeProgram : Helpers.Program := {
  declarations := [{
    id := ⟨0, 0⟩
    name := "echoNative"
    parameters := [{name := "value", ty := .native}]
    result := .scalar .native
    body := [.return (some (.ref "value"))]
  }]
}

noctium_witness_circuit fieldAdd where
  private left : Amount
  private right : Amount
  output result : Amount := disclose(add(left, right))
end

noctium_witness_circuit fieldSub where
  private left : Amount
  private right : Amount
  output result : Amount := disclose(sub(left, right))
end

noctium_witness_circuit fieldMul where
  private left : Amount
  private right : Amount
  output result : Amount := disclose(mul(left, right))
end

noctium_witness_circuit sameAliasConditional where
  public chooseLeft : Bool
  private left : Amount
  private right : Amount
  let selected := if chooseLeft then left else right
  output result : Amount := disclose(selected)
end

noctium_witness_circuit explicitFieldCasts where
  private raw : Native
  let wrapped := cast(Amount, raw)
  output roundTrip : Native := disclose(cast(Native, wrapped))
end

/- error: nominal Field arithmetic requires matching nominal operands -/
#guard_msgs (substring := true) in
noctium_witness_circuit rejectsDistinctFieldAliases where
  private amount : Amount
  private count : Count
  output result : Amount := disclose(add(amount, count))
end

noctium_witness_circuit explicitFieldRebrand where
  private amount : Amount
  output result : Count := disclose(cast(Count, amount))
end

/- error: conditional branches require the same nominal Field type -/
#guard_msgs (substring := true) in
noctium_witness_circuit rejectsMismatchedFieldConditional where
  private chooseLeft : Bool
  private amount : Amount
  private count : Count
  output result : Amount := disclose(if chooseLeft then amount else count)
end

/- error: nominal Field values require an explicit cast and must match the target type -/
#guard_msgs (substring := true) in
noctium_witness_circuit rejectsImplicitFieldErase where
  private amount : Amount
  output result : Native := disclose(amount)
end

/- error: invoke helper arguments do not retain nominal Field identity; explicitly cast to Native -/
#guard_msgs (substring := true) in
noctium_witness_circuit rejectsImplicitFieldInvoke with echoNativeProgram where
  private amount : Amount
  let result := invoke(echoNative, [amount])
  output value : Native := disclose(result)
end

/- error: nominal Field values require an explicit cast to Native before persistentHashNative -/
#guard_msgs (substring := true) in
noctium_witness_circuit rejectsImplicitFieldHash where
  private amount : Amount
  output digest : Bytes32 := disclose(persistentHashNative(amount))
end

noctium_witness_circuit acceptsExplicitFieldInvokeErase with echoNativeProgram where
  private amount : Amount
  let result := invoke(echoNative, [cast(Native, amount)])
  output value : Native := disclose(result)
end

/- error: nominal Field witness callback signatures are unsupported in this scalar slice -/
#guard_msgs (substring := true) in
noctium_witness preserveAmount(value : Amount) : Amount

private def context : EvalContext := {
  modulus := Field.modulus
  poseidon2 := fun _ _ _ => pure 0
}

private def addEntry : String := (fieldAdd.__program.exports.headD {name := "", target := ⟨0, 0⟩}).name
private def subEntry : String := (fieldSub.__program.exports.headD {name := "", target := ⟨0, 0⟩}).name
private def mulEntry : String := (fieldMul.__program.exports.headD {name := "", target := ⟨0, 0⟩}).name

#guard match Witness.compile fieldAdd.__program addEntry with
  | .ok compiled =>
    match compiled.circuit.run context [
      ("left", .native (Field.modulus - 1)), ("right", .native 1)] with
    | .ok [(_, .native 0)] => Bool.true
    | _ => Bool.false
  | .error _ => Bool.false

#guard match Witness.compile fieldSub.__program subEntry with
  | .ok compiled =>
    match compiled.circuit.run context [
      ("left", .native 0), ("right", .native 1)] with
    | .ok [(_, .native result)] => result == Field.modulus - 1
    | _ => Bool.false
  | .error _ => Bool.false

#guard match Witness.compile fieldMul.__program mulEntry with
  | .ok compiled =>
    match compiled.circuit.run context [
      ("left", .native (Field.modulus - 1)), ("right", .native 2)] with
    | .ok [(_, .native result)] => result == Field.modulus - 2
    | _ => Bool.false
  | .error _ => Bool.false

#guard match Witness.compile sameAliasConditional.__program
    (sameAliasConditional.__program.exports.headD {name := "", target := ⟨0, 0⟩}).name with
  | .ok compiled =>
    match compiled.circuit.run context [
      ("chooseLeft", .bool Bool.true),
      ("left", .native (Field.modulus - 1)),
      ("right", .native 2)] with
    | .ok [(_, .native result)] => result == Field.modulus - 1
    | _ => Bool.false
  | .error _ => Bool.false

#guard match Witness.compile fieldAdd.__program addEntry with
  | .ok compiled => (Backend.Zkir.lowerCircuit compiled.circuit).isOk
  | .error _ => Bool.false

#guard match Witness.compile fieldSub.__program subEntry with
  | .ok compiled => (Backend.Zkir.lowerCircuit compiled.circuit).isOk
  | .error _ => Bool.false

#guard match Witness.compile fieldMul.__program mulEntry with
  | .ok compiled => (Backend.Zkir.lowerCircuit compiled.circuit).isOk
  | .error _ => Bool.false

#guard (Witness.compile explicitFieldRebrand.__program
  (explicitFieldRebrand.__program.exports.headD {name := "", target := ⟨0, 0⟩}).name).isOk

#guard (Witness.compile acceptsExplicitFieldInvokeErase.__program
  (acceptsExplicitFieldInvokeErase.__program.exports.headD {name := "", target := ⟨0, 0⟩}).name).isOk

#guard match Witness.compile explicitFieldCasts.__program
    (explicitFieldCasts.__program.exports.headD {name := "", target := ⟨0, 0⟩}).name with
  | .ok compiled => (Backend.Zkir.lowerCircuit compiled.circuit).isOk
  | .error _ => Bool.false

#guard match Witness.compile explicitFieldCasts.__program
    (explicitFieldCasts.__program.exports.headD {name := "", target := ⟨0, 0⟩}).name with
  | .ok compiled =>
    match compiled.circuit.run context [("raw", .native (Field.modulus - 1))] with
    | .ok [(_, .native result)] => result == Field.modulus - 1
    | _ => Bool.false
  | .error _ => Bool.false

end NominalField
