import Noctium.Frontend

open scoped Noctium
open Noctium
open Noctium.Helpers

namespace NominalUInt

noctium_uint_type Amount := UInt 8
noctium_uint_type Count := UInt 8
noctium_uint_type MaxAmount := UInt 248

noctium_witness preserveAmount(value : Amount) : Amount
noctium_witness acceptRaw(value : UInt 8) : UInt 8

noctium_private_state Wallet where
  cell balance : Amount
end

noctium_witness_circuit amountArithmetic where
  private left : Amount
  private right : Amount
  let sum := add(left, right)
  output result : Amount := disclose(sum)
end

noctium_witness_circuit checkedAmountCast where
  private raw : UInt 9
  output result : Amount := disclose(cast(Amount, raw))
end

noctium_witness_circuit amountHelperFlow where
  private amount : Amount
  let returned := witness preserveAmount(amount)
  let sum := add(returned, amount)
  output result : Amount := disclose(sum)
end

noctium_witness_circuit amountPrivateState where
  read private Wallet.balance as balance
  let next := add(balance, default(Amount))
  stage Wallet.balance := next
  output result : Amount := disclose(next)
end

noctium_circuit lowLevelAmountArithmetic where
  private left : Amount
  private right : Amount
  let sum : Amount := add(left, right)
  output result : Amount := disclose(sum)
end

noctium_circuit lowLevelAmountCast where
  private raw : UInt 9
  output result : Amount := disclose(cast(Amount, raw))
end

noctium_circuit lowLevelAmountUnderlyingCast where
  private amount : Amount
  output result : UInt 8 := disclose(cast(UInt 8, amount))
end

noctium_circuit lowLevelCastedAmountArithmetic where
  private left : UInt 8
  private right : UInt 8
  output result : Amount := disclose(add(cast(Amount, left), cast(Amount, right)))
end

#guard preserveAmount.__witnessSignature.parameters.map (·.sourceNominal) ==
  [some "NominalUInt.Amount"]
#guard preserveAmount.__witnessSignature.resultNominal == some "NominalUInt.Amount"
#guard preserveAmount.__witnessSignature.parameters.map (·.type) ==
  [.scalar (.uint 255)]
#guard preserveAmount.__witnessSignature.result == .scalar (.uint 255)
#guard match Wallet.__privateStateSchema.fields with
  | [field] => field.signature.resultNominal == some "NominalUInt.Amount" &&
      field.signature.result == (ResultType.scalar (.uint 255))
  | _ => Bool.false
#guard amountArithmetic.__program.exports.any fun exported =>
  exported.inputs.map (·.ty) == [.uint 255, .uint 255]
#guard amountArithmetic.__program.declarations.any fun declaration =>
  declaration.name == "NominalUInt.amountArithmetic" &&
    declaration.result == .scalar (.uint 255)

private def arithmeticEntry : String :=
  (amountArithmetic.__program.exports.headD {name := "", target := ⟨0, 0⟩}).name
private def castEntry : String :=
  (checkedAmountCast.__program.exports.headD {name := "", target := ⟨0, 0⟩}).name

#guard (Noctium.Witness.compile amountArithmetic.__program arithmeticEntry).isOk
#guard (Noctium.Witness.compile checkedAmountCast.__program castEntry).isOk
#guard (Noctium.Witness.compile amountHelperFlow.__program
  (amountHelperFlow.__program.exports.headD {name := "", target := ⟨0, 0⟩}).name).isOk
#guard (Noctium.Witness.compile amountPrivateState.__program
  (amountPrivateState.__program.exports.headD {name := "", target := ⟨0, 0⟩}).name).isOk

#guard match Noctium.Witness.compile amountArithmetic.__program arithmeticEntry with
  | .ok compiled => (Noctium.Backend.Zkir.lowerCircuit compiled.circuit).isOk
  | .error _ => Bool.false
#guard match Noctium.Witness.compile checkedAmountCast.__program castEntry with
  | .ok compiled => (Noctium.Backend.Zkir.lowerCircuit compiled.circuit).isOk
  | .error _ => Bool.false

#guard (Noctium.Backend.Zkir.lowerCircuit lowLevelAmountArithmetic).isOk
#guard (Noctium.Backend.Zkir.lowerCircuit lowLevelAmountCast).isOk
#guard (Noctium.Backend.Zkir.lowerCircuit lowLevelAmountUnderlyingCast).isOk
#guard (Noctium.Backend.Zkir.lowerCircuit lowLevelCastedAmountArithmetic).isOk

private def context : EvalContext := {
  modulus := Field.modulus,
  poseidon2 := fun _ _ _ => .error "unused Poseidon oracle"
}

#guard match Noctium.Witness.compile amountArithmetic.__program arithmeticEntry with
  | .ok compiled =>
    match compiled.circuit.run context [
      ("left", .uint 255 1), ("right", .uint 255 1)] with
    | .ok [(_, .uint 255 2)] => Bool.true
    | _ => Bool.false
  | .error _ => Bool.false

#guard match Noctium.Witness.compile amountArithmetic.__program arithmeticEntry with
  | .ok compiled =>
    match compiled.circuit.run context [
      ("left", .uint 255 255), ("right", .uint 255 0)] with
    | .ok [(_, .uint 255 255)] => Bool.true
    | _ => Bool.false
  | .error _ => Bool.false

#guard match Noctium.Witness.compile amountArithmetic.__program arithmeticEntry with
  | .ok compiled =>
    match compiled.circuit.run context [
      ("left", .uint 255 255), ("right", .uint 255 1)] with
    | .error _ => Bool.true
    | _ => Bool.false
  | .error _ => Bool.false

#guard match Noctium.Witness.compile checkedAmountCast.__program castEntry with
  | .ok compiled =>
    match compiled.circuit.run context [("raw", .uint 511 255)] with
    | .ok [(_, .uint 255 255)] => Bool.true
    | _ => Bool.false
  | .error _ => Bool.false

#guard match Noctium.Witness.compile amountHelperFlow.__program
    (amountHelperFlow.__program.exports.headD {name := "", target := ⟨0, 0⟩}).name with
  | .ok compiled => compiled.circuit.inputs.map (·.ty) == [.uint 255, .uint 255]
  | .error _ => Bool.false

#guard match Noctium.Witness.compile checkedAmountCast.__program castEntry with
  | .ok compiled =>
    match compiled.circuit.run context [("raw", .uint 511 256)] with
    | .error _ => Bool.true
    | _ => Bool.false
  | .error _ => Bool.false

#guard match lowLevelAmountArithmetic.run context [
    ("left", .uint 255 1), ("right", .uint 255 1)] with
  | .ok [("result", .uint 255 2)] => Bool.true
  | _ => Bool.false

#guard match lowLevelAmountArithmetic.run context [
    ("left", .uint 255 255), ("right", .uint 255 1)] with
  | .error _ => Bool.true
  | _ => Bool.false

#guard match lowLevelAmountCast.run context [("raw", .uint 511 255)] with
  | .ok [("result", .uint 255 255)] => Bool.true
  | _ => Bool.false

#guard match lowLevelAmountCast.run context [("raw", .uint 511 256)] with
  | .error _ => Bool.true
  | _ => Bool.false

#guard match lowLevelAmountUnderlyingCast.run context [("amount", .uint 255 255)] with
  | .ok [("result", .uint 255 255)] => Bool.true
  | _ => Bool.false

#guard match lowLevelCastedAmountArithmetic.run context [
    ("left", .uint 255 1), ("right", .uint 255 1)] with
  | .ok [("result", .uint 255 2)] => Bool.true
  | _ => Bool.false

/- error: nominal UInt values require an explicit cast and must match the target type -/
#guard_msgs (substring := true) in
noctium_witness_circuit rejectsImplicitRawConversion where
  private amount : Amount
  let raw : UInt 8 := amount
  output result : UInt 8 := raw
end

/- error: nominal UInt arithmetic requires matching nominal operands -/
#guard_msgs (substring := true) in
noctium_circuit rejectsLowLevelAliasMix where
  private amount : Amount
  private count : Count
  output result : Amount := add(amount, count)
end

/- error: nominal UInt equality requires matching nominal operands -/
#guard_msgs (substring := true) in
noctium_circuit rejectsLowLevelAliasAssertion where
  private amount : Amount
  private count : Count
  assert eq(amount, count)
end

/- error: nominal UInt values require an explicit cast and must match the target type -/
#guard_msgs (substring := true) in
noctium_circuit rejectsLowLevelImplicitRawOutput where
  private amount : Amount
  output result : UInt 8 := amount
end

/- error: nominal UInt values require an explicit cast and must match the target type -/
#guard_msgs (substring := true) in
noctium_circuit rejectsLowLevelImplicitNominalOutput where
  private raw : UInt 8
  output result : Amount := raw
end

/- error: nominal UInt arithmetic requires matching nominal operands -/
#guard_msgs (substring := true) in
noctium_witness_circuit rejectsDistinctAliases where
  private amount : Amount
  private count : Count
  output result : Amount := add(amount, count)
end

/- error: nominal UInt values require an explicit cast and must match the target type -/
#guard_msgs (substring := true) in
noctium_witness_circuit rejectsRawHelperArgument where
  private raw : UInt 8
  witness preserveAmount(raw)
  output result : Amount := default(Amount)
end

/- error: unsigned width exceeds target maximum -/
#guard_msgs (substring := true) in
noctium_uint_type TooWide := UInt 249

/- error: unsigned type exceeds target maximum -/
#guard_msgs (substring := true) in
noctium_witness_circuit rejectsWideIntermediate where
  private left : MaxAmount
  private right : MaxAmount
  output result : MaxAmount := add(left, right)
end

end NominalUInt
