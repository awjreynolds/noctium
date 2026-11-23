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

noctium_circuit nominalLedgerValues where
  private amount : Amount
  private raw : UInt 8
  output amountResult : Amount := disclose(amount)
end

noctium_circuit countLedgerValue where
  private count : Count
end

noctium_circuit nominalConditionValues where
  private amount : Amount
  private count : Count
end

private def nominalCellReadProgram : Program := {
  ledger := [{name := "balance", kind := .cell (.uint 255)}]
  declarations := [{
    id := ⟨0, 0⟩
    name := "readBalance"
    result := .scalar (.uint 255)
    body := [
      .readCell "balance" "current" (.uint 255),
      .return (some (.ref "current"))]}]
  exports := [{name := "readBalance", target := ⟨0, 0⟩}]
}

private def nominalCellWriteProgram : Program := {
  ledger := [{name := "balance", kind := .cell (.uint 255)}]
  declarations := [{
    id := ⟨0, 0⟩
    name := "writeBalance"
    result := .unit
    body := [
      .writeCell "balance" (.uint 255) (.uint 255 1),
      .return none]}]
  exports := [{name := "writeBalance", target := ⟨0, 0⟩}]
}

noctium_contract RawUIntHelperCells where
  cell balance : UInt 8
  entry readBalance from nominalCellReadProgram entry "readBalance" end
  entry writeBalance from nominalCellWriteProgram entry "writeBalance" end
end

noctium_contract NominalAmountLedger where
  cell balance : Amount
  constructor(initial : Amount) where
    initialize balance := initial
  end

  entry setAmount uses nominalLedgerValues where
    write balance := disclose(amount)
    read balance as current
    return currentAmount : Amount := current
    return forwardedAmount : Amount := amountResult
  end

  entry setRaw uses nominalLedgerValues where
    write balance := disclose(cast(Amount, raw))
    read balance as current
    return currentAmount : Amount := current
  end
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

#guard match NominalAmountLedger.constructor with
  | some {parameters := [parameter], initializers := [initializer], ..} =>
    parameter.name == "initial" && parameter.type == .scalar (.uint 255) &&
      initializer.state == "balance" && initializer.type == .scalar (.uint 255)
  | _ => Bool.false

private def nominalCellRoundTrip : Except String _root_.Bool := do
  let [setAmount, setRaw] := NominalAmountLedger.entrypoints
    | throw "expected two nominal cell operations"
  let inputs : EvalEnv := [("amount", .uint 255 41), ("raw", .uint 255 255)]
  let (amountOutputs, amountState) ← setAmount.run context inputs
    {cells := [("balance", .uint 255 19)]}
  let (rawOutputs, rawState) ← setRaw.run context inputs amountState
  pure (setAmount.name == "setAmount" && setRaw.name == "setRaw" &&
    amountOutputs.lookup "currentAmount" == some (.uint 255 41) &&
    amountOutputs.lookup "forwardedAmount" == some (.uint 255 41) &&
    amountState.cells.lookup "balance" == some (.uint 255 41) &&
    rawOutputs.lookup "currentAmount" == some (.uint 255 255) &&
    rawState.cells.lookup "balance" == some (.uint 255 255))

#guard nominalCellRoundTrip.toOption == some Bool.true

#guard NominalAmountLedger.entrypoints.all fun operation =>
  (Noctium.Backend.Zkir.lowerEntrypoint NominalAmountLedger.state operation).isOk

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

/- error: nominal UInt values require an explicit cast and must match the target type -/
#guard_msgs (substring := true) in
noctium_contract rejectsNominalCellRawWrite where
  cell balance : Amount
  entry setRaw uses nominalLedgerValues where
    write balance := raw
  end
end

/- error: nominal UInt values require an explicit cast and must match the target type -/
#guard_msgs (substring := true) in
noctium_contract rejectsNominalCellCountWrite where
  cell balance : Amount
  entry setCount uses countLedgerValue where
    write balance := count
  end
end

/- error: nominal UInt values require an explicit cast and must match the target type -/
#guard_msgs (substring := true) in
noctium_contract rejectsNominalCellRawConstructor where
  cell balance : Amount
  constructor(initial : UInt 8) where
    initialize balance := initial
  end
end

/- error: nominal UInt values require an explicit cast and must match the target type -/
#guard_msgs (substring := true) in
noctium_contract rejectsNominalTypedReturn where
  cell balance : Amount
  entry returnRaw uses nominalLedgerValues where
    return rawAmount : Amount := raw
  end
end

/- error: nominal UInt values require an explicit cast and must match the target type -/
#guard_msgs (substring := true) in
noctium_contract rejectsNominalCellReadReturn where
  cell balance : Amount
  entry returnRaw uses nominalLedgerValues where
    read balance as current
    return rawAmount : UInt 8 := current
  end
end

/- error: structured entry helpers cannot read nominal UInt Cell 'balance' until helper tags are supported -/
#guard_msgs (substring := true) in
noctium_contract rejectsNominalCellHelperRead where
  cell balance : Amount
  entry readBalance from nominalCellReadProgram entry "readBalance" end
end

/- error: structured entry helpers cannot write nominal UInt Cell 'balance' until helper tags are supported -/
#guard_msgs (substring := true) in
noctium_contract rejectsNominalCellHelperWrite where
  cell balance : Amount
  entry writeBalance from nominalCellWriteProgram entry "writeBalance" end
end

/- error: nominal UInt equality requires matching nominal operands -/
#guard_msgs (substring := true) in
noctium_contract rejectsNominalRequireAliasMismatch where
  cell scratch : UInt 8
  entry check uses nominalConditionValues where
    require eq(amount, count)
  end
end

/- error: nominal UInt equality requires matching nominal operands -/
#guard_msgs (substring := true) in
noctium_contract rejectsNominalBranchAliasMismatch where
  cell scratch : UInt 8
  entry check uses nominalConditionValues where
    if eq(amount, count) then {
    } else {
    }
  end
end

/- error: nominal UInt equality requires matching nominal operands -/
#guard_msgs (substring := true) in
noctium_contract rejectsNominalEffectGuardAliasMismatch where
  cell scratch : UInt 8
  entry check uses nominalConditionValues where
    when eq(amount, count) write scratch := 1
  end
end

/- error: nominal UInt values require an explicit cast and must match the target type -/
#guard_msgs (substring := true) in
noctium_contract rejectsNominalCircuitOutputReturn where
  cell balance : Amount
  entry returnRaw uses nominalLedgerValues where
    return rawAmount : UInt 8 := amountResult
  end
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
