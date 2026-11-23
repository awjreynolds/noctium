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

noctium_circuit nominalListValues where
  private owner : Bytes32
  private amount : Amount
  private count : Count
  private raw : UInt 8
end

noctium_circuit nominalListHeadOnly where
end

noctium_contract NominalAmountLists where
  list amounts : Amount
  sealed list seededAmounts : Amount
  tree counts : Bytes32 => List Count
  tree nestedAmounts : Bytes32 => Bytes32 => List Amount

  constructor(initial : Amount) where
    pushFront amounts := initial
    pushFront seededAmounts := initial
  end

  entry append uses nominalListValues where
    pushFront amounts := disclose(amount)
    head amounts as currentAmount
    pushFront counts[disclose(owner)] := disclose(count)
    head counts[disclose(owner)] as currentCount
    pushFront nestedAmounts[disclose(owner)][disclose(owner)] := disclose(amount)
    head nestedAmounts[disclose(owner)][disclose(owner)] as nestedAmount
    return amountResult : Amount := currentAmount
    return countResult : Count := currentCount
    return nestedAmountResult : Amount := nestedAmount
  end
  entry appendRaw uses nominalListValues where
    pushFront amounts := disclose(cast(Amount, raw))
    head amounts as currentAmount
    return amountResult : Amount := currentAmount
  end
end

noctium_circuit nominalMapValues where
  private key : Count
  private nestedKey : Count
  private amount : Amount
end

noctium_circuit nominalMapRawValues where
  private rawKey : UInt 8
  private rawAmount : UInt 8
end

noctium_contract NominalAmountMaps where
  map balances : Count => Amount
  sealed map seededBalances : Count => Amount
  tree nestedBalances : Count => Count => Amount

  constructor(initialKey : Count, initial : Amount) where
    insert balances[initialKey] := initial
    insert seededBalances[initialKey] := initial
  end

  entry inspect uses nominalMapValues where
    member balances[disclose(key)] as hasKey
    read balances[disclose(key)] as current
    read seededBalances[disclose(key)] as seeded
    return present : Bool := hasKey
    return value : Amount := current
    return initialValue : Amount := seeded
  end
  entry setAmount uses nominalMapValues where
    insert balances[disclose(key)] := disclose(amount)
  end
  entry setRaw uses nominalMapRawValues where
    insert balances[disclose(cast(Count, rawKey))] := disclose(cast(Amount, rawAmount))
    read balances[disclose(cast(Count, rawKey))] as current
    return value : Amount := current
  end
  entry setNested uses nominalMapValues where
    member nestedBalances[disclose(key)] as pathPresent
    when eq(pathPresent, false) insertDefault nestedBalances[disclose(key)]
    insert nestedBalances[disclose(key)][disclose(nestedKey)] := disclose(amount)
    read nestedBalances[disclose(key)][disclose(nestedKey)] as current
    return value : Amount := current
  end
  entry removeAmount uses nominalMapValues where
    remove balances[disclose(key)]
    absent balances[disclose(key)]
    member balances[disclose(key)] as hasKey
    return present : Bool := hasKey
  end
end

noctium_circuit nominalSetRawValues where
  private rawAmount : UInt 8
end

noctium_contract NominalAmountSets where
  set amounts : Amount
  tree amountSets : Count => Set Amount
  tree deepAmountSets : Count => Count => Set Amount

  constructor(initialKey : Count, initial : Amount) where
    insert amounts[initial]
  end

  entry add uses nominalMapValues where
    insert amounts[disclose(amount)]
    member amounts[disclose(amount)] as rootPresent
    member amountSets[disclose(key)] as ownerPresent
    when eq(ownerPresent, false) insertDefault amountSets[disclose(key)]
    insert amountSets[disclose(key)][disclose(amount)]
    member amountSets[disclose(key)][disclose(amount)] as nestedPresent
    member deepAmountSets[disclose(key)] as deepParentPresent
    when eq(deepParentPresent, false) insertDefault deepAmountSets[disclose(key)]
    member deepAmountSets[disclose(key)][disclose(nestedKey)] as deepOwnerPresent
    when eq(deepOwnerPresent, false)
      insertDefault deepAmountSets[disclose(key)][disclose(nestedKey)]
    insert deepAmountSets[disclose(key)][disclose(nestedKey)][disclose(amount)]
    member deepAmountSets[disclose(key)][disclose(nestedKey)][disclose(amount)]
      as deepPresent
    return rootResult : Bool := rootPresent
    return nestedResult : Bool := nestedPresent
    return deepResult : Bool := deepPresent
  end

  entry removeValues uses nominalMapValues where
    remove amounts[disclose(amount)]
    member amounts[disclose(amount)] as rootPresent
    remove amountSets[disclose(key)][disclose(amount)]
    member amountSets[disclose(key)][disclose(amount)] as nestedPresent
    remove deepAmountSets[disclose(key)][disclose(nestedKey)][disclose(amount)]
    member deepAmountSets[disclose(key)][disclose(nestedKey)][disclose(amount)] as deepPresent
    return rootResult : Bool := rootPresent
    return nestedResult : Bool := nestedPresent
    return deepResult : Bool := deepPresent
  end

  entry clear uses nominalMapValues where
    reset amounts
    reset amountSets[disclose(key)]
    reset deepAmountSets[disclose(key)][disclose(nestedKey)]
  end

  entry castRaw uses nominalSetRawValues where
    insert amounts[disclose(cast(Amount, rawAmount))]
    member amounts[disclose(cast(Amount, rawAmount))] as present
    return presentResult : Bool := present
  end
end

private def nominalMapHelperProgram : Program := {
  ledger := [{name := "balances", kind := .map (.uint 255) (.uint 255)}]
  nominalUIntMaps := [("balances", {
    key := some Count.nominalType, value := some Amount.nominalType})]
  declarations := [
    {id := ⟨0, 0⟩, name := "forwardAmount",
      parameters := [⟨"amount", .uint 255⟩],
      nominalUIntParameters := [("amount", Amount.nominalType)],
      result := .scalar (.uint 255), nominalUIntResult := some Amount.nominalType,
      body := [.return (some (.ref "amount"))]},
    {id := ⟨0, 1⟩, name := "get",
      parameters := [⟨"key", .uint 255⟩],
      nominalUIntParameters := [("key", Count.nominalType)],
      result := .scalar (.uint 255), nominalUIntResult := some Amount.nominalType,
      body := [
        .readMember "balances" "present" (.uint 255) (.uint 255) (.ref "key"),
        .readMap "balances" "current" (.uint 255) (.uint 255) (.ref "key"),
        .return (some (.call "forwardAmount" [.ref "current"]))]},
    {id := ⟨0, 2⟩, name := "set",
      parameters := [⟨"key", .uint 255⟩, ⟨"amount", .uint 255⟩],
      nominalUIntParameters := [("key", Count.nominalType), ("amount", Amount.nominalType)],
      result := .unit,
      body := [
        .writeMap "balances" (.uint 255) (.uint 255)
          (.disclose {} (.ref "key")) (.disclose {} (.ref "amount")),
        .return none]}]
  exports := [
    {name := "get", target := ⟨0, 1⟩, inputs := [
      {name := "key", ty := .uint 255, visibility := .public}]},
    {name := "set", target := ⟨0, 2⟩, inputs := [
      {name := "key", ty := .uint 255, visibility := .public},
      {name := "amount", ty := .uint 255, visibility := .private}]}]
}

private def crossedNominalMapReadProgram : Program := {
  nominalMapHelperProgram with
  declarations := nominalMapHelperProgram.declarations.map fun declaration =>
    if declaration.name == "get" then
      {declaration with nominalUIntResult := some Count.nominalType}
    else declaration
}

private def crossedNominalMapKeyProgram : Program := {
  nominalMapHelperProgram with
  declarations := nominalMapHelperProgram.declarations.map fun declaration =>
    if declaration.name == "get" then
      {declaration with nominalUIntParameters := [("key", Amount.nominalType)]}
    else declaration
}

private def crossedNominalMapWriteProgram : Program := {
  nominalMapHelperProgram with
  declarations := nominalMapHelperProgram.declarations.map fun declaration =>
    if declaration.name == "set" then
      {declaration with nominalUIntParameters := [
        ("key", Count.nominalType), ("amount", Count.nominalType)]}
    else declaration
}

noctium_contract NominalAmountMapHelpers where
  map balances : Count => Amount
  entry get from nominalMapHelperProgram entry "get" end
  entry update from nominalMapHelperProgram entry "set" end
end

#guard (Witness.compileLedger nominalMapHelperProgram "get" NominalAmountMapHelpers.state).isOk
#guard (Witness.compileLedger nominalMapHelperProgram "set" NominalAmountMapHelpers.state).isOk

#guard match Witness.Ledger.transform nominalMapHelperProgram with
  | .ok transformed =>
      transformed.host.witnesses.any (fun signature =>
        signature.operation == "noctium.ledger.read.v1" &&
          signature.result == .scalar (.uint 255) &&
          signature.parameters.map (·.sourceNominal) == [some Count.nominalType.name] &&
          signature.resultNominal == some Amount.nominalType.name) &&
      transformed.host.witnesses.any (fun signature =>
        signature.operation == "noctium.ledger.read.v1" &&
          signature.result == .scalar .bool &&
          signature.parameters.map (·.sourceNominal) == [some Count.nominalType.name] &&
          signature.resultNominal.isNone) &&
      transformed.host.witnesses.any (fun signature =>
        signature.operation == "noctium.ledger.write.v1" &&
          signature.result == .unit &&
          signature.parameters.map (·.sourceNominal) ==
            [some Count.nominalType.name, some Amount.nominalType.name])
  | .error _ => Bool.false

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

private def nominalHelperProgram : Program := {
  ledger := [{name := "balance", kind := .cell (.uint 255)}]
  declarations := [
    {id := ⟨0, 0⟩, name := "forward", parameters := [⟨"amount", .uint 255⟩],
      nominalUIntParameters := [("amount", Amount.nominalType)],
      result := .scalar (.uint 255), nominalUIntResult := some Amount.nominalType,
      body := [.return (some (.ref "amount"))]},
    {id := ⟨0, 1⟩, name := "set", parameters := [⟨"amount", .uint 255⟩],
      nominalUIntParameters := [("amount", Amount.nominalType)],
      result := .scalar (.uint 255), nominalUIntResult := some Amount.nominalType,
      body := [
        .writeCell "balance" (.uint 255) (.disclose {} (.call "forward" [.ref "amount"])),
        .readCell "balance" "current" (.uint 255),
        .return (some (.disclose {} (.call "forward" [.ref "current"])))]},
    {id := ⟨0, 2⟩, name := "setRaw", parameters := [⟨"raw", .uint 511⟩],
      result := .scalar (.uint 255), nominalUIntResult := some Amount.nominalType,
      body := [
        .bind "amount" (.scalar (.uint 255)) (.castNominalUInt Amount.nominalType (.ref "raw")),
        .return (some (.call "set" [.ref "amount"]))]}]
  exports := [
    {name := "set", target := ⟨0, 1⟩, inputs := [{name := "amount", ty := .uint 255, visibility := .private}]},
    {name := "setRaw", target := ⟨0, 2⟩, inputs := [{name := "raw", ty := .uint 511, visibility := .private}]}]
}

noctium_contract NominalAmountHelperLedger where
  cell balance : Amount
  entry setAmount from nominalHelperProgram entry "set" end
  entry setRaw from nominalHelperProgram entry "setRaw" end
end

private def nominalAmountListsAppendEntry : Entrypoint :=
  (NominalAmountLists.entrypoints.find? (·.name == "append")).getD
    {name := "missing", circuit := {name := "missing"}}

#guard (nominalAmountListsAppendEntry.validate Capabilities.source NominalAmountLists.state).isOk
#guard (Backend.Impact.lower NominalAmountLists.state nominalAmountListsAppendEntry).isOk
#guard NominalAmountLists.entrypoints.all fun operation =>
  (Backend.Zkir.lowerEntrypoint NominalAmountLists.state operation).isOk
#guard match NominalAmountLists.constructor with
  | some {listPushes := pushes, ..} =>
      pushes.map (·.state) == ["amounts", "seededAmounts"] &&
        pushes.all (fun push => push.valueType == .uint 255 &&
          (match push.value with | .ref "initial" => Bool.true | _ => Bool.false))
  | _ => Bool.false

/- error: use 'entry from' to bind a structured nominal UInt circuit to its contract -/
#guard_msgs (substring := true) in
noctium_contract WrongOwnerNominalHelper where
  cell balance : Count
  entry reuseAmount uses NominalAmountHelperLedger.setAmount.circuit where
  end
end

private def hostedNominalHelperProgram : Program := {
  nominalHelperProgram with
  witnesses := [preserveAmount.__witnessSignature]
  declarations := nominalHelperProgram.declarations.map fun declaration =>
    if declaration.name == "forward" then {declaration with body := [
        .return (some (.witnessCall "preserve-amount" preserveAmount.__witnessSignature.name [.ref "amount"]))]}
    else declaration
}

noctium_contract NominalAmountHostedLedger where
  cell balance : Amount
  entry setAmount from hostedNominalHelperProgram entry "set" end
end

#guard match Witness.Ledger.transform
    {hostedNominalHelperProgram with nominalUIntCells := [("balance", Amount.nominalType)]} with
  | .ok transformed =>
    transformed.host.witnesses.any (fun signature =>
      signature.operation == "noctium.ledger.read.v1" &&
        signature.resultNominal == some Amount.nominalType.name) &&
    transformed.native.witnesses.any (fun signature =>
      signature.operation == "noctium.ledger.write.v1" &&
        signature.parameters.map (·.sourceNominal) == [some Amount.nominalType.name])
  | .error _ => Bool.false

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

private def nominalListRoundTrip : Except String _root_.Bool := do
  let [appendAmount, appendRaw] := NominalAmountLists.entrypoints
    | throw "expected two List operations"
  let owner : Value := .bytes 32 (List.replicate 32 1)
  let inputs : EvalEnv := [
    ("owner", owner), ("amount", .uint 255 41), ("count", .uint 255 11), ("raw", .uint 255 255)]
  let initial : LedgerState := {trees := [
    ("amounts", .list [[.uint 255 19]]), ("counts", .map [(owner, .list [])]),
    ("nestedAmounts", .map [(owner, .map [(owner, .list [])])])]}
  let (amountOutputs, amountState) ← appendAmount.run context inputs initial
  let (rawOutputs, finalState) ← appendRaw.run context inputs amountState
  pure (amountOutputs.lookup "amountResult" == some (.uint 255 41) &&
    amountOutputs.lookup "countResult" == some (.uint 255 11) &&
    amountOutputs.lookup "nestedAmountResult" == some (.uint 255 41) &&
    rawOutputs.lookup "amountResult" == some (.uint 255 255) &&
    finalState.trees.lookup "amounts" == some (.list [[.uint 255 255], [.uint 255 41], [.uint 255 19]]))

#guard nominalListRoundTrip.toOption == some Bool.true

private def nominalMapRoundTrip : Except String _root_.Bool := do
  let [inspect, setAmount, setRaw, setNested, removeAmount] := NominalAmountMaps.entrypoints
    | throw "expected five Map operations"
  let key : Value := .uint 255 2
  let amount : Value := .uint 255 19
  let inputs : EvalEnv := [("key", key), ("nestedKey", .uint 255 3), ("amount", .uint 255 41)]
  let initial : LedgerState := {
    maps := [("balances", [(key, amount)]), ("seededBalances", [(key, amount)])]
    trees := [("nestedBalances", .map [])]}
  let (before, _) ← inspect.run context inputs initial
  let (_, updated) ← setAmount.run context inputs initial
  let (after, _) ← inspect.run context inputs updated
  let (raw, updated) ← setRaw.run context [("rawKey", .uint 255 255), ("rawAmount", .uint 255 255)] updated
  let (nested, updated) ← setNested.run context
    [("key", key), ("nestedKey", .uint 255 3), ("amount", .uint 255 73)] updated
  let (_, updated) ← setNested.run context
    [("key", key), ("nestedKey", .uint 255 4), ("amount", .uint 255 74)] updated
  let (removed, finalState) ← removeAmount.run context inputs updated
  pure (before.lookup "present" == some (.bool Bool.true) &&
    before.lookup "value" == some amount &&
    after.lookup "value" == some (.uint 255 41) &&
    after.lookup "initialValue" == some amount &&
    raw.lookup "value" == some (.uint 255 255) &&
    nested.lookup "value" == some (.uint 255 73) &&
    removed.lookup "present" == some (.bool Bool.false) &&
    finalState.maps.lookup "balances" == some [(.uint 255 255, .uint 255 255)] &&
    finalState.trees.lookup "nestedBalances" == some (.map [
      (key, .map [(.uint 255 4, .scalar (.uint 255 74)), (.uint 255 3, .scalar (.uint 255 73))])]))

#guard nominalMapRoundTrip.toOption == some Bool.true

#guard match NominalAmountMapHelpers.entrypoints with
  | [get, update] =>
      get.circuit.inputs.map (·.ty) == [.uint 255] && get.returns.map (·.ty) == [.uint 255] &&
        get.effects.any (fun effect => match effect with
          | .readMember "balances" _ (.uint 255) (.uint 255) _ => Bool.true
          | _ => Bool.false) &&
        get.effects.any (fun effect => match effect with
          | .readMap "balances" _ (.uint 255) (.uint 255) _ => Bool.true
          | _ => Bool.false) &&
        update.effects.any (fun effect => match effect with
          | .writeMap "balances" (.uint 255) (.uint 255) _ _ => Bool.true
          | _ => Bool.false)
  | _ => Bool.false

#guard match Helpers.compileEntrypointFor crossedNominalMapReadProgram "get"
    NominalAmountMapHelpers.state with
  | .error issue => issue.message ==
      "nominal UInt values require an explicit cast and must match the target type"
  | .ok _ => Bool.false

#guard match Helpers.compileEntrypointFor crossedNominalMapKeyProgram "get"
    NominalAmountMapHelpers.state with
  | .error issue => issue.message ==
      "nominal UInt values require an explicit cast and must match the target type"
  | .ok _ => Bool.false

#guard match Helpers.compileEntrypointFor crossedNominalMapWriteProgram "set"
    NominalAmountMapHelpers.state with
  | .error issue => issue.message ==
      "nominal UInt values require an explicit cast and must match the target type"
  | .ok _ => Bool.false

private def nominalMapHelperRoundTrip : Except String _root_.Bool := do
  let [get, update] := NominalAmountMapHelpers.entrypoints
    | throw "expected two helper Map operations"
  let key : Value := .uint 255 2
  let initialAmount : Value := .uint 255 19
  let nextAmount : Value := .uint 255 41
  let (before, beforeState) ← get.run context [("key", key)]
    {maps := [("balances", [(key, initialAmount)])]}
  let (_, updatedState) ← update.run context [("key", key), ("amount", nextAmount)] beforeState
  let (after, finalState) ← get.run context [("key", key)] updatedState
  pure (before.any (fun (_, value) => value == initialAmount) &&
    after.any (fun (_, value) => value == nextAmount) &&
    finalState.maps.lookup "balances" == some [(key, nextAmount)])

#guard nominalMapHelperRoundTrip.toOption == some Bool.true

#guard match NominalAmountMaps.constructor with
  | some ctor => ctor.mapInserts.map (·.state) == ["balances", "seededBalances"]
  | none => Bool.false
#guard NominalAmountMaps.entrypoints.all fun operation =>
  (Backend.Zkir.lowerEntrypoint NominalAmountMaps.state operation).isOk

#guard (NominalAmountSets.validate Capabilities.source).isOk
#guard NominalAmountSets.entrypoints.all fun operation =>
  (operation.validate Capabilities.source NominalAmountSets.state).isOk
#guard NominalAmountSets.entrypoints.all fun operation =>
  (Backend.Zkir.lowerEntrypoint NominalAmountSets.state operation).isOk
#guard match NominalAmountSets.state with
  | [{kind := .tree (.set (.uint 255)), ..},
     {kind := .tree (.map (.uint 255) (.set (.uint 255))), ..},
     {kind := .tree (.map (.uint 255) (.map (.uint 255) (.set (.uint 255)))), ..}] =>
    Bool.true
  | _ => Bool.false
#guard match NominalAmountSets.constructor with
  | some {setInserts := [{name := "amounts", key := .mk (.uint 255) (.ref "initial")}], ..} =>
    Bool.true
  | _ => Bool.false

private def nominalSetRoundTrip : Except String _root_.Bool := do
  let [add, removeValues, clear, castRaw] := NominalAmountSets.entrypoints
    | throw "expected four Set operations"
  let key : Value := .uint 255 7
  let nestedKey : Value := .uint 255 8
  let amount : Value := .uint 255 19
  let inputs : EvalEnv := [("key", key), ("nestedKey", nestedKey), ("amount", amount)]
  let initial : LedgerState := {trees := [
    ("amounts", .map []), ("amountSets", .map []), ("deepAmountSets", .map [])]}
  let (added, afterAdd) ← add.run context inputs initial
  let (removed, afterRemove) ← removeValues.run context inputs afterAdd
  let (_, cleared) ← clear.run context inputs afterRemove
  let (castOutputs, finalState) ← castRaw.run context [("rawAmount", amount)] cleared
  pure (added.lookup "rootResult" == some (.bool Bool.true) &&
    added.lookup "nestedResult" == some (.bool Bool.true) &&
    added.lookup "deepResult" == some (.bool Bool.true) &&
    removed.lookup "rootResult" == some (.bool Bool.false) &&
    removed.lookup "nestedResult" == some (.bool Bool.false) &&
    removed.lookup "deepResult" == some (.bool Bool.false) &&
    castOutputs.lookup "presentResult" == some (.bool Bool.true) &&
    finalState.trees.lookup "amounts" == some (.map [(amount, .null)]) &&
    finalState.trees.lookup "amountSets" == some (.map [(key, .map [])]) &&
    finalState.trees.lookup "deepAmountSets" ==
      some (.map [(key, .map [(nestedKey, .map [])])]))

#guard nominalSetRoundTrip.toOption == some Bool.true


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

private def nominalHelperCellRoundTrip : Except String _root_.Bool := do
  let [setAmount, setRaw] := NominalAmountHelperLedger.entrypoints
    | throw "expected two nominal cell operations"
  let (_, amountState) ← setAmount.run context [("amount", .uint 255 41)]
    {cells := [("balance", .uint 255 19)]}
  let (_, rawState) ← setRaw.run context [("raw", .uint 511 255)] amountState
  pure (amountState.cells.lookup "balance" == some (.uint 255 41) &&
    rawState.cells.lookup "balance" == some (.uint 255 255) &&
    !(setRaw.run context [("raw", .uint 511 256)] rawState).isOk)

#guard nominalHelperCellRoundTrip.toOption == some Bool.true

#guard NominalAmountHelperLedger.entrypoints.all fun operation =>
  (Noctium.Backend.Zkir.lowerEntrypoint NominalAmountHelperLedger.state operation).isOk

#guard match Witness.compileStateEntrypointWithWitness
    {hostedNominalHelperProgram with nominalUIntCells := [("balance", Amount.nominalType)]}
    "set" NominalAmountHostedLedger.state with
  | .ok (_, some _) => Bool.true
  | _ => Bool.false

private def crossedNominalHelperProgram : Program := {
  nominalHelperProgram with
  declarations := nominalHelperProgram.declarations.map fun declaration =>
    if declaration.name == "forward" then {declaration with
        nominalUIntParameters := [("amount", Count.nominalType)]
        nominalUIntResult := some Count.nominalType}
    else declaration
}

#guard match Witness.compileStateEntrypoint
    {crossedNominalHelperProgram with nominalUIntCells := [("balance", Amount.nominalType)]}
    "set" NominalAmountHelperLedger.state with
  | .error issue => (issue.message.splitOn "nominal UInt values require an explicit cast").length > 1
  | .ok _ => Bool.false

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
noctium_contract rejectsNominalListAliasPush where
  list amounts : Amount
  entry append uses nominalListValues where
    pushFront amounts := disclose(count)
  end
end

/- error: nominal UInt values require an explicit cast and must match the target type -/
#guard_msgs (substring := true) in
noctium_contract rejectsNominalListRawPush where
  list amounts : Amount
  entry append uses nominalListValues where
    pushFront amounts := disclose(raw)
  end
end

/- error: nominal UInt values require an explicit cast and must match the target type -/
#guard_msgs (substring := true) in
noctium_contract rejectsNominalListHeadAliasReturn where
  list amounts : Amount
  entry inspect uses nominalListHeadOnly where
    head amounts as currentAmount
    return wrongAlias : Count := currentAmount
  end
end

/- error: nominal UInt values require an explicit cast and must match the target type -/
#guard_msgs (substring := true) in
noctium_contract rejectsNominalMapConstructorKey where
  sealed map balances : Count => Amount
  constructor(initialKey : Amount, initial : Amount) where
    insert balances[initialKey] := initial
  end
end

/- error: nominal UInt values require an explicit cast and must match the target type -/
#guard_msgs (substring := true) in
noctium_contract rejectsNominalMapValue where
  map balances : Count => Amount
  entry insertWrong uses nominalMapValues where
    insert balances[disclose(key)] := disclose(nestedKey)
  end
end

/- error: nominal UInt values require an explicit cast and must match the target type -/
#guard_msgs (substring := true) in
noctium_contract rejectsNominalMapRawKey where
  map balances : Count => Amount
  entry inspect uses nominalMapRawValues where
    member balances[disclose(rawKey)] as hasKey
  end
end

/- error: nominal UInt values require an explicit cast and must match the target type -/
#guard_msgs (substring := true) in
noctium_contract rejectsNominalMapAbsentKey where
  map balances : Count => Amount
  entry inspect uses nominalMapValues where
    absent balances[disclose(amount)]
  end
end

/- error: nominal UInt values require an explicit cast and must match the target type -/
#guard_msgs (substring := true) in
noctium_contract rejectsNominalMapRawValue where
  map balances : Count => Amount
  entry insertWrong uses nominalMapRawValues where
    insert balances[disclose(cast(Count, rawKey))] := disclose(rawAmount)
  end
end

/- error: nominal UInt values require an explicit cast and must match the target type -/
#guard_msgs (substring := true) in
noctium_contract rejectsNominalNestedMapKey where
  tree balances : Count => Count => Amount
  entry removeWrong uses nominalMapValues where
    remove balances[disclose(key)][disclose(amount)]
  end
end

/- error: nominal UInt values require an explicit cast and must match the target type -/
#guard_msgs (substring := true) in
noctium_contract rejectsNominalSetConstructorKey where
  set amounts : Amount
  constructor(initial : Count) where
    insert amounts[initial]
  end
end

/- error: nominal UInt values require an explicit cast and must match the target type -/
#guard_msgs (substring := true) in
noctium_contract rejectsNominalSetCountElement where
  set amounts : Amount
  entry insertWrong uses nominalMapValues where
    insert amounts[disclose(nestedKey)]
  end
end

/- error: nominal UInt values require an explicit cast and must match the target type -/
#guard_msgs (substring := true) in
noctium_contract rejectsNominalSetRawElement where
  set amounts : Amount
  entry insertWrong uses nominalSetRawValues where
    insert amounts[disclose(rawAmount)]
  end
end

/- error: nominal UInt values require an explicit cast and must match the target type -/
#guard_msgs (substring := true) in
noctium_contract rejectsNominalNestedSetCountElement where
  tree amountSets : Count => Set Amount
  entry insertWrong uses nominalMapValues where
    insert amountSets[disclose(key)][disclose(nestedKey)]
  end
end

/- error: nominal UInt values require an explicit cast and must match the target type -/
#guard_msgs (substring := true) in
noctium_contract rejectsNominalNestedSetRawElement where
  tree amountSets : Count => Set Amount
  entry insertWrong uses nominalMapRawValues where
    insert amountSets[disclose(cast(Count, rawKey))][disclose(rawAmount)]
  end
end

/- error: nominal UInt values require an explicit cast and must match the target type -/
#guard_msgs (substring := true) in
noctium_contract rejectsNominalNestedSetParentKey where
  tree amountSets : Count => Set Amount
  entry inspect uses nominalMapValues where
    member amountSets[disclose(amount)] as hasOwner
  end
end

/- error: nominal UInt values require an explicit cast and must match the target type -/
#guard_msgs (substring := true) in
noctium_contract rejectsNominalMapReadReturn where
  map balances : Count => Amount
  entry inspect uses nominalMapValues where
    read balances[disclose(key)] as current
    return wrongAlias : Count := current
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

/- error: nominal UInt values require an explicit cast and must match the target type -/
#guard_msgs (substring := true) in
noctium_contract rejectsNominalCellHelperRead where
  cell balance : Amount
  entry readBalance from nominalCellReadProgram entry "readBalance" end
end

/- error: nominal UInt values require an explicit cast and must match the target type -/
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
