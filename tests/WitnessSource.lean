import Noctium.Frontend

open Noctium Noctium.Helpers
open scoped Noctium

namespace TypedWitness

def scalarProgram : Program := {
  witnesses := [
    {name := "lookup", operation := "noctium.lookup.v1", capability := "lookup",
      parameters := [{name := "seed", type := .scalar (.uint 255)}], result := .scalar (.uint 255)},
    {name := "cache", operation := "private_state.read.v1", capability := "private", privateKey := some "cache/last",
      result := .scalar (.uint 255)}]
  declarations := [
    {id := ⟨0, 0⟩, name := "fetch", parameters := [{name := "seed", ty := .uint 255}],
      result := .scalar (.uint 255), body := [
        .bind "previous" (.scalar (.uint 255)) (.witnessCall "read-cache" "cache" []),
        .assert (.eq (.ref "previous") (.uint 255 1)),
        .return (some (.witnessCall "fetch-value" "lookup" [.ref "seed"]))]},
    {id := ⟨0, 1⟩, name := "claim", parameters := [{name := "expected", ty := .uint 255}, {name := "seed", ty := .uint 255}],
      result := .scalar (.uint 255), body := [
        .stage "private" "cache/last" (.scalar (.uint 255)) (.uint 255 1),
        .bind "afterStage" (.scalar (.uint 255)) (.witnessCall "read-after-stage" "cache" []),
        .assert (.eq (.ref "afterStage") (.uint 255 1)),
        .bind "first" (.scalar (.uint 255)) (.call "fetch" [.ref "seed"]),
        .bind "second" (.scalar (.uint 255)) (.call "fetch" [.ref "seed"]),
        .assert (.eq (.ref "first") (.ref "expected")),
        .assert (.eq (.ref "second") (.ref "expected")),
        .stage "private" "cache/last" (.scalar (.uint 255)) (.ref "second"),
        .return (some (.ref "expected"))]}]
  exports := [{name := "scalar", target := ⟨0, 1⟩, inputs := [
    {name := "expected", ty := .uint 255, visibility := .public},
    {name := "seed", ty := .uint 255, visibility := .private}]}]
}

noctium_witness_circuit scalarRelation from scalarProgram entry "scalar"

noctium_contract ScalarWitness where
  cell total : UInt 8
  entry claim uses scalarRelation where
    write total := result
  end
end

def pairType : Types.CompositeType := .structure "TypedWitness.Pair"

def pairProgram : Program := {
  composites := {structures := [{id := "TypedWitness.Pair", fields := [
    {name := "amount", type := .scalar (.uint 255)}, {name := "okay", type := .scalar .bool}]}]}
  witnesses := [
    {name := "pair", operation := "noctium.pair.v1", capability := "pair",
      parameters := [{name := "request", type := .composite pairType}], result := .composite pairType}]
  declarations := [
    {id := ⟨0, 0⟩, name := "fetchPair", parameters := [{name := "request", ty := .native}],
      compositeParameters := [("request", pairType)], result := .composite pairType,
      body := [.return (some (.witnessCall "fetch-pair" "pair" [.ref "request"]))]},
    {id := ⟨0, 1⟩, name := "claimPair", parameters := [{name := "expected", ty := .uint 255}, {name := "request", ty := .native}],
      compositeParameters := [("request", pairType)], result := .composite pairType, body := [
        .bind "answer" (.composite pairType) (.call "fetchPair" [.ref "request"]),
        .assert (.eq (.project (.ref "answer") (.field "amount")) (.ref "expected")),
        .assert (.project (.ref "answer") (.field "okay")),
        .stage "private" "cache/last" (.scalar (.uint 255)) (.project (.ref "answer") (.field "amount")),
        .return (some (.disclose {} (.ref "answer")))]}]
  exports := [
    {name := "pair", target := ⟨0, 1⟩,
      inputs := [{name := "expected", ty := .uint 255, visibility := .public}],
      compositeInputs := [{name := "request", type := pairType, visibility := .private}]}]
}

noctium_witness_circuit pairRelation from pairProgram entry "pair"

noctium_contract PairWitness where
  cell total : UInt 8
  entry claim uses pairRelation where
    write total := cast(UInt 8, result.amount)
  end
end

noctium_contract PairCallArguments where
  cell total : UInt 8
  entry claim uses pairRelation arguments [request] where
    write total := cast(UInt 8, result.amount)
    return amount : UInt 8 := cast(UInt 8, result.amount)
  end
end

noctium_circuit pairClaimInputs where
  private opening : Native
  private requestAmount : UInt 8
  private requestOkay : Bool
  private expected : UInt 8
end

noctium_contract PairCaller where
  cell route : Bytes32
  entry forward uses pairClaimInputs where
    read route as target
    claimContractCall(target,
      disclose(callCommitment(PairCallArguments, "claim", opening,
        [request := fields(requestAmount, requestOkay)], [expected])))
  end
end

def emptyProgram : Program := {
  composites := {structures := [{id := "TypedWitness.Empty", fields := []}]}
  witnesses := [
    {name := "empty", operation := "noctium.empty.v1", capability := "empty",
      result := .composite (.structure "TypedWitness.Empty")}]
  declarations := [{id := ⟨0, 0⟩, name := "empty", result := .unit, body := [
    .evaluate (.witnessCall "empty-call" "empty" []), .return none]}]
  exports := [{name := "empty", target := ⟨0, 0⟩}]
}

noctium_witness_circuit emptyRelation from emptyProgram entry "empty"

def unitProgram : Program := {
  witnesses := [{name := "unit", operation := "noctium.unit.v1", capability := "unit", result := .unit}]
  declarations := [{id := ⟨0, 0⟩, name := "unit", result := .unit, body := [
    .evaluate (.witnessCall "unit-call" "unit" []), .return none]}]
  exports := [{name := "unit", target := ⟨0, 0⟩}]
}

noctium_witness_circuit unitRelation from unitProgram entry "unit"

noctium_control scalarHost from scalarProgram entry "scalar"
noctium_control pairHost from pairProgram entry "pair"
noctium_control emptyHost from emptyProgram entry "empty"
noctium_control unitHost from unitProgram entry "unit"

#guard (Witness.compile scalarProgram "scalar").isOk
#guard (Witness.compile pairProgram "pair").isOk
#guard (Witness.compile emptyProgram "empty").isOk
#guard (Witness.compile unitProgram "unit").isOk

def leakingPair : Program := {pairProgram with declarations := pairProgram.declarations.map fun declaration =>
  if declaration.id == ⟨0, 1⟩ then {declaration with body := [
    .return (some (.call "fetchPair" [.ref "request"]))]} else declaration}

#guard !(Witness.compile leakingPair "pair").isOk
#guard !(Witness.compile {scalarProgram with witnesses := []} "scalar").isOk
#guard !(Witness.compile {scalarProgram with witnesses := scalarProgram.witnesses ++ scalarProgram.witnesses} "scalar").isOk

def duplicateSites : Program := {scalarProgram with declarations := scalarProgram.declarations.map fun declaration =>
  if declaration.id == ⟨0, 0⟩ then {declaration with body := [
    .evaluate (.witnessCall "same" "lookup" [.ref "seed"]),
    .return (some (.witnessCall "same" "lookup" [.ref "seed"]))]} else declaration}

#guard !(Witness.compile duplicateSites "scalar").isOk

def reservedCommitProvider : Program := {unitProgram with witnesses := [
  {name := "unit", operation := "private_state.compare_exchange.v1", capability := "unit", result := .unit}]}

#guard !(Witness.compile reservedCommitProvider "unit").isOk

def privateControlLeak : Program := {
  witnesses := [{name := "flag", operation := "noctium.flag.v1", capability := "flag", result := .scalar .bool}]
  declarations := [{id := ⟨0, 0⟩, name := "leak", result := .scalar .native, body := [
    .branch (.witnessCall "flag-call" "flag" []) [.return (some (.native 1))] [.return (some (.native 0))]]}]
  exports := [{name := "leak", target := ⟨0, 0⟩}]
}

#guard !(Control.compileTypedWithLimits {} privateControlLeak "leak").isOk

end TypedWitness
