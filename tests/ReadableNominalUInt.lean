import Noctium.Frontend
import Noctium.Backend.Impact
import Noctium.Compiler

open scoped Noctium
open Noctium

noctium_uint_type Amount := UInt 8
noctium_uint_type Count := UInt 8

noctium_witness_circuit amountEcho where
  private echoed : Amount
  output observed : Amount := disclose(echoed)
end

noctium_contract ReadableNominalUInt where
  entry echo uses amountEcho arguments [echoed] where
    return result : Amount := disclose(echoed)
  end
  entry echoOutput uses amountEcho arguments [echoed] where
    return result : Amount := observed
  end
end

noctium_interface ReadableNominalUIntInterface where
  entry echo accepts [echoed : Amount] yields [result : Amount]
  entry echoOutput accepts [echoed : Amount] yields [result : Amount]
end

noctium_implements ReadableNominalUInt implements ReadableNominalUIntInterface

noctium_witness_circuit groupedEcho where
  private payload : Bytes 2
  private amountIn : Amount
  private countIn : Count
  output payloadResult : Bytes 2 := disclose(payload)
  output amountResult : Amount := disclose(amountIn)
  output countResult : Count := disclose(countIn)
end

noctium_contract ReadableNominalUIntGrouped where
  entry echo uses groupedEcho arguments [payload, amountIn, countIn] where
    return returnedAmount : Amount := amountResult
    return returnedCount : Count := countResult
  end
end

/-- error: nominal UInt values require an explicit cast and must match the target type -/
#guard_msgs (substring := true) in
noctium_contract WrongReadableNominalUInt where
  entry echo uses amountEcho arguments [echoed] where
    return result : Count := disclose(echoed)
  end
end

#guard amountEcho.outputs.map (·.name) == ["observed"]
#guard groupedEcho.outputs.map (·.name) == [
  "result.payloadResult.0", "result.payloadResult.1",
  "result.amountResult", "result.countResult"]

run_cmd do
  let entries := circuitRegistry.getState (← Lean.getEnv)
  let some amountInfo := entries.find? (·.declName == `amountEcho)
    | throwError "missing registered readable witness circuit"
  unless amountInfo.nominalUIntInputs == [("echoed", Amount.nominalType)] do
    throwError "readable witness scalar input tag was not registered"
  unless amountInfo.nominalUIntOutputs == [("observed", Amount.nominalType)] do
    throwError "readable witness scalar output tag was not registered"
  let some groupedInfo := entries.find? (·.declName == `groupedEcho)
    | throwError "missing registered grouped readable witness circuit"
  unless groupedInfo.nominalUIntOutputs == [
      ("amountResult", Amount.nominalType),
      ("result.amountResult", Amount.nominalType),
      ("countResult", Count.nominalType),
      ("result.countResult", Count.nominalType)] do
    throwError "grouped readable witness scalar output tags lost their physical names"
