import Lean
import Noctium.Witness.HostCasCorrelation

open Lean Noctium.Witness.HostCasCorrelation

private def pendingCas : PendingCas := {
  protocolVersion := 1
  requestId := 3
  operation := casOperation
  capability := "store"
  schema := casSchema
  attemptId := String.ofList (List.replicate 64 'a')
  transactionId := String.ofList (List.replicate 64 'b')
  journalDigest := String.ofList (List.replicate 64 'c')
  baseRevision := "r0"
}

private def validCasReply : CasReply := {
  abiVersion := 1
  requestId := pendingCas.requestId
  operation := casOperation
  capability := pendingCas.capability
  schema := casSchema
  attemptId := pendingCas.attemptId
  transactionId := pendingCas.transactionId
  journalDigest := pendingCas.journalDigest
  outcome := "committed"
  baseRevision := pendingCas.baseRevision
  revision := "r1"
}

private def initialState : HostState := {
  evidence := {
    phaseAwaitingCas := true
    successfulExecution := true
    persisted := true
    submitted := true
    accepted := true
    commitCapabilityGranted := true
  }
  pending := some pendingCas
  journalRetained := true
  completed := none
  consumedReplies := 0
}

private def replaceReplyField (reply : CasReply) (field : String) (value : Json) : Except String CasReply := do
  match field with
  | "requestId" => return {reply with requestId := (← value.getNat?)}
  | "operation" => return {reply with operation := (← value.getStr?)}
  | "capability" => return {reply with capability := (← value.getStr?)}
  | "schema" => return {reply with schema := (← value.getStr?)}
  | "attemptId" => return {reply with attemptId := (← value.getStr?)}
  | "transactionId" => return {reply with transactionId := (← value.getStr?)}
  | "journalDigest" => return {reply with journalDigest := (← value.getStr?)}
  | "baseRevision" => return {reply with baseRevision := (← value.getStr?)}
  | _ => throw s!"unknown CAS correlation field: {field}"

private def expectedLocation (field : String) : String :=
  if ["requestId", "operation", "capability", "schema"].contains field then "envelope"
  else "value"

def main (_args : List String) : IO Unit := do
  let fixture ← IO.ofExcept (Json.parse (← IO.FS.readFile "runtime/tests/fixtures/host-cas-correlation.json"))
  let cases ← IO.ofExcept (fixture.getObjVal? "cases" >>= Json.getArr?)
  unless cases.size == 8 do
    throw (IO.userError s!"expected 8 host CAS correlation cases, got {cases.size}")
  for row in cases do
    let field ← IO.ofExcept (row.getObjVal? "field" >>= Json.getStr?)
    let location ← IO.ofExcept (row.getObjVal? "location" >>= Json.getStr?)
    let value ← IO.ofExcept (row.getObjVal? "replacement")
    unless location == expectedLocation field do
      throw (IO.userError s!"wrong fixture location for {field}: {location}")
    let badReply ← IO.ofExcept (replaceReplyField validCasReply field value)
    if validReply pendingCas badReply then
      throw (IO.userError s!"fixture row {field} still correlates with the pending request")
    let step := finishCas initialState badReply
    let invalidResponse := match step.result with
      | .error .invalidResponse => true
      | _ => false
    let noEffect := match step.effect with
      | .none => true
      | _ => false
    unless decide (step.state = initialState) && invalidResponse && noEffect do
      throw (IO.userError s!"fixture row {field} changed state or produced an effect")
