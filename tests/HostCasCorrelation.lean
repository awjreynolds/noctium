import Lean
import Noctium.Witness.HostCasCorrelation

open Lean Noctium.Witness.HostCasCorrelation

private def ensure (condition : Bool) (message : String) : Except String Unit :=
  if condition then .ok () else .error message

private def stringField (value : Json) (field : String) : Except String String := do
  (← value.getObjVal? field).getStr?

private def naturalField (value : Json) (field : String) : Except String Nat := do
  (← value.getObjVal? field).getNat?

private def pendingFromJson (value : Json) : Except String PendingCas := do
  let digest ← stringField value "journalDigest"
  ensure (digest == "<redacted-journal-digest>") "fixture digest marker must stay redacted"
  return {
    protocolVersion := 1
    requestId := ← naturalField value "requestId"
    operation := ← stringField value "operation"
    capability := ← stringField value "capability"
    schema := ← stringField value "schema"
    attemptId := ← stringField value "attemptId"
    transactionId := ← stringField value "transactionId"
    journalDigest := String.ofList (List.replicate 64 'c')
    baseRevision := ← stringField value "baseRevision"
  }

private def caseReply (pending : PendingCas) (overrides : Json) : Except String CasReply := do
  let mut reply : CasReply := {
    abiVersion := 1
    requestId := pending.requestId
    operation := casOperation
    capability := pending.capability
    schema := casSchema
    attemptId := pending.attemptId
    transactionId := pending.transactionId
    journalDigest := pending.journalDigest
    outcome := "committed"
    baseRevision := pending.baseRevision
    revision := "r1"
  }
  for (field, value) in (← overrides.getObj?).toList do
    match field with
    | "requestId" => reply := {reply with requestId := ← value.getNat?}
    | "operation" => reply := {reply with operation := ← value.getStr?}
    | "capability" => reply := {reply with capability := ← value.getStr?}
    | "schema" => reply := {reply with schema := ← value.getStr?}
    | "attemptId" => reply := {reply with attemptId := ← value.getStr?}
    | "transactionId" => reply := {reply with transactionId := ← value.getStr?}
    | "journalDigest" => reply := {reply with journalDigest := ← value.getStr?}
    | "baseRevision" => reply := {reply with baseRevision := ← value.getStr?}
    | "outcome" => reply := {reply with outcome := ← value.getStr?}
    | "revision" => reply := {reply with revision := ← value.getStr?}
    | _ => throw s!"unknown host CAS override: {field}"
  return reply

private def stateFor (after : String) (initial : HostState)
    (committed conflicted : Option HostState) : Except String HostState := do
  if after == "" then pure initial
  else if after == "committed" then
    match committed with
    | some state => pure state
    | none => throw "fixture duplicate precedes its commit"
  else if after == "conflict" then
    match conflicted with
    | some state => pure state
    | none => throw "fixture duplicate precedes its conflict"
  else throw s!"unknown prior host CAS state: {after}"

private def invalidResponse (step : Step) : Bool := match step.result with
  | .error .invalidResponse => true
  | _ => false

private def invalidState (step : Step) : Bool := match step.result with
  | .error .invalidState => true
  | _ => false

private def acknowledged (step : Step) : Bool := match step.result with
  | .ok "committed" => true
  | _ => false

private def conflicted (step : Step) : Bool := match step.result with
  | .ok "conflict" => true
  | _ => false

private def runCases (fixture : Json) : Except String Nat := do
  let version ← naturalField fixture "version"
  ensure (version == 1) "unsupported host CAS fixture version"
  let pending ← pendingFromJson (← fixture.getObjVal? "pending")
  let cases ← (← fixture.getObjVal? "cases").getArr?
  ensure (cases.size == 15) s!"expected 15 cases, got {cases.size}"
  let evidence : Evidence := {
    phaseAwaitingCas := true
    successfulExecution := true
    persisted := true
    submitted := true
    accepted := true
    commitCapabilityGranted := true
  }
  let initial : HostState := {
    evidence
    pending := some pending
    journalRetained := true
    completed := none
    consumedReplies := 0
  }
  let mut committed : Option HostState := none
  let mut conflictedState : Option HostState := none
  let mut pendingCount := 0
  let mut commitCount := 0
  let mut conflictCount := 0
  let mut duplicateCount := 0
  for row in cases do
    let name ← stringField row "name"
    let overrides ← row.getObjVal? "overrides"
    let reply ← caseReply pending overrides
    let after ← stringField row "after"
    let expected ← stringField row "expected"
    let before ← stateFor after initial committed conflictedState
    let step := finishCas before reply
    if expected == "pending" then
      ensure (after == "") s!"{name}: pending mismatch must start from live request"
      ensure (decide (step.state = before) && invalidResponse step && step.effect == .none)
        s!"{name}: invalid response changed pending state or produced an effect"
      ensure (step.state.pending == some pending && step.state.journalRetained)
        s!"{name}: pending journal was not preserved"
      pendingCount := pendingCount + 1
    else if expected == "committed" then
      ensure (after == "" && acknowledged step && step.effect == .dropJournal)
        s!"{name}: valid commit did not acknowledge"
      ensure (step.state.pending == none && !step.state.journalRetained &&
        step.state.completed == some ("committed", reply.revision) &&
        step.state.consumedReplies == 1)
        s!"{name}: commit did not consume the request exactly once"
      committed := some step.state
      commitCount := commitCount + 1
    else if expected == "conflict" then
      ensure (after == "" && conflicted step && step.effect == .dropJournal)
        s!"{name}: valid conflict did not complete"
      ensure (step.state.pending == none && !step.state.journalRetained &&
        step.state.completed == some ("conflict", reply.revision) &&
        step.state.consumedReplies == 1)
        s!"{name}: conflict did not consume without acknowledgement"
      conflictedState := some step.state
      conflictCount := conflictCount + 1
    else if expected == "rejected" then
      ensure ((after == "committed" || after == "conflict") && invalidState step &&
        step.effect == .none && decide (step.state = before) && step.state.pending == none)
        s!"{name}: duplicate changed consumed state"
      duplicateCount := duplicateCount + 1
    else throw s!"{name}: unknown expected result {expected}"
  ensure (pendingCount == 11 && commitCount == 1 && conflictCount == 1 && duplicateCount == 2)
    "host CAS fixture case totals changed"
  return cases.size

def main (args : List String) : IO UInt32 := do
  let path := args.headD "runtime/tests/fixtures/host-cas/cases.json"
  let fixture ← match Json.parse (← IO.FS.readFile path) with
    | .ok value => pure value
    | .error message => throw (IO.userError message)
  match runCases fixture with
  | .ok count =>
    IO.println s!"host CAS model checked {count} shared cases"
    return 0
  | .error message =>
    IO.eprintln message
    return 1
