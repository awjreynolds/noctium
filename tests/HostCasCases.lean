import Lean
import Noctium.Verification.HostCas

open Lean Noctium.Verification.HostCas

private structure Case where
  name : String
  overrides : Json
  after : String
  expected : String

private def ensure (condition : Bool) (message : String) : Except String Unit :=
  if condition then .ok () else .error message

private def exactFields (value : Json) (expected : List String) : Except String Unit := do
  let actual := (← value.getObj?).toList.map Prod.fst
  ensure (actual.length == expected.length && actual.eraseDups.length == actual.length &&
    actual.all expected.contains && expected.all actual.contains)
    "missing, unknown or duplicate fields"

private def stringField (value : Json) (field : String) : Except String String := do
  (← value.getObjVal? field).getStr?

private def naturalField (value : Json) (field : String) : Except String Nat := do
  (← value.getObjVal? field).getNat?

private def pendingFromJson (value : Json) : Except String PendingRequest := do
  exactFields value ["requestId", "operation", "capability", "schema", "attemptId",
    "transactionId", "journalDigest", "baseRevision"]
  return {
    requestId := ← naturalField value "requestId"
    operation := ← stringField value "operation"
    capability := ← stringField value "capability"
    schema := ← stringField value "schema"
    attemptId := ← stringField value "attemptId"
    transactionId := ← stringField value "transactionId"
    journalDigest := ← stringField value "journalDigest"
    baseRevision := ← stringField value "baseRevision"
  }

private def caseFromJson (value : Json) : Except String Case := do
  exactFields value ["name", "overrides", "after", "expected"]
  let overrides ← value.getObjVal? "overrides"
  let _ ← overrides.getObj?
  return {
    name := ← stringField value "name"
    overrides
    after := ← stringField value "after"
    expected := ← stringField value "expected"
  }

private def defaultReply (pending : PendingRequest) : CasReply := {
  requestId := pending.requestId
  operation := pending.operation
  capability := pending.capability
  schema := pending.schema
  attemptId := pending.attemptId
  transactionId := pending.transactionId
  journalDigest := pending.journalDigest
  baseRevision := pending.baseRevision
  outcome := "committed"
  revision := "r1"
}

private def applyOverrides (reply : CasReply) (overrides : Json) : Except String CasReply := do
  let mut reply := reply
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
    | _ => throw "unknown host CAS case override"
  return reply

private def runCases (fixture : Json) : Except String Nat := do
  exactFields fixture ["version", "pending", "cases"]
  ensure ((← naturalField fixture "version") == 1) "unsupported case version"
  let pending ← pendingFromJson (← fixture.getObjVal? "pending")
  let cases ← (← fixture.getObjVal? "cases").getArr?
  let initial : State := {pending := some pending}
  let mut committed : Option State := none
  let mut conflicted : Option State := none
  for value in cases do
    let testCase ← caseFromJson value
    let reply ← applyOverrides (defaultReply pending) testCase.overrides
    let before ← if testCase.after == "committed" then
      match committed with
      | some state => pure state
      | none => throw s!"{testCase.name}: missing prior commit"
    else if testCase.after == "conflict" then
      match conflicted with
      | some state => pure state
      | none => throw s!"{testCase.name}: missing prior conflict"
    else if testCase.after == "" then pure initial
    else throw s!"{testCase.name}: unknown prior state"
    match testCase.expected, finish before reply with
    | "pending", .rejected after =>
      ensure (after == before && after.pending == some pending)
        s!"{testCase.name}: rejection changed pending state"
    | "committed", .committed after =>
      ensure (after.pending == none && after.committedRevision == some reply.revision)
        s!"{testCase.name}: commit did not consume once"
      committed := some after
    | "rejected", .rejected after =>
      ensure (after == before && before.pending == none &&
        (before.committedRevision.isSome || before.conflictRevision.isSome))
        s!"{testCase.name}: duplicate changed consumed state"
    | "conflict", .conflicted after =>
      ensure (after.pending == none && after.committedRevision == none &&
        after.conflictRevision == some reply.revision)
        s!"{testCase.name}: conflict acknowledged a commit or kept the request"
      conflicted := some after
    | _, _ => throw s!"{testCase.name}: unexpected transition"
  return cases.size

def main (args : List String) : IO UInt32 := do
  let [path] := args | throw (IO.userError "usage: lean --run tests/HostCasCases.lean CASES.json")
  let contents ← IO.FS.readFile path
  let fixture ← match Json.parse contents with
    | .ok value => pure value
    | .error message => throw (IO.userError message)
  match runCases fixture with
  | .ok count =>
    IO.println s!"host CAS model checked {count} shared cases"
    return 0
  | .error message =>
    IO.eprintln message
    return 1
