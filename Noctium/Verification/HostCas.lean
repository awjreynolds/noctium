import Lean

namespace Noctium.Verification.HostCas

/-- Identity snapshot of one reachable pending CAS. The journal digest is private
data, not public request metadata. -/
structure PendingRequest where
  requestId : Nat
  operation : String
  capability : String
  schema : String
  attemptId : String
  transactionId : String
  journalDigest : String
  baseRevision : String
  deriving Repr, DecidableEq

/-- Already-decoded response fields checked before the lifecycle transition. -/
structure CasReply where
  requestId : Nat
  operation : String
  capability : String
  schema : String
  attemptId : String
  transactionId : String
  journalDigest : String
  baseRevision : String
  outcome : String
  revision : String
  deriving Repr, DecidableEq

structure State where
  pending : Option PendingRequest
  committedRevision : Option String := none
  conflictRevision : Option String := none
  deriving Repr, DecidableEq

inductive Transition where
  | rejected (state : State)
  | committed (state : State)
  | conflicted (state : State)
  deriving Repr, DecidableEq

private def revisionChar (char : Char) : Bool :=
  let code := char.toNat
  (48 ≤ code && code ≤ 57) || (65 ≤ code && code ≤ 90) ||
    (97 ≤ code && code ≤ 122) || code == 45 || code == 95 || code == 46 || code == 58

/-- Matches Rust lifecycle's bounded ASCII revision grammar. -/
def validRevision (revision : String) : Bool :=
  let chars := revision.toList
  !chars.isEmpty && chars.length ≤ 128 && chars.all revisionChar

/-- The runtime accepts only exact echoes of the pending request and a valid,
different revision. Digest equality is a binding check, not an authenticity proof. -/
def responseMatches (pending : PendingRequest) (reply : CasReply) : Bool :=
  pending.requestId == reply.requestId &&
  pending.operation == reply.operation &&
  pending.capability == reply.capability &&
  pending.schema == reply.schema &&
  pending.attemptId == reply.attemptId &&
  pending.transactionId == reply.transactionId &&
  pending.journalDigest == reply.journalDigest &&
  pending.baseRevision == reply.baseRevision &&
  validRevision reply.baseRevision &&
  validRevision reply.revision &&
  reply.revision != reply.baseRevision

/-- A rejected reply retains the entire state. A valid committed or conflicted
reply consumes the pending request, with acknowledgement only on commit.
This models `Runtime::finish_cas` after FFI has enforced ABI version 1 and
decoded required fields, including the u64 request ID. It assumes a reachable
`AwaitingCas` request with canonical identities and fixed operation/schema.
Decoding optional metadata, identity validation, and lifecycle evidence remain
Rust boundary obligations. -/
def finish (state : State) (reply : CasReply) : Transition :=
  match state.pending with
  | none => .rejected state
  | some pending =>
    if responseMatches pending reply then
      if reply.outcome == "committed" then
        .committed {state with pending := none, committedRevision := some reply.revision}
      else if reply.outcome == "conflict" then
        .conflicted {state with pending := none, conflictRevision := some reply.revision}
      else .rejected state
    else .rejected state

theorem invalidReplyLeavesState (state : State) (pending : PendingRequest)
    (reply : CasReply) (pendingUnchanged : state.pending = some pending)
    (mismatch : responseMatches pending reply = false) :
    finish state reply = .rejected state := by
  simp [finish, pendingUnchanged, mismatch]

theorem unsupportedOutcomeLeavesState (state : State) (pending : PendingRequest)
    (reply : CasReply) (pendingUnchanged : state.pending = some pending)
    (identityMatches : responseMatches pending reply = true)
    (unsupported : reply.outcome ≠ "committed" ∧ reply.outcome ≠ "conflict") :
    finish state reply = .rejected state := by
  simp [finish, pendingUnchanged, identityMatches, unsupported.1, unsupported.2]

theorem acceptedCommitConsumes (state : State) (pending : PendingRequest)
    (reply : CasReply) (pendingMatches : state.pending = some pending)
    (identityMatches : responseMatches pending reply = true)
    (committed : reply.outcome = "committed") :
    finish state reply =
      .committed {state with pending := none, committedRevision := some reply.revision} := by
  simp [finish, pendingMatches, identityMatches, committed]

theorem acceptedConflictConsumes (state : State) (pending : PendingRequest)
    (reply : CasReply) (pendingMatches : state.pending = some pending)
    (identityMatches : responseMatches pending reply = true)
    (conflict : reply.outcome = "conflict") :
    finish state reply =
      .conflicted {state with pending := none, conflictRevision := some reply.revision} := by
  simp [finish, pendingMatches, identityMatches, conflict]

theorem consumedReplyRejected (state : State) (reply : CasReply)
    (consumed : state.pending = none) :
    finish state reply = .rejected state := by
  simp [finish, consumed]

def acknowledgesCommit (state : State) : Bool := state.committedRevision.isSome

theorem conflictHasNoCommitAcknowledgement (state : State) (pending : PendingRequest)
    (reply : CasReply) (pendingMatches : state.pending = some pending)
    (identityMatches : responseMatches pending reply = true)
    (conflict : reply.outcome = "conflict")
    (unacknowledged : state.committedRevision = none) :
    ∃ after, finish state reply = .conflicted after ∧
      after.pending = none ∧ after.committedRevision = none ∧
      acknowledgesCommit after = false := by
  refine ⟨{state with pending := none, conflictRevision := some reply.revision},
    acceptedConflictConsumes state pending reply pendingMatches identityMatches conflict,
    by simp, by simp [unacknowledged], by simp [acknowledgesCommit, unacknowledged]⟩

end Noctium.Verification.HostCas
