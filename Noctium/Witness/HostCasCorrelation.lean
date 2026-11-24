namespace Noctium.Witness.HostCasCorrelation

/-- The request metadata produced by `Runtime::cas_metadata`. -/
def casOperation : String := "private_state.compare_exchange.v1"
def casSchema : String := "PrivateStateCasResult/v1"

private def byteIsDigit (value : UInt8) : Bool :=
  48 ≤ value.toNat && value.toNat ≤ 57

private def byteIsLowerHex (value : UInt8) : Bool :=
  byteIsDigit value || (97 ≤ value.toNat && value.toNat ≤ 102)

private def byteIsRevisionChar (value : UInt8) : Bool :=
  byteIsDigit value ||
    (65 ≤ value.toNat && value.toNat ≤ 90) ||
    (97 ≤ value.toNat && value.toNat ≤ 122) ||
    value.toNat == 45 || value.toNat == 95 || value.toNat == 46 || value.toNat == 58

/-- Mirrors the lowercase, 64-byte identifiers checked by the host lifecycle. -/
def canonicalHash (value : String) : Bool :=
  let bytes := value.toUTF8.data.toList
  bytes.length == 64 && bytes.all byteIsLowerHex

/-- Revisions are opaque tokens. Rust checks their ASCII shape and rejects the
same token as the request base. It does not compare revisions lexically. -/
def validRevision (value : String) : Bool :=
  let bytes := value.toUTF8.data.toList
  !bytes.isEmpty && bytes.length ≤ 128 && bytes.all byteIsRevisionChar

inductive Outcome where
  | committed
  | conflict
  deriving DecidableEq, Repr

def Outcome.abiValue : Outcome → String
  | .committed => "committed"
  | .conflict => "conflict"

/-- Values retained from the authorized `private_state.compare_exchange.v1`
request and its private journal. -/
structure PendingCas where
  protocolVersion : Nat
  requestId : Nat
  operation : String
  capability : String
  schema : String
  attemptId : String
  transactionId : String
  journalDigest : String
  baseRevision : String
  deriving DecidableEq, Repr

/-- The response envelope uses `abiVersion` and `requestId`; its value has the
exact strict `CasResponse` fields from host.rs. Unknown JSON fields are excluded
by the runtime's `deny_unknown_fields` decoder before this model starts. -/
structure CasReply where
  abiVersion : Nat
  requestId : Nat
  operation : String
  capability : String
  schema : String
  attemptId : String
  transactionId : String
  journalDigest : String
  outcome : String
  baseRevision : String
  revision : String
  deriving DecidableEq, Repr

structure Evidence where
  phaseAwaitingCas : Bool
  successfulExecution : Bool
  persisted : Bool
  submitted : Bool
  accepted : Bool
  commitCapabilityGranted : Bool
  deriving DecidableEq, Repr

def Evidence.authorizesCas (evidence : Evidence) : Prop :=
  evidence.phaseAwaitingCas = true ∧
  evidence.successfulExecution = true ∧
  evidence.persisted = true ∧
  evidence.submitted = true ∧
  evidence.accepted = true ∧
  evidence.commitCapabilityGranted = true

structure HostState where
  evidence : Evidence
  pending : Option PendingCas
  journalRetained : Bool
  completed : Option (String × String)
  consumedReplies : Nat
  deriving DecidableEq, Repr

inductive Error where
  | invalidState
  | invalidResponse
  deriving DecidableEq, Repr

inductive Effect where
  | none
  | dropJournal
  deriving DecidableEq, Repr

structure Step where
  state : HostState
  result : Except Error String
  effect : Effect
  deriving Repr

/-- Correlate every response field checked by `finish_cas` and the lifecycle.
The journal digest binds canonical journal contents by an explicit store
assumption below. -/
def replyCorrelates (pending : PendingCas) (reply : CasReply) : Bool :=
  pending.protocolVersion == 1 &&
  pending.operation == casOperation && pending.schema == casSchema &&
  reply.abiVersion == 1 && reply.requestId == pending.requestId &&
  reply.operation == casOperation && reply.operation == pending.operation &&
  reply.capability == pending.capability &&
  reply.schema == casSchema && reply.schema == pending.schema &&
  reply.attemptId == pending.attemptId &&
  reply.transactionId == pending.transactionId &&
  reply.journalDigest == pending.journalDigest &&
  reply.baseRevision == pending.baseRevision

def replyOutcome (reply : CasReply) : Option Outcome :=
  if reply.outcome == "committed" then some .committed
  else if reply.outcome == "conflict" then some .conflict
  else none

def validReply (pending : PendingCas) (reply : CasReply) : Bool :=
  replyCorrelates pending reply &&
  (replyOutcome reply).isSome &&
  validRevision reply.baseRevision &&
  validRevision reply.revision &&
  reply.revision != reply.baseRevision &&
  canonicalHash reply.attemptId && canonicalHash reply.transactionId &&
  canonicalHash reply.journalDigest

def complete (state : HostState) (reply : CasReply) : Step :=
  let outcome := (replyOutcome reply).getD .conflict
  { state := {state with
      evidence := {state.evidence with phaseAwaitingCas := false}
      pending := none
      journalRetained := false
      completed := some (outcome.abiValue, reply.revision)
      consumedReplies := state.consumedReplies + 1}
    result := .ok outcome.abiValue
    effect := .dropJournal }

/-- A failed response leaves the exact pending CAS and its journal available for
a retry. The function does not apply a store write. -/
def finishCas (state : HostState) (reply : CasReply) : Step :=
  match state.pending with
  | none => {state := state, result := .error .invalidState, effect := .none}
  | some pending =>
    if state.evidence.phaseAwaitingCas && state.journalRetained &&
      validReply pending reply then
      complete state reply
    else
      {state := state, result := .error .invalidResponse, effect := .none}

theorem mismatch_preserves_pending_and_has_no_effect
    (state : HostState) (pending : PendingCas) (reply : CasReply)
    (pendingEq : state.pending = some pending)
    (authorized : state.evidence.authorizesCas)
    (retained : state.journalRetained = true)
    (mismatch : validReply pending reply = false) :
    (finishCas state reply).state = state ∧
    (finishCas state reply).result = .error .invalidResponse ∧
    (finishCas state reply).effect = .none := by
  rcases authorized with ⟨phase, execution, persisted, submitted, accepted, capability⟩
  simp [finishCas, pendingEq, retained, phase, mismatch]

/-- A corrected response can retry the still-pending request after a mismatch.
The failed response has no effect, then the valid response consumes the request
and journal exactly once. -/
theorem corrected_retry_after_mismatch_consumes_once
    (state : HostState) (pending : PendingCas)
    (badReply correctedReply : CasReply)
    (pendingEq : state.pending = some pending)
    (authorized : state.evidence.authorizesCas)
    (retained : state.journalRetained = true)
    (mismatch : validReply pending badReply = false)
    (valid : validReply pending correctedReply = true) :
    let rejected := finishCas state badReply
    let retried := finishCas rejected.state correctedReply
    rejected.state = state ∧
    rejected.result = .error .invalidResponse ∧
    rejected.effect = .none ∧
    retried.result = .ok ((replyOutcome correctedReply).getD .conflict).abiValue ∧
    retried.effect = .dropJournal ∧
    retried.state.pending = none ∧
    retried.state.journalRetained = false ∧
    retried.state.consumedReplies = state.consumedReplies + 1 := by
  rcases authorized with ⟨phase, execution, persisted, submitted, accepted, capability⟩
  simp [finishCas, complete, pendingEq, retained, phase, mismatch, valid]

theorem valid_reply_consumes_once
    (state : HostState) (pending : PendingCas) (reply : CasReply)
    (pendingEq : state.pending = some pending)
    (authorized : state.evidence.authorizesCas)
    (retained : state.journalRetained = true)
    (valid : validReply pending reply = true) :
    (finishCas state reply).result = .ok ((replyOutcome reply).getD .conflict).abiValue ∧
    (finishCas state reply).effect = .dropJournal ∧
    (finishCas state reply).state.pending = none ∧
    (finishCas state reply).state.completed =
      some (((replyOutcome reply).getD .conflict).abiValue, reply.revision) ∧
    (finishCas state reply).state.consumedReplies = state.consumedReplies + 1 := by
  rcases authorized with ⟨phase, execution, persisted, submitted, accepted, capability⟩
  simp [finishCas, complete, pendingEq, retained, phase, valid]

theorem duplicate_after_consumption_rejects
    (state : HostState) (pending : PendingCas) (reply : CasReply)
    (pendingEq : state.pending = some pending)
    (authorized : state.evidence.authorizesCas)
    (retained : state.journalRetained = true)
    (valid : validReply pending reply = true) :
    let consumed := (finishCas state reply).state
    (finishCas consumed reply).state = consumed ∧
    (finishCas consumed reply).result = .error .invalidState ∧
    (finishCas consumed reply).effect = .none := by
  rcases authorized with ⟨phase, execution, persisted, submitted, accepted, capability⟩
  simp [finishCas, complete, pendingEq, retained, phase, valid]

structure Journal where
  attemptId : String
  transactionId : String
  namespaceName : String
  baseRevision : String
  contractAddress : String
  entrypoint : String
  journalDigest : String
  writes : List (String × String)
  deriving DecidableEq, Repr

structure Receipt where
  attemptId : String
  transactionId : String
  journalDigest : String
  revision : String
  deriving DecidableEq, Repr

structure Store where
  revision : String
  receipts : List Receipt := []
  appliedJournals : List Journal := []
  deriving DecidableEq, Repr

def findReceipt (attemptId : String) : List Receipt → Option Receipt
  | [] => none
  | receipt :: rest => if receipt.attemptId == attemptId then some receipt
      else findReceipt attemptId rest

structure StoreStep where
  store : Store
  reply : CasReply
  appliedNow : Bool
  deriving DecidableEq, Repr

def makeReply (pending : PendingCas) (journal : Journal)
    (outcome : String) (revision : String) : CasReply := {
  abiVersion := 1
  requestId := pending.requestId
  operation := casOperation
  capability := pending.capability
  schema := casSchema
  attemptId := journal.attemptId
  transactionId := journal.transactionId
  journalDigest := journal.journalDigest
  outcome
  baseRevision := journal.baseRevision
  revision
}

/-- Abstracts the host store's CAS behavior. `appliedJournals` records writes
only on a fresh matching base. Receipts make an identical retry idempotent. -/
def compareExchange (pending : PendingCas) (journal : Journal) (store : Store)
    (nextRevision : String) : StoreStep :=
  match findReceipt journal.attemptId store.receipts with
  | some receipt =>
    if receipt.transactionId == journal.transactionId &&
      receipt.journalDigest == journal.journalDigest then
      {store := store,
        reply := makeReply pending journal "committed" receipt.revision,
        appliedNow := false}
    else
      {store := store,
        reply := makeReply pending journal "conflict" receipt.revision,
        appliedNow := false}
  | none =>
    if journal.baseRevision == store.revision then
      let receipt : Receipt := {
        attemptId := journal.attemptId,
        transactionId := journal.transactionId,
        journalDigest := journal.journalDigest,
        revision := nextRevision}
      let updatedStore : Store := {
        store with
        revision := nextRevision,
        receipts := receipt :: store.receipts,
        appliedJournals := store.appliedJournals ++ [journal]}
      {store := updatedStore,
        reply := makeReply pending journal "committed" nextRevision,
        appliedNow := true}
    else
      {store := store,
        reply := makeReply pending journal "conflict" store.revision,
        appliedNow := false}

def matchesJournal (pending : PendingCas) (journal : Journal) : Prop :=
  pending.attemptId = journal.attemptId ∧
  pending.transactionId = journal.transactionId ∧
  pending.journalDigest = journal.journalDigest ∧
  pending.baseRevision = journal.baseRevision

theorem stale_store_conflict_records_without_apply
    (pending : PendingCas) (journal : Journal) (store : Store) (nextRevision : String)
    (noReceipt : findReceipt journal.attemptId store.receipts = none)
    (stale : journal.baseRevision ≠ store.revision)
    (journalMatch : matchesJournal pending journal)
    (revisionValid : validRevision store.revision = true)
    (baseValid : validRevision journal.baseRevision = true)
    (distinct : store.revision ≠ journal.baseRevision)
    (pendingAuthorized : pending.protocolVersion = 1 ∧
      pending.operation = casOperation ∧ pending.schema = casSchema ∧
      canonicalHash pending.attemptId = true ∧
      canonicalHash pending.transactionId = true ∧
      canonicalHash pending.journalDigest = true ∧
      validRevision pending.baseRevision = true)
    (evidence : Evidence)
    (authorized : evidence.authorizesCas) :
    let stored := compareExchange pending journal store nextRevision
    let finished := finishCas
      {evidence, pending := some pending, journalRetained := true,
        completed := none, consumedReplies := 0}
      stored.reply
    stored.store = store ∧ stored.appliedNow = false ∧
    stored.reply.outcome = "conflict" ∧
    finished.result = .ok "conflict" ∧
    finished.state.completed = some ("conflict", store.revision) ∧
    finished.effect = .dropJournal := by
  rcases journalMatch with ⟨attempt, transaction, digest, base⟩
  rcases authorized with ⟨phase, execution, persisted, submitted, accepted, capability⟩
  rcases pendingAuthorized with ⟨version, operation, schema, attemptHash,
    transactionHash, digestHash, pendingBaseValid⟩
  have storedResult : compareExchange pending journal store nextRevision = {
      store := store,
      reply := makeReply pending journal "conflict" store.revision,
      appliedNow := false} := by
    simp [compareExchange, noReceipt, stale]
  have attemptHashJournal : canonicalHash journal.attemptId = true := by
    simpa [← attempt] using attemptHash
  have transactionHashJournal : canonicalHash journal.transactionId = true := by
    simpa [← transaction] using transactionHash
  have digestHashJournal : canonicalHash journal.journalDigest = true := by
    simpa [← digest] using digestHash
  have replyValid : validReply pending
      (makeReply pending journal "conflict" store.revision) = true := by
    simp [validReply, replyCorrelates, replyOutcome, makeReply, version, operation, schema,
      attempt, transaction, digest, base, attemptHashJournal, transactionHashJournal,
      digestHashJournal, revisionValid, baseValid, distinct]
  have conflictOutcome : replyOutcome
      (makeReply pending journal "conflict" store.revision) = some .conflict := rfl
  have outcomeField : (makeReply pending journal "conflict" store.revision).outcome = "conflict" := rfl
  have revisionField : (makeReply pending journal "conflict" store.revision).revision = store.revision := rfl
  simp [storedResult, finishCas, complete, replyValid, conflictOutcome,
    outcomeField, revisionField, Outcome.abiValue, phase]

end Noctium.Witness.HostCasCorrelation
