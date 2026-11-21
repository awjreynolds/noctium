#ifndef NOCTIUM_NATIVE_H
#define NOCTIUM_NATIVE_H
#include <stddef.h>
#include <stdint.h>
#ifdef __cplusplus
extern "C" {
#endif
/* Native proof API, phase A of the host binding. Funding, signing, submission and
   journal persistence are outside this API. Existing runtime/control ABIs are
   separate. Tokens belong to this ABI and this process only.

   begin receives separate public descriptor, private configuration and public SRS
   byte channels. Descriptor UTF-8 JSON (unknown fields reject):
     {"abiVersion":1,"profile":"<selected profile NAME>",
      "bundleDirectory":"<explicit host-authorized filesystem directory>",
      "trustedManifestSha256":"<independently supplied lowercase SHA256>",
      "proofParametersSha256":"<independently supplied SRS SHA256>",
      "k":9,"ttl":2000000000,"proofServiceCapability":"host.prover",
      "maxResponseBytes":1048576}
   Bundle authentication/key validation and SRS validation precede private parsing.
   A digest authenticates retained bytes. Source certificate authority, native
   implementation/keygen, SRS ceremony relations and service disclosure authority
   require the host's own policy. No network, provider credential or ambient RNG
   is selected by this API. Supply 32 fresh unpredictable secret entropy bytes to
   begin and separately to every local_prove call. Entropy quality stays external.

   advance returns need_proof metadata with requestId, operation native.prove.v1,
   capability, profile, encoding midnight-prove-v2, k, source/SRS identities and
   bounds. Repeated advance returns the same pending request. Scheduling and
   request transport are private host data, outside contract-observer guarantees.
   private_request grants a separate owned token for the witness-bearing official
   /prove payload. Ordinary result access rejects private tokens. The host alone
   authorizes external service transmission and enforces service deadlines.

   resume accepts separate JSON correlation metadata and raw versioned V2 proof:
     {"abiVersion":1,"requestId":<exact uint64>,"operation":"native.prove.v1",
      "capability":"host.prover","profile":"<selected profile NAME>"}
   Wrong/stale/crossed replies reject and retain pending state. Successful resume
   verifies the frozen statement/proof with the retained VK/SRS, attaches native
   ledger V3, rechecks binding and roundtrips serialization inside Rust. Exactly
   one response completes a session. Result JSON contains publicIntentHex and
   publicIntentSha256, with intentEncoding=public-pedersen-commitment, funded=false
   and submitted=false. This public native intent projection contains the binding
   commitment, never its private randomness. It is not a funded/sealed transaction.
   The bounded completed session retains its typed private unsealed ProvedIntent
   until free for a later phase-B integration. Phase A exposes no private-intent
   serialization or funding/sealing operation.

   Optional local_prove dispatches the private token to the linked Rust LocalProver
   synchronously, once per session, returning a raw V2 response result token. The
   host then calls resume. External service adapters instead read private bytes
   and supply their raw response to resume. No callback, foreign pointer, stack
   frame or asynchronous future from these phase-A proof functions survives an ABI call.

   cancel revokes pending payload tokens and rejects subsequent resume. Completion
   rejects later cancellation. Free revokes private tokens. Already copied host
   bytes stay under the host's clearing policy. Owned private payload buffers are
   zeroized on revocation/free. No blanket native-allocation wiping is promised.
   Calls running outside the registry lock retain owned Rust data until return.
   Cancellation discards their late completion but does not hard-stop CPU work.
   Hard stop/deadline enforcement requires a host worker policy. In-flight work
   still occupies its resource slot after cancel/free, until its call returns.

   Limits: 8 combined proof sessions, witness target contexts, client sessions and
   composition owner contexts,
   2 live prepare/prove/verification calls, 64 ordinary result
   tokens, 16 private tokens, 1MiB private config/request/proof/result, 64KiB public
   descriptor/reply metadata, 16MiB declared bundle payload, 128MiB SRS. The
   bundle cap is this ABI host/resource policy, not a compiler capability ceiling
   or a change to other bundle consumers. Real claim
   qualification measured 456374 request / 3852 response / 4433 attached bytes.
   Reaching a bound rejects without an output token. Free tokens after use.

   Inputs must reference the declared readable bytes until return. Output pointers
   and copy buffers must be writable, correctly aligned and non-overlapping.
   Nulls, lengths and token classes are checked. Arbitrary invalid pointers or
   concurrent modification of borrowed foreign memory violate the caller contract.
   Caller-owned copies remain valid after token free. No Rust allocation is freed
   through a foreign allocator. */
enum { NOCTIUM_NATIVE_OK=0, NOCTIUM_NATIVE_INVALID_ARGUMENT=1,
  NOCTIUM_NATIVE_INVALID_HANDLE=2, NOCTIUM_NATIVE_INVALID_STATE=3,
  NOCTIUM_NATIVE_INVALID_RESPONSE=4, NOCTIUM_NATIVE_LIMIT=5,
  NOCTIUM_NATIVE_INTERNAL=6, NOCTIUM_NATIVE_BUFFER_TOO_SMALL=7 };
int32_t noctium_native_begin(const uint8_t*,size_t,const uint8_t*,size_t,
  const uint8_t*,size_t,const uint8_t*,size_t,uint64_t*);
int32_t noctium_native_advance(uint64_t,uint64_t*);
int32_t noctium_native_private_request(uint64_t,uint64_t*);
int32_t noctium_native_resume(uint64_t,const uint8_t*,size_t,const uint8_t*,size_t,uint64_t*);
int32_t noctium_native_local_prove(uint64_t,const uint8_t*,size_t,uint64_t*);
int32_t noctium_native_cancel(uint64_t);
int32_t noctium_native_free(uint64_t);
int32_t noctium_native_result_length(uint64_t,size_t*);
int32_t noctium_native_result_copy(uint64_t,uint8_t*,size_t,size_t*);
int32_t noctium_native_result_free(uint64_t);
int32_t noctium_native_private_length(uint64_t,size_t*);
int32_t noctium_native_private_copy(uint64_t,uint8_t*,size_t,size_t*);
int32_t noctium_native_private_free(uint64_t);

/* Independent owner side of one native contract-call composition. The host supplies
   an authenticated finalized snapshot; this ABI does not contact a ledger.

   Begin descriptor UTF-8 JSON (unknown fields reject):
     {"abiVersion":1,"profile":"<selected profile NAME>",
      "bundleDirectory":"<explicit host-authorized directory>",
      "trustedManifestSha256":"<independently supplied lowercase SHA256>",
      "proofParametersSha256":"<independently supplied SRS SHA256>",
      "k":9,"ttl":2000000000,"networkId":"<ledger network>",
      "contractAddress":"<64 lowercase hex characters>"}
   inputs are a UTF-8 JSON object of private entrypoint inputs. contract_state and
   ledger_parameters are exact canonical tagged Ledger 9 ContractState and
   LedgerParameters encodings from one finalized snapshot. proof_parameters are the
   public pinned native SRS bytes. Supply 32 fresh unpredictable entropy bytes.
   Bundle and SRS pins, profile, k, installed entrypoint, and fixed ledger parameters
   are checked before source inputs are parsed. Fee prices come from the supplied
   current LedgerParameters. The caller authenticates snapshot provenance and pairing.
   The output offer token contains canonical public CompositionOffer bytes.

   Prove accepts the exact public composition draft bytes and this owner's slot index.
   The ABI rebuilds the draft against its retained snapshot, checks its TTL against
   begin, and checks the owner's execution, entrypoint, state and commitment against
   the selected slot before producing a detached native proof. Supply 32 fresh entropy
   bytes. Output proof and offer tokens use the result length/copy/free functions above.
   An invalid draft or slot returns INVALID_RESPONSE, leaves output zero and permits
   retry. A successful proof consumes the owner context for further proof calls.
   Free the context after receiving its detached proof. Free during active proving
   returns INVALID_STATE. Offer and proof outputs follow the 1MiB ordinary result cap.

   Inputs must remain immutable and readable until return, outputs writable and
   non-overlapping. Contract state and snapshot provenance remain the host's
   responsibility. Offers expose the compiled plan's public transcript, including
   authorized disclosures. They contain neither the private input map nor its
   communication opening. Errors contain no private input values. */
int32_t noctium_native_composition_owner_begin(
  const uint8_t *descriptor, size_t descriptor_len,
  const uint8_t *inputs, size_t inputs_len,
  const uint8_t *contract_state, size_t contract_state_len,
  const uint8_t *ledger_parameters, size_t ledger_parameters_len,
  const uint8_t *proof_parameters, size_t proof_parameters_len,
  const uint8_t *coins, size_t coins_len,
  uint64_t *out_owner, uint64_t *out_offer);
int32_t noctium_native_composition_owner_prove(
  uint64_t owner, const uint8_t *draft, size_t draft_len, size_t slot,
  const uint8_t *coins, size_t coins_len, uint64_t *out_proof);
int32_t noctium_native_composition_owner_free(uint64_t owner);

/* Read a bounded JSON page from a public ledger snapshot, or a Merkle path from
   a native Merkle tree snapshot.
   Request UTF-8 JSON (unknown fields reject):
     {"abiVersion":1,"planSha256":"<lowercase SHA-256>",
      "stateSha256":"<lowercase SHA-256>","name":"<state name>",
      "keys":[{"type":"<Noctium scalar type>","value":<canonical JSON>}],
      "offset":0,"limit":32}
   Plan is the exact UTF-8 plan JSON. Snapshot is the exact canonical tagged
   ContractState<Db> serialization. Supply the plan digest independently from a
   verified plan manifest and the state digest from a matching finalized public
   receipt. This function checks both exact byte digests, but the caller remains
   responsible for pairing the plan and snapshot with the right chain provenance.
   No network access occurs. Keep the same snapshot and digests for every page of
   one read. Offsets scan from the beginning of the collection. For a Map
   with scalar values, entries are objects with typed key and value members:
     {"abiVersion":1,"kind":"map","entries":[{"key":"1","value":true}],
      "nextOffset":1}
   For a Set, entries are typed member values:
     {"abiVersion":1,"kind":"set","entries":["1"],"nextOffset":1}
   For a scalar List, entries are typed values in head-to-tail order:
     {"abiVersion":1,"kind":"list","entries":["1"],"nextOffset":1}
   Map and Set pages use the declared scalar types and stable ascending key order:
   numeric values sort numerically, Bool sorts false before true, byte values sort
   lexicographically by bytes, and foreign keys sort by canonical bytes. Use an
   empty keys array for a root collection. To read a nested collection, provide
   one typed key per enclosing Map. The path must resolve to a scalar Map, Set,
   or List. List pages validate each linked node's count and empty sentinel.
   Merkle result JSON has abiVersion, kind, entries, and nextOffset (integer or null).
   Merkle pages also have root and firstFree as decimal strings. The merkleTree kind has
   empty entries. historicMerkleTree entries contain history root digests as
   decimal strings in unspecified order. Use the native result token calls to
   read and free the response.

   For a Merkle path, replace offset and limit with "merklePath":
     {"leaf":{"kind":"field","value":"<canonical Field decimal>"},"index":"3"}
   Omit index to search for a stored match. An index is a decimal UInt64.
   Leaf alternatives are {"kind":"prehashed","value":[<32 bytes>]} and
   {"kind":"structured","schemaJson":"<schema JSON>","valueJson":"<value JSON>"}.
   Curve leaves use the native witness forms jubjubScalar, jubjubPoint, and
   foreign (ZKIR 3.2.1), with the same typed values. A fab leaf takes a
   value object with native FAB value atoms and alignment.
   A Merkle path result has abiVersion, kind (merklePath), snapshotRoot,
   candidateRoot, and steps [{sibling,goesLeft}] in leaf-to-root order.
   Digests and siblings are decimal strings. A missing search match has null
   candidateRoot and steps. Equal roots confirm that the indexed path
   reconstructs the snapshot root. Use a search to require a stored match.
   A missing or out-of-capacity indexed branch returns an error.

   Request is limited to 64KiB, plan and snapshot to 1MiB each, 12 path keys,
   offset 0..=1048576, and page size 1..=64. The state root and plan schema each
   support up to 16 entries. Returned JSON is limited to 1MiB. Errors contain no
   input values. */
int32_t noctium_ledger_collection_page(
  const uint8_t *request, size_t request_len,
  const uint8_t *plan, size_t plan_len,
  const uint8_t *snapshot, size_t snapshot_len,
  uint64_t *out_result);

/* Read one UInt64 Counter from a pinned, canonical contract-state snapshot.
   Request UTF-8 JSON (unknown fields reject):
     {"abiVersion":1,"planSha256":"<lowercase SHA-256>",
      "stateSha256":"<lowercase SHA-256>","name":"<state name>",
      "keys":[{"type":"<Noctium scalar type>","value":<canonical JSON>}]}
   Plan and snapshot use the exact byte encodings and caller-supplied digest
   provenance described for noctium_ledger_collection_page. Use an empty keys
   array for a root Counter. For a Counter nested under Maps, provide one typed
   key for each enclosing Map. The resolved declaration and stored value must
   both use the Counter schema and canonical UInt64 storage alignment.
   On success, out_result owns a copied JSON result under the native result
   handle API: {"abiVersion":1,"kind":"counter","value":"<UInt64>"}.
   Request, plan and snapshot limits match noctium_ledger_collection_page.
   This getter reads the supplied immutable snapshot and does not contact or
   mutate the ledger. */
int32_t noctium_ledger_counter_get(
  const uint8_t *request, size_t request_len,
  const uint8_t *plan, size_t plan_len,
  const uint8_t *snapshot, size_t snapshot_len,
  uint64_t *out_result);


/* Typed source witness handoff, additive to phase A. Prepare a target before source
   providers run. The helper authenticates the selected bundle and SRS, reads only
   private initial contract state, creates the deployment nonce once, and retains
   the exact deployment under an opaque process-local context token. Private state
   JSON is strict: {"state":{...}}. The ordinary result reports the frozen address
   and entrypoint. Control begins through noctium_control_begin_from_native_target
   using this token and the exact retained witness.control.json bytes.

   Target descriptor: {"abiVersion":1,"profile":"<profile>",
     "bundleDirectory":"<selected bundle>","trustedManifestSha256":"<pin>",
     "proofParametersSha256":"<SRS pin>","k":9,"ttl":2000000000}.
   Target preparation validates bundle and SRS before reading state. Supply 32 fresh
   entropy bytes. The target context is one-use and must be freed if abandoned.
   During synchronous proof preparation, target free returns INVALID_STATE while
   the native registry reserves that context; retry free after the call returns.

   begin_from_witness accepts no circuit-input map or arbitrary Runtime. It obtains
   all canonical original inputs and ordered witness leaves from the completed
   Control session, builds Config.inputs inside Rust, prepares against the retained
   exact deployment, and consumes Control plus target only after every proof input
   and target check passes. Pre-take validation failures retain a completed Control
   session and target for retry. If Control is canceled or freed during preparation,
   the target reservation is released and a fresh Control invocation is required.
   Once take succeeds, canceling the proof session drops its owned source Runtime.
   The proof descriptor omits bundleDirectory,
   since the target context pins the selected bundle:
     {"abiVersion":1,"profile":"<profile>",
      "trustedManifestSha256":"<same pin>","proofParametersSha256":"<SRS pin>",
      "k":9,"ttl":2000000000,"proofServiceCapability":"host.prover",
      "maxResponseBytes":1048576}.
   The source Runtime remains owned by the completed proof session. Deployment
   client start uses the existing fresh Setup path and leaves source writes untouched.
   `noctium_client_start_from_witness` consumes the exact source Runtime for the
   proved CALL and persists its typed recovery envelope through the existing SDK60
   journal, finality and CAS lifecycle. */
int32_t noctium_native_witness_target_begin(const uint8_t*,size_t,
  const uint8_t*,size_t,const uint8_t*,size_t,const uint8_t*,size_t,
  uint64_t*,uint64_t*);
int32_t noctium_native_target_context_free(uint64_t);
int32_t noctium_native_begin_from_witness(const uint8_t*,size_t,uint64_t,uint64_t,
  const uint8_t*,size_t,const uint8_t*,size_t,uint64_t*);

/* Multi-entry native contract execution. A target authenticates every selected
   operation bundle and binds their complete operation map to one deployment.
   It retains an opaque current-state token only after SDK60 verifies finalized
   receipt state and durable private-state CAS. It accepts no caller-supplied state
   bytes. Free target and state handles when finished.

   Target descriptor UTF-8 JSON (unknown fields reject):
     {"abiVersion":1,"profile":"<selected profile NAME>","ttl":2000000000,
      "journalDirectory":"<absolute host-authorized SDK60 journal directory>",
      "operations":[{"bundleDirectory":"<explicit directory>",
        "trustedManifestSha256":"<independent lowercase SHA-256>"}, ...]}
   Every contract operation must appear exactly once. The aggregate retained
   payload limit is 16MiB. Private initial state is the existing strict
   {"state":{...}} JSON. Target result metadata includes contractAddress and the
   ordered operation names. Supply fresh 32-byte host entropy.

   target_restore takes the same descriptor, state and entropy, plus the exact
   durable deployment attempt ID. It restores the original address from the
   host-authorized DirectoryJournal before registering the target. call_recover
   takes that restored target, a separate interrupted call attempt ID, an SDK60
   client descriptor and its private hostContext JSON. It recovers through the
   same journal and revalidates that attempt ID against the context.

   deployment_start chooses one authenticated operation name for the SDK60
   deployment binding and accepts the existing client descriptor plus private
   setup JSON. It starts the retained operation-map deployment once.

   contract_state_take returns an opaque state only after finality, receipt
   verification, journal durability and successful private CAS. Each bound
   client issues at most one state token. Repeated extraction returns
   INVALID_STATE. The token is consumed by a successful contract_call_start.
   Failed validation or proof/client startup leaves the token available to retry.

   contract_call_start descriptor UTF-8 JSON (unknown fields reject):
     {"abiVersion":1,"operation":"firstUpdate","k":6,"ttl":2000000000,
      "proofParametersSha256":"<independent SRS SHA-256>"}
   SRS bytes, private scalar input object, entropy, client descriptor and setup
   use separate length-bounded channels. This direct route supports scalar
   entrypoints without a WitnessControl sidecar. Sidecar entrypoints use the
   typed witness front door. The local proof is verified and bound before the
   SDK60 client starts. State is borrowed through every failure path and consumed
   only after successful bound client startup. No receipt, state or proof claim is
   accepted from the host.

   Each byte channel is bounded, immutable and caller-owned until return. Private
   maps and local proof responses are cleared by Rust on drop. DirectoryJournal
   recovery requires feature localnet and otherwise returns INVALID_STATE. */
int32_t noctium_native_contract_target_begin(
  const uint8_t *descriptor,size_t descriptor_len,
  const uint8_t *state_config,size_t state_config_len,
  const uint8_t *coins,size_t coins_len,
  uint64_t *out_target,uint64_t *out_metadata);
int32_t noctium_native_contract_target_restore(
  const uint8_t *descriptor,size_t descriptor_len,
  const uint8_t *state_config,size_t state_config_len,
  const uint8_t *coins,size_t coins_len,
  const uint8_t *deployment_attempt_id,size_t deployment_attempt_id_len,
  uint64_t *out_target,uint64_t *out_metadata);
int32_t noctium_native_contract_target_free(uint64_t target);
int32_t noctium_client_contract_deployment_start(
  uint64_t target,const uint8_t *operation,size_t operation_len,
  const uint8_t *client_descriptor,size_t client_descriptor_len,
  const uint8_t *setup,size_t setup_len,uint64_t *out_client);
int32_t noctium_native_contract_state_take(uint64_t client,uint64_t *out_state);
int32_t noctium_native_contract_state_free(uint64_t state);
/* Sidecar-enabled operation path. It executes the authenticated WitnessControl
   artifact through the typed source interpreter, keeps the exact state token in
   one opaque witness handle, and never calls Node or a second execution engine.

   call_descriptor uses the same UTF-8 JSON shape as contract_call_start:
     {"abiVersion":1,"operation":"advance","k":6,"ttl":2000000000,
      "proofParametersSha256":"<independent SRS SHA-256>"}
   inputs is a UTF-8 JSON object containing the Lean entrypoint arguments.
   host_context is the typed provider context accepted by the native control ABI.
   SRS validation, operation binding and the current state check run before source
   arguments are admitted. `coins` must contain 32 bytes. Source begin currently
   makes no random draws from this channel.

   advance returns an ordinary result token containing only status. A need_host
   status also carries requestId, attemptId, operation, capability and schema.
   The private callback arguments are available only from private_request and the
   native private buffer functions. resume accepts the exact typed V2 response:
     {"protocolVersion":2,"requestId":"...","attemptId":"...",
      "outcome":"value","operation":"...","capability":"...",
      "schema":"...","value":<typed value>}
   Invalid replies retain the pending callback. Accepted replies revoke copied
   private request tokens. Call advance again to obtain the next callback or the
   completed status. Status and callback metadata are host scheduling data, not
   contract outputs.

   witness_start prepares the completed call, proves it with the linked local
   prover, and starts the SDK60 native call client without setup JSON. Fresh
   32-byte entropy is required. Ordinary proof or client errors preserve the
   witness at its retryable phase. Successful startup consumes the witness handle.
   cancel consumes an unprepared witness and returns the same current state in a
   new state token. Once proof preparation succeeds, cancellation cannot return
   state. Freeing an active handle discards its owned state, so cancel first when
   the state must be reused. Free revokes private tokens in either case. */
int32_t noctium_native_contract_witness_begin(
  uint64_t target,uint64_t state,
  const uint8_t *call_descriptor,size_t call_descriptor_len,
  const uint8_t *inputs,size_t inputs_len,
  const uint8_t *host_context,size_t host_context_len,
  const uint8_t *srs,size_t srs_len,
  const uint8_t *coins,size_t coins_len,uint64_t *out_witness);
int32_t noctium_native_contract_witness_advance(uint64_t witness,uint64_t *out_result);
int32_t noctium_native_contract_witness_private_request(uint64_t witness,uint64_t *out_private);
int32_t noctium_native_contract_witness_resume(
  uint64_t witness,const uint8_t *typed_response,size_t typed_response_len,
  uint64_t *out_result);
int32_t noctium_client_contract_witness_start(
  uint64_t witness,const uint8_t *client_descriptor,size_t client_descriptor_len,
  const uint8_t *coins,size_t coins_len,uint64_t *out_client);
int32_t noctium_native_contract_witness_cancel(uint64_t witness,uint64_t *out_state);
int32_t noctium_native_contract_witness_free(uint64_t witness);
int32_t noctium_client_contract_call_start(
  uint64_t target,uint64_t state,
  const uint8_t *call_descriptor,size_t call_descriptor_len,
  const uint8_t *inputs,size_t inputs_len,
  const uint8_t *srs,size_t srs_len,
  const uint8_t *coins,size_t coins_len,
  const uint8_t *client_descriptor,size_t client_descriptor_len,
  const uint8_t *setup,size_t setup_len,uint64_t *out_client);
int32_t noctium_native_contract_call_recover(
  uint64_t target,
  const uint8_t *call_attempt_id,size_t call_attempt_id_len,
  const uint8_t *client_descriptor,size_t client_descriptor_len,
  const uint8_t *host_context,size_t host_context_len,uint64_t *out_client);

/* Phase B: explicit pull/resume SDK60 client extension. Existing phase-A calls
   above keep their original behavior. Only Rust-owned futures/objects survive
   calls. No foreign callback, stack frame or buffer is retained.

   start accepts source proof session, kind 0=exact retained deployment or 1=call,
   public descriptor, and separate private setup. Each source kind starts once.
   Descriptor: {"abiVersion":1,"policy":{"networkId":"undeployed",
     "genesis":"<independent genesis>","specVersion":2001100,
     "transactionVersion":4,"profile":"<selected profile>",
     "maxDust":"10000000000000000000000"},
     "capabilities":{"chain":"dev.chain","funding":"dev.wallet",
                     "signing":"dev.approval","journal":"dev.store"}}
   New u64 identities and u128 budgets use canonical decimal JSON strings or
   opaque uint64_t handles. Phase A numeric requestId remains unchanged.
   Private setup: {"hostContext":<existing host protocol context>,
                   "stages":[<existing private_state.stage.v1 records>]}
   Target address/entrypoint derive from the retained typed native objects.
   Stages are host integration state, with no new source-effect proof claim.

   command is prepare, submit, observe, commit, cancel, deadline or reload.
   advance/resume return need_host metadata or an owned step result. Every host
   request binds requestId (string), operation, capability, schema and profile.
   request returns a typed opaque request token. Checked service replies come
   from an explicit Rust host adapter; arbitrary claimed receipt JSON is never
   accepted. resume accepts the exact metadata fields plus that reply token.
   Wrong/stale/crossed/duplicate/class-mismatched replies reject before mutation.
   service_failure reports a host failure, never finalized rejection evidence.
   Funding/signing remain explicit host approvals/capabilities. SDK60 validates
   the unchanged contract intent, native proof, fees, sealed transaction, applied
   state, receipt and journal correlation inside the library.

   recover takes the public descriptor and private hostContext only. It loads
   the authenticated current full record/revision through journal.load.v1.
   It never imports an unchecked BoundTransaction or rebuilds a funded identity.
   Recovery requires finalized re-observation before private CAS. reload repeats
   that trusted recovery path for a live attempt after lost acknowledgements.
   Durable storage/version-CAS/idempotency truth is the host store capability.

   Preparing/funding/signing supports cancellation. Once submit starts, do not
   drop unresolved persist/broadcast/CAS work: finish the current method through
   its host replies or explicit failure, then use SDK60 deadline/recovery.
   Cancellation after submission rejects. Unknown broadcast stays Uncertain.
   detach refuses live work or a bound record lacking a current durable ack.
   A failed cancellation/deadline persist retains Cancelled but undurable state.
   Retry the same cancel/deadline to obtain its durable acknowledgement. No
   rebroadcast is permitted from Cancelled. CAS completion requires durable
   terminal receipt before runtime acknowledgement.
   Service work stays counted after source/session cancellation until its call
   returns. Hard CPU/transport stop remains host worker/deadline policy.

   Phase-B private_request returns a separate zeroized buffer of native private
   bytes (up to SDK60's 32MiB recovery-record bound). Ordinary token functions
   reject private buffers. transaction returns sealed public bytes (max4MiB).
   receipt_state returns full checked public state (max1MiB). Step metadata is
   private host transport, not a contract observation. Free service/result tokens.
   No blanket native-allocation zeroization is promised. */
int32_t noctium_client_start(uint64_t,uint32_t,const uint8_t*,size_t,const uint8_t*,size_t,uint64_t*);
int32_t noctium_client_start_from_witness(uint64_t,const uint8_t*,size_t,uint64_t*);
int32_t noctium_client_recover(const uint8_t*,size_t,const uint8_t*,size_t,uint64_t*);
int32_t noctium_client_command(uint64_t,const uint8_t*,size_t,uint64_t*);
int32_t noctium_client_advance(uint64_t,uint64_t*);
int32_t noctium_client_request(uint64_t,uint64_t*);
int32_t noctium_client_resume(uint64_t,const uint8_t*,size_t,uint64_t,uint64_t*);
int32_t noctium_client_service_failure(uint64_t,uint64_t*);
int32_t noctium_client_private_request(uint64_t,uint64_t*);
int32_t noctium_client_service_free(uint64_t);
int32_t noctium_client_detach(uint64_t);
int32_t noctium_client_transaction(uint64_t,uint64_t*);
int32_t noctium_client_receipt_state(uint64_t,uint64_t*);
/* Export the idle client's exact private input to recover. Use the native
   private result API and retain bytes securely before submission. */
int32_t noctium_client_recovery_context(uint64_t,uint64_t*);

/* Explicit qualification helper, linked only with feature localnet. It restricts
   execution to the qualified isolated development genesis and loopback endpoint.
   Config includes abiVersion, policy/capabilities above, endpoint, timeoutMillis,
   maxResponseBytes, maxReplayBlocks (string), journalDirectory, parameterCache,
   parameterSource, dustSrsSha256 and publicDevelopmentGenesis=true. Cache/source/
   SRS fields are null for recovery-only use. No cache fetch fallback is enabled.
   open authenticates network/metadata and public proof material before reading
   separate seed bytes. Seed is optional for recovery. This helper selects no
   production wallet or endpoint. resolve dispatches the typed request through
   existing Node, DevelopmentFunding, ExplicitSeal and DirectoryJournal code.
   approve=1 explicitly authorizes signing; funding/signing require fresh32-byte
   host entropy. Native checked replies preserve receipt ancestry/extrinsic/event/
   state validation. context returns public finalized time/reference for TTL.
   At most two adapters exist; blocking jobs share the two live-work slots. */
int32_t noctium_localnet_open(const uint8_t*,size_t,const uint8_t*,size_t,uint64_t*);
int32_t noctium_localnet_context(uint64_t,uint64_t*);
int32_t noctium_localnet_resolve(uint64_t,uint64_t,uint32_t,const uint8_t*,size_t,uint64_t*);
int32_t noctium_localnet_free(uint64_t);
/* Explicit host-store inspection for qualification. Returns a private token. */
int32_t noctium_localnet_private_value(uint64_t,const uint8_t*,size_t,uint64_t*);
#ifdef __cplusplus
}
#endif
#endif
