mod common;
use noctium_runtime::ffi::*;
use serde_json::{Value as Json, json};
use std::{collections::BTreeMap, sync::Mutex};
static TEST_LOCK: Mutex<()> = Mutex::new(());

fn envelope(attempt: char) -> Json {
    let mut context: Json =
        serde_json::from_str(include_str!("fixtures/private-state/context.json")).unwrap();
    context["attemptId"] = json!(attempt.to_string().repeat(64));
    let mut params = Vec::new();
    serialize::tagged_serialize(&ledger::structure::INITIAL_PARAMETERS, &mut params).unwrap();
    json!({"abiVersion":1,"profile":noctium_runtime::profile::ABI,"plan":common::unsigned_json(),"publicInputs":{"expected":"510"},"state":{"total":"0"},"ledgerParametersHex":hex::encode(params),"address":"00".repeat(32),"circuit":serde_json::from_str::<Json>(include_str!("fixtures/unsigned/circuit.zkir")).unwrap(),"hostContext":context})
}
fn take(token: u64) -> Json {
    let mut length = 0;
    assert_eq!(unsafe { noctium_result_length(token, &mut length) }, OK);
    let mut bytes = vec![0; length];
    let mut written = 0;
    assert_eq!(
        unsafe { noctium_result_copy(token, bytes.as_mut_ptr(), length, &mut written) },
        OK
    );
    assert_eq!(noctium_result_free(token), OK);
    let text = String::from_utf8(bytes).unwrap();
    assert!(!text.contains("8675309"));
    assert!(!text.contains("claims/"));
    assert!(!text.contains("journalDigest"));
    serde_json::from_str(&text).unwrap()
}
fn begin(value: Json) -> u64 {
    let bytes = serde_json::to_vec(&value).unwrap();
    let mut session = 0;
    let mut result = 0;
    assert_eq!(
        unsafe { noctium_session_begin(bytes.as_ptr(), bytes.len(), &mut session, &mut result) },
        OK
    );
    take(result);
    session
}
fn advance(session: u64) -> Json {
    let mut result = 0;
    assert_eq!(
        unsafe { noctium_session_advance(session, &mut result) },
        OK
    );
    take(result)
}
fn call(
    session: u64,
    value: Json,
    function: unsafe extern "C" fn(u64, *const u8, usize, *mut u64) -> i32,
) -> Result<Json, i32> {
    let bytes = serde_json::to_vec(&value).unwrap();
    let mut result = 99;
    let status = unsafe { function(session, bytes.as_ptr(), bytes.len(), &mut result) };
    if status == OK {
        Ok(take(result))
    } else {
        assert_eq!(result, 0);
        Err(status)
    }
}
fn response(session: u64, id: u64, value: Json, bound: bool) -> Result<Json, i32> {
    let mut payload = json!({"abiVersion":1,"requestId":id,"value":value});
    if bound {
        payload["operation"] = json!("private_state.read.v1");
        payload["capability"] = json!("store");
        payload["schema"] = json!("UIntRange<256>");
    }
    call(session, payload, noctium_session_resume)
}
fn notice(session: u64, attempt: char, transaction: char, event: &str) -> Result<Json, i32> {
    call(
        session,
        json!({"abiVersion":1,"attemptId":attempt.to_string().repeat(64),"transactionId":transaction.to_string().repeat(64),"event":event}),
        noctium_session_notify,
    )
}
fn stage(session: u64, key: &str) -> Result<Json, i32> {
    call(
        session,
        json!({"abiVersion":1,"operation":"private_state.stage.v1","capability":"store","key":key,"type":"Native","value":"8675309"}),
        noctium_session_stage_private,
    )
}
fn private(session: u64, kind: u32) -> Result<Json, i32> {
    let mut token = 0;
    let status = unsafe { noctium_session_private_data(session, kind, &mut token) };
    if status != OK {
        return Err(status);
    }
    let mut length = 0;
    assert_eq!(
        unsafe { noctium_result_length(token, &mut length) },
        INVALID_HANDLE
    );
    assert_eq!(unsafe { noctium_private_length(token, &mut length) }, OK);
    let mut bytes = vec![0; length];
    let mut written = 99;
    assert_eq!(
        unsafe { noctium_private_copy(token, bytes.as_mut_ptr(), length - 1, &mut written) },
        BUFFER_TOO_SMALL
    );
    assert_eq!(written, 0);
    assert_eq!(
        unsafe { noctium_private_copy(token, bytes.as_mut_ptr(), length, &mut written) },
        OK
    );
    assert_eq!(noctium_private_free(token), OK);
    assert_eq!(noctium_private_free(token), INVALID_HANDLE);
    Ok(serde_json::from_slice(&bytes).unwrap())
}
fn prepare(session: u64) {
    assert_eq!(private(session, PRIVATE_JOURNAL), Err(INVALID_STATE));
    stage(session, "claims/used").unwrap();
    let request = advance(session);
    assert_eq!(request["request"]["operation"], "private_state.read.v1");
    assert_eq!(
        private(session, PRIVATE_REQUEST).unwrap()["arguments"]["key"],
        "claims/secret"
    );
    response(session, 1, json!("255"), true).unwrap();
    assert_eq!(advance(session)["request"]["name"], "right");
    response(session, 2, json!("255"), false).unwrap();
    assert_eq!(advance(session)["status"], "completed");
    assert_eq!(private(session, PRIVATE_JOURNAL), Err(INVALID_STATE));
    assert_eq!(stage(session, "claims/used"), Err(INVALID_STATE));
}
#[derive(Default)]
struct Store {
    revision: u32,
    values: BTreeMap<String, Json>,
    receipts: BTreeMap<String, (String, String, String)>,
    applies: usize,
}
impl Store {
    fn cas(&mut self, journal: &Json) -> Json {
        let attempt = journal["attemptId"].as_str().unwrap().to_owned();
        let transaction = journal["transactionId"].as_str().unwrap().to_owned();
        let base = journal["baseRevision"].as_str().unwrap();
        let fingerprint = journal["journalDigest"].as_str().unwrap().to_owned();
        if let Some((old, revision, old_fingerprint)) = self.receipts.get(&attempt) {
            let outcome = if old == &transaction && old_fingerprint == &fingerprint {
                "committed"
            } else {
                "conflict"
            };
            return json!({"outcome":outcome,"baseRevision":base,"revision":revision,"attemptId":attempt,"transactionId":transaction,"journalDigest":fingerprint});
        }
        if base != format!("r{}", self.revision) {
            return json!({"outcome":"conflict","baseRevision":base,"revision":format!("r{}",self.revision),"attemptId":attempt,"transactionId":transaction,"journalDigest":fingerprint});
        }
        for (key, value) in journal["writes"].as_object().unwrap() {
            self.values.insert(key.clone(), value.clone());
        }
        self.revision += 1;
        self.applies += 1;
        let revision = format!("r{}", self.revision);
        self.receipts.insert(
            attempt.clone(),
            (transaction.clone(), revision.clone(), fingerprint.clone()),
        );
        json!({"outcome":"committed","baseRevision":base,"revision":revision,"attemptId":attempt,"transactionId":transaction,"journalDigest":fingerprint})
    }
}
fn accepted(session: u64, attempt: char, transaction: char) -> Json {
    notice(session, attempt, transaction, "bind").unwrap();
    assert!(private(session, PRIVATE_JOURNAL).is_ok());
    assert_eq!(
        notice(session, attempt, transaction, "submitted"),
        Err(INVALID_STATE)
    );
    notice(session, attempt, transaction, "persisted").unwrap();
    notice(session, attempt, transaction, "persisted").unwrap();
    notice(session, attempt, transaction, "submitted").unwrap();
    notice(session, attempt, transaction, "submitted").unwrap();
    let request = notice(session, attempt, transaction, "accepted").unwrap();
    assert_eq!(
        request["request"]["operation"],
        "private_state.compare_exchange.v1"
    );
    request
}
fn commit(session: u64, value: Json) -> Result<Json, i32> {
    commit_payload(
        session,
        json!({
            "abiVersion":1,
            "requestId":3,
            "operation":"private_state.compare_exchange.v1",
            "capability":"store",
            "schema":"PrivateStateCasResult/v1",
            "value":value
        }),
    )
}
fn commit_payload(session: u64, payload: Json) -> Result<Json, i32> {
    call(session, payload, noctium_session_resume)
}
#[test]
fn provider_capabilities_and_journals_follow_host_cas_lifecycle() {
    let _lock = TEST_LOCK.lock().unwrap();
    let session = begin(envelope('a'));
    assert_eq!(stage(session, "claims_evil/used"), Err(INVALID_RESPONSE));
    stage(session, "claims/used").unwrap();
    assert_eq!(stage(session, "claims/second"), Err(LIMIT));
    let first = advance(session);
    assert_eq!(advance(session), first);
    for (field, value) in [
        ("operation", json!("wrong.v1")),
        ("capability", json!("other")),
        ("schema", json!("Bool")),
        ("requestId", json!(9)),
    ] {
        let mut payload = json!({"abiVersion":1,"requestId":1,"operation":"private_state.read.v1","capability":"store","schema":"UIntRange<256>","value":"255"});
        payload[field] = value;
        assert_eq!(
            call(session, payload, noctium_session_resume),
            Err(INVALID_RESPONSE)
        );
        assert_eq!(advance(session), first);
    }
    assert_eq!(
        response(session, 1, json!("0255"), true),
        Err(INVALID_RESPONSE)
    );
    response(session, 1, json!("255"), true).unwrap();
    assert_eq!(response(session, 1, json!("255"), true), Err(INVALID_STATE));
    advance(session);
    response(session, 2, json!("255"), false).unwrap();
    advance(session);
    let pending = accepted(session, 'a', 'b');
    assert_eq!(notice(session, 'a', 'b', "accepted").unwrap(), pending);
    assert_eq!(notice(session, 'a', 'c', "accepted"), Err(INVALID_STATE));
    // Both attempts are prepared and accepted before either CAS applies.
    let concurrent = begin(envelope('c'));
    prepare(concurrent);
    accepted(concurrent, 'c', 'd');
    let mut store = Store::default();
    assert_eq!(store.applies, 0);
    let journal = private(session, PRIVATE_REQUEST).unwrap()["journal"].clone();
    assert_eq!(journal["writes"]["claims/used"]["value"], "8675309");
    let reply = store.cas(&journal);
    assert_eq!(commit(concurrent, reply.clone()), Err(INVALID_RESPONSE));
    // Each mismatch targets one correlation field. The same pending request
    // remains available until the corrected response arrives.
    let applies_before_mismatches = store.applies;
    let correlation_fixture: Json = serde_json::from_str(include_str!(
        "fixtures/host-cas-correlation.json"
    ))
    .unwrap();
    let correlation_mismatches = correlation_fixture["cases"]
        .as_array()
        .unwrap()
        .iter()
        .map(|case| {
            (
                case["field"].as_str().unwrap(),
                case["location"].as_str().unwrap(),
                case["replacement"].clone(),
            )
        })
        .collect::<Vec<_>>();
    for (field, location, replacement) in correlation_mismatches {
        let mut payload = json!({
            "abiVersion":1,
            "requestId":3,
            "operation":"private_state.compare_exchange.v1",
            "capability":"store",
            "schema":"PrivateStateCasResult/v1",
            "value":reply
        });
        if location == "envelope" {
            payload[field] = replacement;
        } else {
            payload["value"][field] = replacement;
        }
        assert_eq!(
            commit_payload(session, payload),
            Err(INVALID_RESPONSE),
            "{field}"
        );
        assert_eq!(
            notice(session, 'a', 'b', "accepted").unwrap(),
            pending,
            "{field}"
        );
        assert_eq!(
            private(session, PRIVATE_JOURNAL).unwrap()["journalDigest"],
            journal["journalDigest"],
            "{field}"
        );
        assert_eq!(store.applies, applies_before_mismatches, "{field}");
    }
    let mut same_base = reply.clone();
    same_base["baseRevision"] = json!("r0");
    same_base["revision"] = json!("r0");
    assert_eq!(commit(session, same_base), Err(INVALID_RESPONSE));
    assert_eq!(notice(session, 'a', 'b', "accepted").unwrap(), pending);
    let result = commit(session, reply).unwrap();
    assert_eq!(result["phase"], "committed");
    assert_eq!(store.applies, 1);
    assert_eq!(
        notice(session, 'a', 'b', "accepted").unwrap()["phase"],
        "committed"
    );
    assert_eq!(private(session, PRIVATE_JOURNAL), Err(INVALID_STATE));
    assert_eq!(
        commit(
            session,
            json!({"outcome":"committed","baseRevision":"r0","revision":"r1"})
        ),
        Err(INVALID_STATE)
    );
    assert_eq!(noctium_session_free(session), OK);
    // The second CAS now observes the stale revision and never applies.
    let journal = private(concurrent, PRIVATE_REQUEST).unwrap()["journal"].clone();
    assert_eq!(
        commit(concurrent, store.cas(&journal)).unwrap()["phase"],
        "conflicted"
    );
    assert_eq!(store.applies, 1);
    noctium_session_free(concurrent);
    // Recovery of an identical persisted attempt uses the host receipt, never a second apply.
    let retry = begin(envelope('a'));
    prepare(retry);
    accepted(retry, 'a', 'b');
    let journal = private(retry, PRIVATE_REQUEST).unwrap()["journal"].clone();
    assert_eq!(
        commit(retry, store.cas(&journal)).unwrap()["phase"],
        "committed"
    );
    assert_eq!(store.applies, 1);
    noctium_session_free(retry);
    let changed = begin(envelope('a'));
    stage(changed, "claims/used").unwrap();
    call(changed,json!({"abiVersion":1,"operation":"private_state.stage.v1","capability":"store","key":"claims/used","type":"Native","value":"8675310"}),noctium_session_stage_private).unwrap();
    advance(changed);
    response(changed, 1, json!("255"), true).unwrap();
    advance(changed);
    response(changed, 2, json!("255"), false).unwrap();
    advance(changed);
    accepted(changed, 'a', 'b');
    let journal = private(changed, PRIVATE_REQUEST).unwrap()["journal"].clone();
    assert_eq!(
        commit(changed, store.cas(&journal)).unwrap()["phase"],
        "conflicted"
    );
    assert_eq!(store.applies, 1);
    noctium_session_free(changed);
    let uncertain = begin(envelope('e'));
    prepare(uncertain);
    notice(uncertain, 'e', 'f', "bind").unwrap();
    notice(uncertain, 'e', 'f', "persisted").unwrap();
    notice(uncertain, 'e', 'f', "submitted").unwrap();
    assert_eq!(
        notice(uncertain, 'e', 'f', "uncertain").unwrap()["hostCasAcknowledged"],
        false
    );
    assert_eq!(private(uncertain, PRIVATE_REQUEST), Err(INVALID_STATE));
    let mut output = 0;
    assert_eq!(
        unsafe { noctium_session_cancel(uncertain, &mut output) },
        INVALID_STATE
    );
    assert_eq!(
        notice(uncertain, 'e', 'f', "rejected").unwrap()["phase"],
        "rejected"
    );
    assert_eq!(private(uncertain, PRIVATE_JOURNAL), Err(INVALID_STATE));
    noctium_session_free(uncertain);
    let cancelled = begin(envelope('1'));
    stage(cancelled, "claims/used").unwrap();
    assert_eq!(
        unsafe { noctium_session_cancel(cancelled, &mut output) },
        OK
    );
    take(output);
    assert_eq!(private(cancelled, PRIVATE_JOURNAL), Err(INVALID_STATE));
    noctium_session_free(cancelled);
    let mut failed = envelope('2');
    failed["publicInputs"]["expected"] = json!("509");
    let failed = begin(failed);
    stage(failed, "claims/used").unwrap();
    advance(failed);
    response(failed, 1, json!("255"), true).unwrap();
    advance(failed);
    response(failed, 2, json!("255"), false).unwrap();
    assert_eq!(advance(failed)["status"], "failed");
    assert_eq!(private(failed, PRIVATE_JOURNAL), Err(INVALID_STATE));
    noctium_session_free(failed);
}

#[test]
fn host_descriptor_scopes_and_private_buffer_limits_reject_without_partial_effects() {
    let _lock = TEST_LOCK.lock().unwrap();
    for (pointer, value, expected) in [
        ("/hostContext/limits/requests", json!(2), LIMIT),
        (
            "/hostContext/capabilities/0/keyPrefix",
            json!("*"),
            INVALID_ARGUMENT,
        ),
        (
            "/hostContext/capabilities/0/keyPrefix",
            json!("claims//"),
            INVALID_ARGUMENT,
        ),
        (
            "/hostContext/capabilities/0/namespace",
            json!("another_wallet"),
            INVALID_ARGUMENT,
        ),
        (
            "/hostContext/providers/0/arguments/key",
            json!("claims_evil/secret"),
            INVALID_RESPONSE,
        ),
        (
            "/hostContext/operations/0/resultSchema",
            json!("Bool"),
            INVALID_ARGUMENT,
        ),
        (
            "/hostContext/operations/0/resultSchema",
            json!("SourceCellType"),
            INVALID_ARGUMENT,
        ),
    ] {
        let mut value_envelope = envelope('3');
        *value_envelope.pointer_mut(pointer).unwrap() = value;
        let bytes = serde_json::to_vec(&value_envelope).unwrap();
        let mut session = 99;
        let mut result = 99;
        assert_eq!(
            unsafe {
                noctium_session_begin(bytes.as_ptr(), bytes.len(), &mut session, &mut result)
            },
            expected
        );
        assert_eq!((session, result), (0, 0));
    }
    let session = begin(envelope('3'));
    prepare(session);
    notice(session, '3', '4', "bind").unwrap();
    let mut tokens = Vec::new();
    for _ in 0..MAX_PRIVATE_RESULTS {
        let mut token = 0;
        assert_eq!(
            unsafe { noctium_session_private_data(session, PRIVATE_JOURNAL, &mut token) },
            OK
        );
        tokens.push(token);
    }
    let mut extra = 99;
    assert_eq!(
        unsafe { noctium_session_private_data(session, PRIVATE_JOURNAL, &mut extra) },
        LIMIT
    );
    assert_eq!(extra, 0);
    for token in tokens {
        assert_eq!(noctium_private_free(token), OK);
    }
    assert!(private(session, PRIVATE_JOURNAL).is_ok());
    let mut cancelled = 0;
    assert_eq!(
        unsafe { noctium_session_cancel(session, &mut cancelled) },
        OK
    );
    take(cancelled);
    noctium_session_free(session);
    let mut small = envelope('5');
    small["hostContext"]["limits"]["privateBytes"] = json!(1024);
    small["hostContext"]["limits"]["writes"] = json!(64);
    let small = begin(small);
    let mut rejected = false;
    for index in 0..64 {
        let name = format!("claims/{}{}", "k".repeat(100), index);
        match stage(small, &name) {
            Ok(_) => {}
            Err(LIMIT) => {
                rejected = true;
                break;
            }
            Err(status) => panic!("unexpected numeric status {status}"),
        }
    }
    assert!(rejected);
    assert_eq!(
        unsafe { noctium_session_cancel(small, &mut cancelled) },
        OK
    );
    take(cancelled);
    noctium_session_free(small);
}
