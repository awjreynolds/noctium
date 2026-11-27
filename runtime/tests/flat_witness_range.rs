#![cfg(feature = "zkir-321")]

use anyhow::Result;
use coin_structure::contract::ContractAddress;
use noctium_runtime::{
    Plan, check,
    control::{InvocationTarget, Session, TypedResponse},
    create_state,
    host::{self, Capability, Context, Limits, Operation, Provider},
    prepare,
    zkir::IrSource,
};
use serde_json::{Value as Json, json};
use sha2::{Digest, Sha256};
use std::{collections::BTreeMap, fs, path::PathBuf};

const STEM: &str = "FlatWitnessRange.longRange";
const RANGE_END: u32 = 1024;
const FAILURE_AFTER: u32 = 3;
const REQUEST_BUDGET: usize = 1026;

fn artifact_root() -> PathBuf {
    PathBuf::from(
        std::env::var_os("NOCTIUM_FLAT_WITNESS_RANGE_DIR")
            .expect("set NOCTIUM_FLAT_WITNESS_RANGE_DIR to fresh FlatWitnessRange artifacts"),
    )
}

fn binding(control: &Json) -> Json {
    serde_json::from_str(control["binding"].as_str().expect("binding string")).unwrap()
}

fn context(control: &Json, attempt_id: &str, requests: usize) -> Context {
    let witness = &control["witnesses"][0];
    let input = witness["name"].as_str().expect("witness name").to_owned();
    let operation = witness["operation"]
        .as_str()
        .expect("witness operation")
        .to_owned();
    let capability = witness["capability"]
        .as_str()
        .expect("witness capability")
        .to_owned();
    let argument_schema = witness["parameters"]
        .as_array()
        .expect("witness parameters")
        .iter()
        .map(|parameter| {
            (
                parameter["name"].as_str().unwrap().to_owned(),
                parameter["type"].as_str().unwrap().to_owned(),
            )
        })
        .collect();
    let result_schema = witness["resultType"]
        .as_str()
        .expect("witness result type")
        .to_owned();

    Context {
        protocol_version: 1,
        namespace: "noctium".into(),
        base_revision: "r0".into(),
        attempt_id: attempt_id.into(),
        capabilities: vec![
            Capability {
                id: capability.clone(),
                namespace: "noctium".into(),
                key_prefix: "lookup/".into(),
                operations: vec![operation.clone()],
            },
            Capability {
                id: "commit".into(),
                namespace: "noctium".into(),
                key_prefix: "claims/".into(),
                operations: vec![host::CAS.into()],
            },
        ],
        operations: vec![Operation {
            operation: operation.clone(),
            argument_schema,
            result_schema,
        }],
        providers: vec![Provider {
            input,
            operation,
            capability,
            arguments: BTreeMap::new(),
        }],
        commit_capability: "commit".into(),
        limits: Limits {
            requests,
            ..Limits::default()
        },
    }
}

fn session(control: &Json, attempt_id: &str) -> Result<Session> {
    session_with_budget(control, attempt_id, REQUEST_BUDGET)
}

fn session_with_budget(control: &Json, attempt_id: &str, requests: usize) -> Result<Session> {
    let binding = binding(control);
    let pin = hex::encode(Sha256::digest(
        control["binding"]
            .as_str()
            .expect("binding string")
            .as_bytes(),
    ));
    let entrypoint = binding["target"]["entrypoint"]
        .as_str()
        .expect("target entrypoint")
        .to_owned();
    Ok(Session::from_json_with_invocation_target(
        control.clone(),
        BTreeMap::new(),
        context(control, attempt_id, requests),
        Some(&pin),
        Some(InvocationTarget {
            contract_address: "a".repeat(64),
            entrypoint,
        }),
    )?)
}

fn reply(request: &Json, attempt_id: &str, outcome: &str) -> TypedResponse {
    let mut response = json!({
        "protocolVersion":2,
        "requestId":request["requestId"],
        "attemptId":attempt_id,
        "outcome":outcome,
        "operation":request["operation"],
        "capability":request["capability"],
        "schema":request["schema"],
    });
    if outcome == "value" {
        response["value"] = json!({"kind":"unit"});
    } else {
        response["error"] = json!({"code":"provider_failed"});
    }
    serde_json::from_value(response).unwrap()
}

fn callback_index(session: &mut Session, request: &Json, expected: u32) {
    assert_eq!(request["name"], "visit");
    assert_eq!(request["schema"], "Unit");
    assert_eq!(
        request["arguments"],
        json!([{"name":"index","type":"Native"}])
    );
    assert_eq!(
        session.private_request().unwrap()["arguments"],
        json!({"index":expected.to_string()})
    );
}

#[test]
#[ignore = "requires fresh FlatWitnessRange artifacts in NOCTIUM_FLAT_WITNESS_RANGE_DIR"]
fn flat_witness_range_replays_every_provider_in_order_and_stops_on_failure() -> Result<()> {
    let root = artifact_root();
    let control: Json = serde_json::from_slice(&fs::read(
        root.join(format!("{STEM}.witness.control.json")),
    )?)?;
    assert_eq!(control["mode"], "native");
    assert_eq!(control["kind"], "host-control");
    assert_eq!(control["witnesses"].as_array().unwrap().len(), 1);
    assert_eq!(control["witnesses"][0]["name"], "visit");
    assert_eq!(
        control["witnesses"][0]["parameters"],
        json!([{"name":"index","type":"Native"}])
    );
    assert_eq!(control["witnesses"][0]["resultType"], "Unit");
    assert!(control["inputs"].as_array().unwrap().is_empty());
    assert_eq!(Limits::default().requests, 64);

    let plan: Plan = serde_json::from_slice(&fs::read(root.join(format!("{STEM}.impact.json")))?)?;
    let circuit = IrSource::load(fs::File::open(root.join(format!("{STEM}.zkir")))?)?;
    let attempt = "c".repeat(64);
    assert!(session_with_budget(&control, &attempt, REQUEST_BUDGET + 1).is_err());
    let mut accepted = session(&control, &attempt)?;
    let mut seen = Vec::with_capacity((RANGE_END + 1) as usize);
    loop {
        let status = accepted.advance()?;
        if status["status"] == "completed" {
            assert_eq!(status["result"], "0");
            break;
        }
        assert_eq!(status["status"], "need_host", "{status}");
        let request = status["request"].clone();
        let expected = seen.len() as u32;
        callback_index(&mut accepted, &request, expected);
        seen.push(expected);
        accepted.resume_typed(reply(&request, &attempt, "value"))?;
    }
    assert_eq!(seen, (0..=RANGE_END).collect::<Vec<_>>());

    let completion = accepted.private_completion(&binding(&control)["nativeRelation"])?;
    let native_inputs = serde_json::from_value(completion["inputs"].clone())?;
    let state = create_state(&plan, &BTreeMap::new())?;
    let execution = prepare(
        &plan,
        &native_inputs,
        &state,
        &ledger::structure::INITIAL_PARAMETERS,
        ContractAddress::default(),
    )?;
    assert_eq!(check(&execution, &circuit)?, execution.activity_schedule);
    assert_eq!(
        execution.returns_json(),
        BTreeMap::from([("result".into(), json!("0"))])
    );

    let mut failed = session(&control, &attempt)?;
    let mut failure_log = Vec::new();
    loop {
        let status = failed.advance()?;
        assert_eq!(
            status["status"], "need_host",
            "failure callback was not reached"
        );
        let request = status["request"].clone();
        let expected = failure_log.len() as u32;
        callback_index(&mut failed, &request, expected);
        failure_log.push(expected);
        if expected == FAILURE_AFTER {
            assert_eq!(
                failed.resume_typed(reply(&request, &attempt, "error"))?["status"],
                "failed"
            );
            break;
        }
        failed.resume_typed(reply(&request, &attempt, "value"))?;
    }
    assert_eq!(failure_log, (0..=FAILURE_AFTER).collect::<Vec<_>>());
    assert_eq!(failed.advance()?["status"], "failed");
    Ok(())
}
