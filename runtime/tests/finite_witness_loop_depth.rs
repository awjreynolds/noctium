#![cfg(feature = "zkir-321")]

use anyhow::{Context as _, Result};
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
use std::{
    collections::{BTreeMap, BTreeSet},
    fs,
    path::PathBuf,
};
use transient_crypto::curve::Fr;

fn artifact_root() -> PathBuf {
    PathBuf::from(
        std::env::var_os("NOCTIUM_FINITE_WITNESS_LOOP_DEPTH_DIR")
            .expect("set NOCTIUM_FINITE_WITNESS_LOOP_DEPTH_DIR to fresh finite witness loop artifacts"),
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

fn session_with_budget(
    control: &Json,
    entrypoint: &str,
    attempt_id: &str,
    requests: usize,
) -> Result<Session> {
    let pin = hex::encode(Sha256::digest(
        control["binding"]
            .as_str()
            .expect("binding string")
            .as_bytes(),
    ));
    Ok(Session::from_json_with_invocation_target(
        control.clone(),
        BTreeMap::new(),
        context(control, attempt_id, requests),
        Some(&pin),
        Some(InvocationTarget {
            contract_address: "a".repeat(64),
            entrypoint: entrypoint.to_owned(),
        }),
    )?)
}

fn reply(request: &Json, attempt_id: &str, value: &str) -> TypedResponse {
    serde_json::from_value(json!({
        "protocolVersion": 2,
        "requestId": request["requestId"],
        "attemptId": attempt_id,
        "outcome": "value",
        "operation": request["operation"],
        "capability": request["capability"],
        "schema": request["schema"],
        "value": value,
    }))
    .unwrap()
}

fn check_metadata(control: &Json, plan: &Plan, count: usize) {
    assert_eq!(control["mode"], "native");
    assert_eq!(control["kind"], "host-control");
    assert_eq!(control["witnesses"].as_array().unwrap().len(), 1);
    assert_eq!(control["witnesses"][0]["name"], "visitValue");
    assert_eq!(control["witnesses"][0]["resultType"], "Native");
    assert_eq!(
        control["witnesses"][0]["parameters"],
        json!([{"name":"index","type":"UIntRange<256>"}])
    );
    assert!(control["inputs"].as_array().unwrap().is_empty());

    let binding = binding(control);
    let calls = binding["calls"].as_array().expect("binding calls");
    assert_eq!(calls.len(), count);
    for (ordinal, call) in calls.iter().enumerate() {
        assert_eq!(call["name"], "visitValue");
        assert_eq!(call["ordinal"], ordinal.to_string());
        assert_eq!(call["resultType"], "Native");
    }

    let inputs = &plan.circuit.inputs;
    assert_eq!(inputs.len(), count, "each call needs its own circuit input");
    let names: BTreeSet<_> = inputs.iter().map(|input| input.name.as_str()).collect();
    assert_eq!(names.len(), count, "witness result bindings must stay distinct");
    assert!(inputs
        .iter()
        .all(|input| input.ty == "Native" && input.visibility == "private"));
}

fn replay(
    control: &Json,
    entrypoint: &str,
    attempt_id: &str,
    count: usize,
    changed_at: Option<usize>,
) -> Result<(Session, Vec<u32>)> {
    let mut session = session_with_budget(control, entrypoint, attempt_id, count + 1)?;
    let mut seen = Vec::with_capacity(count);
    loop {
        let status = session.advance()?;
        if status["status"] == "completed" {
            assert_eq!(status["result"], "0");
            break;
        }
        assert_eq!(status["status"], "need_host", "{status}");
        let request = status["request"].clone();
        assert_eq!(request["name"], "visitValue");
        assert_eq!(request["schema"], "Native");
        assert_eq!(
            request["arguments"],
            json!([{"name":"index","type":"UIntRange<256>"}])
        );
        let expected = seen.len() as u32;
        let private = session.private_request()?;
        assert_eq!(private["arguments"]["index"], expected.to_string());
        seen.push(expected);
        let changed = changed_at == Some(expected as usize);
        let value = if changed { "1" } else { "0" };
        session.resume_typed(reply(&request, attempt_id, value))?;
        if changed {
            assert_eq!(session.advance()?["status"], "failed");
            break;
        }
    }
    let expected_count = changed_at.map_or(count, |ordinal| ordinal + 1);
    assert_eq!(seen, (0..expected_count as u32).collect::<Vec<_>>());
    Ok((session, seen))
}

#[test]
#[ignore = "requires fresh FiniteWitnessLoopDepth artifacts in NOCTIUM_FINITE_WITNESS_LOOP_DEPTH_DIR"]
fn finite_witness_loop_depth_preserves_ordered_calls_and_native_constraints() -> Result<()> {
    let root = artifact_root();
    for (entrypoint, count) in [("witnessLoop16", 16), ("witnessLoop32", 32)] {
        let stem = format!("FiniteWitnessLoopDepth.{entrypoint}");
        let control: Json = serde_json::from_slice(&fs::read(
            root.join(format!("{stem}.witness.control.json")),
        )?)?;
        let plan: Plan = serde_json::from_slice(&fs::read(root.join(format!("{stem}.impact.json")))?)?;
        let circuit = IrSource::load(fs::File::open(root.join(format!("{stem}.zkir")))?)?;
        check_metadata(&control, &plan, count);

        let attempt = format!("{:064x}", count);
        let (mut accepted, seen) = replay(&control, entrypoint, &attempt, count, None)?;
        assert_eq!(seen, (0..count as u32).collect::<Vec<_>>());
        let completion = accepted
            .private_completion(&binding(&control)["nativeRelation"])
            .context("prepare accepted native completion")?;
        let inputs = serde_json::from_value(completion["inputs"].clone())?;
        let state = create_state(&plan, &BTreeMap::new())?;
        let mut execution = prepare(
            &plan,
            &inputs,
            &state,
            &ledger::structure::INITIAL_PARAMETERS,
            ContractAddress::default(),
        )?;
        assert_eq!(check(&execution, &circuit)?, execution.activity_schedule);
        assert_eq!(execution.returns_json()["result"], "0");
        if count == 32 {
            assert_eq!(execution.preimage.private_transcript.len(), 32);
            execution.preimage.private_transcript[19] = Fr::from(1u64);
            assert!(check(&execution, &circuit).is_err());

            let attempt = "f".repeat(64);
            let (mut changed, _) = replay(&control, entrypoint, &attempt, count, Some(19))?;
            assert!(changed.private_completion(&binding(&control)["nativeRelation"]).is_err());

            let limited_attempt = "e".repeat(64);
            let mut limited = session_with_budget(&control, entrypoint, &limited_attempt, 2)?;
            for expected in 0..2 {
                let status = limited.advance()?;
                assert_eq!(status["status"], "need_host");
                let request = status["request"].clone();
                assert_eq!(limited.private_request()?["arguments"]["index"], expected.to_string());
                limited.resume_typed(reply(&request, &limited_attempt, "0"))?;
            }
            assert_eq!(limited.advance()?["status"], "failed");
        }
    }
    Ok(())
}
