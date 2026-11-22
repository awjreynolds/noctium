#![cfg(feature = "zkir-321")]

use noctium_runtime::{
    control::{InvocationTarget, Session, TypedResponse},
    host::{self, Capability, Context, Limits, Operation, Provider},
};
use serde_json::{Value as Json, json};
use sha2::{Digest, Sha256};
use std::{collections::BTreeMap, fs, path::PathBuf};

fn source_context(attempt_id: &str) -> Context {
    let mut operations = Vec::new();
    let mut providers = Vec::new();
    let capability = |id: &str, operation: String| Capability {
        id: id.into(),
        namespace: "noctium".into(),
        key_prefix: "noctium/".into(),
        operations: vec![operation],
    };
    let mut capabilities = vec![capability("commit", host::CAS.into())];
    for (name, result_type) in [("unitObserve", "Unit"), ("unitFinish", "Native")] {
        let operation = format!("noctium.witness.{name}.v1");
        operations.push(Operation {
            operation: operation.clone(),
            argument_schema: BTreeMap::from([("value".into(), "Native".into())]),
            result_schema: result_type.into(),
        });
        providers.push(Provider {
            input: name.into(),
            operation: operation.clone(),
            capability: name.into(),
            arguments: BTreeMap::new(),
        });
        capabilities.push(capability(name, operation));
    }
    Context {
        protocol_version: 1,
        namespace: "noctium".into(),
        base_revision: "r0".into(),
        attempt_id: attempt_id.into(),
        capabilities,
        operations,
        providers,
        commit_capability: "commit".into(),
        limits: Limits::default(),
    }
}

fn session(control: &Json, attempt: &str) -> Session {
    let binding = control["binding"]
        .as_str()
        .expect("embedded witness binding");
    let digest = hex::encode(Sha256::digest(binding.as_bytes()));
    Session::from_json_with_invocation_target(
        control.clone(),
        BTreeMap::from([("seed".into(), json!("7"))]),
        source_context(attempt),
        Some(&digest),
        Some(InvocationTarget {
            contract_address: "a".repeat(64),
            entrypoint: "update".into(),
        }),
    )
    .expect("readable unit binding session starts")
}

fn reply(request: &Json, attempt_id: &str, value: Json) -> TypedResponse {
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
    .expect("typed host response")
}

#[test]
#[ignore = "requires fresh ReadableUnitBindings outputs in NOCTIUM_UNIT_BINDINGS_DIR"]
fn readable_unit_bindings_keep_expression_lets_and_order_host_calls() -> anyhow::Result<()> {
    let directory = PathBuf::from(
        std::env::var_os("NOCTIUM_UNIT_BINDINGS_DIR").expect("NOCTIUM_UNIT_BINDINGS_DIR"),
    );
    let stem = "ReadableUnitBindings.update";
    let binding: Json =
        serde_json::from_slice(&fs::read(directory.join(format!("{stem}.witness.json")))?)?;
    let control: Json = serde_json::from_slice(&fs::read(
        directory.join(format!("{stem}.witness.control.json")),
    )?)?;
    assert_eq!(
        serde_json::from_str::<Json>(control["binding"].as_str().unwrap())?,
        binding
    );

    let attempt = "4".repeat(64);
    let mut execution = session(&control, &attempt);
    let pending = execution.advance()?;
    assert_eq!(pending["status"], "need_host");
    assert_eq!(pending["request"]["name"], "unitObserve");
    let wrong_unit_frame = reply(
        &pending["request"],
        &attempt,
        json!({"kind":"native","value":"7"}),
    );
    assert!(execution.resume_typed(wrong_unit_frame).is_err());
    assert_eq!(
        execution.advance()?,
        pending,
        "malformed Unit reply leaves the same provider pending"
    );

    let unit = json!({"kind":"unit"});
    for (name, argument, value) in [
        ("unitObserve", "7", unit.clone()),
        ("unitObserve", "8", unit),
        ("unitFinish", "9", json!("10")),
    ] {
        let pending = execution.advance()?;
        assert_eq!(pending["status"], "need_host");
        assert_eq!(pending["request"]["name"], name);
        assert_eq!(execution.private_request()?["arguments"]["value"], argument);
        execution.resume_typed(reply(&pending["request"], &attempt, value))?;
    }
    assert_eq!(execution.advance()?["status"], "completed");
    let completion = execution.private_completion(&binding["nativeRelation"])?;
    let inputs: BTreeMap<String, Json> = serde_json::from_value(completion["inputs"].clone())?;
    assert_eq!(
        inputs.len(),
        2,
        "only seed and the Native reply occupy fields"
    );
    let plan: noctium_runtime::Plan = serde_json::from_reader(fs::File::open(
        directory.join(format!("{stem}.impact.json")),
    )?)?;
    let circuit = noctium_runtime::zkir::IrSource::load(fs::File::open(
        directory.join(format!("{stem}.zkir")),
    )?)?;
    let initial = noctium_runtime::create_state(&plan, &BTreeMap::new())?;
    let execution = noctium_runtime::prepare(
        &plan,
        &inputs,
        &initial,
        &ledger::structure::INITIAL_PARAMETERS,
        coin_structure::contract::ContractAddress::default(),
    )?;
    noctium_runtime::check(&execution, &circuit)?;
    assert_eq!(execution.returns_json()["value"], "10");
    Ok(())
}
