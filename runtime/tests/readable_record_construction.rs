#![cfg(feature = "zkir-321")]

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

const SOURCE_NAMESPACE: &str = "ReadableRecordConstruction";

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
    for (name, result_type) in [
        ("observeActive", "Bool"),
        ("observeCount", "UIntRange<256>"),
        ("observeReading", "Native"),
    ] {
        let name = format!("{SOURCE_NAMESPACE}.{name}");
        let operation = format!("noctium.witness.{name}.v1");
        operations.push(Operation {
            operation: operation.clone(),
            argument_schema: BTreeMap::from([("marker".into(), "Native".into())]),
            result_schema: result_type.into(),
        });
        providers.push(Provider {
            input: name.clone(),
            operation: operation.clone(),
            capability: name.clone(),
            arguments: BTreeMap::new(),
        });
        capabilities.push(capability(&name, operation));
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

fn session(control: &Json, attempt_id: &str) -> anyhow::Result<Session> {
    let binding = control["binding"]
        .as_str()
        .expect("embedded witness binding");
    let digest = hex::encode(Sha256::digest(binding.as_bytes()));
    Ok(Session::from_json_with_invocation_target(
        control.clone(),
        BTreeMap::from([("seed".into(), json!("7"))]),
        source_context(attempt_id),
        Some(&digest),
        Some(InvocationTarget {
            contract_address: "a".repeat(64),
            entrypoint: "build".into(),
        }),
    )?)
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
#[ignore = "requires fresh ReadableRecordConstruction outputs in NOCTIUM_RECORD_CONSTRUCTION_DIR"]
fn readable_record_construction_preserves_provider_order_and_field_order() -> anyhow::Result<()> {
    let directory = PathBuf::from(
        std::env::var_os("NOCTIUM_RECORD_CONSTRUCTION_DIR")
            .expect("NOCTIUM_RECORD_CONSTRUCTION_DIR"),
    );
    let stem = "ReadableRecordConstruction.build";
    let binding: Json =
        serde_json::from_slice(&fs::read(directory.join(format!("{stem}.witness.json")))?)?;
    let control: Json = serde_json::from_slice(&fs::read(
        directory.join(format!("{stem}.witness.control.json")),
    )?)?;
    assert_eq!(
        serde_json::from_str::<Json>(control["binding"].as_str().unwrap())?,
        binding
    );

    let attempt = "5".repeat(64);
    let mut session = session(&control, &attempt)?;
    for (name, marker, value) in [
        ("observeReading", "10", json!("9")),
        ("observeCount", "9", json!("17")),
        ("observeActive", "8", json!(true)),
    ] {
        let pending = session.advance()?;
        assert_eq!(pending["status"], "need_host");
        assert_eq!(
            pending["request"]["name"],
            format!("{SOURCE_NAMESPACE}.{name}")
        );
        assert_eq!(session.private_request()?["arguments"]["marker"], marker);
        if name == "observeCount" {
            let overflow = reply(&pending["request"], &attempt, json!("256"));
            assert!(session.resume_typed(overflow).is_err());
            assert_eq!(session.advance()?, pending);
        }
        session.resume_typed(reply(&pending["request"], &attempt, value))?;
    }
    let completed = session.advance()?;
    assert_eq!(completed["status"], "completed");

    let expected = json!({
        "kind":"struct",
        "id":"ReadableRecordConstruction.Reading",
        "fields":[
            {"name":"reading","value":{"kind":"native","value":"9"}},
            {"name":"count","value":{"kind":"uint","maximum":"255","value":"17"}},
            {"name":"active","value":{"kind":"bool","value":true}}
        ]
    });
    assert_eq!(completed["result"], expected);
    let completion = session.private_completion(&binding["nativeRelation"])?;
    let inputs: BTreeMap<String, Json> = serde_json::from_value(completion["inputs"].clone())?;

    let plan: Plan =
        serde_json::from_slice(&fs::read(directory.join(format!("{stem}.impact.json")))?)?;
    let circuit = IrSource::load(fs::File::open(directory.join(format!("{stem}.zkir")))?)?;
    let initial = create_state(&plan, &BTreeMap::new())?;
    let execution = prepare(
        &plan,
        &inputs,
        &initial,
        &ledger::structure::INITIAL_PARAMETERS,
        ContractAddress::default(),
    )?;
    assert_eq!(check(&execution, &circuit)?, execution.activity_schedule);
    let returns = execution.returns_json();
    assert_eq!(returns.len(), 1);
    assert_eq!(returns.get("result"), Some(&expected));
    Ok(())
}
