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

const SOURCE_NAMESPACE: &str = "ReadableBindPatterns";
const PROFILE: &str = "midnight-ledger-9-zkir-3.2.1";
const PROVIDER: &str = "ReadableBindPatterns.load";

fn source_context(attempt_id: &str, result_type: &str) -> Context {
    let operation = format!("noctium.witness.{PROVIDER}.v1");
    Context {
        protocol_version: 1,
        namespace: "noctium".into(),
        base_revision: "r0".into(),
        attempt_id: attempt_id.into(),
        capabilities: vec![
            Capability {
                id: "commit".into(),
                namespace: "noctium".into(),
                key_prefix: "noctium/".into(),
                operations: vec![host::CAS.into()],
            },
            Capability {
                id: PROVIDER.into(),
                namespace: "noctium".into(),
                key_prefix: "noctium/".into(),
                operations: vec![operation.clone()],
            },
        ],
        operations: vec![Operation {
            operation: operation.clone(),
            argument_schema: BTreeMap::from([("seed".into(), "Native".into())]),
            result_schema: result_type.into(),
        }],
        providers: vec![Provider {
            input: PROVIDER.into(),
            operation,
            capability: PROVIDER.into(),
            arguments: BTreeMap::new(),
        }],
        commit_capability: "commit".into(),
        limits: Limits::default(),
    }
}

fn session(control: &Json, attempt_id: &str, result_type: &str) -> anyhow::Result<Session> {
    let binding = control["binding"]
        .as_str()
        .expect("embedded witness binding");
    let digest = hex::encode(Sha256::digest(binding.as_bytes()));
    Ok(Session::from_json_with_invocation_target(
        control.clone(),
        BTreeMap::from([("seed".into(), json!("7"))]),
        source_context(attempt_id, result_type),
        Some(&digest),
        Some(InvocationTarget {
            contract_address: "a".repeat(64),
            entrypoint: "unpack".into(),
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
#[ignore = "requires fresh ReadableBindPatterns artifacts in NOCTIUM_BIND_PATTERNS_DIR"]
fn readable_bind_patterns_unpack_one_packet_and_check_its_native_total() -> anyhow::Result<()> {
    let directory = PathBuf::from(
        std::env::var_os("NOCTIUM_BIND_PATTERNS_DIR").expect("NOCTIUM_BIND_PATTERNS_DIR"),
    );
    let stem = "ReadableBindPatterns.unpack";
    let binding: Json =
        serde_json::from_slice(&fs::read(directory.join(format!("{stem}.witness.json")))?)?;
    let control: Json = serde_json::from_slice(&fs::read(
        directory.join(format!("{stem}.witness.control.json")),
    )?)?;
    assert_eq!(
        serde_json::from_str::<Json>(control["binding"].as_str().unwrap())?,
        binding
    );
    assert_eq!(
        binding["sourceExport"],
        format!("noctium.witness-circuit.{SOURCE_NAMESPACE}.unpack.v1")
    );
    let result_type = control["witnesses"]
        .as_array()
        .expect("witness declarations")
        .iter()
        .find(|witness| witness["name"] == PROVIDER)
        .and_then(|witness| witness["resultType"].as_str())
        .expect("load aggregate result type");
    let type_id = result_type
        .strip_prefix("Aggregate:")
        .expect("load result is an aggregate");
    assert!(binding["types"].as_array().is_some_and(|types| {
        types.iter().any(|ty| {
            ty["id"] == type_id && ty["schema"]["layout"]["id"] == "ReadableBindPatterns.Packet"
        })
    }));

    let plan: Plan =
        serde_json::from_slice(&fs::read(directory.join(format!("{stem}.impact.json")))?)?;
    assert_eq!(plan.target.as_deref(), Some(PROFILE));
    assert_eq!(
        plan.target_profile
            .as_ref()
            .and_then(|profile| profile["name"].as_str()),
        Some(PROFILE)
    );
    let circuit = IrSource::load(fs::File::open(directory.join(format!("{stem}.zkir")))?)?;
    let packet = json!({
        "kind":"struct",
        "id":"ReadableBindPatterns.Packet",
        "fields":[
            {"name":"reading","value":{
                "kind":"struct",
                "id":"ReadableBindPatterns.Reading",
                "fields":[
                    {"name":"count","value":{"kind":"uint","maximum":"255","value":"17"}},
                    {"name":"active","value":{"kind":"bool","value":true}}
                ]
            }},
            {"name":"measures","value":{"kind":"tuple","items":[
                {"kind":"native","value":"9"},
                {"kind":"bool","value":false}
            ]}},
            {"name":"omitted","value":{"kind":"native","value":"5"}}
        ]
    });

    let attempt = "6".repeat(64);
    let mut session = session(&control, &attempt, result_type)?;
    let pending = session.advance()?;
    assert_eq!(pending["status"], "need_host");
    assert_eq!(pending["request"]["name"], PROVIDER);
    assert_eq!(
        pending["request"]["operation"],
        "noctium.witness.ReadableBindPatterns.load.v1"
    );
    assert_eq!(pending["request"]["schema"], result_type);
    assert_eq!(session.private_request()?["arguments"]["seed"], "7");
    session.resume_typed(reply(&pending["request"], &attempt, packet))?;
    let completed = session.advance()?;
    assert_eq!(completed["status"], "completed");
    assert_eq!(completed["result"], "26");

    let completion = session.private_completion(&binding["nativeRelation"])?;
    let inputs: BTreeMap<String, Json> = serde_json::from_value(completion["inputs"].clone())?;
    let initial = create_state(&plan, &BTreeMap::new())?;
    let execution = prepare(
        &plan,
        &inputs,
        &initial,
        &ledger::structure::INITIAL_PARAMETERS,
        ContractAddress::default(),
    )?;
    assert_eq!(check(&execution, &circuit)?, execution.activity_schedule);
    assert_eq!(execution.returns_json()["totalResult"], "26");
    Ok(())
}
