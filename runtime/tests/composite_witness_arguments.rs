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
use transient_crypto::curve::Fr;

const LIMITS_FINGERPRINT: &str = "NoctiumCompositeTypeV1;r32:CompositeWitnessArguments.LimitsNoctiumCompositeLayoutV1;1;R32:CompositeWitnessArguments.Limits3;f5:countsU255;f7:enabledsBf4:memob4;0;";

fn callback_context(control: &Json, attempt_id: &str) -> Context {
    let witness = &control["witnesses"][0];
    let input = witness["name"].as_str().expect("callback name").to_owned();
    let operation = witness["operation"]
        .as_str()
        .expect("callback operation")
        .to_owned();
    let capability = witness["capability"]
        .as_str()
        .expect("callback capability")
        .to_owned();
    let argument_schema = witness["parameters"]
        .as_array()
        .expect("callback parameters")
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
        .expect("callback result type")
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
        limits: Limits::default(),
    }
}

fn typed_reply(request: &Json, attempt_id: &str, value: Json) -> Result<TypedResponse> {
    Ok(serde_json::from_value(json!({
        "protocolVersion": 2,
        "requestId": request["requestId"],
        "attemptId": attempt_id,
        "outcome": "value",
        "operation": request["operation"],
        "capability": request["capability"],
        "schema": request["schema"],
        "value": value,
    }))?)
}

fn limits_payload() -> Json {
    json!({
        "kind":"struct",
        "id":"CompositeWitnessArguments.Limits",
        "fields":[
            {"name":"count","value":{"kind":"uint","maximum":"255","value":"17"}},
            {"name":"enabled","value":{"kind":"bool","value":true}},
            {"name":"memo","value":{"kind":"bytes","values":[0,1,2,255]}}
        ]
    })
}

#[test]
#[ignore = "requires fresh artifacts in NOCTIUM_COMPOSITE_WITNESS_ARGUMENTS_DIR"]
fn composite_callback_arguments_preserve_order_and_bind_native_completion() -> Result<()> {
    let directory = PathBuf::from(
        std::env::var_os("NOCTIUM_COMPOSITE_WITNESS_ARGUMENTS_DIR")
            .expect("NOCTIUM_COMPOSITE_WITNESS_ARGUMENTS_DIR"),
    );
    let stem = "CompositeWitnessArguments.inspectLimits";
    let control: Json = serde_json::from_slice(&fs::read(
        directory.join(format!("{stem}.witness.control.json")),
    )?)?;
    let binding: Json = serde_json::from_str(control["binding"].as_str().expect("binding"))?;
    assert_eq!(control["types"].as_array().unwrap().len(), 1);
    assert_eq!(control["types"][0]["id"], "t0");
    assert_eq!(
        control["types"][0]["schema"]["typeFingerprint"],
        LIMITS_FINGERPRINT
    );
    assert_eq!(
        control["witnesses"][0]["parameters"],
        json!([
            {"name":"payload","type":"Aggregate:t0"},
            {"name":"amount","type":"UIntRange<256>"}
        ])
    );
    assert_eq!(control["witnesses"][0]["resultType"], "Bool");
    assert_eq!(control["inputs"].as_array().unwrap().len(), 2);
    assert_eq!(control["inputs"][0]["name"], "payload");
    assert_eq!(control["inputs"][1]["name"], "amount");
    assert!(
        control["inputs"]
            .as_array()
            .unwrap()
            .iter()
            .all(|input| { input["visibility"] == "public" })
    );

    let attempt_id = "c".repeat(64);
    let digest = hex::encode(Sha256::digest(
        control["binding"].as_str().unwrap().as_bytes(),
    ));
    let target = binding["target"]["entrypoint"]
        .as_str()
        .expect("witness circuit entrypoint")
        .to_owned();
    let mut session = Session::from_json_with_invocation_target(
        control.clone(),
        BTreeMap::from([
            ("payload".into(), limits_payload()),
            ("amount".into(), json!("5")),
        ]),
        callback_context(&control, &attempt_id),
        Some(&digest),
        Some(InvocationTarget {
            contract_address: "a".repeat(64),
            entrypoint: target,
        }),
    )?;

    let pending = session.advance()?;
    assert_eq!(pending["status"], "need_host");
    let request = pending["request"].clone();
    assert_eq!(request["name"], control["witnesses"][0]["name"]);
    assert_eq!(request["operation"], control["witnesses"][0]["operation"]);
    assert_eq!(request["schema"], "Bool");
    assert_eq!(
        request["arguments"],
        json!([
            {"name":"payload","type":"Aggregate:t0"},
            {"name":"amount","type":"UIntRange<256>"}
        ])
    );
    let private = session.private_request()?;
    assert_eq!(
        private["arguments"],
        json!({"payload":limits_payload(),"amount":"5"})
    );

    assert!(
        session
            .resume_typed(typed_reply(&request, &attempt_id, json!("true"))?)
            .is_err()
    );
    assert_eq!(session.advance()?, pending);
    session.resume_typed(typed_reply(&request, &attempt_id, json!(true))?)?;
    assert_eq!(session.advance()?["status"], "completed");

    let completion = session.private_completion(&binding["nativeRelation"])?;
    let native_inputs: BTreeMap<String, Json> =
        serde_json::from_value(completion["inputs"].clone())?;
    let plan: Plan =
        serde_json::from_slice(&fs::read(directory.join(format!("{stem}.impact.json")))?)?;
    let circuit = IrSource::load(fs::File::open(directory.join(format!("{stem}.zkir")))?)?;
    assert_eq!(
        plan.circuit
            .inputs
            .iter()
            .filter(|input| input.visibility == "public")
            .map(|input| input.name.as_str())
            .collect::<Vec<_>>(),
        [
            "amount",
            "payload.count",
            "payload.enabled",
            "payload.memo.0",
            "payload.memo.1",
            "payload.memo.2",
            "payload.memo.3",
        ]
    );
    let state = create_state(&plan, &BTreeMap::new())?;
    let execution = prepare(
        &plan,
        &native_inputs,
        &state,
        &ledger::structure::INITIAL_PARAMETERS,
        ContractAddress::default(),
    )?;
    check(&execution, &circuit)?;
    assert_eq!(
        execution.preimage.public_transcript_outputs,
        [5u64, 17, 1, 0, 1, 2, 255].map(Fr::from)
    );
    assert_eq!(execution.returns_json()["acceptedResult"], json!(true));
    Ok(())
}
