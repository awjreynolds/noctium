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
use std::{collections::BTreeMap, env, fs, path::PathBuf};

fn host_context(control: &Json, attempt_id: &str) -> Context {
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
    let result_schema = witness["resultType"]
        .as_str()
        .expect("callback result type")
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

#[test]
#[ignore = "requires fresh ReadableNominalFieldWitness outputs in NOCTIUM_NOMINAL_FIELD_WITNESS_DIR"]
fn typed_nominal_field_witness_runs_on_native_relation() -> Result<()> {
    let directory = PathBuf::from(
        env::var_os("NOCTIUM_NOMINAL_FIELD_WITNESS_DIR")
            .expect("NOCTIUM_NOMINAL_FIELD_WITNESS_DIR must point at fresh compiler outputs"),
    );
    let stem = "ReadableNominalFieldWitness.AmountWitnessContract.accept";
    let control: Json = serde_json::from_slice(&fs::read(
        directory.join(format!("{stem}.witness.control.json")),
    )?)?;
    let binding: Json = serde_json::from_str(control["binding"].as_str().expect("binding"))?;
    assert_eq!(control["witnesses"][0]["resultType"], "Native");
    assert_eq!(
        control["witnesses"][0]["parameters"],
        json!([{"name":"amount","type":"Native"}])
    );
    assert_eq!(control["inputs"][0]["name"], "prior");
    assert_eq!(control["inputs"][0]["type"], "Native");

    let attempt_id = "d".repeat(64);
    let digest = hex::encode(Sha256::digest(
        control["binding"].as_str().expect("binding").as_bytes(),
    ));
    let mut session = Session::from_json_with_invocation_target(
        control.clone(),
        BTreeMap::from([("prior".into(), json!("19"))]),
        host_context(&control, &attempt_id),
        Some(&digest),
        Some(InvocationTarget {
            contract_address: "b".repeat(64),
            entrypoint: "accept".into(),
        }),
    )?;
    let pending = session.advance()?;
    assert_eq!(pending["status"], "need_host");
    let request = pending["request"].clone();
    assert_eq!(request["schema"], "Native");
    assert_eq!(
        request["arguments"],
        json!([{"name":"amount","type":"Native"}])
    );
    assert_eq!(
        session.private_request()?["arguments"],
        json!({"amount":"19"})
    );
    session.resume_typed(typed_reply(&request, &attempt_id, json!("23"))?)?;
    assert_eq!(session.advance()?["status"], "completed");

    let completion = session.private_completion(&binding["nativeRelation"])?;
    let native_inputs: BTreeMap<String, Json> =
        serde_json::from_value(completion["inputs"].clone())?;
    let plan: Plan =
        serde_json::from_slice(&fs::read(directory.join(format!("{stem}.impact.json")))?)?;
    let circuit = IrSource::load(fs::File::open(directory.join(format!("{stem}.zkir")))?)?;
    assert_eq!(plan.circuit.inputs[0].ty, "Native");
    assert!(
        plan.circuit
            .outputs
            .iter()
            .all(|output| output.ty == "Native")
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
    assert_eq!(execution.returns_json()["returned"], json!("42"));
    Ok(())
}
