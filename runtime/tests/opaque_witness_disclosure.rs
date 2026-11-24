#![cfg(feature = "zkir-321")]

use anyhow::{ensure, Result};
use base_crypto::fab::{AlignedValue, Alignment, AlignmentAtom, Value as FabValue, ValueAtom};
use coin_structure::contract::ContractAddress;
use noctium_runtime::{check, create_state, prepare, zkir::IrSource, Plan};
use onchain_runtime::state::{ChargedState, StateValue};
use serde_json::{json, Value as Json};
use sha2::{Digest, Sha256};
use std::{collections::BTreeMap, fs, path::PathBuf};
use transient_crypto::fab::AlignedValueExt;

const LABEL: &str = "A\0夜\0B";
const NAMESPACE: &str = "opaque-witness";
const COMMIT: &str = "commit";

fn attempt() -> String {
    "a".repeat(64)
}

fn artifacts() -> PathBuf {
    PathBuf::from(
        std::env::var_os("NOCTIUM_OPAQUE_WITNESS_DIR")
            .expect("set fresh OpaqueWitnessDisclosure outputs in NOCTIUM_OPAQUE_WITNESS_DIR"),
    )
}

fn stem() -> &'static str {
    "OpaqueWitnessDisclosure.OpaqueWitnessDisclosure.publish"
}

fn binding(control: &Json) -> Json {
    serde_json::from_str(control["binding"].as_str().expect("native binding text"))
        .expect("valid native binding JSON")
}

fn context(control: &Json) -> noctium_runtime::host::Context {
    use noctium_runtime::host::{Capability, Context, Limits, Operation, Provider};

    let witness = control["witnesses"].as_array().unwrap().first().unwrap();
    let name = witness["name"].as_str().unwrap().to_owned();
    let operation = witness["operation"].as_str().unwrap().to_owned();
    let capability = witness["capability"].as_str().unwrap().to_owned();
    Context {
        protocol_version: noctium_runtime::host::PROTOCOL_VERSION,
        namespace: NAMESPACE.into(),
        base_revision: "0".repeat(64),
        attempt_id: attempt(),
        capabilities: vec![
            Capability {
                id: COMMIT.into(),
                namespace: NAMESPACE.into(),
                key_prefix: "lookup/".into(),
                operations: vec![noctium_runtime::host::CAS.into()],
            },
            Capability {
                id: capability.clone(),
                namespace: NAMESPACE.into(),
                key_prefix: "lookup/".into(),
                operations: vec![operation.clone()],
            },
        ],
        operations: vec![Operation {
            operation: operation.clone(),
            argument_schema: BTreeMap::new(),
            result_schema: "OpaqueString".into(),
        }],
        providers: vec![Provider {
            input: name,
            operation,
            capability,
            arguments: BTreeMap::new(),
        }],
        commit_capability: COMMIT.into(),
        limits: Limits::default(),
    }
}

fn response(request: &Json, value: Json) -> noctium_runtime::control::TypedResponse {
    use noctium_runtime::control::TypedResponse;
    TypedResponse {
        protocol_version: 2,
        request_id: request["requestId"].as_str().unwrap().to_owned(),
        attempt_id: attempt(),
        outcome: "value".into(),
        operation: request["operation"].as_str().unwrap().to_owned(),
        capability: request["capability"].as_str().unwrap().to_owned(),
        schema: request["schema"].as_str().unwrap().to_owned(),
        value: Some(value),
        error: None,
    }
}

fn compressed(bytes: &[u8]) -> AlignedValue {
    AlignedValue::new(
        FabValue(vec![ValueAtom::from(bytes)]),
        Alignment::singleton(AlignmentAtom::Compress),
    )
    .expect("canonical opaque string Compress value")
}

fn assert_cell(state: &ChargedState<noctium_runtime::Db>, plan: &Plan, expected: &[u8]) {
    let StateValue::Array(slots) = state.get_ref() else {
        panic!("expected root Cell state")
    };
    let slot = plan
        .state
        .iter()
        .position(|declaration| declaration.name == "label")
        .expect("label Cell declaration");
    let StateValue::Cell(value) = &*slots.get(slot).expect("label Cell slot") else {
        panic!("expected one Cell value")
    };
    assert_eq!(**value, compressed(expected));
}

#[test]
#[ignore = "requires fresh OpaqueWitnessDisclosure Lean artifacts"]
fn opaque_string_provider_is_disclosed_into_a_root_cell_and_bindings_reject_tampering() -> Result<()>
{
    let directory = artifacts();
    let control_path = directory.join(format!("{}.witness.control.json", stem()));
    let control_text = fs::read_to_string(&control_path)?;
    let control: Json = serde_json::from_str(&control_text)?;
    let plan: Plan = serde_json::from_slice(&fs::read(
        directory.join(format!("{}.impact.json", stem())),
    )?)?;
    let circuit_bytes = fs::read(directory.join(format!("{}.zkir", stem())))?;
    let circuit = IrSource::load(circuit_bytes.as_slice())?;
    let original_binding_text = control["binding"].as_str().unwrap();
    let expected_binding_hash = hex::encode(Sha256::digest(original_binding_text.as_bytes()));
    let target = noctium_runtime::control::InvocationTarget {
        contract_address: "00".repeat(32),
        entrypoint: "publish".into(),
    };

    let mut altered = control.clone();
    let mut changed_binding = binding(&control);
    changed_binding["calls"][0]["resultType"] = json!("OpaqueBytes");
    altered["binding"] = json!(changed_binding.to_string());
    let altered_session = noctium_runtime::control::Session::from_json_with_invocation_target(
        altered,
        BTreeMap::new(),
        context(&control),
        Some(&expected_binding_hash),
        Some(target.clone()),
    );
    assert!(
        altered_session.is_err(),
        "altered OpaqueString binding was accepted"
    );

    let mut session = noctium_runtime::control::Session::from_json_with_invocation_target(
        control,
        BTreeMap::new(),
        context(&serde_json::from_str(&control_text)?),
        Some(&expected_binding_hash),
        Some(target),
    )?;
    let pending = session.advance()?;
    ensure!(
        pending["status"] == "need_host",
        "expected provider request: {pending}"
    );
    ensure!(
        pending["request"]["schema"] == "OpaqueString",
        "wrong provider schema: {pending}"
    );
    let wrong_reply = response(
        &pending["request"],
        json!({"kind":"opaqueBytes", "values":[1]}),
    );
    assert!(
        session.resume_typed(wrong_reply).is_err(),
        "wrong OpaqueString reply type was accepted"
    );
    assert_eq!(
        session.advance()?,
        pending,
        "bad reply must leave request pending"
    );
    session.resume_typed(response(
        &pending["request"],
        json!({"kind":"opaqueString", "value":LABEL}),
    ))?;
    ensure!(
        session.advance()?["status"] == "completed",
        "provider did not complete"
    );

    let native_binding = binding(&serde_json::from_str(&control_text)?);
    let completion = session.private_completion(&native_binding["nativeRelation"])?;
    let inputs = serde_json::from_value(completion["inputs"].clone())?;
    let state = create_state(
        &plan,
        &BTreeMap::from([("label".into(), json!({"kind":"opaqueString", "value":""}))]),
    )?;
    assert_cell(&state, &plan, b"");
    let execution = prepare(
        &plan,
        &inputs,
        &state,
        &ledger::structure::INITIAL_PARAMETERS,
        ContractAddress::default(),
    )?;
    check(&execution, &circuit)?;
    assert_cell(&execution.after.state, &plan, LABEL.as_bytes());
    let mut expected_projection = Vec::new();
    compressed(LABEL.as_bytes()).value_only_field_repr(&mut expected_projection);
    assert_eq!(expected_projection.len(), 1);
    assert_eq!(
        execution
            .preimage
            .public_transcript_inputs
            .iter()
            .filter(|value| **value == expected_projection[0])
            .count(),
        1,
        "disclosed Cell write did not bind the Compress projection"
    );
    Ok(())
}
