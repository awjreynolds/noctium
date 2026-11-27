#![cfg(feature = "zkir-321")]

use noctium_runtime::{
    control::{InvocationTarget, Session, TypedResponse},
    host::{self, Capability, Context, Limits, Operation, Provider},
};
use serde_json::{Value as Json, json};
use sha2::{Digest, Sha256};
use std::{collections::BTreeMap, fs, path::PathBuf};

fn source_context(control: &Json, attempt_id: &str) -> Context {
    let mut operations = Vec::new();
    let mut providers = Vec::new();
    let capability = |id: &str, operation: String| Capability {
        id: id.into(),
        namespace: "noctium".into(),
        key_prefix: "noctium/".into(),
        operations: vec![operation],
    };
    let mut capabilities = vec![capability("commit", host::CAS.into())];
    for witness in control["witnesses"]
        .as_array()
        .expect("witness declarations")
    {
        let name = witness["name"].as_str().expect("witness name");
        let operation = witness["operation"].as_str().expect("witness operation");
        let capability_id = witness["capability"].as_str().expect("witness capability");
        let result_type = witness["resultType"].as_str().expect("witness result type");
        let argument_schema = witness["parameters"]
            .as_array()
            .expect("witness parameters")
            .iter()
            .map(|parameter| {
                (
                    parameter["name"].as_str().expect("argument name").into(),
                    parameter["type"].as_str().expect("argument type").into(),
                )
            })
            .collect();
        operations.push(Operation {
            operation: operation.into(),
            argument_schema,
            result_schema: result_type.into(),
        });
        providers.push(Provider {
            input: name.into(),
            operation: operation.into(),
            capability: capability_id.into(),
            arguments: BTreeMap::new(),
        });
        capabilities.push(capability(capability_id, operation.into()));
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

fn session(control: &Json, attempt: &str, entrypoint: &str, seed: &str) -> Session {
    let binding = control["binding"]
        .as_str()
        .expect("embedded witness binding");
    let digest = hex::encode(Sha256::digest(binding.as_bytes()));
    Session::from_json_with_invocation_target(
        control.clone(),
        BTreeMap::from([("seed".into(), json!(seed))]),
        source_context(control, attempt),
        Some(&digest),
        Some(InvocationTarget {
            contract_address: "a".repeat(64),
            entrypoint: entrypoint.into(),
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
    let mut execution = session(&control, &attempt, "update", "7");
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
        ("unitObserve", "8", unit.clone()),
        ("unitFinish", "9", json!("10")),
        ("unitObserve", "10", unit),
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
    let mut plan: noctium_runtime::Plan = serde_json::from_reader(fs::File::open(
        directory.join(format!("{stem}.impact.json")),
    )?)?;
    let circuit = noctium_runtime::zkir::IrSource::load(fs::File::open(
        directory.join(format!("{stem}.zkir")),
    )?)?;
    let initial = noctium_runtime::create_state(&plan, &BTreeMap::new())?;
    let prepare = |plan: &noctium_runtime::Plan| {
        noctium_runtime::prepare(
            plan,
            &inputs,
            &initial,
            &ledger::structure::INITIAL_PARAMETERS,
            coin_structure::contract::ContractAddress::default(),
        )
    };
    let execution = prepare(&plan)?;
    noctium_runtime::check(&execution, &circuit)?;
    assert_eq!(
        execution.returns().len(),
        3,
        "Native result and two Maybe tags"
    );
    let returns = execution.returns_json();
    assert_eq!(returns["value"], "10");
    assert_eq!(returns["presentUnit"]["id"], returns["absentUnit"]["id"]);
    for (name, tag) in [("presentUnit", true), ("absentUnit", false)] {
        assert_eq!(
            returns[name]["fields"],
            json!([
                {"name":"is_some", "value":{"kind":"bool", "value":tag}},
                {"name":"value", "value":{"kind":"unit"}},
            ])
        );
    }
    let tag = &plan
        .return_views
        .iter()
        .find(|view| view.name == "presentUnit")
        .expect("present Maybe return view")
        .fields[0];
    plan.returns
        .iter_mut()
        .find(|output| output.name == *tag)
        .expect("present Maybe tag")
        .expression = noctium_runtime::Expr::Constant { value: "0".into() };
    assert!(noctium_runtime::check(&prepare(&plan)?, &circuit).is_err());
    Ok(())
}

#[test]
#[ignore = "requires fresh ReadableUnitBindings outputs in NOCTIUM_UNIT_BINDINGS_DIR"]
fn readable_unit_witness_argument_keeps_its_logical_position() -> anyhow::Result<()> {
    let directory = PathBuf::from(std::env::var("NOCTIUM_UNIT_BINDINGS_DIR")?);
    let stem = "ReadableUnitBindings.passUnit";
    let control: Json = serde_json::from_slice(&fs::read(
        directory.join(format!("{stem}.witness.control.json")),
    )?)?;
    let binding: Json = serde_json::from_str(control["binding"].as_str().expect("binding"))?;
    let attempt = "5".repeat(64);
    let mut session = session(&control, &attempt, "passUnit", "17");
    let pending = session.advance()?;
    assert_eq!(pending["status"], "need_host");
    assert_eq!(pending["request"]["name"], "echoUnit");
    assert_eq!(
        pending["request"]["arguments"],
        json!([
            {"name":"emptyArg", "type":"Unit"},
            {"name":"seed", "type":"Native"}
        ])
    );
    assert_eq!(
        session.private_request()?["arguments"],
        json!({
            "emptyArg":{"kind":"unit"}, "seed":"17"
        })
    );
    session.resume_typed(reply(&pending["request"], &attempt, json!("22")))?;
    let completed = session.advance()?;
    assert_eq!(completed["status"], "completed");
    assert_eq!(completed["result"], "22");
    let completion = session.private_completion(&binding["nativeRelation"])?;
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
    assert_eq!(execution.preimage.private_transcript.len(), 1);
    assert_eq!(execution.returns_json()["value"], "22");
    Ok(())
}
