#![cfg(feature = "zkir-321")]

use anyhow::Result;
use coin_structure::contract::ContractAddress;
use noctium_runtime::{
    Expr, Plan, check,
    control::{InvocationTarget, Session},
    create_state,
    host::{self, Capability, Context, Limits},
    prepare,
    zkir::IrSource,
};
use serde_json::{Value as Json, json};
use sha2::{Digest, Sha256};
use std::{collections::BTreeMap, fs, path::PathBuf};

fn view_id(plan: &Plan, name: &str) -> String {
    plan.return_views
        .iter()
        .find(|view| view.name == name)
        .and_then(|view| view.schema.get("layout"))
        .and_then(|layout| layout.get("id"))
        .and_then(Json::as_str)
        .unwrap_or_else(|| panic!("{name} nominal return id"))
        .to_owned()
}

fn wire_session(control: &Json, inputs: BTreeMap<String, Json>) -> Result<Session> {
    let binding_text = control["binding"].as_str().expect("witness binding");
    let pin = hex::encode(Sha256::digest(binding_text.as_bytes()));
    Session::from_json_with_invocation_target(
        control.clone(),
        inputs,
        Context {
            protocol_version: 1,
            namespace: "noctium".into(),
            base_revision: "r0".into(),
            attempt_id: "b".repeat(64),
            capabilities: vec![Capability {
                id: "commit".into(),
                namespace: "noctium".into(),
                key_prefix: "noctium/".into(),
                operations: vec![host::CAS.into()],
            }],
            operations: vec![],
            providers: vec![],
            commit_capability: "commit".into(),
            limits: Limits::default(),
        },
        Some(&pin),
        Some(InvocationTarget {
            contract_address: "a".repeat(64),
            entrypoint: "options".into(),
        }),
    )
}

fn limits(count: &str, enabled: bool, memo: &[u8]) -> Json {
    json!({
        "kind":"struct",
        "id":"CompositeMaybe.Limits",
        "fields":[
            {"name":"count","value":{"kind":"uint","maximum":"255","value":count}},
            {"name":"enabled","value":{"kind":"bool","value":enabled}},
            {"name":"memo","value":{"kind":"bytes","values":memo}}
        ]
    })
}

fn maybe(id: &str, is_some: bool, value: Json) -> Json {
    json!({
        "kind":"struct",
        "id":id,
        "fields":[
            {"name":"is_some","value":{"kind":"bool","value":is_some}},
            {"name":"value","value":value}
        ]
    })
}

#[test]
#[ignore = "requires fresh artifacts in NOCTIUM_COMPOSITE_MAYBE_DIR"]
fn readable_composite_maybe_input_binds_present_and_absent_payloads() -> Result<()> {
    let directory = PathBuf::from(
        std::env::var_os("NOCTIUM_COMPOSITE_MAYBE_DIR").expect("NOCTIUM_COMPOSITE_MAYBE_DIR"),
    );
    let name = "CompositeMaybe.options";
    let control: Json = serde_json::from_slice(&fs::read(
        directory.join(format!("{name}.witness.control.json")),
    )?)?;
    let binding: Json = serde_json::from_str(control["binding"].as_str().expect("binding"))?;
    assert_eq!(control["inputs"].as_array().unwrap().len(), 1);
    assert_eq!(control["inputs"][0]["name"], "value");
    assert_eq!(control["inputs"][0]["visibility"], "public");
    let sample = limits("17", true, &[0, 1, 2, 255]);
    let mut session = wire_session(&control, BTreeMap::from([("value".into(), sample)]))?;
    assert_eq!(session.advance()?["status"], "completed");
    let completion = session.private_completion(&binding["nativeRelation"])?;
    let inputs: BTreeMap<String, Json> = serde_json::from_value(completion["inputs"].clone())?;

    let mut plan: Plan =
        serde_json::from_slice(&fs::read(directory.join(format!("{name}.impact.json")))?)?;
    let circuit = IrSource::load(fs::File::open(directory.join(format!("{name}.zkir")))?)?;
    assert_eq!(
        plan.circuit
            .inputs
            .iter()
            .map(|input| input.name.as_str())
            .collect::<Vec<_>>(),
        [
            "value.count",
            "value.enabled",
            "value.memo.0",
            "value.memo.1",
            "value.memo.2",
            "value.memo.3",
        ]
    );
    let state = create_state(&plan, &BTreeMap::new())?;
    let maybe_id = view_id(&plan, "presentValue");
    assert!(maybe_id.starts_with("CompositeMaybe.options.MaybeComposite"));
    assert_eq!(view_id(&plan, "absentValue"), maybe_id);
    let execution = prepare(
        &plan,
        &inputs,
        &state,
        &ledger::structure::INITIAL_PARAMETERS,
        ContractAddress::default(),
    )?;
    check(&execution, &circuit)?;
    assert_eq!(
        execution.preimage.public_transcript_outputs,
        [17u64, 1, 0, 1, 2, 255].map(transient_crypto::curve::Fr::from)
    );
    let present = maybe(&maybe_id, true, limits("17", true, &[0, 1, 2, 255]));
    let absent = maybe(&maybe_id, false, limits("0", false, &[0, 0, 0, 0]));
    assert_eq!(
        execution.returns_json(),
        BTreeMap::from([
            ("presentValue".into(), present),
            ("absentValue".into(), absent),
        ])
    );
    let (original_commitment, _) = execution.preimage.communications_commitment.unwrap();

    let count_name = plan
        .return_views
        .iter()
        .find(|view| view.name == "presentValue")
        .and_then(|view| view.fields.get(1))
        .expect("presentValue payload count output")
        .clone();
    let count_output = plan
        .returns
        .iter_mut()
        .find(|output| output.name == count_name)
        .expect("presentValue count output");
    count_output.expression = Expr::Constant { value: "18".into() };
    let changed = prepare(
        &plan,
        &inputs,
        &state,
        &ledger::structure::INITIAL_PARAMETERS,
        ContractAddress::default(),
    )?;
    let (changed_commitment, _) = changed.preimage.communications_commitment.unwrap();
    assert_ne!(changed_commitment, original_commitment);
    assert!(check(&changed, &circuit).is_err());
    Ok(())
}
