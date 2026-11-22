#![cfg(feature = "zkir-321")]

use anyhow::Result;
use coin_structure::contract::ContractAddress;
use noctium_runtime::{
    Plan, check,
    control::{InvocationTarget, Session},
    create_state,
    host::{self, Capability, Context, Limits},
    prepare,
    zkir::IrSource,
};
use serde_json::{Value as Json, json};
use sha2::{Digest, Sha256};
use std::{collections::BTreeMap, fs, path::PathBuf};
use transient_crypto::curve::Fr;

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
            entrypoint: "choose".into(),
        }),
    )
}

fn limits(count: &str, enabled: bool, memo: &[u8]) -> Json {
    json!({
        "kind":"struct",
        "id":"CompositeEither.Limits",
        "fields":[
            {"name":"count","value":{"kind":"uint","maximum":"255","value":count}},
            {"name":"enabled","value":{"kind":"bool","value":enabled}},
            {"name":"memo","value":{"kind":"bytes","values":memo}}
        ]
    })
}

fn bool_vector(values: &[bool]) -> Json {
    json!({
        "kind":"vector",
        "items":values.iter().map(|value| json!({"kind":"bool","value":value})).collect::<Vec<_>>()
    })
}

fn either(id: &str, is_left: bool, left: Json, right: Json) -> Json {
    json!({
        "kind":"struct",
        "id":id,
        "fields":[
            {"name":"is_left","value":{"kind":"bool","value":is_left}},
            {"name":"left","value":left},
            {"name":"right","value":right}
        ]
    })
}

#[test]
#[ignore = "requires fresh artifacts in NOCTIUM_COMPOSITE_EITHER_DIR"]
fn readable_composite_either_input_binds_both_tags_and_zeroes_the_inactive_side() -> Result<()> {
    let directory = PathBuf::from(
        std::env::var_os("NOCTIUM_COMPOSITE_EITHER_DIR").expect("NOCTIUM_COMPOSITE_EITHER_DIR"),
    );
    let name = "CompositeEither.choose";
    let control: Json = serde_json::from_slice(&fs::read(
        directory.join(format!("{name}.witness.control.json")),
    )?)?;
    let binding: Json = serde_json::from_str(control["binding"].as_str().expect("binding"))?;
    assert_eq!(control["inputs"].as_array().unwrap().len(), 3);
    for (index, name) in ["isLeft", "leftValue", "rightValue"].iter().enumerate() {
        assert_eq!(control["inputs"][index]["name"], *name);
        assert_eq!(control["inputs"][index]["visibility"], "public");
    }

    let plan: Plan =
        serde_json::from_slice(&fs::read(directory.join(format!("{name}.impact.json")))?)?;
    let circuit = IrSource::load(fs::File::open(directory.join(format!("{name}.zkir")))?)?;
    let state = create_state(&plan, &BTreeMap::new())?;
    let either_id = view_id(&plan, "eitherValue");
    assert!(either_id.starts_with("CompositeEither.choose.EitherComposite"));

    let active_left = limits("17", true, &[0, 1, 2, 255]);
    let zero_left = limits("0", false, &[0, 0, 0, 0]);
    let active_right = bool_vector(&[true, false]);
    let zero_right = bool_vector(&[false, false]);

    for (is_left, expected_left, expected_right) in [
        (true, active_left, zero_right),
        (false, zero_left, active_right),
    ] {
        let mut session = wire_session(
            &control,
            BTreeMap::from([
                ("isLeft".into(), json!(is_left)),
                ("leftValue".into(), limits("17", true, &[0, 1, 2, 255])),
                ("rightValue".into(), bool_vector(&[true, false])),
            ]),
        )?;
        assert_eq!(session.advance()?["status"], "completed");
        let completion = session.private_completion(&binding["nativeRelation"])?;
        let inputs: BTreeMap<String, Json> = serde_json::from_value(completion["inputs"].clone())?;

        assert_eq!(
            plan.circuit
                .inputs
                .iter()
                .map(|input| input.name.as_str())
                .collect::<Vec<_>>(),
            [
                "isLeft",
                "leftValue.count",
                "leftValue.enabled",
                "leftValue.memo.0",
                "leftValue.memo.1",
                "leftValue.memo.2",
                "leftValue.memo.3",
                "rightValue.0",
                "rightValue.1",
            ]
        );
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
            [u64::from(is_left), 17, 1, 0, 1, 2, 255, 1, 0,].map(Fr::from)
        );
        assert_eq!(
            execution.returns_json(),
            BTreeMap::from([(
                "eitherValue".into(),
                either(&either_id, is_left, expected_left, expected_right),
            )])
        );
    }

    Ok(())
}
