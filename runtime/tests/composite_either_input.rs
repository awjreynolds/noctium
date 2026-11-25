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

fn wire_session(control: &Json, entrypoint: &str, value: Json) -> Result<Session> {
    let binding_text = control["binding"].as_str().expect("witness binding");
    let pin = hex::encode(Sha256::digest(binding_text.as_bytes()));
    Session::from_json_with_invocation_target(
        control.clone(),
        BTreeMap::from([("value".into(), value)]),
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
            entrypoint: entrypoint.into(),
        }),
    )
}

fn limits(count: &str, enabled: bool, memo: &[u8]) -> Json {
    json!({
        "kind":"struct",
        "id":"CompositeEitherInput.Limits",
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
#[ignore = "requires fresh artifacts in NOCTIUM_COMPOSITE_EITHER_INPUT_DIR"]
fn readable_composite_either_input_preserves_both_arms_and_discloses_tag() -> Result<()> {
    let directory = PathBuf::from(
        std::env::var_os("NOCTIUM_COMPOSITE_EITHER_INPUT_DIR")
            .expect("NOCTIUM_COMPOSITE_EITHER_INPUT_DIR"),
    );
    let name = "CompositeEitherInput.echo";
    let control: Json = serde_json::from_slice(&fs::read(
        directory.join(format!("{name}.witness.control.json")),
    )?)?;
    let binding: Json = serde_json::from_str(control["binding"].as_str().expect("binding"))?;
    assert_eq!(control["inputs"].as_array().unwrap().len(), 1);
    assert_eq!(control["inputs"][0]["name"], "value");
    assert_eq!(control["inputs"][0]["visibility"], "public");
    assert_eq!(binding["target"]["entrypoint"], "echo");

    let plan: Plan =
        serde_json::from_slice(&fs::read(directory.join(format!("{name}.impact.json")))?)?;
    let circuit = IrSource::load(fs::File::open(directory.join(format!("{name}.zkir")))?)?;
    let either_id = view_id(&plan, "echoed");
    assert_eq!(either_id, "CompositeEitherInput.LimitsOrBoolPair");
    assert_eq!(
        plan.circuit
            .inputs
            .iter()
            .map(|input| input.name.as_str())
            .collect::<Vec<_>>(),
        [
            "value.is_left",
            "value.left.count",
            "value.left.enabled",
            "value.left.memo.0",
            "value.left.memo.1",
            "value.left.memo.2",
            "value.left.memo.3",
            "value.right.0",
            "value.right.1",
        ]
    );

    let initial = create_state(&plan, &BTreeMap::from([("seen".into(), json!(false))]))?;
    let params = &ledger::structure::INITIAL_PARAMETERS;
    let address = ContractAddress::default();
    let left = limits("17", true, &[0, 1, 2, 255]);
    let right = bool_vector(&[true, true]);

    for is_left in [true, false] {
        let source_value = either(&either_id, is_left, left.clone(), right.clone());
        let mut session = wire_session(&control, "echo", source_value)?;
        assert_eq!(session.advance()?["status"], "completed");
        let completion = session.private_completion(&binding["nativeRelation"])?;
        let inputs: BTreeMap<String, Json> = serde_json::from_value(completion["inputs"].clone())?;
        let execution = prepare(&plan, &inputs, &initial, params, address)?;
        check(&execution, &circuit)?;
        assert_eq!(
            execution.preimage.public_transcript_outputs,
            [u64::from(is_left), 17, 1, 0, 1, 2, 255, 1, 1].map(Fr::from)
        );
        assert_eq!(
            execution.returns_json(),
            BTreeMap::from([(
                "echoed".into(),
                either(&either_id, is_left, left.clone(), right.clone()),
            )])
        );
        let expected_after =
            create_state(&plan, &BTreeMap::from([("seen".into(), json!(is_left))]))?;
        assert_eq!(execution.after.state.get_ref(), expected_after.get_ref());
    }

    let mut malformed_tag = either(&either_id, false, left.clone(), right.clone());
    malformed_tag["fields"][0]["value"]["value"] = json!("false");
    assert!(wire_session(&control, "echo", malformed_tag).is_err());
    let malformed_arm = either(&either_id, false, left, bool_vector(&[true]));
    assert!(wire_session(&control, "echo", malformed_arm).is_err());
    Ok(())
}

#[test]
#[ignore = "requires fresh artifacts in NOCTIUM_COMPOSITE_EITHER_INPUT_DIR"]
fn readable_either_input_preserves_a_nested_maybe_payload() -> Result<()> {
    let directory = PathBuf::from(
        std::env::var_os("NOCTIUM_COMPOSITE_EITHER_INPUT_DIR")
            .expect("NOCTIUM_COMPOSITE_EITHER_INPUT_DIR"),
    );
    let name = "CompositeEitherInput.echoNested";
    let control: Json = serde_json::from_slice(&fs::read(
        directory.join(format!("{name}.witness.control.json")),
    )?)?;
    let binding: Json = serde_json::from_str(control["binding"].as_str().expect("binding"))?;
    assert_eq!(binding["target"]["entrypoint"], "echoNested");
    assert_eq!(control["inputs"].as_array().unwrap().len(), 1);
    assert_eq!(control["inputs"][0]["name"], "value");
    assert_eq!(control["inputs"][0]["visibility"], "public");

    let plan: Plan =
        serde_json::from_slice(&fs::read(directory.join(format!("{name}.impact.json")))?)?;
    let circuit = IrSource::load(fs::File::open(directory.join(format!("{name}.zkir")))?)?;
    let input_names = [
        "value.is_left",
        "value.left",
        "value.right.is_some",
        "value.right.value",
    ];
    assert_eq!(
        plan.circuit
            .inputs
            .iter()
            .map(|input| input.name.as_str())
            .collect::<Vec<_>>(),
        input_names
    );
    let [view] = plan.return_views.as_slice() else {
        panic!("expected one grouped Either return");
    };
    assert_eq!(view.name, "echoed");
    assert_eq!(view.fields.len(), 4);
    let layout = &view.schema["layout"];
    let inner = &layout["fields"][2]["layout"];
    assert_eq!(layout["id"], "CompositeEitherInput.BoolOrMaybeUInt8");
    assert_eq!(inner["id"], "CompositeEitherInput.MaybeUInt8");
    assert_eq!(
        layout["fields"]
            .as_array()
            .unwrap()
            .iter()
            .map(|field| field["name"].as_str().unwrap())
            .collect::<Vec<_>>(),
        ["is_left", "left", "right"]
    );
    assert_eq!(
        inner["fields"]
            .as_array()
            .unwrap()
            .iter()
            .map(|field| field["name"].as_str().unwrap())
            .collect::<Vec<_>>(),
        ["is_some", "value"]
    );
    assert_eq!(
        inner["fields"][1]["layout"]["leaf"],
        json!({"kind":"uint", "maximum":"255"})
    );

    let examples: Json = serde_json::from_str(include_str!(
        "../../tests/compact/composite-either-nested-maybe-cases.json"
    ))?;
    let typed = |row: &Json| {
        either(
            "CompositeEitherInput.BoolOrMaybeUInt8",
            row["is_left"].as_bool().unwrap(),
            json!({"kind":"bool", "value":row["left"]}),
            json!({"kind":"struct", "id":"CompositeEitherInput.MaybeUInt8", "fields":[
                {"name":"is_some", "value":{"kind":"bool", "value":row["right"]["is_some"]}},
                {"name":"value", "value":{"kind":"uint", "maximum":"255", "value":row["right"]["value"].to_string()}}
            ]}),
        )
    };
    let initial = create_state(&plan, &BTreeMap::from([("seen".into(), json!(false))]))?;
    let params = &ledger::structure::INITIAL_PARAMETERS;
    let address = ContractAddress::default();
    for row in examples["accepted"].as_array().unwrap() {
        let is_left = row["is_left"].as_bool().unwrap();
        let fields = [
            u64::from(is_left),
            u64::from(row["left"].as_bool().unwrap()),
            u64::from(row["right"]["is_some"].as_bool().unwrap()),
            row["right"]["value"].as_u64().unwrap(),
        ];
        let source_value = typed(row);
        let mut session = wire_session(&control, "echoNested", source_value.clone())?;
        assert_eq!(session.advance()?["status"], "completed");
        let completion = session.private_completion(&binding["nativeRelation"])?;
        let inputs: BTreeMap<String, Json> = serde_json::from_value(completion["inputs"].clone())?;
        assert_eq!(
            inputs,
            BTreeMap::from_iter(
                input_names
                    .into_iter()
                    .zip(fields)
                    .map(|(name, value)| (name.into(), json!(value.to_string())))
            )
        );
        let execution = prepare(&plan, &inputs, &initial, params, address)?;
        check(&execution, &circuit)?;
        assert_eq!(
            execution.preimage.public_transcript_outputs,
            fields.map(Fr::from)
        );
        assert_eq!(
            execution.returns_json(),
            BTreeMap::from([("echoed".into(), source_value)])
        );
        let expected_after =
            create_state(&plan, &BTreeMap::from([("seen".into(), json!(is_left))]))?;
        assert_eq!(execution.after.state.get_ref(), expected_after.get_ref());
    }
    for row in examples["rejected"].as_array().unwrap() {
        assert!(wire_session(&control, "echoNested", typed(row)).is_err());
    }
    Ok(())
}
