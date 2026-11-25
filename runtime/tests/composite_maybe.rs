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

#[test]
#[ignore = "requires fresh NestedMaybeUInt artifacts and the pinned Compact oracle"]
fn nested_maybe_uint_preserves_tags_defaults_and_result_binding() -> Result<()> {
    let directory = PathBuf::from(
        std::env::var_os("NOCTIUM_NESTED_MAYBE_UINT_DIR").expect("NOCTIUM_NESTED_MAYBE_UINT_DIR"),
    );
    let oracle_path = std::env::var_os("NOCTIUM_NESTED_MAYBE_UINT_COMPACT")
        .expect("NOCTIUM_NESTED_MAYBE_UINT_COMPACT");
    let oracle: Json = serde_json::from_slice(&fs::read(oracle_path)?)?;
    assert!(
        oracle["compactVersion"]
            .as_str()
            .unwrap()
            .starts_with("0.36.1 (7fa3a117c")
    );
    assert_eq!(oracle["runtimeVersion"], "0.21.0");
    let name = "NestedMaybeUInt.inspect";
    let mut plan: Plan =
        serde_json::from_slice(&fs::read(directory.join(format!("{name}.impact.json")))?)?;
    let circuit = IrSource::load(fs::File::open(directory.join(format!("{name}.zkir")))?)?;
    let [view] = plan.return_views.as_slice() else {
        panic!("expected one grouped nested Maybe output");
    };
    assert_eq!(view.name, "result");
    assert_eq!(view.fields.len(), 3);
    let fields = view.fields.clone();
    let layout = &view.schema["layout"];
    let inner_layout = &layout["fields"][1]["layout"];
    let outer_id = layout["id"].as_str().expect("outer Maybe type").to_owned();
    let inner_id = inner_layout["id"]
        .as_str()
        .expect("inner Maybe type")
        .to_owned();
    assert_ne!(outer_id, inner_id);
    for level in [layout, inner_layout] {
        assert_eq!(level["kind"], "struct");
        assert_eq!(level["fields"].as_array().unwrap().len(), 2);
        assert_eq!(level["fields"][0]["name"], "is_some");
        assert_eq!(
            level["fields"][0]["layout"]["leaf"],
            json!({"kind": "bool"})
        );
        assert_eq!(level["fields"][1]["name"], "value");
    }
    assert_eq!(
        inner_layout["fields"][1]["layout"]["leaf"],
        json!({"kind": "uint", "maximum": "255"})
    );

    let expected = |outer, inner, value| {
        maybe(
            &outer_id,
            outer,
            maybe(
                &inner_id,
                inner,
                json!({"kind":"uint", "maximum":"255", "value":value}),
            ),
        )
    };
    let inputs = |outer, inner, value: &str| {
        BTreeMap::from([
            ("outer".into(), json!(outer)),
            ("inner".into(), json!(inner)),
            ("value".into(), json!(value)),
        ])
    };
    let state = create_state(&plan, &BTreeMap::new())?;
    let address = ContractAddress::default();
    let params = &ledger::structure::INITIAL_PARAMETERS;
    let cases = oracle["cases"]
        .as_array()
        .expect("four observed Compact results");
    let fixtures = [
        (false, true, "255", false, false, "0"),
        (true, false, "255", true, false, "0"),
        (true, true, "0", true, true, "0"),
        (true, true, "255", true, true, "255"),
    ];
    assert_eq!(cases.len(), fixtures.len());
    let decimal = |value: &Json| match value {
        Json::String(text) => text.clone(),
        value => value.to_string(),
    };
    for ((outer, inner, value, outer_some, inner_some, payload), row) in
        fixtures.into_iter().zip(cases)
    {
        assert_eq!(row["outer"], outer);
        assert_eq!(row["inner"], inner);
        assert_eq!(decimal(&row["value"]), value);
        assert_eq!(row["result"]["is_some"], outer_some);
        assert_eq!(row["result"]["value"]["is_some"], inner_some);
        assert_eq!(decimal(&row["result"]["value"]["value"]), payload);
        let execution = prepare(&plan, &inputs(outer, inner, value), &state, params, address)?;
        check(&execution, &circuit)?;
        let native_fields = [
            u64::from(outer_some),
            u64::from(inner_some),
            payload.parse()?,
        ];
        assert_eq!(execution.returns().len(), 3);
        for ((name, value), (expected_name, field)) in execution
            .returns()
            .iter()
            .zip(fields.iter().zip(native_fields))
        {
            assert_eq!(name, expected_name);
            assert_eq!(
                value,
                &noctium_runtime::Value::Native(transient_crypto::curve::Fr::from(field))
            );
        }
        assert_eq!(
            execution.returns_json(),
            BTreeMap::from([("result".into(), expected(outer_some, inner_some, payload))])
        );
    }

    let accepted_inputs = inputs(true, true, "255");
    let accepted = prepare(&plan, &accepted_inputs, &state, params, address)?;
    let output = plan
        .returns
        .iter_mut()
        .find(|output| output.name == fields[2])
        .expect("bound UInt8 result leaf");
    output.expression = Expr::Constant {
        value: "254".into(),
    };
    let altered = prepare(&plan, &accepted_inputs, &state, params, address)?;
    assert_eq!(
        altered.returns_json()["result"],
        expected(true, true, "254")
    );
    assert_ne!(
        accepted.preimage.communications_commitment.unwrap().0,
        altered.preimage.communications_commitment.unwrap().0
    );
    assert!(
        check(&altered, &circuit).is_err(),
        "emitted relation rejects a substituted UInt8 result"
    );
    Ok(())
}
