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
        "id":"CompositeMaybeInput.Limits",
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
#[ignore = "requires fresh artifacts in NOCTIUM_COMPOSITE_MAYBE_INPUT_DIR"]
fn readable_composite_maybe_input_preserves_tag_payload_and_state() -> Result<()> {
    let directory = PathBuf::from(
        std::env::var_os("NOCTIUM_COMPOSITE_MAYBE_INPUT_DIR")
            .expect("NOCTIUM_COMPOSITE_MAYBE_INPUT_DIR"),
    );
    let name = "CompositeMaybeInput.echo";
    let control: Json = serde_json::from_slice(&fs::read(
        directory.join(format!("{name}.witness.control.json")),
    )?)?;
    let binding: Json = serde_json::from_str(control["binding"].as_str().expect("binding"))?;
    let plan: Plan =
        serde_json::from_slice(&fs::read(directory.join(format!("{name}.impact.json")))?)?;
    let circuit = IrSource::load(fs::File::open(directory.join(format!("{name}.zkir")))?)?;
    let echoed_id = view_id(&plan, "echoed");
    assert_eq!(echoed_id, "CompositeMaybeInput.MaybeLimits");
    assert_eq!(control["inputs"].as_array().unwrap().len(), 1);
    assert_eq!(control["inputs"][0]["name"], "value");
    assert_eq!(control["inputs"][0]["visibility"], "public");
    assert_eq!(binding["target"]["entrypoint"], "echo");
    assert_eq!(
        plan.circuit
            .inputs
            .iter()
            .map(|input| input.name.as_str())
            .collect::<Vec<_>>(),
        [
            "value.is_some",
            "value.value.count",
            "value.value.enabled",
            "value.value.memo.0",
            "value.value.memo.1",
            "value.value.memo.2",
            "value.value.memo.3",
        ]
    );
    let initial = create_state(&plan, &BTreeMap::from([("seen".into(), json!(false))]))?;
    let params = &ledger::structure::INITIAL_PARAMETERS;
    let address = ContractAddress::default();
    let zero = limits("0", false, &[0, 0, 0, 0]);
    let nonzero = limits("17", true, &[0, 1, 2, 255]);

    for (is_some, payload, expected_inputs) in [
        (false, nonzero.clone(), [0u64, 17, 1, 0, 1, 2, 255]),
        (true, nonzero.clone(), [1u64, 17, 1, 0, 1, 2, 255]),
        (false, zero.clone(), [0u64, 0, 0, 0, 0, 0, 0]),
    ] {
        let source_value = maybe("CompositeMaybeInput.MaybeLimits", is_some, payload.clone());
        let mut session = wire_session(&control, "echo", source_value)?;
        assert_eq!(session.advance()?["status"], "completed");
        let completion = session.private_completion(&binding["nativeRelation"])?;
        let inputs: BTreeMap<String, Json> = serde_json::from_value(completion["inputs"].clone())?;
        let execution = prepare(&plan, &inputs, &initial, params, address)?;
        check(&execution, &circuit)?;
        assert_eq!(
            execution.preimage.public_transcript_outputs,
            expected_inputs.map(Fr::from)
        );
        assert_eq!(
            execution.returns_json(),
            BTreeMap::from([(
                "echoed".into(),
                maybe("CompositeMaybeInput.MaybeLimits", is_some, payload.clone()),
            )])
        );
        let expected_after =
            create_state(&plan, &BTreeMap::from([("seen".into(), json!(is_some))]))?;
        assert_eq!(execution.after.state.get_ref(), expected_after.get_ref());
    }

    let mut malformed_tag = maybe("CompositeMaybeInput.MaybeLimits", false, zero.clone());
    malformed_tag["fields"][0]["value"]["value"] = json!("false");
    assert!(wire_session(&control, "echo", malformed_tag).is_err());
    let malformed_fixed_bytes = maybe(
        "CompositeMaybeInput.MaybeLimits",
        false,
        limits("17", true, &[0, 1, 2]),
    );
    assert!(wire_session(&control, "echo", malformed_fixed_bytes).is_err());
    Ok(())
}
