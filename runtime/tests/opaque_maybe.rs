#![cfg(feature = "zkir-321")]

use anyhow::{Context as _, Result};
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

#[test]
#[ignore = "requires fresh OpaqueMaybe ledger/witness artifacts and the pinned Compact output"]
fn opaque_maybe_preserves_payloads_and_binds_their_compressed_fields() -> Result<()> {
    let directory = PathBuf::from(std::env::var("NOCTIUM_OPAQUE_MAYBE_DIR")?);
    let compact: Json = serde_json::from_reader(fs::File::open(std::env::var(
        "NOCTIUM_OPAQUE_MAYBE_COMPACT",
    )?)?)?;
    let mut plan: Plan = serde_json::from_reader(fs::File::open(
        directory.join("OpaqueMaybe.inspect.impact.json"),
    )?)?;
    let circuit = IrSource::load(fs::File::open(directory.join("OpaqueMaybe.inspect.zkir"))?)?;
    let control: Json = serde_json::from_reader(fs::File::open(
        directory.join("OpaqueMaybe.inspect.witness.control.json"),
    )?)?;
    let binding_text = control["binding"]
        .as_str()
        .context("missing witness binding")?;
    let pin = hex::encode(Sha256::digest(binding_text.as_bytes()));
    let binding: Json = serde_json::from_str(binding_text)?;
    let address = ContractAddress::default();
    let start = |inputs| {
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
                contract_address: hex::encode(address.0.0),
                entrypoint: "inspect".into(),
            }),
        )
    };
    let inputs = BTreeMap::from([
        (
            "textValue".into(),
            json!({"kind":"opaqueString","value":compact["stringSome"]["value"]}),
        ),
        (
            "bytesValue".into(),
            json!({"kind":"opaqueBytes","values":compact["bytesSome"]["value"]}),
        ),
    ]);
    let mut wrong_kind = inputs.clone();
    wrong_kind.insert("textValue".into(), inputs["bytesValue"].clone());
    assert!(start(wrong_kind).is_err());
    let mut session = start(inputs)?;
    let result = session.advance()?;
    assert_eq!(result["status"], "completed", "witness result: {result}");
    let completion = session.private_completion(&binding["nativeRelation"])?;
    let inputs = serde_json::from_value(completion["inputs"].clone())?;
    let state = create_state(&plan, &BTreeMap::new())?;
    let execution = prepare(
        &plan,
        &inputs,
        &state,
        &ledger::structure::INITIAL_PARAMETERS,
        address,
    )?;
    check(&execution, &circuit)?;
    let returns = execution.returns_json();
    for name in ["stringSome", "stringNone", "bytesSome", "bytesNone"] {
        let payload = if name.starts_with("string") {
            json!({"kind":"opaqueString","value":compact[name]["value"]})
        } else {
            json!({"kind":"opaqueBytes","values":compact[name]["value"]})
        };
        assert_eq!(
            returns[name]["fields"],
            json!([
                {"name":"is_some","value":{"kind":"bool","value":compact[name]["is_some"]}},
                {"name":"value","value":payload}
            ]),
            "{name}"
        );
    }
    assert_eq!(execution.returns().len(), 8);
    let payload_name = plan
        .return_views
        .iter()
        .find(|view| view.name == "stringSome")
        .and_then(|view| view.fields.get(1))
        .context("missing stringSome payload field")?;
    plan.returns
        .iter_mut()
        .find(|output| output.name == *payload_name)
        .context("missing physical stringSome return")?
        .expression = Expr::OpaqueEmpty { ty: "OpaqueString".into() };
    let changed = prepare(
        &plan,
        &inputs,
        &state,
        &ledger::structure::INITIAL_PARAMETERS,
        address,
    )?;
    assert_ne!(
        execution.preimage.communications_commitment,
        changed.preimage.communications_commitment,
    );
    assert!(check(&changed, &circuit).is_err());
    Ok(())
}
