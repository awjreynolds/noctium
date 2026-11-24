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
#[ignore = "requires fresh OpaqueEither artifacts and the pinned Compact output"]
fn opaque_either_binds_the_typed_selected_arm() -> Result<()> {
    let directory = PathBuf::from(std::env::var("NOCTIUM_OPAQUE_EITHER_DIR")?);
    let vectors: Json = serde_json::from_reader(fs::File::open(std::env::var(
        "NOCTIUM_OPAQUE_EITHER_COMPACT",
    )?)?)?;
    let plan: Plan = serde_json::from_reader(fs::File::open(
        directory.join("OpaqueEither.inspect.impact.json"),
    )?)?;
    let relation = IrSource::load(fs::File::open(directory.join("OpaqueEither.inspect.zkir"))?)?;
    let control: Json = serde_json::from_reader(fs::File::open(
        directory.join("OpaqueEither.inspect.witness.control.json"),
    )?)?;
    let binding_text = control["binding"].as_str().context("missing binding")?;
    let pin = hex::encode(Sha256::digest(binding_text.as_bytes()));
    let binding: Json = serde_json::from_str(binding_text)?;
    let address = ContractAddress::default();
    let state = create_state(&plan, &BTreeMap::new())?;

    for case in vectors["cases"]
        .as_array()
        .context("missing Compact cases")?
    {
        let input = BTreeMap::from([
            ("isLeft".into(), case["isLeft"].clone()),
            ("boolValue".into(), vectors["boolValue"].clone()),
            (
                "textValue".into(),
                json!({"kind":"opaqueString","value":vectors["textValue"]}),
            ),
            (
                "bytesValue".into(),
                json!({"kind":"opaqueBytes","values":vectors["bytesValue"]}),
            ),
        ]);
        let mut session = Session::from_json_with_invocation_target(
            control.clone(),
            input,
            Context {
                protocol_version: 1,
                namespace: "noctium".into(),
                base_revision: "r0".into(),
                attempt_id: "c".repeat(64),
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
        )?;
        assert_eq!(session.advance()?["status"], "completed");
        let completion = session.private_completion(&binding["nativeRelation"])?;
        let inputs = serde_json::from_value(completion["inputs"].clone())?;
        let execution = prepare(
            &plan,
            &inputs,
            &state,
            &ledger::structure::INITIAL_PARAMETERS,
            address,
        )?;
        check(&execution, &relation)?;
        let returns = execution.returns_json();
        let string_choice = &case["stringChoice"];
        assert_eq!(
            returns["stringChoice"]["fields"],
            json!([
                {"name":"is_left","value":{"kind":"bool","value":string_choice["is_left"]}},
                {"name":"left","value":{"kind":"opaqueString","value":string_choice["left"]}},
                {"name":"right","value":{"kind":"bool","value":string_choice["right"]}}
            ])
        );
        let bytes_choice = &case["bytesChoice"];
        assert_eq!(
            returns["bytesChoice"]["fields"],
            json!([
                {"name":"is_left","value":{"kind":"bool","value":bytes_choice["is_left"]}},
                {"name":"left","value":{"kind":"bool","value":bytes_choice["left"]}},
                {"name":"right","value":{"kind":"opaqueBytes","values":bytes_choice["right"]}}
            ])
        );

        let (name, leaf, ty) = if case["isLeft"] == true {
            ("stringChoice", 1, "OpaqueString")
        } else {
            ("bytesChoice", 2, "OpaqueBytes")
        };
        let mut altered = plan.clone();
        let field = altered
            .return_views
            .iter()
            .find(|view| view.name == name)
            .and_then(|view| view.fields.get(leaf))
            .context("missing selected return field")?;
        altered
            .returns
            .iter_mut()
            .find(|output| output.name == *field)
            .context("missing physical return")?
            .expression = Expr::OpaqueEmpty { ty: ty.into() };
        let changed = prepare(
            &altered,
            &inputs,
            &state,
            &ledger::structure::INITIAL_PARAMETERS,
            address,
        )?;
        assert_ne!(
            execution.preimage.communications_commitment,
            changed.preimage.communications_commitment,
        );
        assert!(check(&changed, &relation).is_err());
    }
    Ok(())
}
