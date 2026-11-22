#![cfg(feature = "zkir-321")]

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

fn bytes(value: &[u8]) -> Json {
    json!({"kind":"bytes", "values":value})
}

fn jubjub(x: &str, y: &str) -> Json {
    json!({"kind":"jubjubPoint", "x":x, "y":y})
}

fn secp(bytes: &[u8]) -> Json {
    json!({"kind":"foreign", "type":"Secp256k1Point", "bytes":bytes})
}

#[test]
#[ignore = "requires fresh artifacts in NOCTIUM_MAYBE_BYTES_CURVES_DIR"]
fn checked_maybe_returns_preserve_bytes_points_and_default_identities() -> anyhow::Result<()> {
    let directory = PathBuf::from(
        std::env::var_os("NOCTIUM_MAYBE_BYTES_CURVES_DIR").expect("NOCTIUM_MAYBE_BYTES_CURVES_DIR"),
    );
    let stem = "MaybeBytesCurves.inspect";
    let mut plan: Plan = serde_json::from_reader(fs::File::open(
        directory.join(format!("{stem}.impact.json")),
    )?)?;
    let circuit = IrSource::load(fs::File::open(directory.join(format!("{stem}.zkir")))?)?;
    let control: Json = serde_json::from_reader(fs::File::open(
        directory.join(format!("{stem}.witness.control.json")),
    )?)?;
    let binding = control["binding"].as_str().expect("witness binding");
    let native_relation: Json = serde_json::from_str(binding)?;
    let digest = hex::encode(Sha256::digest(binding.as_bytes()));
    let memo = bytes(&[0, 145, 255]);
    let jubjub_generator = jubjub(
        "28336281903124990867587793011069573392383982287722241916350956173377953689573",
        "39385640392217313770878525135509063452020585410343666726093009378539878503883",
    );
    let secp_generator = secp(&hex::decode(
        "0279be667ef9dcbbac55a06295ce870b07029bfcdb2dce28d959f2815b16f81798",
    )?);
    let mut invocation = Session::from_json_with_invocation_target(
        control,
        BTreeMap::from([
            ("memo".into(), memo.clone()),
            ("jubjub".into(), jubjub_generator.clone()),
            ("secp".into(), secp_generator.clone()),
        ]),
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
        Some(&digest),
        Some(InvocationTarget {
            contract_address: "a".repeat(64),
            entrypoint: "inspect".into(),
        }),
    )?;
    assert_eq!(invocation.advance()?["status"], "completed");
    let completion = invocation.private_completion(&native_relation["nativeRelation"])?;
    let inputs = serde_json::from_value(completion["inputs"].clone())?;
    let state = create_state(&plan, &BTreeMap::new())?;
    let params = &ledger::structure::INITIAL_PARAMETERS;
    let address = ContractAddress::default();
    let execution = prepare(&plan, &inputs, &state, params, address)?;
    assert_eq!(check(&execution, &circuit)?, execution.activity_schedule);
    let returns = execution.returns_json();
    for (present_name, present, absent_name, absent) in [
        ("presentMemo", memo, "absentMemo", bytes(&[0; 3])),
        (
            "presentJubjub",
            jubjub_generator,
            "absentJubjub",
            jubjub("0", "1"),
        ),
        ("presentSecp", secp_generator, "absentSecp", secp(&[0; 33])),
        ("presentEmpty", bytes(&[]), "absentEmpty", bytes(&[])),
    ] {
        assert_eq!(returns[present_name]["id"], returns[absent_name]["id"]);
        for (name, tag, payload) in [(present_name, true, present), (absent_name, false, absent)] {
            assert_eq!(
                returns[name]["fields"],
                json!([
                    {"name":"is_some", "value":{"kind":"bool", "value":tag}},
                    {"name":"value", "value":payload},
                ]),
                "{name}"
            );
        }
    }

    let tag = plan
        .return_views
        .iter()
        .find(|view| view.name == "presentMemo")
        .and_then(|view| view.fields.first())
        .expect("presentMemo tag");
    plan.returns
        .iter_mut()
        .find(|output| output.name == *tag)
        .expect("presentMemo tag output")
        .expression = Expr::Constant { value: "0".into() };
    let changed = prepare(&plan, &inputs, &state, params, address)?;
    assert!(check(&changed, &circuit).is_err());
    Ok(())
}
