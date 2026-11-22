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
use std::{
    collections::BTreeMap,
    fs,
    path::{Path, PathBuf},
};

fn uint(maximum: &str, value: u16) -> Json {
    json!({"kind":"uint", "maximum":maximum, "value":value.to_string()})
}

fn vector(maximum: &str, values: [u16; 2]) -> Json {
    json!({
        "kind":"vector",
        "items":values.into_iter().map(|value| uint(maximum, value)).collect::<Vec<_>>()
    })
}

fn tuple(maximum: &str, narrow: u16, field: &str) -> Json {
    json!({
        "kind":"tuple",
        "items":[uint(maximum, narrow), {"kind":"native", "value":field}]
    })
}

fn wire_session(
    control: &Json,
    entrypoint: &str,
    attempt_id: &str,
    left: Json,
    right: Json,
) -> Result<Session> {
    let binding = control["binding"].as_str().expect("witness binding");
    let pin = hex::encode(Sha256::digest(binding.as_bytes()));
    Ok(Session::from_json_with_invocation_target(
        control.clone(),
        BTreeMap::from([("left".into(), left), ("right".into(), right)]),
        Context {
            protocol_version: 1,
            namespace: "noctium".into(),
            base_revision: "r0".into(),
            attempt_id: attempt_id.into(),
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
    )?)
}

fn assert_equal(
    directory: &Path,
    entrypoint: &str,
    left: Json,
    right: Json,
    expected: bool,
    attempt: usize,
) -> Result<()> {
    let stem = format!("StructuralEqualityWidening.{entrypoint}");
    let control: Json = serde_json::from_slice(&fs::read(
        directory.join(format!("{stem}.witness.control.json")),
    )?)?;
    let binding: Json = serde_json::from_str(control["binding"].as_str().expect("binding"))?;
    let plan: Plan =
        serde_json::from_slice(&fs::read(directory.join(format!("{stem}.impact.json")))?)?;
    let circuit = IrSource::load(fs::File::open(directory.join(format!("{stem}.zkir")))?)?;
    let initial = create_state(&plan, &BTreeMap::new())?;

    let mut session =
        wire_session(&control, entrypoint, &format!("{attempt:064x}"), left, right)?;
    let completed = session.advance()?;
    assert_eq!(completed["status"], "completed");
    assert_eq!(completed["result"], expected);
    let completion = session.private_completion(&binding["nativeRelation"])?;
    let inputs: BTreeMap<String, Json> = serde_json::from_value(completion["inputs"].clone())?;
    let execution = prepare(
        &plan,
        &inputs,
        &initial,
        &ledger::structure::INITIAL_PARAMETERS,
        ContractAddress::default(),
    )?;
    check(&execution, &circuit)?;
    assert_eq!(
        execution.returns_json().get("same"),
        Some(&json!(expected)),
        "unexpected equality result for {entrypoint}"
    );
    Ok(())
}

#[test]
#[ignore = "requires fresh artifacts in NOCTIUM_STRUCTURAL_EQUALITY_DIR"]
fn structural_equality_widens_checked_vectors_and_tuples() -> Result<()> {
    let directory = PathBuf::from(
        std::env::var_os("NOCTIUM_STRUCTURAL_EQUALITY_DIR")
            .expect("NOCTIUM_STRUCTURAL_EQUALITY_DIR"),
    );
    let vector_stem = "StructuralEqualityWidening.compareVectors";
    let vector_control: Json = serde_json::from_slice(&fs::read(
        directory.join(format!("{vector_stem}.witness.control.json")),
    )?)?;
    let tuple_stem = "StructuralEqualityWidening.compareTuples";
    let tuple_control: Json = serde_json::from_slice(&fs::read(
        directory.join(format!("{tuple_stem}.witness.control.json")),
    )?)?;

    for control in [&vector_control, &tuple_control] {
        assert_eq!(control["inputs"][0]["name"], "left");
        assert_eq!(control["inputs"][0]["visibility"], "public");
        assert_eq!(control["inputs"][1]["name"], "right");
        assert_eq!(control["inputs"][1]["visibility"], "private");
        let left_type = control["inputs"][0]["type"]
            .as_str()
            .expect("declared left logical type");
        let right_type = control["inputs"][1]["type"]
            .as_str()
            .expect("declared right logical type");
        assert_ne!(
            left_type, right_type,
            "checked input types must stay distinct"
        );
    }

    let vector_left = vector("255", [1, 2]);
    for (attempt, (right, expected)) in [
        (vector("65535", [1, 2]), true),
        (vector("65535", [1, 3]), false),
        (vector("65535", [1, 256]), false),
    ]
    .into_iter()
    .enumerate()
    {
        assert_equal(
            &directory,
            "compareVectors",
            vector_left.clone(),
            right,
            expected,
            attempt + 1,
        )?;
    }

    let tuple_left = tuple("255", 1, "11");
    for (attempt, (right, expected)) in [
        (tuple("65535", 1, "11"), true),
        (tuple("65535", 2, "11"), false),
        (tuple("65535", 1, "12"), false),
    ]
    .into_iter()
    .enumerate()
    {
        assert_equal(
            &directory,
            "compareTuples",
            tuple_left.clone(),
            right,
            expected,
            attempt + 4,
        )?;
    }

    let invalid_result = wire_session(
        &vector_control,
        "compareVectors",
        &format!("{:064x}", 10),
        vector("255", [1, 256]),
        vector("65535", [1, 256]),
    );
    assert!(
        invalid_result.err().is_some_and(
            |error| format!("{error:#}").contains("aggregate scalar outside declared range")
        ),
        "the typed UInt8 input boundary must reject 256"
    );

    Ok(())
}
