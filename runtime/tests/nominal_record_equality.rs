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

fn wire_session(control: &Json, left: Json, right: Json) -> Result<Session> {
    let binding = control["binding"].as_str().expect("witness binding");
    let pin = hex::encode(Sha256::digest(binding.as_bytes()));
    Session::from_json_with_invocation_target(
        control.clone(),
        BTreeMap::from([("left".into(), left), ("right".into(), right)]),
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
            entrypoint: "compare".into(),
        }),
    )
}

fn reading(id: &str, reading: &str, count: &str, active: bool) -> Json {
    json!({
        "kind":"struct",
        "id":id,
        "fields":[
            {"name":"reading","value":{"kind":"native","value":reading}},
            {"name":"count","value":{"kind":"uint","maximum":"255","value":count}},
            {"name":"active","value":{"kind":"bool","value":active}}
        ]
    })
}

#[test]
#[ignore = "requires fresh artifacts in NOCTIUM_NOMINAL_RECORD_EQUALITY_DIR"]
fn nominal_record_equality_compares_each_field() -> Result<()> {
    let directory = PathBuf::from(
        std::env::var_os("NOCTIUM_NOMINAL_RECORD_EQUALITY_DIR")
            .expect("NOCTIUM_NOMINAL_RECORD_EQUALITY_DIR"),
    );
    let name = "NominalRecordEqualityFixture.compare";
    let control: Json = serde_json::from_slice(&fs::read(
        directory.join(format!("{name}.witness.control.json")),
    )?)?;
    let binding: Json = serde_json::from_str(control["binding"].as_str().expect("binding"))?;
    assert_eq!(control["inputs"][0]["name"], "left");
    assert_eq!(control["inputs"][0]["visibility"], "public");
    assert_eq!(control["inputs"][1]["name"], "right");
    assert_eq!(control["inputs"][1]["visibility"], "public");
    assert_eq!(binding["target"]["entrypoint"], "compare");

    let plan: Plan =
        serde_json::from_slice(&fs::read(directory.join(format!("{name}.impact.json")))?)?;
    let circuit = IrSource::load(fs::File::open(directory.join(format!("{name}.zkir")))?)?;
    let initial = create_state(&plan, &BTreeMap::new())?;
    let id = "NominalRecordEquality.PairedReading";
    let left = reading(id, "9", "17", true);
    let cases = [
        (reading(id, "9", "17", true), true),
        (reading(id, "10", "17", true), false),
        (reading(id, "9", "18", true), false),
        (reading(id, "9", "17", false), false),
    ];

    for (right, same) in cases {
        let mut session = wire_session(&control, left.clone(), right)?;
        assert_eq!(session.advance()?["status"], "completed");
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
            execution.returns_json(),
            BTreeMap::from([("same".into(), json!(same))])
        );
    }

    let wrong_id = reading("NominalRecordEquality.OtherReading", "9", "17", true);
    assert!(wire_session(&control, left, wrong_id).is_err());
    Ok(())
}
