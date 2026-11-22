#![cfg(feature = "zkir-321")]

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

const SAMPLE_ID: &str = "NestedAggregateEquality.Sample";
const INNER_ID: &str = "NestedAggregateEquality.Inner";
const KIND_ID: &str = "NestedAggregateEquality.Kind";

fn native(value: &str) -> Json {
    json!({"kind":"native", "value":value})
}

fn sample(
    head: &str,
    octets: [u8; 2],
    enabled: bool,
    amount: &str,
    pair_head: &str,
    pair_tail: [&str; 2],
    bytes: [u8; 2],
    kind: &str,
) -> Json {
    json!({
        "kind":"struct",
        "id":SAMPLE_ID,
        "fields":[
            {"name":"head", "value":native(head)},
            {"name":"inner", "value":{
                "kind":"struct",
                "id":INNER_ID,
                "fields":[
                    {"name":"octets", "value":{"kind":"bytes", "values":octets}},
                    {"name":"enabled", "value":{"kind":"bool", "value":enabled}},
                    {"name":"amount", "value":{"kind":"uint", "maximum":"255", "value":amount}}
                ]
            }},
            {"name":"pair", "value":{"kind":"tuple", "items":[
                native(pair_head),
                {"kind":"vector", "items":[native(pair_tail[0]), native(pair_tail[1])]}
            ]}},
            {"name":"bytes", "value":{"kind":"bytes", "values":bytes}},
            {"name":"kind", "value":{"kind":"enum", "id":KIND_ID, "variant":kind, "fields":[]}}
        ]
    })
}

fn session(control: &Json, attempt_id: &str, left: Json, right: Json) -> anyhow::Result<Session> {
    let binding = control["binding"]
        .as_str()
        .expect("embedded witness binding");
    let digest = hex::encode(Sha256::digest(binding.as_bytes()));
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
            operations: Vec::new(),
            providers: Vec::new(),
            commit_capability: "commit".into(),
            limits: Limits::default(),
        },
        Some(&digest),
        Some(InvocationTarget {
            contract_address: "a".repeat(64),
            entrypoint: "compare".into(),
        }),
    )?)
}

#[test]
#[ignore = "requires fresh NestedAggregateEquality artifacts in NOCTIUM_NESTED_EQUALITY_DIR"]
fn nested_aggregate_equality_checks_each_typed_leaf() -> anyhow::Result<()> {
    let directory = PathBuf::from(
        std::env::var_os("NOCTIUM_NESTED_EQUALITY_DIR").expect("NOCTIUM_NESTED_EQUALITY_DIR"),
    );
    let stem = "NestedAggregateEquality.compare";
    let control: Json = serde_json::from_slice(&fs::read(
        directory.join(format!("{stem}.witness.control.json")),
    )?)?;
    let binding: Json =
        serde_json::from_str(control["binding"].as_str().expect("embedded binding"))?;
    assert_eq!(control["inputs"][0]["name"], "left");
    assert_eq!(control["inputs"][0]["visibility"], "public");
    assert_eq!(control["inputs"][1]["name"], "right");
    assert_eq!(control["inputs"][1]["visibility"], "private");
    assert_eq!(control["inputs"][0]["type"], control["inputs"][1]["type"]);
    let aggregate_type = control["inputs"][0]["type"]
        .as_str()
        .and_then(|ty| ty.strip_prefix("Aggregate:"))
        .expect("logical inputs use the same aggregate type");
    assert!(binding["types"].as_array().is_some_and(|types| {
        types
            .iter()
            .any(|ty| ty["id"] == aggregate_type && ty["schema"]["layout"]["id"] == SAMPLE_ID)
    }));
    let plan: Plan = serde_json::from_reader(fs::File::open(
        directory.join(format!("{stem}.impact.json")),
    )?)?;
    let circuit = IrSource::load(fs::File::open(directory.join(format!("{stem}.zkir")))?)?;
    let initial = create_state(&plan, &BTreeMap::new())?;
    let left = sample("11", [1, 2], true, "5", "31", ["41", "42"], [9, 8], "C");
    let cases = [
        (
            "baseline",
            sample("11", [1, 2], true, "5", "31", ["41", "42"], [9, 8], "C"),
            true,
        ),
        (
            "head",
            sample("12", [1, 2], true, "5", "31", ["41", "42"], [9, 8], "C"),
            false,
        ),
        (
            "inner.octets",
            sample("11", [1, 3], true, "5", "31", ["41", "42"], [9, 8], "C"),
            false,
        ),
        (
            "inner.enabled",
            sample("11", [1, 2], false, "5", "31", ["41", "42"], [9, 8], "C"),
            false,
        ),
        (
            "inner.amount",
            sample("11", [1, 2], true, "6", "31", ["41", "42"], [9, 8], "C"),
            false,
        ),
        (
            "pair.head",
            sample("11", [1, 2], true, "5", "32", ["41", "42"], [9, 8], "C"),
            false,
        ),
        (
            "pair.tail[0]",
            sample("11", [1, 2], true, "5", "31", ["40", "42"], [9, 8], "C"),
            false,
        ),
        (
            "pair.tail[1]",
            sample("11", [1, 2], true, "5", "31", ["41", "43"], [9, 8], "C"),
            false,
        ),
        (
            "bytes",
            sample("11", [1, 2], true, "5", "31", ["41", "42"], [9, 7], "C"),
            false,
        ),
        (
            "kind",
            sample("11", [1, 2], true, "5", "31", ["41", "42"], [9, 8], "B"),
            false,
        ),
    ];

    for (index, (case, right, expected_same)) in cases.into_iter().enumerate() {
        let attempt_id = format!("{:064x}", index + 1);
        let mut invocation = session(&control, &attempt_id, left.clone(), right)?;
        assert_eq!(invocation.advance()?["status"], "completed");
        let completion = invocation.private_completion(&binding["nativeRelation"])?;
        let inputs: BTreeMap<String, Json> = serde_json::from_value(completion["inputs"].clone())?;
        let execution = prepare(
            &plan,
            &inputs,
            &initial,
            &ledger::structure::INITIAL_PARAMETERS,
            ContractAddress::default(),
        )?;
        assert_eq!(check(&execution, &circuit)?, execution.activity_schedule);
        assert_eq!(
            execution.returns_json().get("same"),
            Some(&json!(expected_same)),
            "unexpected equality result for {case}"
        );
    }

    Ok(())
}
