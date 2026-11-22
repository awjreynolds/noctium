#![cfg(feature = "zkir-321")]

use coin_structure::contract::ContractAddress;
use noctium_runtime::{
    check,
    control::{InvocationTarget, Session, TypedResponse},
    create_state,
    host::{self, Capability, Context, Limits, Operation, Provider},
    prepare,
    zkir::IrSource,
    Plan,
};
use serde_json::{json, Value as Json};
use sha2::{Digest, Sha256};
use std::{collections::BTreeMap, fs, path::PathBuf};

const SOURCE_NAMESPACE: &str = "ReadableRecordConstruction";

fn source_context(control: &Json, attempt_id: &str) -> Context {
    let mut operations = Vec::new();
    let mut providers = Vec::new();
    let capability = |id: &str, operation: String| Capability {
        id: id.into(),
        namespace: "noctium".into(),
        key_prefix: "noctium/".into(),
        operations: vec![operation],
    };
    let mut capabilities = vec![capability("commit", host::CAS.into())];
    for witness in control["witnesses"]
        .as_array()
        .expect("witness declarations")
    {
        let name = witness["name"].as_str().expect("witness name").to_owned();
        let operation = witness["operation"]
            .as_str()
            .expect("witness operation")
            .to_owned();
        let capability_id = witness["capability"]
            .as_str()
            .expect("witness capability")
            .to_owned();
        let argument_schema = witness["parameters"]
            .as_array()
            .expect("witness parameters")
            .iter()
            .map(|parameter| {
                (
                    parameter["name"]
                        .as_str()
                        .expect("parameter name")
                        .to_owned(),
                    parameter["type"]
                        .as_str()
                        .expect("parameter type")
                        .to_owned(),
                )
            })
            .collect();
        let result_schema = witness["resultType"]
            .as_str()
            .expect("witness result type")
            .to_owned();
        operations.push(Operation {
            operation: operation.clone(),
            argument_schema,
            result_schema,
        });
        providers.push(Provider {
            input: name.clone(),
            operation: operation.clone(),
            capability: capability_id.clone(),
            arguments: BTreeMap::new(),
        });
        capabilities.push(capability(&capability_id, operation));
    }
    Context {
        protocol_version: 1,
        namespace: "noctium".into(),
        base_revision: "r0".into(),
        attempt_id: attempt_id.into(),
        capabilities,
        operations,
        providers,
        commit_capability: "commit".into(),
        limits: Limits::default(),
    }
}

fn session(control: &Json, entrypoint: &str, attempt_id: &str) -> anyhow::Result<Session> {
    let binding = control["binding"]
        .as_str()
        .expect("embedded witness binding");
    let digest = hex::encode(Sha256::digest(binding.as_bytes()));
    Ok(Session::from_json_with_invocation_target(
        control.clone(),
        BTreeMap::from([("seed".into(), json!("7"))]),
        source_context(control, attempt_id),
        Some(&digest),
        Some(InvocationTarget {
            contract_address: "a".repeat(64),
            entrypoint: entrypoint.into(),
        }),
    )?)
}

fn reading_record(reading: &str, count: &str, active: bool) -> Json {
    json!({
        "kind":"struct",
        "id":"ReadableRecordConstruction.Reading",
        "fields":[
            {"name":"reading","value":{"kind":"native","value":reading}},
            {"name":"count","value":{"kind":"uint","maximum":"255","value":count}},
            {"name":"active","value":{"kind":"bool","value":active}}
        ]
    })
}

fn reply(request: &Json, attempt_id: &str, value: Json) -> TypedResponse {
    serde_json::from_value(json!({
        "protocolVersion": 2,
        "requestId": request["requestId"],
        "attemptId": attempt_id,
        "outcome": "value",
        "operation": request["operation"],
        "capability": request["capability"],
        "schema": request["schema"],
        "value": value,
    }))
    .expect("typed host response")
}

fn check_case(
    entrypoint: &str,
    callbacks: impl IntoIterator<Item = (&'static str, &'static str, Json)>,
    expected: Json,
) -> anyhow::Result<()> {
    let directory = PathBuf::from(
        std::env::var_os("NOCTIUM_RECORD_CONSTRUCTION_DIR")
            .expect("NOCTIUM_RECORD_CONSTRUCTION_DIR"),
    );
    let stem = format!("{SOURCE_NAMESPACE}.{entrypoint}");
    let binding: Json =
        serde_json::from_slice(&fs::read(directory.join(format!("{stem}.witness.json")))?)?;
    let control: Json = serde_json::from_slice(&fs::read(
        directory.join(format!("{stem}.witness.control.json")),
    )?)?;
    assert_eq!(
        serde_json::from_str::<Json>(control["binding"].as_str().unwrap())?,
        binding
    );

    let attempt = "5".repeat(64);
    let mut session = session(&control, entrypoint, &attempt)?;
    for (name, marker, value) in callbacks {
        let pending = session.advance()?;
        assert_eq!(pending["status"], "need_host");
        assert_eq!(
            pending["request"]["name"],
            format!("{SOURCE_NAMESPACE}.{name}")
        );
        assert_eq!(session.private_request()?["arguments"]["marker"], marker);
        if name == "observeCount" {
            let overflow = reply(&pending["request"], &attempt, json!("256"));
            assert!(session.resume_typed(overflow).is_err());
            assert_eq!(session.advance()?, pending);
        }
        session.resume_typed(reply(&pending["request"], &attempt, value))?;
    }
    let completed = session.advance()?;
    assert_eq!(completed["status"], "completed");

    assert_eq!(completed["result"], expected);
    let completion = session.private_completion(&binding["nativeRelation"])?;
    let inputs: BTreeMap<String, Json> = serde_json::from_value(completion["inputs"].clone())?;

    let plan: Plan =
        serde_json::from_slice(&fs::read(directory.join(format!("{stem}.impact.json")))?)?;
    let circuit = IrSource::load(fs::File::open(directory.join(format!("{stem}.zkir")))?)?;
    let initial = create_state(&plan, &BTreeMap::new())?;
    let execution = prepare(
        &plan,
        &inputs,
        &initial,
        &ledger::structure::INITIAL_PARAMETERS,
        ContractAddress::default(),
    )?;
    assert_eq!(check(&execution, &circuit)?, execution.activity_schedule);
    let returns = execution.returns_json();
    assert_eq!(returns.len(), 1);
    assert_eq!(returns.get("result"), Some(&expected));
    Ok(())
}

#[test]
#[ignore = "requires fresh ReadableRecordConstruction outputs in NOCTIUM_RECORD_CONSTRUCTION_DIR"]
fn readable_record_construction_preserves_provider_order_and_field_order() -> anyhow::Result<()> {
    check_case(
        "build",
        [
            ("observeReading", "10", json!("9")),
            ("observeCount", "9", json!("17")),
            ("observeActive", "8", json!(true)),
        ],
        reading_record("9", "17", true),
    )
}

#[test]
#[ignore = "requires fresh ReadableRecordConstruction outputs in NOCTIUM_RECORD_CONSTRUCTION_DIR"]
fn record_spread_evaluates_each_base_once_and_preserves_override_order() -> anyhow::Result<()> {
    let base = reading_record("13", "19", false);
    check_case(
        "patch",
        [
            ("loadBase", "7", base.clone()),
            ("observeCount", "9", json!("17")),
            ("observeActive", "8", json!(true)),
            ("loadBase", "10", base),
        ],
        reading_record("13", "17", true),
    )
}

#[test]
#[ignore = "requires fresh ReadableRecordConstruction outputs in NOCTIUM_RECORD_CONSTRUCTION_DIR"]
fn tuple_spread_flattens_composite_values_in_order() -> anyhow::Result<()> {
    check_case(
        "spreadTuple",
        [
            (
                "loadPair",
                "8",
                json!({
                    "kind":"tuple",
                    "items":[
                        {"kind":"native","value":"11"},
                        {"kind":"bool","value":true}
                    ]
                }),
            ),
            (
                "loadVector",
                "9",
                json!({
                    "kind":"vector",
                    "items":[
                        {"kind":"uint","maximum":"255","value":"17"},
                        {"kind":"uint","maximum":"255","value":"19"}
                    ]
                }),
            ),
            ("loadBytes", "10", json!({"kind":"bytes","values":[165,60]})),
            ("loadUnit", "11", json!({"kind":"unit"})),
        ],
        json!({
            "kind":"tuple",
            "items":[
                {"kind":"tuple","items":[
                    {"kind":"native","value":"7"},
                    {"kind":"native","value":"11"},
                    {"kind":"bool","value":true}
                ]},
                {"kind":"tuple","items":[
                    {"kind":"uint","maximum":"255","value":"17"},
                    {"kind":"uint","maximum":"255","value":"19"},
                    {"kind":"uint","maximum":"255","value":"165"},
                    {"kind":"uint","maximum":"255","value":"60"}
                ]},
                {"kind":"tuple","items":[
                    {"kind":"bool","value":true},
                    {"kind":"uint","maximum":"1","value":"1"}
                ]}
            ]
        }),
    )
}

#[test]
#[ignore = "requires fresh ReadableRecordConstruction outputs in NOCTIUM_RECORD_CONSTRUCTION_DIR"]
fn byte_spread_packs_and_reverses_in_order() -> anyhow::Result<()> {
    check_case(
        "packOctets",
        [
            (
                "loadVector",
                "9",
                json!({
                    "kind":"vector",
                    "items":[
                        {"kind":"uint","maximum":"255","value":"17"},
                        {"kind":"uint","maximum":"255","value":"19"}
                    ]
                }),
            ),
            ("loadBytes", "10", json!({"kind":"bytes","values":[165,60]})),
            ("loadUnit", "11", json!({"kind":"unit"})),
        ],
        json!({"kind":"bytes","values":[23,60,165,19,17,7]}),
    )
}

#[test]
#[ignore = "requires fresh ReadableRecordConstruction outputs in NOCTIUM_RECORD_CONSTRUCTION_DIR"]
fn sequence_slices_preserve_composite_shapes_and_order() -> anyhow::Result<()> {
    let pair = json!({
        "kind":"tuple",
        "items":[
            {"kind":"native","value":"11"},
            {"kind":"bool","value":true}
        ]
    });
    check_case(
        "sliceSequences",
        [
            ("loadPair", "8", pair.clone()),
            (
                "loadVector",
                "9",
                json!({
                    "kind":"vector",
                    "items":[
                        {"kind":"uint","maximum":"255","value":"17"},
                        {"kind":"uint","maximum":"255","value":"19"}
                    ]
                }),
            ),
            ("loadPair", "10", pair),
            ("loadBytes", "11", json!({"kind":"bytes","values":[165,60]})),
        ],
        json!({
            "kind":"tuple",
            "items":[
                {"kind":"tuple","items":[{"kind":"bool","value":true}]},
                {"kind":"vector","items":[
                    {"kind":"uint","maximum":"255","value":"19"}
                ]},
                {"kind":"tuple","items":[]},
                {"kind":"bytes","values":[60]}
            ]
        }),
    )
}

#[test]
#[ignore = "requires fresh ReadableRecordConstruction outputs in NOCTIUM_RECORD_CONSTRUCTION_DIR"]
fn vector_construction_preserves_inferred_and_explicit_element_types() -> anyhow::Result<()> {
    check_case(
        "constructVectors",
        [
            (
                "loadVector",
                "9",
                json!({
                    "kind":"vector",
                    "items":[
                        {"kind":"uint","maximum":"255","value":"17"},
                        {"kind":"uint","maximum":"255","value":"19"}
                    ]
                }),
            ),
            ("loadUnit", "11", json!({"kind":"unit"})),
        ],
        json!({
            "kind":"tuple",
            "items":[
                {"kind":"vector","items":[
                    {"kind":"uint","maximum":"255","value":"5"},
                    {"kind":"uint","maximum":"255","value":"17"},
                    {"kind":"uint","maximum":"255","value":"19"}
                ]},
                {"kind":"vector","items":[
                    {"kind":"uint","maximum":"65535","value":"5"},
                    {"kind":"uint","maximum":"65535","value":"17"},
                    {"kind":"uint","maximum":"65535","value":"19"}
                ]},
                {"kind":"vector","items":[]}
            ]
        }),
    )
}

#[test]
#[ignore = "requires fresh ReadableRecordConstruction outputs in NOCTIUM_RECORD_CONSTRUCTION_DIR"]
fn record_helpers_rewrite_and_project_nested_values() -> anyhow::Result<()> {
    let base = reading_record("13", "19", false);
    check_case(
        "helperRewrite",
        [
            ("loadBase", "7", base.clone()),
            ("observeActive", "8", json!(true)),
        ],
        reading_record("14", "19", true),
    )?;
    check_case("helperProject", [("loadBase", "7", base)], json!("14"))
}
