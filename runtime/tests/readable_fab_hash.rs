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

fn payload() -> Json {
    json!({
        "kind":"struct",
        "id":"ReadableFabHash.Payload",
        "fields":[
            {"name":"head","value":{"kind":"native","value":"11"}},
            {"name":"inner","value":{
                "kind":"struct",
                "id":"ReadableFabHash.Inner",
                "fields":[
                    {"name":"tag","value":{"kind":"bytes","values":[18,52]}},
                    {"name":"enabled","value":{"kind":"bool","value":true}},
                    {"name":"amount","value":{"kind":"uint","maximum":"65535","value":"513"}}
                ]
            }},
            {"name":"pair","value":{"kind":"tuple","items":[
                {"kind":"native","value":"31"},
                {"kind":"vector","items":[
                    {"kind":"native","value":"41"},
                    {"kind":"native","value":"42"}
                ]}
            ]}},
            {"name":"empty","value":{"kind":"vector","items":[]}},
            {"name":"tail","value":{"kind":"native","value":"99"}}
        ]
    })
}

fn session(control: &Json, attempt_id: &str) -> anyhow::Result<Session> {
    let binding = control["binding"]
        .as_str()
        .expect("embedded witness binding");
    let digest = hex::encode(Sha256::digest(binding.as_bytes()));
    Ok(Session::from_json_with_invocation_target(
        control.clone(),
        BTreeMap::from([("payload".into(), payload())]),
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
            entrypoint: "digest".into(),
        }),
    )?)
}

#[test]
#[ignore = "requires fresh ReadableFabHash artifacts in NOCTIUM_READABLE_FAB_HASH_DIR"]
fn readable_fab_hash_accepts_one_typed_payload_and_matches_compact() -> anyhow::Result<()> {
    let directory = PathBuf::from(
        std::env::var_os("NOCTIUM_READABLE_FAB_HASH_DIR").expect("NOCTIUM_READABLE_FAB_HASH_DIR"),
    );
    let stem = "ReadableFabHash.digest";
    let binding: Json =
        serde_json::from_slice(&fs::read(directory.join(format!("{stem}.witness.json")))?)?;
    let control: Json = serde_json::from_slice(&fs::read(
        directory.join(format!("{stem}.witness.control.json")),
    )?)?;
    assert_eq!(
        serde_json::from_str::<Json>(control["binding"].as_str().unwrap())?,
        binding
    );
    assert_eq!(
        binding["sourceExport"],
        "noctium.witness-circuit.ReadableFabHash.hashReadablePayload.v1"
    );

    let logical_inputs = control["inputs"].as_array().expect("logical inputs");
    assert_eq!(logical_inputs.len(), 1);
    assert_eq!(logical_inputs[0]["name"], "payload");
    let type_id = logical_inputs[0]["type"]
        .as_str()
        .and_then(|ty| ty.strip_prefix("Aggregate:"))
        .expect("payload aggregate schema");
    assert!(binding["types"].as_array().is_some_and(|types| {
        types.iter().any(|ty| {
            ty["id"] == type_id && ty["schema"]["layout"]["id"] == "ReadableFabHash.Payload"
        })
    }));
    assert_eq!(logical_inputs[0]["visibility"], "private");

    let plan: Plan = serde_json::from_reader(fs::File::open(
        directory.join(format!("{stem}.impact.json")),
    )?)?;
    let circuit = IrSource::load(fs::File::open(directory.join(format!("{stem}.zkir")))?)?;
    let attempt = "8".repeat(64);
    let mut session = session(&control, &attempt)?;
    assert_eq!(session.advance()?["status"], "completed");
    let completion = session.private_completion(&binding["nativeRelation"])?;
    let inputs: BTreeMap<String, Json> = serde_json::from_value(completion["inputs"].clone())?;
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
    assert_eq!(returns.len(), 2);
    assert_eq!(
        returns.get("digest"),
        Some(&json!(
            "15768837897521911811722696040654606308073209539648838630070805017733391969083"
        ))
    );
    assert_eq!(returns.get("emptyDigest"), Some(&json!("0")));
    Ok(())
}
