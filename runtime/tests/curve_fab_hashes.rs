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
use transient_crypto::curve::Fr;

fn artifacts() -> PathBuf {
    std::env::var_os("NOCTIUM_CURVE_FAB_HASHES_DIR")
        .map(PathBuf::from)
        .expect("NOCTIUM_CURVE_FAB_HASHES_DIR")
}

fn foreign(ty: &str, bytes: &[u8]) -> Json {
    json!({"kind":"foreign", "type":ty, "bytes":bytes})
}

fn inputs() -> BTreeMap<String, Json> {
    let mut secp_base = [0u8; 32];
    secp_base[0] = 42;
    BTreeMap::from([
        (
            "jubjubScalar".into(),
            json!({"kind":"jubjubScalar", "value":"17"}),
        ),
        (
            "jubjubPoint".into(),
            json!({
                "kind":"jubjubPoint",
                "x":"28336281903124990867587793011069573392383982287722241916350956173377953689573",
                "y":"39385640392217313770878525135509063452020585410343666726093009378539878503883"
            }),
        ),
        ("secpBase".into(), foreign("Secp256k1Base", &secp_base)),
        (
            "secpPoint".into(),
            foreign(
                "Secp256k1Point",
                &hex::decode("0279be667ef9dcbbac55a06295ce870b07029bfcdb2dce28d959f2815b16f81798")
                    .unwrap(),
            ),
        ),
        (
            "pairJubjubPoint".into(),
            json!({"kind":"jubjubPoint", "x":"0", "y":"1"}),
        ),
        ("pairSecpPoint".into(), foreign("Secp256k1Point", &[0; 33])),
    ])
}

fn readable_payload() -> Json {
    let inputs = inputs();
    let field = |name: &str| inputs.get(name).expect("oracle input").clone();
    json!({
        "kind":"struct",
        "id":"CurveFabHashes.CurvePayload",
        "fields":[
            {"name":"inner","value":{
                "kind":"struct",
                "id":"CurveFabHashes.Inner",
                "fields":[
                    {"name":"scalar","value":field("jubjubScalar")},
                    {"name":"point","value":field("jubjubPoint")}
                ]
            }},
            {"name":"secpBase","value":field("secpBase")},
            {"name":"secpPoint","value":field("secpPoint")},
            {"name":"pair","value":{"kind":"tuple","items":[
                field("pairJubjubPoint"),
                field("pairSecpPoint")
            ]}}
        ]
    })
}

#[test]
#[ignore = "requires fresh Lean outputs in NOCTIUM_CURVE_FAB_HASHES_DIR"]
fn curve_fab_hashes_match_compact_oracles_and_bind_return_commitment() -> anyhow::Result<()> {
    let directory = artifacts();
    let stem = "CurveFabHashes.hash";
    let plan: Plan =
        serde_json::from_slice(&fs::read(directory.join(format!("{stem}.impact.json")))?)?;
    let circuit = IrSource::load(fs::File::open(directory.join(format!("{stem}.zkir")))?)?;
    let initial = create_state(&plan, &BTreeMap::new())?;
    let mut execution = prepare(
        &plan,
        &inputs(),
        &initial,
        &ledger::structure::INITIAL_PARAMETERS,
        coin_structure::contract::ContractAddress::default(),
    )?;

    assert_eq!(check(&execution, &circuit)?, execution.activity_schedule);
    assert_eq!(
        execution.returns_json(),
        BTreeMap::from([
            (
                "persistentResult".into(),
                json!({
                    "kind":"bytes",
                    "values":hex::decode(
                        "f7a88f2c30c717772757acbd8d86c87b4c1e8cc88cdfe2f5efb608a1e61ed7b8"
                    )?
                }),
            ),
            (
                "transientResult".into(),
                json!(
                    "22293029467289654224445560286591595292864875000282287882633570107188179417385"
                ),
            ),
            (
                "curveResult".into(),
                json!({
                    "kind":"jubjubPoint",
                    "x":"5187241681299452555252327364509344370508477903483857193377192133060431926242",
                    "y":"23820288451142401238103521862534681424716203618312892062945957612621911308121"
                }),
            ),
            (
                "persistentCommitOutput".into(),
                json!({
                    "kind":"bytes",
                    "values":hex::decode(
                        "64e39fd0347562cd6bc4bf0e240a5081700885dc8193008f3d531283b7a772bc"
                    )?
                }),
            ),
            (
                "transientCommitOutput".into(),
                json!(
                    "43834219855257331008480478917217379826888172132588787922878333292523868224849"
                ),
            ),
            (
                "sha512Output".into(),
                json!({
                    "kind":"bytes",
                    "values":hex::decode(
                        "d21d1fd0b4e7915f8419812e711ea0c4746cef7ebe95b10a4c661a7d128fa71bbef47a4b077aeac0542882d29cc4f838dfdbd701746f9f51b756faceab01bdb2"
                    )?
                }),
            ),
        ])
    );

    let (commitment, randomness) = execution
        .preimage
        .communications_commitment
        .expect("the native return commitment");
    execution.preimage.communications_commitment = Some((commitment + Fr::from(1u64), randomness));
    assert!(check(&execution, &circuit).is_err());
    Ok(())
}

#[test]
#[ignore = "requires fresh Lean outputs in NOCTIUM_CURVE_FAB_HASHES_DIR/readable"]
fn readable_curve_fab_hash_matches_host_and_native_relation() -> anyhow::Result<()> {
    let directory = artifacts().join("readable");
    let stem = "ReadableCurveTransientHash.hash";
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
        "noctium.witness-circuit.ReadableCurveTransientHash.hashCurvePayload.v1"
    );

    let logical_inputs = control["inputs"].as_array().expect("logical inputs");
    assert_eq!(logical_inputs.len(), 1);
    assert_eq!(logical_inputs[0]["name"], "payload");
    assert_eq!(logical_inputs[0]["visibility"], "private");
    let type_id = logical_inputs[0]["type"]
        .as_str()
        .and_then(|ty| ty.strip_prefix("Aggregate:"))
        .expect("payload aggregate schema");
    assert!(binding["types"].as_array().is_some_and(|types| {
        types.iter().any(|ty| {
            ty["id"] == type_id && ty["schema"]["layout"]["id"] == "CurveFabHashes.CurvePayload"
        })
    }));

    let binding_text = control["binding"].as_str().expect("embedded binding");
    let pin = hex::encode(Sha256::digest(binding_text.as_bytes()));
    let attempt = "8".repeat(64);
    let mut session = Session::from_json_with_invocation_target(
        control,
        BTreeMap::from([("payload".into(), readable_payload())]),
        Context {
            protocol_version: 1,
            namespace: "noctium".into(),
            base_revision: "r0".into(),
            attempt_id: attempt,
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
        Some(&pin),
        Some(InvocationTarget {
            contract_address: "a".repeat(64),
            entrypoint: "hash".into(),
        }),
    )?;
    let completed = session.advance()?;
    assert_eq!(completed["status"], "completed");
    let expected =
        json!("22293029467289654224445560286591595292864875000282287882633570107188179417385");
    assert_eq!(completed["result"], expected);

    let completion = session.private_completion(&binding["nativeRelation"])?;
    let native_inputs: BTreeMap<String, Json> =
        serde_json::from_value(completion["inputs"].clone())?;
    let plan: Plan = serde_json::from_reader(fs::File::open(
        directory.join(format!("{stem}.impact.json")),
    )?)?;
    let circuit = IrSource::load(fs::File::open(directory.join(format!("{stem}.zkir")))?)?;
    let initial = create_state(&plan, &BTreeMap::new())?;
    let execution = prepare(
        &plan,
        &native_inputs,
        &initial,
        &ledger::structure::INITIAL_PARAMETERS,
        ContractAddress::default(),
    )?;
    assert_eq!(check(&execution, &circuit)?, execution.activity_schedule);
    assert_eq!(
        execution.returns_json().get("digestResult"),
        Some(&expected)
    );
    Ok(())
}
