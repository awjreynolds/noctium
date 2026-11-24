#![cfg(feature = "zkir-321")]

use noctium_runtime::{
    Plan, check,
    control::{InvocationTarget, Session, TypedResponse},
    create_state,
    host::{self, Capability, Context, Limits, Operation, Provider},
    prepare,
    proof::TrustedParameters,
    zkir::IrSource,
};
use futures::executor::block_on;
use rand::rngs::OsRng;
use serde_json::{Value as Json, json};
use sha2::{Digest, Sha256};
use std::{
    collections::BTreeMap,
    env, fs,
    path::{Path, PathBuf},
};
use transient_crypto::{
    curve::Fr,
    proofs::{ParamsVerifier, Zkir},
};

const EXPECTED_ROOT: &str =
    "23615363679718302500648733510038242834016166715802047945282536128750549339216";
const PROOF_K: u8 = 9;
const RELATION_SHA256: &str =
    "654f463d8adad531e45220fe4f62e546b1c1c124d61b7b05f96d02106a9b3d7c";
const OFFICIAL_SRS_SHA256: &str =
    "b9009f1098bcefffec3c461ab3a5e3a17f7e5599f0f08c70fcdc55a89227bcbd";

fn artifacts() -> PathBuf {
    env::var_os("NOCTIUM_MERKLE_PATH_TYPES_DIR")
        .map(PathBuf::from)
        .expect("set fresh outputs in NOCTIUM_MERKLE_PATH_TYPES_DIR")
}

fn context(control: &Json, attempt_id: &str) -> Context {
    let signature = &control["witnesses"][0];
    let name = signature["name"].as_str().unwrap().to_owned();
    let operation = signature["operation"].as_str().unwrap().to_owned();
    let capability = signature["capability"].as_str().unwrap().to_owned();
    let arguments = signature["parameters"]
        .as_array()
        .unwrap()
        .iter()
        .map(|parameter| {
            (
                parameter["name"].as_str().unwrap().to_owned(),
                parameter["type"].as_str().unwrap().to_owned(),
            )
        })
        .collect();
    Context {
        protocol_version: 1,
        namespace: "noctium".into(),
        base_revision: "merkle-path-types-test".into(),
        attempt_id: attempt_id.into(),
        capabilities: vec![
            Capability {
                id: capability.clone(),
                namespace: "noctium".into(),
                key_prefix: "lookup/".into(),
                operations: vec![operation.clone()],
            },
            Capability {
                id: "private".into(),
                namespace: "noctium".into(),
                key_prefix: "cache/".into(),
                operations: vec![host::STAGE.into()],
            },
            Capability {
                id: "commit".into(),
                namespace: "noctium".into(),
                key_prefix: "cache/".into(),
                operations: vec![host::CAS.into()],
            },
        ],
        operations: vec![Operation {
            operation: operation.clone(),
            argument_schema: arguments,
            result_schema: signature["resultType"].as_str().unwrap().into(),
        }],
        providers: vec![Provider {
            input: name,
            operation,
            capability,
            arguments: BTreeMap::new(),
        }],
        commit_capability: "commit".into(),
        limits: Limits::default(),
    }
}

fn session(control: &Json, attempt_id: &str) -> Session {
    let binding_text = control["binding"].as_str().unwrap();
    let binding: Json = serde_json::from_str(binding_text).unwrap();
    let digest = hex::encode(Sha256::digest(binding_text.as_bytes()));
    Session::from_json_with_invocation_target(
        control.clone(),
        BTreeMap::new(),
        context(control, attempt_id),
        Some(&digest),
        Some(InvocationTarget {
            contract_address: "a".repeat(64),
            entrypoint: binding["target"]["entrypoint"].as_str().unwrap().into(),
        }),
    )
    .unwrap()
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
    .unwrap()
}

fn digest(field: &str) -> Json {
    json!({
        "kind":"struct", "id":"MerkleTreeDigest", "fields":[
            {"name":"field","value":{"kind":"native","value":field}}
        ]
    })
}

fn path_entry(sibling: &str, direction: Json) -> Json {
    json!({
        "kind":"struct", "id":"MerkleTreePathEntry", "fields":[
            {"name":"sibling","value":digest(sibling)},
            {"name":"goes_left","value":{"kind":"bool", "value":direction}}
        ]
    })
}

fn path_payload(direction: Option<Json>, depth: usize) -> Json {
    let siblings = ["17", "29"];
    let directions = [json!(true), json!(false)];
    let entries = (0..depth)
        .map(|index| {
            path_entry(
                siblings[index],
                direction
                    .clone()
                    .unwrap_or_else(|| directions[index].clone()),
            )
        })
        .collect::<Vec<_>>();
    json!({
        "kind":"struct", "id":"MerklePathRootNoLeafHash.Path", "fields":[
            {"name":"leaf","value":{"kind":"bytes","values":(1u8..=32).collect::<Vec<_>>()}},
            {"name":"path","value":{"kind":"vector","items":entries}}
        ]
    })
}

fn reject_provider_payload(control: &Json, value: Json) {
    let attempt_id = "b".repeat(64);
    let mut session = session(control, &attempt_id);
    let pending = session.advance().unwrap();
    assert_eq!(pending["status"], "need_host");
    assert!(
        session
            .resume_typed(reply(&pending["request"], &attempt_id, value))
            .is_err()
    );
}

fn check_path_root(
    directory: &Path,
    stem: &str,
    control: &Json,
    payload: Json,
) -> anyhow::Result<Json> {
    let plan: Plan = serde_json::from_reader(fs::File::open(
        directory.join(format!("{stem}.impact.json")),
    )?)?;
    let relation = IrSource::load(fs::File::open(directory.join(format!("{stem}.zkir")))?)?;
    let attempt_id = "a".repeat(64);
    let mut session = session(control, &attempt_id);
    let pending = session.advance()?;
    assert_eq!(pending["status"], "need_host");
    session.resume_typed(reply(&pending["request"], &attempt_id, payload))?;
    assert_eq!(session.advance()?["status"], "completed");
    let binding: Json = serde_json::from_str(control["binding"].as_str().unwrap())?;
    let completion = session.private_completion(&binding["nativeRelation"])?;
    let inputs = serde_json::from_value(completion["inputs"].clone())?;
    let initial = create_state(&plan, &BTreeMap::new())?;
    let execution = prepare(
        &plan,
        &inputs,
        &initial,
        &ledger::structure::INITIAL_PARAMETERS,
        coin_structure::contract::ContractAddress::default(),
    )?;
    assert_eq!(check(&execution, &relation)?, execution.activity_schedule);
    Ok(execution.returns_json()["root"].clone())
}

#[test]
#[ignore = "requires fresh MerklePathRootNoLeafHash outputs in NOCTIUM_MERKLE_PATH_TYPES_DIR"]
fn nested_merkle_path_preserves_entry_order_and_checks_provider_shape() -> anyhow::Result<()> {
    let directory = artifacts();
    let stem = "MerklePathRootNoLeafHashSource.digest";
    let control: Json = serde_json::from_reader(fs::File::open(
        directory.join(format!("{stem}.witness.control.json")),
    )?)?;
    assert_eq!(
        check_path_root(&directory, stem, &control, path_payload(None, 2))?,
        digest(EXPECTED_ROOT)
    );

    reject_provider_payload(&control, path_payload(Some(json!(2)), 2));
    reject_provider_payload(&control, path_payload(None, 1));

    let mut wrong_entry_id = path_payload(None, 2);
    wrong_entry_id["fields"][1]["value"]["items"][0]["id"] = json!("WrongPathEntry");
    reject_provider_payload(&control, wrong_entry_id);
    let mut wrong_digest_id = path_payload(None, 2);
    wrong_digest_id["fields"][1]["value"]["items"][0]["fields"][0]["value"]["id"] =
        json!("WrongMerkleDigest");
    reject_provider_payload(&control, wrong_digest_id);
    Ok(())
}

#[test]
#[ignore = "requires fresh MerklePathRootNoLeafHash outputs and the pinned trusted SRS"]
fn merkle_path_entry_generates_and_binds_native_proof() -> anyhow::Result<()> {
    let directory = artifacts();
    let stem = "MerklePathRootNoLeafHashSource.digest";
    let control: Json = serde_json::from_reader(fs::File::open(
        directory.join(format!("{stem}.witness.control.json")),
    )?)?;
    let relation_bytes = fs::read(directory.join(format!("{stem}.zkir")))?;
    assert_eq!(hex::encode(Sha256::digest(&relation_bytes)), RELATION_SHA256);
    let relation = IrSource::load(relation_bytes.as_slice())?;
    assert_eq!(relation.k(), PROOF_K);
    let plan: Plan = serde_json::from_reader(fs::File::open(
        directory.join(format!("{stem}.impact.json")),
    )?)?;

    let attempt_id = "c".repeat(64);
    let mut invocation = session(&control, &attempt_id);
    let pending = invocation.advance()?;
    assert_eq!(pending["status"], "need_host");
    invocation.resume_typed(reply(
        &pending["request"],
        &attempt_id,
        path_payload(None, 2),
    ))?;
    assert_eq!(invocation.advance()?["status"], "completed");
    let binding: Json = serde_json::from_str(control["binding"].as_str().unwrap())?;
    let completion = invocation.private_completion(&binding["nativeRelation"])?;
    let inputs: BTreeMap<String, Json> = serde_json::from_value(completion["inputs"].clone())?;
    let initial = create_state(&plan, &BTreeMap::new())?;
    let execution = prepare(
        &plan,
        &inputs,
        &initial,
        &ledger::structure::INITIAL_PARAMETERS,
        coin_structure::contract::ContractAddress::default(),
    )?;
    assert_eq!(check(&execution, &relation)?, execution.activity_schedule);
    assert_eq!(execution.returns_json()["root"], digest(EXPECTED_ROOT));
    assert_eq!(
        execution.preimage.private_transcript,
        (1u64..=32)
            .chain([17u64, 1, 29, 0])
            .map(Fr::from)
            .collect::<Vec<_>>()
    );

    let mut invalid_direction = execution.preimage.clone();
    invalid_direction.private_transcript[33] = Fr::from(2u64);
    assert!(invalid_direction.check(&relation).is_err());

    let parameter_bytes = fs::read(
        env::var_os("NOCTIUM_MERKLE_PATH_PROOF_PARAMETERS")
            .expect("NOCTIUM_MERKLE_PATH_PROOF_PARAMETERS"),
    )?;
    let parameters = TrustedParameters::from_bytes(&parameter_bytes, PROOF_K, OFFICIAL_SRS_SHA256)?;
    assert_eq!(parameters.sha256(), OFFICIAL_SRS_SHA256);
    let verifier_parameters = ParamsVerifier::read(parameter_bytes.as_slice())?;
    let (prover_key, verifier_key) = block_on(relation.keygen(&parameters))?;
    let (proof, statement, activity) = block_on(relation.prove(
        OsRng,
        &parameters,
        prover_key,
        &execution.preimage,
    ))?;
    assert_eq!(activity, execution.activity_schedule);
    let (return_commitment, _) = execution
        .preimage
        .communications_commitment
        .expect("public return is bound by the communication commitment");
    assert_eq!(statement.get(1), Some(&return_commitment));
    verifier_key.verify(&verifier_parameters, &proof, statement.iter().copied())?;

    let mut changed_return_commitment = statement;
    changed_return_commitment[1] = return_commitment + Fr::from(1u64);
    assert!(verifier_key
        .verify(
            &verifier_parameters,
            &proof,
            changed_return_commitment.iter().copied(),
        )
        .is_err());
    Ok(())
}

#[test]
#[ignore = "requires fresh TypedMerklePathRoot outputs in NOCTIUM_TYPED_MERKLE_PATH_ROOT_DIR"]
fn typed_merkle_path_hashes_the_canonical_leaf_and_matches_compact() -> anyhow::Result<()> {
    let directory = PathBuf::from(env::var("NOCTIUM_TYPED_MERKLE_PATH_ROOT_DIR")?);
    let stem = "TypedMerklePathRootSource.root";
    let control: Json = serde_json::from_reader(fs::File::open(
        directory.join(format!("{stem}.witness.control.json")),
    )?)?;
    let payload = json!({"kind":"struct", "id":"TypedMerklePathRoot.Path", "fields":[
        {"name":"leaf","value":{"kind":"struct", "id":"TypedMerklePathRoot.MixedMerkleLeaf", "fields":[
            {"name":"tag", "value":{"kind":"bytes","values":[12,0,0]}},
            {"name":"details", "value":{"kind":"tuple","items":[
                {"kind":"bool","value":true},
                {"kind":"uint","maximum":"65535","value":"258"},
                {"kind":"enum","id":"TypedMerklePathRoot.LeafMarker","variant":"Only","fields":[]}
            ]}}
        ]}},
        {"name":"path","value":{"kind":"vector","items":[
            path_entry("0", json!(false)), path_entry("0", json!(false))
        ]}}
    ]});
    let root = check_path_root(&directory, stem, &control, payload.clone())?;
    assert_eq!(
        root,
        digest("31400609395615079034746563944767363629115546679921774204850545210160415781421")
    );

    let mut wrong_leaf = payload;
    wrong_leaf["fields"][0]["value"]["id"] = json!("WrongLeaf");
    reject_provider_payload(&control, wrong_leaf);
    Ok(())
}
