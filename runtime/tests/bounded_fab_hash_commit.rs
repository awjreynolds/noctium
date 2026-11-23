#![cfg(feature = "zkir-321")]

use coin_structure::contract::ContractAddress;
use noctium_runtime::{
    check,
    control::{InvocationTarget, Session},
    create_state,
    host::{self, Capability, Context, Limits},
    prepare,
    zkir::IrSource,
    Plan,
};
use serde_json::{json, Value as Json};
use sha2::{Digest, Sha256};
use std::{collections::BTreeMap, fs, path::PathBuf};

fn artifacts() -> PathBuf {
    std::env::var_os("NOCTIUM_BOUNDED_FAB_HASH_COMMIT_DIR")
        .map(PathBuf::from)
        .expect("NOCTIUM_BOUNDED_FAB_HASH_COMMIT_DIR")
}

fn bytes(value: &[u8]) -> Json {
    json!({"kind":"bytes", "values":value})
}

fn direct_inputs(
    count: u8,
    persistent_opening: &[u8],
    transient_opening: u64,
) -> BTreeMap<String, Json> {
    BTreeMap::from([
        ("count".into(), json!(count.to_string())),
        ("persistentOpening".into(), bytes(persistent_opening)),
        (
            "transientOpening".into(),
            json!(transient_opening.to_string()),
        ),
    ])
}

fn readable_payload(count: u8) -> Json {
    json!({
        "kind":"struct",
        "id":"BoundedFabHashCommit.Payload",
        "fields":[{
            "name":"count",
            "value":{"kind":"uint", "maximum":"6", "value":count.to_string()}
        }]
    })
}

fn readable_session(control: &Json, count: u8, attempt_id: &str) -> anyhow::Result<Session> {
    let binding = control["binding"]
        .as_str()
        .expect("embedded witness binding");
    let digest = hex::encode(Sha256::digest(binding.as_bytes()));
    Ok(Session::from_json_with_invocation_target(
        control.clone(),
        BTreeMap::from([("payload".into(), readable_payload(count))]),
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
            entrypoint: "readable".into(),
        }),
    )?)
}

#[test]
#[ignore = "requires fresh compiler outputs in NOCTIUM_BOUNDED_FAB_HASH_COMMIT_DIR"]
fn bounded_fab_hash_commit_matches_compact_and_rejects_out_of_range_count() -> anyhow::Result<()> {
    let directory = artifacts();
    let plan: Plan = serde_json::from_slice(&fs::read(
        directory.join("BoundedFabHashCommit.commit.impact.json"),
    )?)?;
    let source_relation: Json = serde_json::from_slice(&fs::read(
        directory.join("BoundedFabHashCommit.commit.zkir"),
    )?)?;
    let instructions = source_relation["instructions"]
        .as_array()
        .expect("native relation instructions");
    assert_eq!(instructions[0]["op"], "private_input");
    assert_eq!(instructions[0]["output"], "%input_count");
    assert_eq!(instructions[1]["op"], "constrain_bits");
    assert_eq!(instructions[1]["val"], "%input_count");
    assert_eq!(instructions[1]["bits"], 3);
    assert_eq!(instructions[2]["op"], "less_than");
    assert_eq!(instructions[2]["a"], "%input_count");
    assert_eq!(instructions[2]["b"], "0x07");
    assert_eq!(instructions[2]["bits"], 3);
    assert_eq!(instructions[3]["op"], "assert");
    let circuit = IrSource::load(fs::File::open(
        directory.join("BoundedFabHashCommit.commit.zkir"),
    )?)?;
    let initial = create_state(&plan, &BTreeMap::new())?;
    let parameters = &ledger::structure::INITIAL_PARAMETERS;
    let address = ContractAddress::default();
    let opening_forward = (1u8..=32).collect::<Vec<_>>();
    let opening_reverse = (1u8..=32).rev().collect::<Vec<_>>();
    let cases = [
        (
            5,
            opening_forward.as_slice(),
            17,
            "e77b9a9ae9e30b0dbdb6f510a264ef9de781501d7b6b92ae89eb059c5ab743db",
            "7a124d8ba6ccc92c05299f38e935e85816875e75d98b0a53133aa0632351c886",
            "47699447692912459726522410466534423256066746656616207079667384395905208673480",
            "32897551855539531353075362223083106206342642377093571727659772813750899550245",
        ),
        (
            6,
            opening_forward.as_slice(),
            17,
            "67586e98fad27da0b9968bc039a1ef34c939b9b8e523a8bef89d478608c5ecf6",
            "52f70840aa0bc85f12cf075bc1dcd09985aac5e98c7e2af1dd0aa7fe8474cb4b",
            "6287741155009174685068248488276955603895669534698111446895299689163609634373",
            "22303504228254332940538443893749386311847149014689687363555693487392721321009",
        ),
        (
            5,
            opening_reverse.as_slice(),
            18,
            "e77b9a9ae9e30b0dbdb6f510a264ef9de781501d7b6b92ae89eb059c5ab743db",
            "75d884ed4ce25784f89889084d0a0b110010eca921856af01a16a6668bfe281c",
            "47699447692912459726522410466534423256066746656616207079667384395905208673480",
            "3614288230654847062934431037799109620006385912217859110602866898799661824041",
        ),
    ];

    for (
        count,
        persistent_opening,
        transient_opening,
        expected_hash,
        expected_persistent_commit,
        expected_transient_hash,
        expected_transient_commit,
    ) in cases
    {
        let execution = prepare(
            &plan,
            &direct_inputs(count, persistent_opening, transient_opening),
            &initial,
            parameters,
            address,
        )?;
        assert_eq!(check(&execution, &circuit)?, execution.activity_schedule);
        let returns = execution.returns_json();
        assert_eq!(
            returns.get("persistentResult"),
            Some(&bytes(&hex::decode(expected_hash)?))
        );
        assert_eq!(
            returns.get("persistentCommitResult"),
            Some(&bytes(&hex::decode(expected_persistent_commit)?))
        );
        assert_eq!(
            returns.get("transientResult"),
            Some(&json!(expected_transient_hash))
        );
        assert_eq!(
            returns.get("transientCommitResult"),
            Some(&json!(expected_transient_commit))
        );
    }

    assert!(prepare(
        &plan,
        &direct_inputs(7, &opening_forward, 17),
        &initial,
        parameters,
        address,
    )
    .is_err());

    let binding: Json = serde_json::from_slice(&fs::read(
        directory.join("BoundedFabHashCommit.readable.witness.json"),
    )?)?;
    let control: Json = serde_json::from_slice(&fs::read(
        directory.join("BoundedFabHashCommit.readable.witness.control.json"),
    )?)?;
    assert_eq!(
        serde_json::from_str::<Json>(control["binding"].as_str().unwrap())?,
        binding
    );
    let readable_plan: Plan = serde_json::from_slice(&fs::read(
        directory.join("BoundedFabHashCommit.readable.impact.json"),
    )?)?;
    let readable_circuit = IrSource::load(fs::File::open(
        directory.join("BoundedFabHashCommit.readable.zkir"),
    )?)?;
    let mut session = readable_session(&control, 5, &"8".repeat(64))?;
    assert_eq!(session.advance()?["status"], "completed");
    let completion = session.private_completion(&binding["nativeRelation"])?;
    let inputs: BTreeMap<String, Json> = serde_json::from_value(completion["inputs"].clone())?;
    let readable_initial = create_state(&readable_plan, &BTreeMap::new())?;
    let execution = prepare(
        &readable_plan,
        &inputs,
        &readable_initial,
        parameters,
        address,
    )?;
    assert_eq!(
        check(&execution, &readable_circuit)?,
        execution.activity_schedule
    );
    assert_eq!(
        execution.returns_json().get("readableDigest"),
        Some(&json!(
            "47699447692912459726522410466534423256066746656616207079667384395905208673480"
        ))
    );

    match readable_session(&control, 7, &"9".repeat(64)) {
        Ok(mut rejected_readable) => {
            assert_eq!(rejected_readable.advance()?["status"], "failed");
        }
        Err(error) => assert!(
            error.to_string().contains("outside") || error.to_string().contains("maximum"),
            "unexpected readable rejection: {error:#}"
        ),
    }
    Ok(())
}
