#![cfg(feature = "zkir-321")]

use anyhow::Context;
use num_bigint::BigUint;
use noctium_runtime::{MODULUS, Plan, check, create_state, prepare, zkir::IrSource};
use serde_json::{Value as Json, json};
use std::{collections::BTreeMap, fs::File, path::PathBuf};

fn bytes(value: &[u8]) -> Json {
    json!({"kind":"bytes", "values":value})
}

fn inputs(value: &str) -> BTreeMap<String, Json> {
    BTreeMap::from([("value".into(), json!(value))])
}

fn load_entrypoint(directory: &std::path::Path, stem: &str) -> anyhow::Result<(Plan, IrSource)> {
    Ok((
        serde_json::from_reader(File::open(directory.join(format!("{stem}.impact.json")))?)?,
        IrSource::load(File::open(directory.join(format!("{stem}.zkir")))?)?,
    ))
}

#[test]
#[ignore = "requires fresh FieldKeccak outputs in NOCTIUM_FIELD_KECCAK_DIR"]
fn field_keccak_matches_compact_boundaries_and_rejects_the_modulus() -> anyhow::Result<()> {
    let directory = PathBuf::from(
        std::env::var_os("NOCTIUM_FIELD_KECCAK_DIR").context("NOCTIUM_FIELD_KECCAK_DIR")?,
    );
    let entries = [
        ("hash", load_entrypoint(&directory, "FieldKeccak.hash")?),
        (
            "hashReadable",
            load_entrypoint(&directory, "FieldKeccak.hashReadable")?,
        ),
    ];
    let modulus = MODULUS.parse::<BigUint>()?;
    let largest = (modulus - BigUint::from(1u8)).to_string();
    let vectors = [
        (
            "0".to_owned(),
            "290decd9548b62a8d60345a988386fc84ba6bc95484008f6362f93160ef3e563",
        ),
        (
            "1".to_owned(),
            "48078cfed56339ea54962e72c37c7f588fc4f8e5bc173827ba75cb10a63a96a5",
        ),
        (
            largest,
            "33f61b7bb4f118891d967a507c5d62c3b394224532993745cf48e6de4b388af5",
        ),
    ];
    let parameters = &ledger::structure::INITIAL_PARAMETERS;
    let address = coin_structure::contract::ContractAddress::default();

    for (name, (plan, circuit)) in &entries {
        let initial = create_state(plan, &BTreeMap::new())?;
        for (value, expected_digest) in &vectors {
            let supplied = inputs(value);
            let execution = prepare(plan, &supplied, &initial, parameters, address)
                .with_context(|| format!("prepare {name} for Field {value}"))?;
            assert_eq!(check(&execution, circuit)?, execution.activity_schedule);
            assert_eq!(
                execution.returns_json()["digest"],
                bytes(&hex::decode(expected_digest)?)
            );
        }
        assert!(
            prepare(plan, &inputs(MODULUS), &initial, parameters, address).is_err(),
            "{name} accepted the noncanonical Field modulus"
        );
    }
    Ok(())
}
