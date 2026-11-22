#![cfg(feature = "zkir-321")]

use anyhow::Context;
use noctium_runtime::{
    Expr, FabHashInput, Plan, check, create_state, evaluate, prepare, zkir::IrSource,
};
use serde_json::{Value as Json, json};
use std::{collections::BTreeMap, fs::File, path::PathBuf};
use transient_crypto::curve::Fr;

fn artifacts() -> PathBuf {
    std::env::var_os("NOCTIUM_MIXED_FAB_PERSISTENT_HASH_DIR")
        .map(PathBuf::from)
        .expect("NOCTIUM_MIXED_FAB_PERSISTENT_HASH_DIR")
}

fn bytes(value: &[u8]) -> Json {
    json!({"kind":"bytes", "values":value})
}

fn inputs(counter: u16) -> BTreeMap<String, Json> {
    BTreeMap::from([
        ("octets".into(), bytes(&(1u8..=32).collect::<Vec<_>>())),
        ("flag".into(), json!(true)),
        ("counterInput".into(), json!(counter.to_string())),
        ("anchor".into(), json!("42")),
    ])
}

#[test]
#[ignore = "requires fresh compiler outputs in NOCTIUM_MIXED_FAB_PERSISTENT_HASH_DIR"]
fn mixed_fab_persistent_hash_matches_compact_and_native_relation() -> anyhow::Result<()> {
    let directory = artifacts();
    let plan: Plan = serde_json::from_reader(File::open(
        directory.join("MixedFabPersistentHash.hash.impact.json"),
    )?)?;
    let circuit = IrSource::load(File::open(
        directory.join("MixedFabPersistentHash.hash.zkir"),
    )?)?;
    let initial = create_state(&plan, &BTreeMap::new())?;
    let parameters = &ledger::structure::INITIAL_PARAMETERS;
    let address = coin_structure::contract::ContractAddress::default();
    let vectors = [
        (
            257,
            "05743c725c44c8d77bf1b9601385ef901ec4040ecb770014a535ddcb5e2840d9",
        ),
        (
            258,
            "4376a00dd2129c85219a8aecd9a8209cad4fdc8d333ed7e127f71220697490c2",
        ),
    ];

    let output_expression = plan
        .circuit
        .outputs
        .iter()
        .find(|output| output.name == "digest")
        .expect("digest circuit output")
        .expression
        .clone();
    let Expr::PersistentHashFab { schema, mut values } = output_expression else {
        anyhow::bail!("digest output is not a FAB persistent hash")
    };
    let FabHashInput::Bytes { length, .. } = &mut values[0] else {
        anyhow::bail!("first FAB value is not Bytes")
    };
    *length = 31;
    let malformed = Expr::PersistentHashFab { schema, values };
    let error = evaluate(&malformed, &BTreeMap::new()).unwrap_err();
    assert!(
        error
            .to_string()
            .contains("FAB byte field length differs from schema")
    );

    for (counter, expected) in vectors {
        let execution = prepare(&plan, &inputs(counter), &initial, parameters, address)
            .with_context(|| format!("prepare FAB hash with counter {counter}"))?;
        assert_eq!(check(&execution, &circuit)?, execution.activity_schedule);
        let expected = hex::decode(expected)?;
        assert_eq!(
            execution.returns_json().get("resultHash"),
            Some(&bytes(&expected))
        );
    }
    Ok(())
}

#[test]
#[ignore = "requires fresh compiler outputs in NOCTIUM_EMPTY_FAB_BYTES_DIR"]
fn empty_fab_bytes_preserve_hashes_and_assertions() -> anyhow::Result<()> {
    let directory = PathBuf::from(
        std::env::var_os("NOCTIUM_EMPTY_FAB_BYTES_DIR").context("NOCTIUM_EMPTY_FAB_BYTES_DIR")?,
    );
    let plan: Plan = serde_json::from_reader(File::open(
        directory.join("EmptyFabBytes.hash.impact.json"),
    )?)?;
    let circuit = IrSource::load(File::open(directory.join("EmptyFabBytes.hash.zkir"))?)?;
    let initial = create_state(&plan, &BTreeMap::new())?;
    let parameters = &ledger::structure::INITIAL_PARAMETERS;
    let address = coin_structure::contract::ContractAddress::default();
    let mut inputs = BTreeMap::from([
        ("mustPass".into(), json!(true)),
        ("value".into(), json!(false)),
        ("emptyBytes".into(), bytes(&[])),
    ]);

    let empty_digest =
        hex::decode("e3b0c44298fc1c149afbf4c8996fb92427ae41e4649b934ca495991b7852b855")?;
    for (value, digest) in [
        (
            false,
            "6e340b9cffb37a989ca544e6bb780a2c78901d3fb33738768511a30617afa01d",
        ),
        (
            true,
            "4bf5122f344554c53bde2ebb8cd2b7e3d1600ad631c385a5d7cce23c7785459a",
        ),
    ] {
        inputs.insert("value".into(), json!(value));
        let mut execution = prepare(&plan, &inputs, &initial, parameters, address)?;
        assert_eq!(check(&execution, &circuit)?, execution.activity_schedule);
        assert_eq!(
            execution.returns_json(),
            BTreeMap::from([
                ("mixedDigestResult".into(), bytes(&hex::decode(digest)?)),
                ("emptyOnlyDigestResult".into(), bytes(&empty_digest)),
            ])
        );
        assert_eq!(
            execution.preimage.private_transcript,
            [Fr::from(1u64), Fr::from(u64::from(value))]
        );
        execution.preimage.private_transcript[0] = Fr::from(0u64);
        assert!(check(&execution, &circuit).is_err());
    }

    inputs.insert("mustPass".into(), json!(false));
    assert!(prepare(&plan, &inputs, &initial, parameters, address).is_err());
    Ok(())
}
