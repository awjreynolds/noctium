#![cfg(feature = "zkir-321")]

use anyhow::Context;
use noctium_runtime::{
    Expr, FabHashInput, Plan, check, create_state, evaluate, prepare, zkir::IrSource,
};
use serde_json::{Value as Json, json};
use std::{collections::BTreeMap, fs::File, path::PathBuf};
use transient_crypto::curve::Fr;

fn artifacts() -> PathBuf {
    std::env::var_os("NOCTIUM_SHA512_FAB_DIR")
        .map(PathBuf::from)
        .expect("NOCTIUM_SHA512_FAB_DIR")
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
#[ignore = "requires fresh compiler outputs in NOCTIUM_SHA512_FAB_DIR"]
fn sha512_fab_matches_compact_and_native_relation() -> anyhow::Result<()> {
    let directory = artifacts();
    let plan: Plan =
        serde_json::from_reader(File::open(directory.join("Sha512Fab.hash.impact.json"))?)?;
    let circuit = IrSource::load(File::open(directory.join("Sha512Fab.hash.zkir"))?)?;
    let initial = create_state(&plan, &BTreeMap::new())?;
    let parameters = &ledger::structure::INITIAL_PARAMETERS;
    let address = coin_structure::contract::ContractAddress::default();

    let output_expression = plan
        .circuit
        .outputs
        .iter()
        .find(|output| output.name == "digest")
        .expect("digest circuit output")
        .expression
        .clone();
    let Expr::Sha512Fab { schema, mut values } = output_expression else {
        anyhow::bail!("digest output is not a FAB SHA-512 expression")
    };
    let FabHashInput::Bytes { length, .. } = &mut values[0] else {
        anyhow::bail!("first FAB value is not Bytes")
    };
    *length = 31;
    let malformed = Expr::Sha512Fab { schema, values };
    let error = evaluate(&malformed, &BTreeMap::new()).unwrap_err();
    assert!(
        error
            .to_string()
            .contains("FAB byte field length differs from schema")
    );

    let vectors = [
        (
            257,
            "6f2b8bc408127949730a24dd6a4b5562a8ec69a7d895a79329c13976447a1c948c4a84e6d070af7e02ea37d89408d1a0679dee79fd6c3cb40e548e4438b7bfae",
            "0a3cf3d2108f7463f9ef5896ebfd31c7fcdde34ac2171cc6b3c48f28d03e8683",
        ),
        (
            258,
            "d65da98a4c62937f9f0aa99c4b68dd81d171a73be6f09f03a85d251ea58d1b6d54d55002038ad3ef43a53c8e43ef808eda8beb48679b092434bffc063bd519aa",
            "eb28a2f9796f720f03aea8e43e7e6ec85e202d85258bd36da513f50f32acf5ee",
        ),
    ];

    for (counter, sha512_digest, keccak_digest) in vectors {
        let mut execution = prepare(&plan, &inputs(counter), &initial, parameters, address)
            .with_context(|| format!("prepare typed FAB hashes with counter {counter}"))?;
        assert_eq!(check(&execution, &circuit)?, execution.activity_schedule);
        let results = execution.returns_json();
        assert_eq!(results["resultDigest"], bytes(&hex::decode(sha512_digest)?));
        assert_eq!(results["keccakResult"], bytes(&hex::decode(keccak_digest)?));
        let (commitment, randomness) = execution.preimage.communications_commitment.unwrap();
        execution.preimage.communications_commitment =
            Some((commitment + Fr::from(1u64), randomness));
        assert!(check(&execution, &circuit).is_err());
    }
    let mut invalid = inputs(257);
    invalid.insert("counterInput".into(), json!("65536"));
    assert!(prepare(&plan, &invalid, &initial, parameters, address).is_err());
    Ok(())
}
