#![cfg(feature = "zkir-321")]

use noctium_runtime::{
    Plan, check, create_state, prepare, proof::TrustedParameters, zkir::IrSource,
};
use serde_json::{Value as Json, json};
use sha2::{Digest, Sha256};
use std::{collections::BTreeMap, env, fs, fs::File, path::PathBuf};

const INDEXED_SHIELDED_NONCE_K: u8 = 10;
const INDEXED_SHIELDED_NONCE_RELATION_SHA256: &str =
    "75c49e96fcfe08babd2666a17420821480be5fe2705c25c78984dd3c9640e82e";
const OFFICIAL_K10_SRS_SHA256: &str =
    "46b2290933cbed4c378889e4ba971f1a92888331ffb09466acd4ff61a1e2cb42";
const INDEXED_SHIELDED_NONCE_DIGEST_AT_ZERO: &str =
    "f2bd6732969e6e5d895070978de9462e7d70a932ac37b21387b1521f207f5300";

fn artifacts() -> PathBuf {
    std::env::var_os("NOCTIUM_INDEXED_SHIELDED_NONCE_DIR")
        .map(PathBuf::from)
        .expect("NOCTIUM_INDEXED_SHIELDED_NONCE_DIR")
}

fn bytes(value: &[u8]) -> Json {
    json!({"kind":"bytes", "values":value})
}

fn inputs(index: &str, nonce: &[u8]) -> BTreeMap<String, Json> {
    BTreeMap::from([
        ("index".into(), json!(index)),
        ("nonce".into(), bytes(nonce)),
    ])
}

#[test]
#[ignore = "requires fresh compiler outputs in NOCTIUM_INDEXED_SHIELDED_NONCE_DIR"]
fn indexed_shielded_nonce_matches_compact_and_discards_the_high_byte() -> anyhow::Result<()> {
    let directory = artifacts();
    let plan: Plan = serde_json::from_reader(File::open(
        directory.join("IndexedShieldedNonce.evolve.impact.json"),
    )?)?;
    let circuit = IrSource::load(File::open(
        directory.join("IndexedShieldedNonce.evolve.zkir"),
    )?)?;
    let initial = create_state(&plan, &BTreeMap::new())?;
    let parameters = &ledger::structure::INITIAL_PARAMETERS;
    let address = coin_structure::contract::ContractAddress::default();
    const MAX_INDEX: &str = "340282366920938463463374607431768211455";
    let expected_at_zero = bytes(&hex::decode(INDEXED_SHIELDED_NONCE_DIGEST_AT_ZERO)?);
    let expected_at_maximum = bytes(&hex::decode(
        "0c0163afc8a0a7f18df615e077cfc07cb21784e19a74f23eb48318b51ccb1800",
    )?);
    let mut first_nonce = [0u8; 32];
    for (offset, byte) in first_nonce.iter_mut().enumerate() {
        *byte = u8::try_from(offset + 1)?;
    }
    let mut nonce_with_changed_high_byte = first_nonce;
    nonce_with_changed_high_byte[31] ^= 0xff;

    let cases = [
        ("0", first_nonce, expected_at_zero),
        (MAX_INDEX, first_nonce, expected_at_maximum.clone()),
        (MAX_INDEX, nonce_with_changed_high_byte, expected_at_maximum),
    ];
    for (index, nonce, expected) in cases {
        let execution = prepare(&plan, &inputs(index, &nonce), &initial, parameters, address)?;
        assert_eq!(check(&execution, &circuit)?, execution.activity_schedule);
        assert_eq!(execution.returns_json().get("result"), Some(&expected));
    }

    const OVERFLOW_INDEX: &str = "340282366920938463463374607431768211456";
    assert!(
        prepare(
            &plan,
            &inputs(OVERFLOW_INDEX, &first_nonce),
            &initial,
            parameters,
            address,
        )
        .is_err(),
        "index above UInt128 must reject"
    );
    assert!(
        prepare(
            &plan,
            &inputs("0", &first_nonce[..31]),
            &initial,
            parameters,
            address,
        )
        .is_err(),
        "nonce with the wrong byte width must reject"
    );
    Ok(())
}

#[test]
#[ignore = "requires fresh compiler outputs in NOCTIUM_INDEXED_SHIELDED_NONCE_DIR and the official k10 SRS in NOCTIUM_INDEXED_SHIELDED_NONCE_PROOF_PARAMETERS"]
fn indexed_shielded_nonce_generates_and_binds_native_proof() -> anyhow::Result<()> {
    use futures::executor::block_on;
    use rand::rngs::OsRng;
    use transient_crypto::{
        curve::Fr,
        proofs::{ParamsVerifier, Zkir},
    };

    let directory = artifacts();
    let plan: Plan = serde_json::from_reader(File::open(
        directory.join("IndexedShieldedNonce.evolve.impact.json"),
    )?)?;
    let relation_bytes = fs::read(directory.join("IndexedShieldedNonce.evolve.zkir"))?;
    assert_eq!(
        hex::encode(Sha256::digest(&relation_bytes)),
        INDEXED_SHIELDED_NONCE_RELATION_SHA256
    );
    let relation = IrSource::load(relation_bytes.as_slice())?;
    assert_eq!(relation.k(), INDEXED_SHIELDED_NONCE_K);
    let parameter_bytes = fs::read(
        env::var_os("NOCTIUM_INDEXED_SHIELDED_NONCE_PROOF_PARAMETERS")
            .expect("NOCTIUM_INDEXED_SHIELDED_NONCE_PROOF_PARAMETERS"),
    )?;
    let parameters = TrustedParameters::from_bytes(
        &parameter_bytes,
        INDEXED_SHIELDED_NONCE_K,
        OFFICIAL_K10_SRS_SHA256,
    )?;
    assert_eq!(parameters.sha256(), OFFICIAL_K10_SRS_SHA256);
    let verifier_parameters = ParamsVerifier::read(parameter_bytes.as_slice())?;
    let initial = create_state(&plan, &BTreeMap::new())?;
    let nonce: [u8; 32] = std::array::from_fn(|offset| (offset + 1) as u8);
    let execution = prepare(
        &plan,
        &inputs("0", &nonce),
        &initial,
        &ledger::structure::INITIAL_PARAMETERS,
        coin_structure::contract::ContractAddress::default(),
    )?;
    assert_eq!(check(&execution, &relation)?, execution.activity_schedule);
    let expected = bytes(&hex::decode(INDEXED_SHIELDED_NONCE_DIGEST_AT_ZERO)?);
    assert_eq!(execution.returns_json().get("result"), Some(&expected));

    let (prover_key, verifier_key) = block_on(relation.keygen(&parameters))?;
    let (proof, statement, activity) = block_on(relation.prove(
        OsRng,
        &parameters,
        prover_key,
        &execution.preimage,
    ))?;
    assert_eq!(activity, execution.activity_schedule);
    verifier_key.verify(&verifier_parameters, &proof, statement.iter().copied())?;

    let (commitment, _) = execution
        .preimage
        .communications_commitment
        .expect("the declared digest is bound by the communication commitment");
    assert_eq!(statement.get(1), Some(&commitment));
    let mut changed_statement = statement;
    changed_statement[1] = commitment + Fr::from(1u64);
    assert!(verifier_key
        .verify(
            &verifier_parameters,
            &proof,
            changed_statement.iter().copied(),
        )
        .is_err());

    println!(
        "Indexed shielded nonce proof passed: k={}, relation_sha256={}, srs_sha256={}, expected_digest={}, proof_bytes={}, altered_communication_commitment=rejected",
        INDEXED_SHIELDED_NONCE_K,
        INDEXED_SHIELDED_NONCE_RELATION_SHA256,
        parameters.sha256(),
        INDEXED_SHIELDED_NONCE_DIGEST_AT_ZERO,
        proof.0.len(),
    );
    Ok(())
}
