#![cfg(feature = "zkir-321")]

use coin_structure::contract::ContractAddress;
use futures::executor::block_on;
use noctium_runtime::{Plan, check, create_state, prepare, proof::TrustedParameters, zkir::IrSource};
use rand::rngs::OsRng;
use serde_json::{Value as Json, json};
use sha2::{Digest, Sha256};
use std::{collections::BTreeMap, env, fs, fs::File, path::PathBuf};
use transient_crypto::{
    curve::Fr,
    proofs::{ParamsVerifier, Zkir},
};

const PROOF_K: u8 = 8;
const CONVERT_RELATION_SHA256: &str =
    "bd7a08abe4654722e1a3d3aec37ca4b7b3a0f3993ab2a2b0efc06481df834dc7";
const OFFICIAL_SRS_SHA256: &str =
    "909b707551eaaea79828e883cde6fc46ab15986c3b1d791bed462c9e2805c933";

#[test]
#[ignore = "requires fresh CheckedEnumCasts artifacts in NOCTIUM_CHECKED_ENUM_CASTS_DIR"]
fn numeric_enum_casts_match_the_compact_ordinals_and_bounds() -> anyhow::Result<()> {
    let directory = PathBuf::from(
        std::env::var_os("NOCTIUM_CHECKED_ENUM_CASTS_DIR").expect("NOCTIUM_CHECKED_ENUM_CASTS_DIR"),
    );
    let run = |entrypoint: &str,
               inputs: &[(&str, &str)]|
     -> anyhow::Result<BTreeMap<String, Json>> {
        let stem = format!("CheckedEnumCasts.CheckedEnumCasts.{entrypoint}");
        let plan: Plan =
            serde_json::from_reader(File::open(directory.join(format!("{stem}.impact.json")))?)?;
        let circuit = IrSource::load(File::open(directory.join(format!("{stem}.zkir")))?)?;
        let initial = create_state(&plan, &BTreeMap::new())?;
        let inputs = inputs
            .iter()
            .map(|(name, value)| ((*name).into(), json!(value)))
            .collect();
        let execution = prepare(
            &plan,
            &inputs,
            &initial,
            &ledger::structure::INITIAL_PARAMETERS,
            ContractAddress::default(),
        )?;
        assert_eq!(check(&execution, &circuit)?, execution.activity_schedule);
        Ok(execution.returns_json())
    };

    let converted = run("convert", &[("fieldOrdinal", "0"), ("uintOrdinal", "2")])?;
    assert_eq!(converted["fromField"]["variant"], "Pending");
    assert_eq!(converted["fromUInt"]["variant"], "Done");
    assert_eq!(converted["first"]["variant"], "Pending");
    assert!(run("convert", &[("fieldOrdinal", "3"), ("uintOrdinal", "0")]).is_err());
    assert!(run("convert", &[("fieldOrdinal", "0"), ("uintOrdinal", "3")]).is_err());

    let extracted = run("extract", &[("choice.$tag", "2")])?;
    assert_eq!(extracted["fieldValue"], "2");
    assert_eq!(extracted["unsignedValue"], "2");
    assert_eq!(run("narrow", &[("choice.$tag", "1")])?["narrowValue"], "1");
    assert!(run("narrow", &[("choice.$tag", "2")]).is_err());
    Ok(())
}

#[test]
#[ignore = "requires fresh CheckedEnumCasts artifacts and the pinned trusted SRS"]
fn checked_enum_casts_generates_and_binds_native_proof() -> anyhow::Result<()> {
    let directory = PathBuf::from(
        env::var_os("NOCTIUM_CHECKED_ENUM_CASTS_DIR").expect("NOCTIUM_CHECKED_ENUM_CASTS_DIR"),
    );
    let relation_bytes = fs::read(
        directory.join("CheckedEnumCasts.CheckedEnumCasts.convert.zkir"),
    )?;
    assert_eq!(
        hex::encode(Sha256::digest(&relation_bytes)),
        CONVERT_RELATION_SHA256
    );
    let relation = IrSource::load(relation_bytes.as_slice())?;
    assert_eq!(relation.k(), PROOF_K);

    let plan: Plan = serde_json::from_reader(File::open(
        directory.join("CheckedEnumCasts.CheckedEnumCasts.convert.impact.json"),
    )?)?;
    let state = create_state(&plan, &BTreeMap::new())?;
    let execution = prepare(
        &plan,
        &BTreeMap::from([
            ("fieldOrdinal".into(), json!("0")),
            ("uintOrdinal".into(), json!("2")),
        ]),
        &state,
        &ledger::structure::INITIAL_PARAMETERS,
        ContractAddress::default(),
    )?;
    assert_eq!(
        execution.preimage.public_transcript_outputs,
        [Fr::from(0u64), Fr::from(2u64)]
    );
    assert_eq!(check(&execution, &relation)?, execution.activity_schedule);
    let returns = execution.returns_json();
    assert_eq!(returns["fromField"]["variant"], "Pending");
    assert_eq!(returns["fromUInt"]["variant"], "Done");
    assert_eq!(returns["first"]["variant"], "Pending");

    for input in 0..2 {
        let mut invalid_ordinal = execution.preimage.clone();
        invalid_ordinal.public_transcript_outputs[input] = Fr::from(3u64);
        assert!(invalid_ordinal.check(&relation).is_err());
    }

    let parameter_bytes = fs::read(
        env::var_os("NOCTIUM_CHECKED_ENUM_CAST_PROOF_PARAMETERS")
            .expect("NOCTIUM_CHECKED_ENUM_CAST_PROOF_PARAMETERS"),
    )?;
    let parameters =
        TrustedParameters::from_bytes(&parameter_bytes, PROOF_K, OFFICIAL_SRS_SHA256)?;
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
        .expect("public returns are bound by the communication commitment");
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
