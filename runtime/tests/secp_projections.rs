#![cfg(feature = "zkir-321")]

use noctium_runtime::{Plan, check, create_state, prepare, proof::TrustedParameters, zkir::IrSource};
use serde::Deserialize;
use serde_json::{Value, json};
use std::{collections::BTreeMap, env, fs, fs::File, path::Path, path::PathBuf};

const SECP_PROJECTIONS_K: u8 = 12;
const SECP_PROJECTIONS_RELATION_SHA256: &str =
    "69ca97ac286d3e464e40f49265ef66f22e7aabfcd9085c34eaf8ca73ebb23c68";
const OFFICIAL_K12_SRS_SHA256: &str =
    "ef08eb3fcf62df8f72c515cffa027e681808b530cb016eea104115545ef6d5c8";

#[derive(Deserialize)]
struct Reference {
    inputs: BTreeMap<String, Value>,
    outputs: BTreeMap<String, Value>,
}

fn artifacts(directory: &Path) -> anyhow::Result<(Plan, IrSource)> {
    let directory = directory.join("lean");
    let plan: Plan = serde_json::from_reader(File::open(
        directory.join("SecpProjections.inspect.impact.json"),
    )?)?;
    let circuit = IrSource::load(File::open(
        directory.join("SecpProjections.inspect.zkir"),
    )?)?;
    Ok((plan, circuit))
}

#[test]
#[ignore = "requires fresh Lean and Compact outputs in NOCTIUM_SECP_PROJECTIONS_DIR"]
fn native_secp_points_scalars_and_affine_coordinates_match_compact() -> anyhow::Result<()> {
    let directory = PathBuf::from(std::env::var("NOCTIUM_SECP_PROJECTIONS_DIR")?);
    let reference: Reference =
        serde_json::from_reader(File::open(directory.join("compact.json"))?)?;
    let (plan, circuit) = artifacts(&directory)?;
    let initial = create_state(&plan, &BTreeMap::new())?;
    let parameters = &ledger::structure::INITIAL_PARAMETERS;
    let address = coin_structure::contract::ContractAddress::default();
    let execution = prepare(&plan, &reference.inputs, &initial, parameters, address)?;
    check(&execution, &circuit)?;
    assert_eq!(execution.returns_json(), reference.outputs);

    for (name, ty) in [
        ("kPoint", "Secp256k1Point"),
        ("rPoint", "Secp256r1Point"),
    ] {
        let mut identity = reference.inputs.clone();
        identity.insert(
            name.into(),
            json!({"kind":"foreign", "type":ty, "bytes":vec![0; 33]}),
        );
        let Err(error) = prepare(&plan, &identity, &initial, parameters, address) else {
            anyhow::bail!("native projection must reject the {ty} identity");
        };
        assert!(
            format!("{error:#}").contains("Cannot extract coordinates"),
            "{error:#}"
        );
    }

    let mut invalid = reference.inputs;
    invalid.insert("kPoint".into(), invalid["rPoint"].clone());
    assert!(prepare(&plan, &invalid, &initial, parameters, address).is_err());
    Ok(())
}

#[test]
#[ignore = "requires fresh Lean and Compact outputs in NOCTIUM_SECP_PROJECTIONS_DIR and the official k12 SRS in NOCTIUM_SECP_PROJECTIONS_PROOF_PARAMETERS"]
fn secp_projections_generate_and_bind_native_proof() -> anyhow::Result<()> {
    use futures::executor::block_on;
    use rand::rngs::OsRng;
    use sha2::{Digest, Sha256};
    use transient_crypto::{curve::Fr, proofs::{ParamsVerifier, Zkir}};

    let directory = PathBuf::from(
        env::var_os("NOCTIUM_SECP_PROJECTIONS_DIR")
            .expect("NOCTIUM_SECP_PROJECTIONS_DIR must point to fresh compiler outputs"),
    );
    let parameter_bytes = fs::read(
        env::var_os("NOCTIUM_SECP_PROJECTIONS_PROOF_PARAMETERS")
            .expect("NOCTIUM_SECP_PROJECTIONS_PROOF_PARAMETERS must point to the official k12 SRS"),
    )?;
    let relation_bytes = fs::read(directory.join("lean/SecpProjections.inspect.zkir"))?;
    assert_eq!(
        hex::encode(Sha256::digest(&relation_bytes)),
        SECP_PROJECTIONS_RELATION_SHA256
    );
    let relation = IrSource::load(relation_bytes.as_slice())?;
    assert_eq!(relation.k(), SECP_PROJECTIONS_K);
    let parameters = TrustedParameters::from_bytes(
        &parameter_bytes,
        SECP_PROJECTIONS_K,
        OFFICIAL_K12_SRS_SHA256,
    )?;
    assert_eq!(parameters.sha256(), OFFICIAL_K12_SRS_SHA256);
    let verifier_parameters = ParamsVerifier::read(parameter_bytes.as_slice())?;

    let reference: Reference =
        serde_json::from_reader(File::open(directory.join("compact.json"))?)?;
    let plan: Plan = serde_json::from_reader(File::open(
        directory.join("lean/SecpProjections.inspect.impact.json"),
    )?)?;
    let initial = create_state(&plan, &BTreeMap::new())?;
    let execution = prepare(
        &plan,
        &reference.inputs,
        &initial,
        &ledger::structure::INITIAL_PARAMETERS,
        coin_structure::contract::ContractAddress::default(),
    )?;
    assert_eq!(check(&execution, &relation)?, execution.activity_schedule);
    assert_eq!(execution.returns_json(), reference.outputs);

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
        .expect("the native projection binds its communicated return values");
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
        "Secp projection proof passed: k={}, relation_sha256={}, srs_sha256={}, proof_bytes={}, altered_return_commitment=rejected",
        SECP_PROJECTIONS_K,
        SECP_PROJECTIONS_RELATION_SHA256,
        parameters.sha256(),
        proof.0.len(),
    );
    Ok(())
}
