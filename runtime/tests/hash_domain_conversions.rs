#![cfg(feature = "zkir-321")]

use coin_structure::contract::ContractAddress;
use noctium_runtime::{MODULUS, Plan, check, create_state, prepare, zkir::IrSource};
use num_bigint::BigUint;
use serde_json::json;
use std::{collections::BTreeMap, fs::File, path::PathBuf};

#[test]
#[ignore = "requires freshly emitted hash conversion artifacts"]
fn hash_domain_conversions_match_compact_boundaries() -> anyhow::Result<()> {
    let artifacts = PathBuf::from(
        std::env::var_os("NOCTIUM_HASH_DOMAIN_CONVERSIONS_DIR")
            .expect("set the fresh hash conversion artifact directory"),
    );
    let plan: Plan = serde_json::from_reader(File::open(
        artifacts.join("HashDomainConversions.inspect.impact.json"),
    )?)?;
    let circuit = IrSource::load(File::open(
        artifacts.join("HashDomainConversions.inspect.zkir"),
    )?)?;
    assert_eq!(
        plan.circuit
            .inputs
            .iter()
            .map(|input| (
                input.name.as_str(),
                input.ty.as_str(),
                input.visibility.as_str()
            ))
            .collect::<Vec<_>>(),
        [
            ("digest", "Bytes<32>", "private"),
            ("field", "Native", "private")
        ],
    );
    assert_eq!(
        plan.returns
            .iter()
            .map(|value| (
                value.name.as_str(),
                value.ty.as_str(),
                value.visibility.as_str()
            ))
            .collect::<Vec<_>>(),
        [
            ("truncated", "Native", "public"),
            ("encoded", "Bytes<32>", "public")
        ],
    );
    let state = create_state(&plan, &BTreeMap::new())?;
    let params = &ledger::structure::INITIAL_PARAMETERS;
    let modulus: BigUint = MODULUS.parse()?;
    let truncated = BigUint::from_bytes_le(&[255; 31]).to_string();
    let inputs = |high_byte, field: &BigUint| {
        let mut digest = [255u8; 32];
        digest[31] = high_byte;
        BTreeMap::from([
            ("digest".into(), json!({"kind":"bytes", "values":digest})),
            ("field".into(), json!(field.to_string())),
        ])
    };

    for (high_byte, field) in [(0, BigUint::from(0u8)), (255, &modulus - 1u8)] {
        let execution = prepare(
            &plan,
            &inputs(high_byte, &field),
            &state,
            params,
            ContractAddress::default(),
        )?;
        check(&execution, &circuit)?;
        let mut encoded = field.to_bytes_le();
        encoded.resize(32, 0);
        encoded[31] = 0;
        assert_eq!(execution.returns_json()["truncated"], json!(truncated));
        assert_eq!(
            execution.returns_json()["encoded"],
            json!({"kind":"bytes", "values":encoded})
        );
    }

    assert!(
        prepare(
            &plan,
            &inputs(255, &modulus),
            &state,
            params,
            ContractAddress::default(),
        )
        .is_err()
    );
    let valid = inputs(255, &(&modulus - 1u8));
    for length in [31, 33] {
        let mut malformed = valid.clone();
        malformed.insert(
            "digest".into(),
            json!({"kind":"bytes","values":vec![0; length]}),
        );
        assert!(
            prepare(
                &plan,
                &malformed,
                &state,
                params,
                ContractAddress::default()
            )
            .is_err()
        );
    }
    let mut malformed = valid;
    malformed.insert("field".into(), json!("01"));
    assert!(
        prepare(
            &plan,
            &malformed,
            &state,
            params,
            ContractAddress::default()
        )
        .is_err()
    );
    Ok(())
}

#[test]
#[ignore = "requires trusted parameters and the authenticated hash conversion bundle"]
fn hash_conversion_proof_binds_disclosed_results() -> anyhow::Result<()> {
    use futures::executor::block_on;
    use noctium_runtime::{
        artifacts,
        proof::{PreparedProof, TrustedParameters},
    };
    use rand::{SeedableRng, rngs::StdRng};
    use std::{env, fs};

    let bundle = artifacts::verify(
        PathBuf::from(env::var("NOCTIUM_HASH_DOMAIN_CONVERSIONS_BUNDLE")?).as_path(),
        Some(&env::var(
            "NOCTIUM_HASH_DOMAIN_CONVERSIONS_MANIFEST_SHA256",
        )?),
    )?;
    let field = (&MODULUS.parse::<BigUint>()? - 1u8).to_string();
    let prepare = |digest: [u8; 32], field: &str| {
        let config = serde_json::to_vec(&json!({
            "inputs": {"digest": {"kind":"bytes","values":digest}, "field": field},
            "state": {},
        }))?;
        // Keep public context and communication randomness identical across witnesses.
        let mut rng = StdRng::from_seed([31; 32]);
        Ok::<_, anyhow::Error>(PreparedProof::from_config(
            &bundle,
            &config,
            2_000_000_000,
            &mut rng,
        )?)
    };
    let digest = [255; 32];
    let prepared = prepare(digest, &field)?;
    let parameters = TrustedParameters::from_bytes(
        &fs::read(env::var(
            "NOCTIUM_HASH_DOMAIN_CONVERSIONS_PROOF_PARAMETERS",
        )?)?,
        prepared.k(),
        &env::var("NOCTIUM_HASH_DOMAIN_CONVERSIONS_PROOF_PARAMETERS_SHA256")?,
    )?;
    let proof =
        block_on(prepared.local_response(&parameters, 1_048_576, StdRng::from_seed([32; 32])))?;
    prepared.verify_response(&parameters, &proof, 1_048_576)?;

    let mut high_byte_only = digest;
    high_byte_only[31] = 0;
    prepare(high_byte_only, &field)?.verify_response(&parameters, &proof, 1_048_576)?;

    let mut changed_result = digest;
    changed_result[0] = 0;
    assert!(
        prepare(changed_result, &field)?
            .verify_response(&parameters, &proof, 1_048_576)
            .is_err()
    );
    assert!(
        prepare(digest, "0")?
            .verify_response(&parameters, &proof, 1_048_576)
            .is_err()
    );
    Ok(())
}
