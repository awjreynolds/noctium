#![cfg(feature = "zkir-321")]

use base_crypto::hash::HashOutput;
use coin_structure::contract::ContractAddress;
use noctium_runtime::{Plan, check, create_state, prepare_with_context, zkir::IrSource};
use onchain_runtime::context::QueryContext;
use serde_json::{Value as Json, json};
use std::{collections::BTreeMap, env, fs, path::PathBuf};

fn bytes(value: &[u8]) -> Json {
    json!({"kind":"bytes", "values":value})
}

#[test]
#[ignore = "requires fresh NativeTokenColors artifacts in NOCTIUM_NATIVE_TOKEN_COLORS_DIR"]
fn native_token_and_contract_colors_match_compact() {
    let directory = PathBuf::from(
        env::var_os("NOCTIUM_NATIVE_TOKEN_COLORS_DIR").expect("NOCTIUM_NATIVE_TOKEN_COLORS_DIR"),
    );
    let plan: Plan = serde_json::from_slice(
        &fs::read(directory.join("NativeTokenColors.derive.impact.json")).unwrap(),
    )
    .unwrap();
    let circuit_bytes = fs::read(directory.join("NativeTokenColors.derive.zkir")).unwrap();
    let circuit = IrSource::load(circuit_bytes.as_slice()).unwrap();
    let initial = create_state(&plan, &BTreeMap::new()).unwrap();
    let domain: [u8; 32] = std::array::from_fn(|index| (index + 1) as u8);
    let inputs = BTreeMap::<String, Json>::from([("domain".into(), bytes(&domain))]);
    let parameters = &ledger::structure::INITIAL_PARAMETERS;
    let cases = [
        (
            std::array::from_fn(|index| (index + 1) as u8),
            "f134d9173e664429ea3152bf6097ed6daa96b76357737c1442a008b9ce3e4d3f",
        ),
        (
            [0xa5; 32],
            "91592370010382a8902fc27fa786031af985768817d249f35c77b3678271cd42",
        ),
    ];

    for (address_bytes, expected_color) in cases {
        let address = ContractAddress(HashOutput(address_bytes));
        let context = QueryContext::new(initial.clone(), address);
        let execution = prepare_with_context(&plan, &inputs, context, parameters).unwrap();
        assert_eq!(
            check(&execution, &circuit).unwrap(),
            execution.activity_schedule
        );
        assert_eq!(execution.returns_json()["nativeColor"], bytes(&[0; 32]));
        assert_eq!(
            execution.returns_json()["derivedColor"],
            bytes(&hex::decode(expected_color).unwrap()),
        );
    }
}

#[test]
#[ignore = "requires fresh NativeTokenColors artifacts in NOCTIUM_NATIVE_TOKEN_COLORS_DIR"]
fn explicit_token_color_arguments_and_results_match_compact() {
    let directory = PathBuf::from(
        env::var_os("NOCTIUM_NATIVE_TOKEN_COLORS_DIR").expect("NOCTIUM_NATIVE_TOKEN_COLORS_DIR"),
    );
    let plan: Plan = serde_json::from_slice(
        &fs::read(directory.join("NativeTokenColors.deriveFor.impact.json")).unwrap(),
    )
    .unwrap();
    let circuit =
        IrSource::load(fs::File::open(directory.join("NativeTokenColors.deriveFor.zkir")).unwrap())
            .unwrap();
    assert_eq!(
        plan.circuit
            .inputs
            .iter()
            .map(|input| (input.name.as_str(), input.ty.as_str()))
            .collect::<Vec<_>>(),
        [("domain", "Bytes<32>"), ("contractAddress", "Bytes<32>")],
    );
    assert_eq!(
        plan.returns
            .iter()
            .map(|output| (output.name.as_str(), output.ty.as_str()))
            .collect::<Vec<_>>(),
        [("nativeColor", "Bytes<32>"), ("derivedColor", "Bytes<32>")],
    );

    let initial = create_state(&plan, &BTreeMap::new()).unwrap();
    let address = ContractAddress(HashOutput([9; 32]));
    let parameters = &ledger::structure::INITIAL_PARAMETERS;
    let increasing = std::array::from_fn(|index| (index + 1) as u8);
    let cases = [
        (
            increasing,
            increasing,
            "f134d9173e664429ea3152bf6097ed6daa96b76357737c1442a008b9ce3e4d3f",
        ),
        (
            increasing,
            [0xa5; 32],
            "91592370010382a8902fc27fa786031af985768817d249f35c77b3678271cd42",
        ),
        (
            [0; 32],
            [255; 32],
            "ee4c98312eda93944f99b1462f74552d15fe1224e31533dd4ceaf50950a547d9",
        ),
        (
            [255; 32],
            [0; 32],
            "6290fa06dfb79c6071d8234f95bf3733d8902046bdda1c7a823655ad9c80accf",
        ),
    ];

    for (domain, target, expected_color) in cases {
        let inputs = BTreeMap::<String, Json>::from([
            ("domain".into(), bytes(&domain)),
            ("contractAddress".into(), bytes(&target)),
        ]);
        let context = QueryContext::new(initial.clone(), address);
        let execution = prepare_with_context(&plan, &inputs, context, parameters).unwrap();
        check(&execution, &circuit).unwrap();
        let returns = execution.returns_json();
        assert_eq!(returns["nativeColor"], bytes(&[0; 32]));
        assert_eq!(
            returns["derivedColor"],
            bytes(&hex::decode(expected_color).unwrap())
        );
    }
    for invalid in [
        bytes(&[0; 31]),
        bytes(&[0; 33]),
        json!({"kind":"bytes","values":vec![256;32]}),
    ] {
        let inputs = BTreeMap::<String, Json>::from([
            ("domain".into(), bytes(&[0; 32])),
            ("contractAddress".into(), invalid),
        ]);
        assert!(
            prepare_with_context(
                &plan,
                &inputs,
                QueryContext::new(initial.clone(), address),
                parameters,
            )
            .is_err()
        );
    }
}

#[test]
#[ignore = "requires a verified deriveFor bundle and trusted proof parameters"]
fn token_color_proof_binds_the_exact_public_arguments() -> anyhow::Result<()> {
    use futures::executor::block_on;
    use noctium_runtime::{
        artifacts,
        proof::{PreparedProof, TrustedParameters},
    };
    use rand::{SeedableRng, rngs::StdRng};

    let bundle = artifacts::verify(
        PathBuf::from(env::var("NOCTIUM_NATIVE_TOKEN_COLORS_BUNDLE")?).as_path(),
        Some(&env::var("NOCTIUM_NATIVE_TOKEN_COLORS_MANIFEST_SHA256")?),
    )?;
    let config = |domain: u8, target: u8| {
        serde_json::to_vec(&json!({
            "inputs": {
                "domain": bytes(&[domain; 32]),
                "contractAddress": bytes(&[target; 32]),
            },
            "state": {},
        }))
    };
    let prepare = |domain, target| -> anyhow::Result<PreparedProof> {
        // Test entropy is fixed so only the public arguments change between statements.
        let mut rng = StdRng::from_seed([21; 32]);
        Ok(PreparedProof::from_config(
            &bundle,
            &config(domain, target)?,
            2_000_000_000,
            &mut rng,
        )?)
    };
    let prepared = prepare(0, 255)?;
    let params = TrustedParameters::from_bytes(
        &fs::read(env::var("NOCTIUM_NATIVE_TOKEN_COLORS_PROOF_PARAMETERS")?)?,
        prepared.k(),
        &env::var("NOCTIUM_NATIVE_TOKEN_COLORS_PROOF_PARAMETERS_SHA256")?,
    )?;
    let max_response = 1_048_576;
    let proof =
        block_on(prepared.local_response(&params, max_response, StdRng::from_seed([22; 32])))?;
    prepared.verify_response(&params, &proof, max_response)?;
    for (domain, address) in [(1, 255), (0, 254)] {
        assert!(
            prepare(domain, address)?
                .verify_response(&params, &proof, max_response)
                .is_err()
        );
    }
    Ok(())
}
