#![cfg(feature = "zkir-321")]

use anyhow::Result;
use coin_structure::contract::ContractAddress;
use futures::executor::block_on;
use noctium_runtime::{
    Plan, check, create_state, prepare, proof::TrustedParameters, zkir::IrSource,
};
use rand::rngs::OsRng;
use serde_json::json;
use std::{collections::BTreeMap, env, fs, fs::File, path::PathBuf};
use transient_crypto::{
    curve::Fr,
    proofs::{ParamsVerifier, Zkir},
};

#[test]
#[ignore = "requires fresh PureHelpers artifacts and official K6 parameters"]
fn declared_pure_helper_preserves_its_assertion_and_checked_cast() -> Result<()> {
    let directory =
        PathBuf::from(env::var_os("NOCTIUM_PURE_HELPERS_DIR").expect("NOCTIUM_PURE_HELPERS_DIR"));
    let plan: Plan = serde_json::from_reader(File::open(
        directory.join("PureHelpers.calculate.impact.json"),
    )?)?;
    let circuit = IrSource::load(File::open(directory.join("PureHelpers.calculate.zkir"))?)?;
    let state = create_state(&plan, &BTreeMap::new())?;

    let evaluate = |value: &str, expected: &str| {
        prepare(
            &plan,
            &BTreeMap::from([
                ("value".into(), json!(value)),
                ("expected".into(), json!(expected)),
            ]),
            &state,
            &ledger::structure::INITIAL_PARAMETERS,
            ContractAddress::default(),
        )
    };
    for (input, output) in [("7", "8"), ("255", "256")] {
        let execution = evaluate(input, input)?;
        assert_eq!(check(&execution, &circuit)?, execution.activity_schedule);
        assert_eq!(execution.returns_json()["answer"], json!(output));
        assert_eq!(execution.after.state, state);
    }
    for (value, expected) in [("7", "8"), ("256", "256")] {
        if let Ok(execution) = evaluate(value, expected) {
            assert!(check(&execution, &circuit).is_err());
        }
    }
    let execution = evaluate("7", "7")?;
    let parameter_bytes =
        fs::read(env::var_os("NOCTIUM_PURE_HELPERS_K6_SRS").expect("NOCTIUM_PURE_HELPERS_K6_SRS"))?;
    const K6_SRS_SHA256: &str = "cf2ad6be7d0fedf5bec2aaa35f6be4aca33053d74268fdf5aa54fcb2891ea6df";
    assert_eq!(circuit.k(), 6);
    let parameters = TrustedParameters::from_bytes(&parameter_bytes, 6, K6_SRS_SHA256)?;
    let verifier_parameters = ParamsVerifier::read(parameter_bytes.as_slice())?;
    let (prover_key, verifier_key) = block_on(circuit.keygen(&parameters))?;
    let (proof, mut statement, activity) =
        block_on(circuit.prove(OsRng, &parameters, prover_key, &execution.preimage))?;
    assert_eq!(activity, execution.activity_schedule);
    let (commitment, _) = execution.preimage.communications_commitment.unwrap();
    assert_eq!(statement.get(1), Some(&commitment));
    verifier_key.verify(&verifier_parameters, &proof, statement.iter().copied())?;
    statement[1] = commitment + Fr::from(1u64);
    assert!(
        verifier_key
            .verify(&verifier_parameters, &proof, statement.iter().copied())
            .is_err()
    );
    Ok(())
}

#[test]
#[ignore = "requires fresh ReadableLinkedHelpers artifacts"]
fn linked_readable_helpers_preserve_native_argument_order() -> Result<()> {
    let directory = PathBuf::from(
        env::var_os("NOCTIUM_READABLE_LINKED_HELPERS_DIR")
            .expect("NOCTIUM_READABLE_LINKED_HELPERS_DIR"),
    );
    let plan: Plan = serde_json::from_reader(File::open(
        directory.join("LinkedHelperContract.calculate.impact.json"),
    )?)?;
    let circuit = IrSource::load(File::open(
        directory.join("LinkedHelperContract.calculate.zkir"),
    )?)?;
    let state = create_state(&plan, &BTreeMap::new())?;
    for (x, y, result) in [("7", "2", "207"), ("2", "7", "702")] {
        let execution = prepare(
            &plan,
            &BTreeMap::from([("x".into(), json!(x)), ("y".into(), json!(y))]),
            &state,
            &ledger::structure::INITIAL_PARAMETERS,
            ContractAddress::default(),
        )?;
        assert_eq!(check(&execution, &circuit)?, execution.activity_schedule);
        assert_eq!(execution.returns_json()["result"], json!(result));
        assert_eq!(execution.after.state, state);
    }
    Ok(())
}
