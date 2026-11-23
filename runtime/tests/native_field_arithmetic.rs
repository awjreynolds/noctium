#![cfg(feature = "zkir-321")]

use anyhow::Result;
use coin_structure::contract::ContractAddress;
use noctium_runtime::{Plan, check, create_state, prepare, zkir::IrSource};
use serde_json::{Value as Json, json};
use std::{collections::BTreeMap, fs, path::PathBuf};
use transient_crypto::curve::Fr;

// Compile with:
// lake exe noctium compile tests/FieldArithmetic.lean --target profiles/midnight-ledger-9-zkir-3.2.1-target.json --emit ledger --output build/experiments/field-arithmetic-native
// Then run with NOCTIUM_NATIVE_FIELD_ARITHMETIC_DIR pointing at that output.
fn artifacts() -> Result<(Plan, IrSource)> {
    let directory = PathBuf::from(
        std::env::var_os("NOCTIUM_NATIVE_FIELD_ARITHMETIC_DIR")
            .expect("set NOCTIUM_NATIVE_FIELD_ARITHMETIC_DIR to fresh compiler outputs"),
    );
    let plan: Plan = serde_json::from_slice(&fs::read(
        directory.join("NativeFieldArithmetic.calculate.impact.json"),
    )?)?;
    assert!(noctium_runtime::profile::validate_plan(
        plan.target.as_deref(),
        plan.target_profile.as_ref()
    ));
    let circuit = IrSource::load(
        fs::read(directory.join("NativeFieldArithmetic.calculate.zkir"))?.as_slice(),
    )?;
    Ok((plan, circuit))
}

fn inputs(left: &str, right: &str) -> BTreeMap<String, Json> {
    BTreeMap::from([("left".into(), json!(left)), ("right".into(), json!(right))])
}

#[test]
#[ignore = "requires fresh FieldArithmetic outputs in NOCTIUM_NATIVE_FIELD_ARITHMETIC_DIR"]
fn source_native_field_arithmetic_matches_modular_relation_and_rejects_forged_witness() -> Result<()>
{
    let (plan, circuit) = artifacts()?;
    let initial = create_state(&plan, &BTreeMap::new())?;
    let modulus_minus_one =
        "52435875175126190479447740508185965837690552500527637822603658699938581184512";
    let modulus_minus_two =
        "52435875175126190479447740508185965837690552500527637822603658699938581184511";
    let cases = [
        (
            modulus_minus_one,
            "1",
            BTreeMap::from([
                ("returnedSum".into(), json!("0")),
                ("returnedDifference".into(), json!(modulus_minus_two)),
                ("returnedProduct".into(), json!(modulus_minus_one)),
                ("returnedSubtractFromZero".into(), json!("1")),
                ("returnedEqual".into(), json!(false)),
                ("returnedNotEqual".into(), json!(true)),
            ]),
        ),
        (
            modulus_minus_one,
            modulus_minus_one,
            BTreeMap::from([
                ("returnedSum".into(), json!(modulus_minus_two)),
                ("returnedDifference".into(), json!("0")),
                ("returnedProduct".into(), json!("1")),
                ("returnedSubtractFromZero".into(), json!("1")),
                ("returnedEqual".into(), json!(true)),
                ("returnedNotEqual".into(), json!(false)),
            ]),
        ),
        (
            "0",
            "1",
            BTreeMap::from([
                ("returnedSum".into(), json!("1")),
                ("returnedDifference".into(), json!(modulus_minus_one)),
                ("returnedProduct".into(), json!("0")),
                ("returnedSubtractFromZero".into(), json!("0")),
                ("returnedEqual".into(), json!(false)),
                ("returnedNotEqual".into(), json!(true)),
            ]),
        ),
    ];
    for (left, right, expected) in cases {
        let mut execution = prepare(
            &plan,
            &inputs(left, right),
            &initial,
            &ledger::structure::INITIAL_PARAMETERS,
            ContractAddress::default(),
        )?;
        assert_eq!(check(&execution, &circuit)?, execution.activity_schedule);
        assert_eq!(execution.returns_json(), expected, "{left} + {right}");

        if left == modulus_minus_one && right == "1" {
            let private_names: Vec<_> = plan
                .circuit
                .inputs
                .iter()
                .filter(|input| input.visibility == "private")
                .map(|input| input.name.as_str())
                .collect();
            let input_position = private_names
                .iter()
                .position(|name| *name == "left")
                .unwrap();
            let original = execution.preimage.private_transcript[input_position];
            execution.preimage.private_transcript[input_position] = Fr::from(0u64);
            assert!(
                check(&execution, &circuit).is_err(),
                "native relation accepted a forged field witness"
            );
            execution.preimage.private_transcript[input_position] = original;
            check(&execution, &circuit)?;
        }
    }

    Ok(())
}
