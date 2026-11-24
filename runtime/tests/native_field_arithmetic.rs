#![cfg(feature = "zkir-321")]

use anyhow::Result;
use coin_structure::contract::ContractAddress;
use noctium_runtime::{Plan, check, create_state, prepare, zkir::IrSource};
use num_bigint::BigUint;
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

fn mixed_artifacts(directory: &PathBuf, entrypoint: &str) -> Result<(Plan, IrSource)> {
    let stem = format!("MixedFieldArithmetic.{entrypoint}");
    let plan: Plan =
        serde_json::from_slice(&fs::read(directory.join(format!("{stem}.impact.json")))?)?;
    assert!(noctium_runtime::profile::validate_plan(
        plan.target.as_deref(),
        plan.target_profile.as_ref()
    ));
    let circuit = IrSource::load(fs::read(directory.join(format!("{stem}.zkir")))?.as_slice())?;
    Ok((plan, circuit))
}

fn mixed_inputs(field_value: &BigUint, amount: &BigUint, zero: u8) -> BTreeMap<String, Json> {
    BTreeMap::from([
        ("fieldValue".into(), json!(field_value.to_str_radix(10))),
        ("amount".into(), json!(amount.to_str_radix(10))),
        ("zero".into(), json!(zero.to_string())),
    ])
}

fn mixed_expected(
    field_value: &BigUint,
    amount: &BigUint,
    modulus: &BigUint,
) -> BTreeMap<String, Json> {
    let sum = (field_value + amount) % modulus;
    let difference_field_first = (field_value + modulus - amount) % modulus;
    let difference_uint_first = (amount + modulus - field_value) % modulus;
    let product = (field_value * amount) % modulus;
    let equal = field_value == amount;
    BTreeMap::from([
        ("sumFieldFirst".into(), json!(sum.to_str_radix(10))),
        ("sumUIntFirst".into(), json!(sum.to_str_radix(10))),
        (
            "differenceFieldFirst".into(),
            json!(difference_field_first.to_str_radix(10)),
        ),
        (
            "differenceUIntFirst".into(),
            json!(difference_uint_first.to_str_radix(10)),
        ),
        ("productFieldFirst".into(), json!(product.to_str_radix(10))),
        ("productUIntFirst".into(), json!(product.to_str_radix(10))),
        ("withZero".into(), json!(field_value.to_str_radix(10))),
        ("equalFieldFirst".into(), json!(equal)),
        ("equalUIntFirst".into(), json!(equal)),
        ("notEqualFieldFirst".into(), json!(!equal)),
        ("notEqualUIntFirst".into(), json!(!equal)),
    ])
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

#[test]
#[ignore = "requires fresh MixedFieldArithmetic outputs and the official k8 SRS"]
fn mixed_native_field_and_uint_arithmetic_matches_both_frontends() -> Result<()> {
    use futures::executor::block_on;
    use transient_crypto::proofs::{ParamsVerifier, Zkir};

    let directory = PathBuf::from(
        std::env::var_os("NOCTIUM_MIXED_FIELD_ARITHMETIC_DIR")
            .expect("set NOCTIUM_MIXED_FIELD_ARITHMETIC_DIR to fresh compiler outputs"),
    );
    let (ordinary_plan, ordinary_circuit) = mixed_artifacts(&directory, "ordinary")?;
    let (readable_plan, readable_circuit) = mixed_artifacts(&directory, "readable")?;
    let ordinary_state = create_state(&ordinary_plan, &BTreeMap::new())?;
    let readable_state = create_state(&readable_plan, &BTreeMap::new())?;
    let modulus = BigUint::parse_bytes(noctium_runtime::MODULUS.as_bytes(), 10).unwrap();
    let modulus_minus_one = &modulus - 1u8;
    let uint_maximum: BigUint = (BigUint::from(1u8) << 248usize) - BigUint::from(1u8);
    let vectors = [
        (BigUint::from(0u8), BigUint::from(0u8)),
        (modulus_minus_one.clone(), BigUint::from(1u8)),
        (modulus_minus_one, uint_maximum.clone()),
        (uint_maximum.clone(), uint_maximum),
    ];

    for (field_value, amount) in vectors {
        let inputs = mixed_inputs(&field_value, &amount, 0);
        let expected = mixed_expected(&field_value, &amount, &modulus);
        for (plan, circuit, state, route) in [
            (
                &ordinary_plan,
                &ordinary_circuit,
                &ordinary_state,
                "ordinary",
            ),
            (
                &readable_plan,
                &readable_circuit,
                &readable_state,
                "readable",
            ),
        ] {
            let execution = prepare(
                plan,
                &inputs,
                state,
                &ledger::structure::INITIAL_PARAMETERS,
                ContractAddress::default(),
            )?;
            assert_eq!(check(&execution, circuit)?, execution.activity_schedule);
            assert_eq!(
                execution.returns_json(),
                expected,
                "{route}: {field_value}, {amount}"
            );
        }
    }

    for (plan, state, route) in [
        (&ordinary_plan, &ordinary_state, "ordinary"),
        (&readable_plan, &readable_state, "readable"),
    ] {
        let invalid_zero = BTreeMap::from([
            ("fieldValue".into(), json!("0")),
            ("amount".into(), json!("0")),
            ("zero".into(), json!("1")),
        ]);
        assert!(
            prepare(
                plan,
                &invalid_zero,
                state,
                &ledger::structure::INITIAL_PARAMETERS,
                ContractAddress::default(),
            )
            .is_err(),
            "{route} must reject one for the zero-only UIntRange"
        );
    }

    let proof_field_value = &modulus - 1u8;
    let proof_amount = BigUint::from(1u8);
    let proof_execution = prepare(
        &ordinary_plan,
        &mixed_inputs(&proof_field_value, &proof_amount, 0),
        &ordinary_state,
        &ledger::structure::INITIAL_PARAMETERS,
        ContractAddress::default(),
    )?;
    assert_eq!(
        check(&proof_execution, &ordinary_circuit)?,
        proof_execution.activity_schedule
    );
    let parameter_bytes = fs::read(
        std::env::var_os("NOCTIUM_MIXED_FIELD_ARITHMETIC_K8_SRS")
            .expect("set NOCTIUM_MIXED_FIELD_ARITHMETIC_K8_SRS to the official k8 SRS"),
    )?;
    const K8_SRS_SHA256: &str = "909b707551eaaea79828e883cde6fc46ab15986c3b1d791bed462c9e2805c933";
    assert_eq!(ordinary_circuit.k(), 8);
    let parameters = noctium_runtime::proof::TrustedParameters::from_bytes(
        &parameter_bytes,
        ordinary_circuit.k(),
        K8_SRS_SHA256,
    )?;
    let verifier_parameters = ParamsVerifier::read(parameter_bytes.as_slice())?;
    let (prover_key, verifier_key) = block_on(ordinary_circuit.keygen(&parameters))?;
    let (proof, statement, activity) = block_on(ordinary_circuit.prove(
        rand::rngs::OsRng,
        &parameters,
        prover_key,
        &proof_execution.preimage,
    ))?;
    assert_eq!(activity, proof_execution.activity_schedule);
    verifier_key.verify(&verifier_parameters, &proof, statement.iter().copied())?;
    let (commitment, _) = proof_execution
        .preimage
        .communications_commitment
        .expect("mixed arithmetic returns bind through a communication commitment");
    assert_eq!(statement.get(1), Some(&commitment));
    let mut changed_statement = statement;
    changed_statement[1] = commitment + Fr::from(1u64);
    assert!(
        verifier_key
            .verify(
                &verifier_parameters,
                &proof,
                changed_statement.iter().copied(),
            )
            .is_err()
    );

    Ok(())
}
