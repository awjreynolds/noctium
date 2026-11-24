#![cfg(feature = "zkir-321")]

use anyhow::Result;
use noctium_runtime::{
    Plan, Value, check,
    constructor::construct_state,
    foreign::{ForeignType, ForeignValue},
    prepare,
    zkir::IrSource,
};
use num_bigint::BigUint;
use serde_json::{Value as Json, json};
use std::{collections::BTreeMap, env, fs, path::PathBuf};

fn artifacts() -> PathBuf {
    PathBuf::from(
        env::var_os("NOCTIUM_FOREIGN_FIELD_NEG_INV_DIR")
            .expect("set fresh outputs in NOCTIUM_FOREIGN_FIELD_NEG_INV_DIR"),
    )
}

fn modulus(type_name: &str) -> BigUint {
    for fixture in [
        include_str!("fixtures/foreign-codec/321/encoding.json"),
        include_str!("fixtures/curve25519/321/encoding.json"),
    ] {
        let fixture: Json = serde_json::from_str(fixture).unwrap();
        if let Some(row) = fixture["fields"]
            .as_array()
            .and_then(|fields| fields.iter().find(|row| row["type"] == type_name))
        {
            return BigUint::parse_bytes(row["modulus"].as_str().unwrap().as_bytes(), 10).unwrap();
        }
    }
    panic!("missing modulus for {type_name}");
}

fn bytes32(number: &BigUint) -> [u8; 32] {
    let bytes = number.to_bytes_le();
    assert!(bytes.len() <= 32);
    let mut output = [0u8; 32];
    output[..bytes.len()].copy_from_slice(&bytes);
    output
}

fn foreign_json(ty: ForeignType, value: &BigUint) -> Json {
    Value::Foreign(ForeignValue::from_bytes(ty, &bytes32(value)).unwrap()).public_json()
}

#[test]
#[ignore = "requires fresh ForeignFieldNegInv artifacts and the official k14 SRS"]
fn typed_foreign_field_negation_and_inverse_match_pinned_native_relations() -> Result<()> {
    use futures::executor::block_on;
    use transient_crypto::proofs::{ParamsVerifier, Zkir};
    let directory = artifacts();
    let plan: Plan = serde_json::from_slice(&fs::read(
        directory.join("ForeignFieldNegInv.checkFields.impact.json"),
    )?)?;
    let circuit = IrSource::load(fs::File::open(
        directory.join("ForeignFieldNegInv.checkFields.zkir"),
    )?)?;
    let state = construct_state(&plan, &BTreeMap::new())?;
    let address = coin_structure::contract::ContractAddress::default();
    let fields = [
        (
            "k1Base",
            "k1BaseZero",
            "rejectK1BaseInvZero",
            "k1BaseNeg",
            "k1BaseInv",
            "k1BaseZeroNeg",
            "k1BaseBoundary",
            "k1BaseBoundaryNeg",
            "k1BaseBoundaryInv",
            "Base<Secp256k1>",
            "Secp256k1Base",
            5u8,
        ),
        (
            "k1Scalar",
            "k1ScalarZero",
            "rejectK1ScalarInvZero",
            "k1ScalarNeg",
            "k1ScalarInv",
            "k1ScalarZeroNeg",
            "k1ScalarBoundary",
            "k1ScalarBoundaryNeg",
            "k1ScalarBoundaryInv",
            "Scalar<Secp256k1>",
            "Secp256k1Scalar",
            7u8,
        ),
        (
            "r1Base",
            "r1BaseZero",
            "rejectR1BaseInvZero",
            "r1BaseNeg",
            "r1BaseInv",
            "r1BaseZeroNeg",
            "r1BaseBoundary",
            "r1BaseBoundaryNeg",
            "r1BaseBoundaryInv",
            "Base<Secp256r1>",
            "Secp256r1Base",
            11u8,
        ),
        (
            "r1Scalar",
            "r1ScalarZero",
            "rejectR1ScalarInvZero",
            "r1ScalarNeg",
            "r1ScalarInv",
            "r1ScalarZeroNeg",
            "r1ScalarBoundary",
            "r1ScalarBoundaryNeg",
            "r1ScalarBoundaryInv",
            "Scalar<Secp256r1>",
            "Secp256r1Scalar",
            13u8,
        ),
        (
            "c255Base",
            "c255BaseZero",
            "rejectC255BaseInvZero",
            "c255BaseNeg",
            "c255BaseInv",
            "c255BaseZeroNeg",
            "c255BaseBoundary",
            "c255BaseBoundaryNeg",
            "c255BaseBoundaryInv",
            "Base<Curve25519>",
            "Curve25519Base",
            17u8,
        ),
        (
            "c255Scalar",
            "c255ScalarZero",
            "rejectC255ScalarInvZero",
            "c255ScalarNeg",
            "c255ScalarInv",
            "c255ScalarZeroNeg",
            "c255ScalarBoundary",
            "c255ScalarBoundaryNeg",
            "c255ScalarBoundaryInv",
            "Scalar<Curve25519>",
            "Curve25519Scalar",
            19u8,
        ),
    ];
    let mut inputs = BTreeMap::new();
    let mut expected: BTreeMap<String, Json> = BTreeMap::new();
    for (
        value_name,
        zero_name,
        guard_name,
        neg_name,
        inv_name,
        zero_neg_name,
        boundary_name,
        boundary_neg_name,
        boundary_inv_name,
        type_name,
        source_name,
        value,
    ) in fields
    {
        let ty = ForeignType::parse_source_name(source_name)?;
        let number = BigUint::from(value);
        let zero = BigUint::from(0u8);
        let prime = modulus(type_name);
        inputs.insert(value_name.into(), foreign_json(ty, &number));
        inputs.insert(zero_name.into(), foreign_json(ty, &zero));
        let boundary = &prime - 1u8;
        inputs.insert(boundary_name.into(), foreign_json(ty, &boundary));
        inputs.insert(guard_name.into(), json!(false));
        expected.insert(neg_name.into(), foreign_json(ty, &(&prime - &number)));
        expected.insert(
            inv_name.into(),
            foreign_json(ty, &number.modpow(&(&prime - 2u8), &prime)),
        );
        expected.insert(zero_neg_name.into(), foreign_json(ty, &zero));
        expected.insert(boundary_neg_name.into(), foreign_json(ty, &BigUint::from(1u8)));
        expected.insert(boundary_inv_name.into(), foreign_json(ty, &(&prime - 1u8)));
    }

    let execution = prepare(
        &plan,
        &inputs,
        &state,
        &ledger::structure::INITIAL_PARAMETERS,
        address,
    )?;
    check(&execution, &circuit)?;
    let actual = execution.returns_json();
    assert_eq!(actual.len(), expected.len(), "unexpected native return set");
    for (name, value) in &expected {
        assert_eq!(actual.get(name), Some(value), "return mismatch for {name}");
    }
    assert_eq!(execution.after.state.get_ref(), state.get_ref());

    for (_, _, guard_name, _, _, _, _, _, _, _, _, _) in fields {
        let mut zero_inverse = inputs.clone();
        zero_inverse.insert(guard_name.into(), json!(true));
        assert!(
            prepare(
                &plan,
                &zero_inverse,
                &state,
                &ledger::structure::INITIAL_PARAMETERS,
                address,
            )
            .is_err(),
            "zero inverse must reject for {guard_name}"
        );
    }

    let readable_plan: Plan = serde_json::from_slice(&fs::read(
        directory.join("ForeignFieldNegInv.checkReadableFields.impact.json"),
    )?)?;
    let readable_circuit = IrSource::load(fs::File::open(
        directory.join("ForeignFieldNegInv.checkReadableFields.zkir"),
    )?)?;
    let readable_state = construct_state(&readable_plan, &BTreeMap::new())?;
    let readable_value = BigUint::from(5u8);
    let readable_modulus = modulus("Base<Secp256k1>");
    let readable_inputs = BTreeMap::from([
        (
            "input.value.$curve0".into(),
            json!("4"),
        ),
        (
            "input.value.$curve1".into(),
            json!("0"),
        ),
    ]);
    let readable_execution = prepare(
        &readable_plan,
        &readable_inputs,
        &readable_state,
        &ledger::structure::INITIAL_PARAMETERS,
        address,
    )?;
    check(&readable_execution, &readable_circuit)?;
    assert_eq!(
        readable_execution.returns_json(),
        BTreeMap::from([
            (
                "neg".to_owned(),
                foreign_json(
                    ForeignType::parse_source_name("Secp256k1Base")?,
                    &(&readable_modulus - &readable_value),
                ),
            ),
            (
                "inv".to_owned(),
                foreign_json(
                    ForeignType::parse_source_name("Secp256k1Base")?,
                    &readable_value.modpow(&(&readable_modulus - 2u8), &readable_modulus),
                ),
            ),
        ])
    );

    let parameter_bytes = fs::read(
        env::var_os("NOCTIUM_FOREIGN_FIELD_NEG_INV_K14_SRS")
            .expect("set NOCTIUM_FOREIGN_FIELD_NEG_INV_K14_SRS to the official k14 SRS"),
    )?;
    const K14_SRS_SHA256: &str =
        "fc253016885ec830e97808c9ec920bb5cab5c21af590380a6cb5eb0538e2b244";
    assert_eq!(circuit.k(), 14);
    let parameters = noctium_runtime::proof::TrustedParameters::from_bytes(
        &parameter_bytes,
        circuit.k(),
        K14_SRS_SHA256,
    )?;
    let verifier_parameters = ParamsVerifier::read(parameter_bytes.as_slice())?;
    let (prover_key, verifier_key) = block_on(circuit.keygen(&parameters))?;
    let (proof, statement, activity) = block_on(circuit.prove(
        rand::rngs::OsRng,
        &parameters,
        prover_key,
        &execution.preimage,
    ))?;
    assert_eq!(activity, execution.activity_schedule);
    verifier_key.verify(&verifier_parameters, &proof, statement.iter().copied())?;
    let (commitment, _) = execution
        .preimage
        .communications_commitment
        .expect("foreign arithmetic results bind through the communication commitment");
    assert!(statement.contains(&commitment));
    let mut changed_statement = statement;
    let commitment_index = changed_statement
        .iter()
        .position(|value| *value == commitment)
        .expect("statement contains the output commitment");
    changed_statement[commitment_index] = commitment + transient_crypto::curve::Fr::from(1u64);
    assert!(verifier_key
        .verify(
            &verifier_parameters,
            &proof,
            changed_statement.iter().copied(),
        )
        .is_err());
    Ok(())
}
