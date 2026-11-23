#![cfg(feature = "zkir-321")]

use anyhow::Result;
use coin_structure::contract::ContractAddress;
use noctium_runtime::{
    Plan, Value, check, create_state,
    foreign::{ForeignFamily, ForeignRole, ForeignType, ForeignValue},
    prepare,
    proof::TrustedParameters,
    zkir::IrSource,
};
use num_bigint::BigUint;
use onchain_runtime::state::ChargedState;
use rand::rngs::OsRng;
use std::{
    collections::BTreeMap,
    env, fs,
    path::{Path, PathBuf},
};
use transient_crypto::curve::Fr;
use transient_crypto::proofs::{ParamsVerifier, Zkir};

fn coordinate(value: &str) -> ForeignValue {
    let number = BigUint::parse_bytes(value.as_bytes(), 10).expect("decimal coordinate");
    let mut bytes = number.to_bytes_le();
    assert!(bytes.len() <= 32);
    bytes.resize(32, 0);
    ForeignValue::from_bytes(
        ForeignType::new(ForeignFamily::Curve25519, ForeignRole::Base),
        &bytes,
    )
    .expect("valid Curve25519Base coordinate")
}

fn point(bytes: &[u8; 32]) -> ForeignValue {
    ForeignValue::from_bytes(
        ForeignType::new(ForeignFamily::Curve25519, ForeignRole::Point),
        bytes,
    )
    .expect("valid Curve25519Point")
}

fn generator_vector() -> (ForeignValue, ForeignValue, ForeignValue) {
    let mut bytes = [0x66; 32];
    bytes[0] = 0x58;
    (
        point(&bytes),
        coordinate("15112221349535400772501151409588531511454012693041857206046113283949847762202"),
        coordinate("46316835694926478169428394003475163141307993866256225615783033603165251855960"),
    )
}

fn check_projection(
    plan: &Plan,
    relation: &IrSource,
    state: &ChargedState<noctium_runtime::Db>,
    input: ForeignValue,
    x: ForeignValue,
    y: ForeignValue,
) -> Result<()> {
    let inputs = BTreeMap::from([("point".into(), Value::Foreign(input).public_json())]);
    let mut execution = prepare(
        plan,
        &inputs,
        state,
        &ledger::structure::INITIAL_PARAMETERS,
        ContractAddress::default(),
    )?;
    assert_eq!(check(&execution, relation)?, execution.activity_schedule);
    assert_eq!(execution.after.state.get_ref(), state.get_ref());
    assert_eq!(
        execution.returns(),
        [
            ("x".into(), Value::Foreign(x)),
            ("y".into(), Value::Foreign(y)),
        ]
    );
    let output = &mut execution.preimage.public_transcript_outputs[0];
    *output = *output + Fr::from(1u64);
    assert!(check(&execution, relation).is_err());
    Ok(())
}

fn fixture(directory: &Path) -> Result<(Plan, IrSource)> {
    let stem = "Curve25519ProjectionParity.project";
    let plan: Plan =
        serde_json::from_slice(&fs::read(directory.join(format!("{stem}.impact.json")))?)?;
    let relation = IrSource::load(fs::read(directory.join(format!("{stem}.zkir")))?.as_slice())?;
    Ok((plan, relation))
}

#[test]
#[ignore = "requires fresh Curve25519ProjectionParity artifacts in NOCTIUM_CURVE25519_PROJECTION_DIR"]
fn curve25519_point_projection_matches_compact_coordinates() -> Result<()> {
    let directory = PathBuf::from(std::env::var("NOCTIUM_CURVE25519_PROJECTION_DIR")?);
    let (plan, relation) = fixture(&directory)?;
    assert_eq!(plan.entrypoint, "project");
    assert_eq!(plan.target.as_deref(), Some("midnight-ledger-9-zkir-3.2.1"));
    assert_eq!(plan.circuit.inputs.len(), 1);
    assert_eq!(plan.circuit.inputs[0].name, "point");
    assert_eq!(plan.circuit.inputs[0].ty, "Curve25519Point");
    assert_eq!(
        plan.returns
            .iter()
            .map(|output| (output.name.as_str(), output.ty.as_str()))
            .collect::<Vec<_>>(),
        [("x", "Curve25519Base"), ("y", "Curve25519Base")]
    );

    let initial = create_state(&plan, &BTreeMap::new())?;
    let (generator, generator_x, generator_y) = generator_vector();
    let point_type = ForeignType::new(ForeignFamily::Curve25519, ForeignRole::Point);
    let identity = ForeignValue::zero(point_type)?;

    check_projection(
        &plan,
        &relation,
        &initial,
        generator,
        generator_x,
        generator_y,
    )?;
    check_projection(
        &plan,
        &relation,
        &initial,
        identity,
        coordinate("0"),
        coordinate("1"),
    )?;
    Ok(())
}

#[test]
#[ignore = "requires fresh projection artifacts and pinned proof parameters"]
fn curve25519_point_projection_generates_and_binds_a_native_proof() -> Result<()> {
    let directory = PathBuf::from(env::var_os("NOCTIUM_CURVE25519_PROJECTION_DIR").expect(
        "set NOCTIUM_CURVE25519_PROJECTION_DIR to the fresh Curve25519ProjectionParity artifacts",
    ));
    let parameter_path = env::var_os("NOCTIUM_CURVE25519_PROJECTION_PROOF_PARAMETERS")
        .expect("set NOCTIUM_CURVE25519_PROJECTION_PROOF_PARAMETERS to the pinned SRS file");
    let parameter_sha256 = env::var("NOCTIUM_CURVE25519_PROJECTION_PROOF_PARAMETERS_SHA256")
        .expect("set NOCTIUM_CURVE25519_PROJECTION_PROOF_PARAMETERS_SHA256 to its pinned digest");
    let parameter_bytes = fs::read(parameter_path)?;
    let (plan, relation) = fixture(&directory)?;
    let parameters =
        TrustedParameters::from_bytes(&parameter_bytes, relation.k(), &parameter_sha256)?;
    let initial = create_state(&plan, &BTreeMap::new())?;
    let (generator, generator_x, generator_y) = generator_vector();
    let inputs = BTreeMap::from([("point".into(), Value::Foreign(generator).public_json())]);
    let execution = prepare(
        &plan,
        &inputs,
        &initial,
        &ledger::structure::INITIAL_PARAMETERS,
        ContractAddress::default(),
    )?;
    assert_eq!(check(&execution, &relation)?, execution.activity_schedule);
    assert_eq!(
        execution.returns(),
        [
            ("x".into(), Value::Foreign(generator_x)),
            ("y".into(), Value::Foreign(generator_y)),
        ]
    );

    let (prover_key, verifier_key) = futures::executor::block_on(relation.keygen(&parameters))?;
    let (proof, statement, activity) = futures::executor::block_on(relation.prove(
        OsRng,
        &parameters,
        prover_key,
        &execution.preimage,
    ))?;
    assert_eq!(activity, execution.activity_schedule);
    let verifier_parameters = ParamsVerifier::read(parameter_bytes.as_slice())?;
    verifier_key.verify(&verifier_parameters, &proof, statement.iter().copied())?;

    let (commitment, _) = execution
        .preimage
        .communications_commitment
        .expect("the native projection binds its communicated return");
    assert_eq!(statement[1], commitment);
    let mut changed_statement = statement;
    changed_statement[1] = commitment + Fr::from(1u64);
    assert!(
        verifier_key
            .verify(
                &verifier_parameters,
                &proof,
                changed_statement.iter().copied()
            )
            .is_err()
    );
    Ok(())
}
