#![cfg(feature = "zkir-321")]

use anyhow::Result;
use coin_structure::contract::ContractAddress;
use noctium_runtime::{
    Plan, Value, check,
    create_state,
    foreign::{ForeignFamily, ForeignRole, ForeignType, ForeignValue},
    prepare,
    zkir::IrSource,
};
use num_bigint::BigUint;
use onchain_runtime::state::ChargedState;
use std::{
    collections::BTreeMap,
    fs,
    path::{Path, PathBuf},
};
use transient_crypto::curve::Fr;

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
    let plan: Plan = serde_json::from_slice(&fs::read(
        directory.join(format!("{stem}.impact.json")),
    )?)?;
    let relation = IrSource::load(
        fs::read(directory.join(format!("{stem}.zkir")))?.as_slice(),
    )?;
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
    let point_type = ForeignType::new(ForeignFamily::Curve25519, ForeignRole::Point);
    let identity = ForeignValue::zero(point_type)?;
    let mut generator_bytes = [0x66; 32];
    generator_bytes[0] = 0x58;
    let generator = point(&generator_bytes);

    check_projection(
        &plan,
        &relation,
        &initial,
        generator,
        coordinate("15112221349535400772501151409588531511454012693041857206046113283949847762202"),
        coordinate("46316835694926478169428394003475163141307993866256225615783033603165251855960"),
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
