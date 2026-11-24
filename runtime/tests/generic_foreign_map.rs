#![cfg(feature = "zkir-321")]

use coin_structure::contract::ContractAddress;
use ledger::structure::INITIAL_PARAMETERS;
use noctium_runtime::{
    Db, Execution, Plan, Value, check, create_state,
    foreign::{ForeignRole, ForeignType, ForeignUnaryOp, ForeignValue},
    prepare,
    zkir::IrSource,
};
use onchain_runtime::state::ChargedState;
use serde_json::{Value as Json, json};
use std::{collections::BTreeMap, env, fs::File, path::Path};

fn artifacts(dir: &Path, entry: &str) -> anyhow::Result<(Plan, IrSource)> {
    let stem = format!("GenericForeignMap.{entry}");
    Ok((
        serde_json::from_reader(File::open(dir.join(format!("{stem}.impact.json")))?)?,
        IrSource::load(File::open(dir.join(format!("{stem}.zkir")))?)?,
    ))
}

fn foreign_value(name: &str, byte: u8) -> anyhow::Result<Json> {
    let ty = ForeignType::parse_source_name(name)?;
    let mut bytes = [0; 32];
    bytes[0] = byte;
    let value = if ty.role() == ForeignRole::Point {
        ForeignValue::from_bytes(ForeignType::new(ty.family(), ForeignRole::Scalar), &bytes)?
            .unary(ForeignUnaryOp::MulGenerator)?
    } else {
        ForeignValue::from_bytes(ty, &bytes)?
    };
    Ok(Value::Foreign(value).public_json())
}

fn run(
    operation: &(Plan, IrSource),
    inputs: &BTreeMap<String, Json>,
    state: &ChargedState<Db>,
) -> anyhow::Result<Execution> {
    let execution = prepare(
        &operation.0,
        inputs,
        state,
        &INITIAL_PARAMETERS,
        ContractAddress::default(),
    )?;
    assert_eq!(
        check(&execution, &operation.1)?,
        execution.activity_schedule
    );
    Ok(execution)
}

fn map_state(plan: &Plan) -> anyhow::Result<ChargedState<Db>> {
    let config = plan
        .state
        .iter()
        .map(|state| (state.name.clone(), json!([])))
        .collect();
    Ok(create_state(plan, &config)?)
}

fn insert_inputs(key: Json, next: Json) -> BTreeMap<String, Json> {
    BTreeMap::from([("key".into(), key), ("next".into(), next)])
}

fn read_inputs(key: Json) -> BTreeMap<String, Json> {
    BTreeMap::from([("key".into(), key)])
}

fn check_map(
    directory: &Path,
    insert_entry: &str,
    read_entry: &str,
    key_type: &str,
    value_type: &str,
    wrong_family_key_type: Option<&str>,
    key_values: [u8; 3],
    value_values: [u8; 2],
) -> anyhow::Result<()> {
    let insert = artifacts(directory, insert_entry)?;
    let read = artifacts(directory, read_entry)?;
    assert!(
        insert
            .0
            .state
            .iter()
            .map(|decl| (&decl.name, &decl.kind))
            .eq(read.0.state.iter().map(|decl| (&decl.name, &decl.kind))),
        "{insert_entry}/{read_entry}"
    );

    let keys = key_values
        .map(|byte| foreign_value(key_type, byte))
        .into_iter()
        .collect::<anyhow::Result<Vec<_>>>()?;
    let values = value_values
        .map(|byte| foreign_value(value_type, byte))
        .into_iter()
        .collect::<anyhow::Result<Vec<_>>>()?;
    let initial = map_state(&insert.0)?;

    let put = |state: &ChargedState<Db>, key: Json, value: Json| {
        let inputs = insert_inputs(key, value);
        let execution = run(&insert, &inputs, state)?;
        assert!(
            execution.returns_json().is_empty(),
            "{insert_entry} has no return"
        );
        Ok::<_, anyhow::Error>(execution.after.state)
    };
    let lookup = |state: &ChargedState<Db>, key: Json, expected: &Json| {
        let execution = run(&read, &read_inputs(key), state)?;
        assert_eq!(
            execution.returns_json()["result"],
            *expected,
            "{read_entry}"
        );
        assert_eq!(
            execution.after.state, *state,
            "{read_entry} changed the Map"
        );
        Ok::<_, anyhow::Error>(())
    };

    let first = put(&initial, keys[0].clone(), values[0].clone())?;
    lookup(&first, keys[0].clone(), &values[0])?;
    let sibling = put(&first, keys[1].clone(), values[1].clone())?;
    lookup(&sibling, keys[0].clone(), &values[0])?;
    lookup(&sibling, keys[1].clone(), &values[1])?;
    assert!(
        prepare(
            &read.0,
            &read_inputs(keys[2].clone()),
            &sibling,
            &INITIAL_PARAMETERS,
            ContractAddress::default(),
        )
        .is_err(),
        "lookup of a missing foreign Map key must reject"
    );

    if let Some(wrong_type) = wrong_family_key_type {
        let mut wrong_key = keys[0].clone();
        wrong_key["type"] = json!(wrong_type);
        assert!(
            prepare(
                &insert.0,
                &insert_inputs(wrong_key, values[0].clone()),
                &sibling,
                &INITIAL_PARAMETERS,
                ContractAddress::default(),
            )
            .is_err(),
            "wrong-family foreign Map key must reject"
        );
        lookup(&sibling, keys[0].clone(), &values[0])?;
        lookup(&sibling, keys[1].clone(), &values[1])?;
    }
    Ok(())
}

#[test]
#[ignore = "requires fresh GenericForeignMap artifacts in NOCTIUM_GENERIC_FOREIGN_MAP_DIR"]
fn generic_foreign_root_maps_preserve_typed_keys_and_values() -> anyhow::Result<()> {
    let directory = env::var("NOCTIUM_GENERIC_FOREIGN_MAP_DIR")?;
    let directory = Path::new(&directory);
    check_map(
        directory,
        "insertSecpPointToR1Base",
        "readSecpPointToR1Base",
        "Secp256k1Point",
        "Secp256r1Base",
        Some("Secp256r1Point"),
        [1, 2, 3],
        [17, 23],
    )?;
    check_map(
        directory,
        "insertC255ScalarToC255Point",
        "readC255ScalarToC255Point",
        "Curve25519Scalar",
        "Curve25519Point",
        None,
        [19, 20, 21],
        [1, 2],
    )
}
