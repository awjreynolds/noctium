#![cfg(feature = "zkir-321")]

use coin_structure::contract::ContractAddress;
use noctium_runtime::{Plan, check, construct_state, prepare, zkir::IrSource};
use serde_json::{Value as Json, json};
use std::{
    collections::BTreeMap,
    env,
    fs::File,
    path::{Path, PathBuf},
};

fn artifacts(directory: &Path, contract: &str, entry: &str) -> anyhow::Result<(Plan, IrSource)> {
    let stem = format!("{contract}.{entry}");
    Ok((
        serde_json::from_reader(File::open(directory.join(format!("{stem}.impact.json")))?)?,
        IrSource::load(File::open(directory.join(format!("{stem}.zkir")))?)?,
    ))
}

fn scalar(value: &str) -> Json {
    json!({"kind": "jubjubScalar", "value": value})
}

fn point(x: &str, y: &str) -> Json {
    json!({"kind": "jubjubPoint", "x": x, "y": y})
}

fn check_cell(
    contract: &str,
    initial: Json,
    replacement: Json,
    invalid: Json,
) -> anyhow::Result<()> {
    let directory = PathBuf::from(
        env::var_os("NOCTIUM_GENERIC_JUBJUB_CELL_DIR")
            .expect("set NOCTIUM_GENERIC_JUBJUB_CELL_DIR to fresh artifacts"),
    );
    let (read_plan, read_relation) = artifacts(&directory, contract, "read")?;
    let (update_plan, update_relation) = artifacts(&directory, contract, "update")?;
    let parameters = &ledger::structure::INITIAL_PARAMETERS;
    let state = construct_state(
        &read_plan,
        &BTreeMap::from([("initial".into(), initial.clone())]),
    )?;
    let read = |state| {
        prepare(
            &read_plan,
            &BTreeMap::new(),
            state,
            parameters,
            ContractAddress::default(),
        )
    };

    let before = read(&state)?;
    check(&before, &read_relation)?;
    assert_eq!(before.returns_json().get("result"), Some(&initial));
    let updated = prepare(
        &update_plan,
        &BTreeMap::from([("next".into(), replacement.clone())]),
        &state,
        parameters,
        ContractAddress::default(),
    )?;
    check(&updated, &update_relation)?;
    assert_eq!(updated.returns_json().get("result"), Some(&replacement));
    let after = read(&updated.after.state)?;
    check(&after, &read_relation)?;
    assert_eq!(after.returns_json().get("result"), Some(&replacement));

    assert!(construct_state(&read_plan, &BTreeMap::from([("initial".into(), invalid)])).is_err());
    Ok(())
}

#[test]
#[ignore = "requires fresh GenericJubjubScalarCell artifacts"]
fn generic_jubjub_scalar_cell_keeps_its_typed_value() -> anyhow::Result<()> {
    const JUBJUB_ORDER: &str =
        "6554484396890773809930967563523245729705921265872317281365359162392183254199";
    check_cell(
        "GenericJubjubScalarCell",
        scalar("5"),
        scalar("17"),
        scalar(JUBJUB_ORDER),
    )
}

#[test]
#[ignore = "requires fresh GenericJubjubPointCell artifacts"]
fn generic_jubjub_point_cell_keeps_its_coordinates() -> anyhow::Result<()> {
    check_cell(
        "GenericJubjubPointCell",
        point("0", "1"),
        point(
            "28336281903124990867587793011069573392383982287722241916350956173377953689573",
            "39385640392217313770878525135509063452020585410343666726093009378539878503883",
        ),
        point("0", "0"),
    )
}
