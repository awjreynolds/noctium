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

fn artifacts(directory: &Path, entry: &str) -> anyhow::Result<(Plan, IrSource)> {
    let stem = format!("GenericJubjubScalarCell.{entry}");
    Ok((
        serde_json::from_reader(File::open(directory.join(format!("{stem}.impact.json")))?)?,
        IrSource::load(File::open(directory.join(format!("{stem}.zkir")))?)?,
    ))
}

fn scalar(value: &str) -> Json {
    json!({"kind": "jubjubScalar", "value": value})
}

#[test]
#[ignore = "requires fresh GenericJubjubScalarCell artifacts"]
fn generic_jubjub_cell_keeps_its_typed_value_across_update_and_read() -> anyhow::Result<()> {
    let directory = PathBuf::from(
        env::var_os("NOCTIUM_GENERIC_JUBJUB_CELL_DIR")
            .expect("set NOCTIUM_GENERIC_JUBJUB_CELL_DIR to fresh artifacts"),
    );
    let (read_plan, read_relation) = artifacts(&directory, "read")?;
    let (update_plan, update_relation) = artifacts(&directory, "update")?;
    let parameters = &ledger::structure::INITIAL_PARAMETERS;
    let initial = scalar("5");
    let replacement = scalar("17");
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

    const JUBJUB_ORDER: &str =
        "6554484396890773809930967563523245729705921265872317281365359162392183254199";
    assert!(
        construct_state(
            &read_plan,
            &BTreeMap::from([("initial".into(), scalar(JUBJUB_ORDER))]),
        )
        .is_err()
    );
    Ok(())
}
