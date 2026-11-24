#![cfg(feature = "zkir-321")]

use coin_structure::contract::ContractAddress;
use noctium_runtime::{Db, Plan, check, construct_state, prepare, zkir::IrSource};
use onchain_runtime::state::ChargedState;
use serde_json::{Value as Json, json};
use std::{
    collections::BTreeMap,
    env,
    fs::File,
    path::{Path, PathBuf},
};

fn artifacts() -> PathBuf {
    env::var_os("NOCTIUM_GENERIC_SCALAR_CELL_CONSTRUCTOR_DIR")
        .map(PathBuf::from)
        .expect("set fresh outputs in NOCTIUM_GENERIC_SCALAR_CELL_CONSTRUCTOR_DIR")
}

fn fixture(directory: &Path, entry: &str) -> anyhow::Result<(Plan, IrSource)> {
    let stem = format!("GenericScalarCellConstructor.{entry}");
    Ok((
        serde_json::from_reader(File::open(directory.join(format!("{stem}.impact.json")))?)?,
        IrSource::load(File::open(directory.join(format!("{stem}.zkir")))?)?,
    ))
}

fn constructor_arguments(initial_count: u64) -> BTreeMap<String, Json> {
    BTreeMap::from([
        ("initialField".into(), json!("5")),
        ("initialFlag".into(), json!(true)),
        ("initialCount".into(), json!(initial_count.to_string())),
    ])
}

fn assert_read(
    plan: &Plan,
    relation: &IrSource,
    state: &ChargedState<Db>,
    expected: Json,
) -> anyhow::Result<()> {
    assert!(
        plan.circuit.inputs.is_empty(),
        "read entrypoints take no arguments"
    );
    let execution = prepare(
        plan,
        &BTreeMap::new(),
        state,
        &ledger::structure::INITIAL_PARAMETERS,
        ContractAddress::default(),
    )?;
    assert_eq!(check(&execution, relation)?, execution.activity_schedule);
    assert_eq!(
        execution.returns_json(),
        BTreeMap::from([("result".into(), expected)])
    );
    assert_eq!(execution.after.state.get_ref(), state.get_ref());
    Ok(())
}

#[test]
#[ignore = "requires fresh GenericScalarCellConstructor artifacts in NOCTIUM_GENERIC_SCALAR_CELL_CONSTRUCTOR_DIR"]
fn generic_scalar_cell_constructor_reads_initialized_values() -> anyhow::Result<()> {
    let directory = artifacts();
    let (read_field, field_relation) = fixture(&directory, "readField")?;
    let (read_flag, flag_relation) = fixture(&directory, "readFlag")?;
    let (read_count, count_relation) = fixture(&directory, "readCount")?;

    let state = construct_state(&read_field, &constructor_arguments(42))?;
    assert_read(&read_field, &field_relation, &state, json!("5"))?;
    assert_read(&read_flag, &flag_relation, &state, json!(true))?;
    assert_read(&read_count, &count_relation, &state, json!("42"))?;

    assert!(
        construct_state(&read_field, &constructor_arguments(65_536)).is_err(),
        "constructor must reject an initialCount outside UInt16"
    );
    Ok(())
}
