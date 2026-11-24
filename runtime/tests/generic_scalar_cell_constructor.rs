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

fn update_inputs(enabled: bool, next: Json) -> BTreeMap<String, Json> {
    BTreeMap::from([("enabled".into(), json!(enabled)), ("next".into(), next)])
}

fn apply_update(
    fixture: &(Plan, IrSource),
    state: &ChargedState<Db>,
    enabled: bool,
    next: Json,
    expected: &Json,
) -> anyhow::Result<ChargedState<Db>> {
    let (plan, relation) = fixture;
    let execution = prepare(
        plan,
        &update_inputs(enabled, next),
        state,
        &ledger::structure::INITIAL_PARAMETERS,
        ContractAddress::default(),
    )?;
    assert_eq!(check(&execution, relation)?, execution.activity_schedule);
    assert_eq!(execution.returns_json().get("result"), Some(expected));
    Ok(execution.after.state)
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

#[test]
#[ignore = "requires fresh GenericScalarCellConstructor artifacts in NOCTIUM_GENERIC_SCALAR_CELL_CONSTRUCTOR_DIR"]
fn generic_scalar_cell_constructor_updates_only_the_selected_cell() -> anyhow::Result<()> {
    let directory = artifacts();
    let reads = [
        fixture(&directory, "readField")?,
        fixture(&directory, "readFlag")?,
        fixture(&directory, "readCount")?,
    ];
    let updates = [
        fixture(&directory, "updateField")?,
        fixture(&directory, "updateFlag")?,
        fixture(&directory, "updateCount")?,
    ];
    let mut values = [json!("5"), json!(true), json!("42")];
    let replacements = [json!("8"), json!(false), json!("65535")];
    let mut state = construct_state(&reads[0].0, &constructor_arguments(42))?;

    for (index, update) in updates.iter().enumerate() {
        let disabled = apply_update(
            update,
            &state,
            false,
            replacements[index].clone(),
            &values[index],
        )?;
        assert_eq!(disabled, state);
    }
    for (index, update) in updates.iter().enumerate() {
        let next = replacements[index].clone();
        state = apply_update(update, &state, true, next.clone(), &next)?;
        values[index] = next;
        for ((plan, relation), expected) in reads.iter().zip(&values) {
            assert_read(plan, relation, &state, expected.clone())?;
        }
    }
    assert!(
        prepare(
            &updates[2].0,
            &update_inputs(true, json!("65536")),
            &state,
            &ledger::structure::INITIAL_PARAMETERS,
            ContractAddress::default(),
        )
        .is_err(),
        "UInt16 update must reject 65536"
    );
    Ok(())
}
