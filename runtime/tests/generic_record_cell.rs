#![cfg(feature = "zkir-321")]

use anyhow::Result;
use coin_structure::contract::ContractAddress;
use noctium_runtime::{Db, Execution, Plan, check, construct_state, prepare, zkir::IrSource};
use onchain_runtime::state::ChargedState;
use serde_json::{Value as Json, json};
use std::{collections::BTreeMap, fs::File, path::PathBuf};

fn fixture(directory: &PathBuf, entry: &str) -> Result<(Plan, IrSource)> {
    let stem = format!("GenericRecordCell.{entry}");
    let plan = serde_json::from_reader(File::open(
        directory.join(format!("{stem}.impact.json")),
    )?)?;
    let relation = IrSource::load(File::open(directory.join(format!("{stem}.zkir")))?)?;
    Ok((plan, relation))
}

fn run(
    operation: &(Plan, IrSource),
    inputs: &BTreeMap<String, Json>,
    state: &ChargedState<Db>,
) -> Result<Execution> {
    let execution = prepare(
        &operation.0,
        inputs,
        state,
        &ledger::structure::INITIAL_PARAMETERS,
        ContractAddress::default(),
    )?;
    assert_eq!(
        check(&execution, &operation.1)?,
        execution.activity_schedule
    );
    Ok(execution)
}

fn update_inputs(
    enabled: bool,
    next_issued: &str,
    next_spent: &str,
    next_tag: [u8; 4],
) -> BTreeMap<String, Json> {
    let mut inputs = BTreeMap::from([
        ("enabled".into(), json!(enabled)),
        ("next.issued".into(), json!(next_issued)),
        ("next.spent".into(), json!(next_spent)),
    ]);
    for (index, byte) in next_tag.into_iter().enumerate() {
        inputs.insert(format!("next.tag.{index}"), json!(byte.to_string()));
    }
    inputs
}

fn assert_result(execution: &Execution, issued: &str, spent: &str, tag: [u8; 4]) {
    assert_eq!(
        execution.returns_json(),
        BTreeMap::from([(
            "result".into(),
            json!({
                "kind":"struct",
                "id":"GenericRecordCell.Ledger",
                "fields":[
                    {"name":"issued", "value":{"kind":"native", "value":issued}},
                    {"name":"spent", "value":{"kind":"native", "value":spent}},
                    {"name":"tag", "value":{"kind":"bytes", "values":tag}}
                ]
            }),
        )])
    );
}

#[test]
#[ignore = "requires fresh GenericRecordCell artifacts in NOCTIUM_GENERIC_RECORD_CELL_DIR"]
fn generic_record_cell_constructor_and_guarded_write_round_trip() -> Result<()> {
    let directory = PathBuf::from(
        std::env::var_os("NOCTIUM_GENERIC_RECORD_CELL_DIR")
            .expect("NOCTIUM_GENERIC_RECORD_CELL_DIR"),
    );
    let inspect = fixture(&directory, "inspect")?;
    let update = fixture(&directory, "update")?;
    let constructor_inputs = BTreeMap::from([
        ("issued".into(), json!("5")),
        ("spent".into(), json!("42")),
        (
            "initialTag".into(),
            json!({"kind":"bytes", "values":[1, 2, 3, 4]}),
        ),
    ]);
    let no_inputs = BTreeMap::new();
    let initial = construct_state(&inspect.0, &constructor_inputs)?;

    let before = run(&inspect, &no_inputs, &initial)?;
    assert_result(&before, "5", "42", [1, 2, 3, 4]);
    assert_eq!(before.after.state, initial);

    let disabled = run(
        &update,
        &update_inputs(false, "11", "13", [9, 8, 7, 6]),
        &before.after.state,
    )?;
    assert_result(&disabled, "5", "42", [1, 2, 3, 4]);
    assert_eq!(disabled.after.state, before.after.state);

    let changed = run(
        &update,
        &update_inputs(true, "8", "99", [128, 0, 255, 42]),
        &disabled.after.state,
    )?;
    assert_result(&changed, "8", "99", [128, 0, 255, 42]);
    let after_change = run(&inspect, &no_inputs, &changed.after.state)?;
    assert_result(&after_change, "8", "99", [128, 0, 255, 42]);
    assert_eq!(after_change.after.state, changed.after.state);

    let mut invalid_byte = update_inputs(true, "8", "99", [128, 0, 255, 42]);
    invalid_byte.insert("next.tag.0".into(), json!("256"));
    let invalid_execution = prepare(
        &update.0,
        &invalid_byte,
        &changed.after.state,
        &ledger::structure::INITIAL_PARAMETERS,
        ContractAddress::default(),
    )
    .and_then(|execution| {
        check(&execution, &update.1)?;
        Ok(())
    });
    assert!(
        invalid_execution.is_err(),
        "a byte input outside 0..=255 must reject"
    );

    let mut wrong_width = constructor_inputs;
    wrong_width.insert(
        "initialTag".into(),
        json!({"kind":"bytes", "values":[1, 2, 3]}),
    );
    assert!(construct_state(&inspect.0, &wrong_width).is_err());

    Ok(())
}
