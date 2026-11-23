#![cfg(feature = "zkir-321")]

use anyhow::Result;
use coin_structure::contract::ContractAddress;
use noctium_runtime::{Db, Execution, Plan, check, construct_state, prepare, zkir::IrSource};
use onchain_runtime::state::ChargedState;
use serde_json::{Value as Json, json};
use std::{collections::BTreeMap, fs::File, path::PathBuf};

fn fixture(directory: &PathBuf, entry: &str) -> Result<(Plan, IrSource)> {
    let stem = format!("ConstructorRecordList.{entry}");
    let plan = serde_json::from_reader(File::open(directory.join(format!("{stem}.impact.json")))?)?;
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

fn assert_head(execution: &Execution, present: bool, owner: u64, active: bool) {
    let returns = execution.returns_json();
    assert_eq!(returns.len(), 1);
    assert_eq!(returns["head"]["kind"], "struct");
    assert_eq!(
        returns["head"]["fields"],
        json!([
            {"name":"is_some", "value":{"kind":"bool", "value":present}},
            {"name":"value", "value":{
                "kind":"struct", "id":"ConstructorRecordList.Position",
                "fields":[
                    {"name":"owner", "value":{"kind":"native", "value":owner.to_string()}},
                    {"name":"active", "value":{"kind":"bool", "value":active}}
                ]
            }}
        ])
    );
}

#[test]
#[ignore = "requires fresh ConstructorRecordList artifacts in NOCTIUM_CONSTRUCTOR_RECORD_LIST_DIR"]
fn constructor_record_list_initializes_lifo_and_pops_to_absent() -> Result<()> {
    let directory = PathBuf::from(
        std::env::var_os("NOCTIUM_CONSTRUCTOR_RECORD_LIST_DIR")
            .expect("NOCTIUM_CONSTRUCTOR_RECORD_LIST_DIR"),
    );
    let head = fixture(&directory, "head")?;
    let pop = fixture(&directory, "pop")?;
    let constructor_inputs = BTreeMap::from([
        ("firstOwner".into(), json!("11")),
        ("secondOwner".into(), json!("22")),
        ("includeThird".into(), json!(false)),
    ]);
    let no_inputs = BTreeMap::new();
    let initial = construct_state(&head.0, &constructor_inputs)?;

    let newest = run(&head, &no_inputs, &initial)?;
    assert_eq!(newest.after.state, initial);
    assert_head(&newest, true, 22, true);

    let after_first_pop = run(&pop, &no_inputs, &newest.after.state)?;
    assert!(after_first_pop.returns_json().is_empty());
    let older = run(&head, &no_inputs, &after_first_pop.after.state)?;
    assert_eq!(older.after.state, after_first_pop.after.state);
    assert_head(&older, true, 11, false);

    let after_second_pop = run(&pop, &no_inputs, &older.after.state)?;
    assert!(after_second_pop.returns_json().is_empty());
    let empty = run(&head, &no_inputs, &after_second_pop.after.state)?;
    assert_eq!(empty.after.state, after_second_pop.after.state);
    assert_head(&empty, false, 0, false);
    Ok(())
}
