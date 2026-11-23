#![cfg(feature = "zkir-321")]

use anyhow::Result;
use coin_structure::contract::ContractAddress;
use ledger::structure::INITIAL_PARAMETERS;
use noctium_runtime::{Db, Execution, Plan, check, create_state, prepare, zkir::IrSource};
use onchain_runtime::state::ChargedState;
use serde_json::{Value as Json, json};
use std::{collections::BTreeMap, fs, path::PathBuf};

fn fixture(directory: &PathBuf, entry: &str) -> Result<(Plan, IrSource)> {
    let stem = format!("NestedRecordList.{entry}");
    let plan = serde_json::from_slice(&fs::read(
        directory.join(format!("{stem}.impact.json")),
    )?)?;
    let circuit = IrSource::load(
        fs::read(directory.join(format!("{stem}.zkir")))?.as_slice(),
    )?;
    Ok((plan, circuit))
}

fn push_inputs(first: u64, active: bool, tag: u64) -> BTreeMap<String, Json> {
    BTreeMap::from([
        ("first".into(), json!(first.to_string())),
        ("active".into(), json!(active)),
        ("tag".into(), json!(tag.to_string())),
    ])
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
        &INITIAL_PARAMETERS,
        ContractAddress::default(),
    )?;
    assert_eq!(
        check(&execution, &operation.1)?,
        execution.activity_schedule
    );
    Ok(execution)
}

fn assert_head(execution: &Execution, present: bool, first: u64, active: bool, tag: u64) {
    let returns = execution.returns_json();
    assert_eq!(returns.len(), 1);
    assert_eq!(returns["head"]["kind"], "struct");
    assert_eq!(
        returns["head"]["fields"],
        json!([
            {"name":"is_some", "value":{"kind":"bool", "value":present}},
            {"name":"value", "value":{
                "kind":"struct", "id":"NestedRecordList.Envelope",
                "fields":[
                    {"name":"memo", "value":{
                        "kind":"struct", "id":"NestedRecordList.Envelope.memo.Inner",
                        "fields":[
                            {"name":"first", "value":{"kind":"native", "value":first.to_string()}},
                            {"name":"active", "value":{"kind":"bool", "value":active}}
                        ]
                    }},
                    {"name":"tag", "value":{"kind":"native", "value":tag.to_string()}}
                ]
            }}
        ])
    );
}

#[test]
#[ignore = "requires fresh NestedRecordList Plan and ZKIR artifacts in NOCTIUM_NESTED_RECORD_LIST_DIR"]
fn nested_record_list_matches_compact_push_head_pop_and_empty_maybe() -> Result<()> {
    let directory = PathBuf::from(std::env::var("NOCTIUM_NESTED_RECORD_LIST_DIR")?);
    let push = fixture(&directory, "push")?;
    let head = fixture(&directory, "head")?;
    let pop = fixture(&directory, "pop")?;
    let empty = create_state(&head.0, &BTreeMap::from([("records".into(), json!([]))]))?;
    let no_inputs = BTreeMap::new();

    let initial_head = run(&head, &no_inputs, &empty)?;
    assert_eq!(initial_head.after.state, empty);
    assert_head(&initial_head, false, 0, false, 0);

    let first = run(&push, &push_inputs(11, true, 101), &empty)?;
    let second = run(&push, &push_inputs(22, false, 202), &first.after.state)?;

    let newest_head = run(&head, &no_inputs, &second.after.state)?;
    assert_eq!(newest_head.after.state, second.after.state);
    assert_head(&newest_head, true, 22, false, 202);

    let after_first_pop = run(&pop, &no_inputs, &second.after.state)?;
    let older_head = run(&head, &no_inputs, &after_first_pop.after.state)?;
    assert_eq!(older_head.after.state, after_first_pop.after.state);
    assert_head(&older_head, true, 11, true, 101);

    let after_second_pop = run(&pop, &no_inputs, &after_first_pop.after.state)?;
    let empty_again = run(&head, &no_inputs, &after_second_pop.after.state)?;
    assert_eq!(empty_again.after.state, after_second_pop.after.state);
    assert_head(&empty_again, false, 0, false, 0);
    Ok(())
}
