#![cfg(feature = "zkir-321")]

use anyhow::Result;
use coin_structure::contract::ContractAddress;
use ledger::structure::INITIAL_PARAMETERS;
use noctium_runtime::{
    Db, Execution, Plan, check, create_state, field_decimal, prepare, zkir::IrSource,
};
use onchain_runtime::state::{ChargedState, StateValue};
use serde_json::{Value as Json, json};
use std::{collections::BTreeMap, fs, path::PathBuf};
use transient_crypto::fab::AlignedValueExt;

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

fn assert_uint16_head(execution: &Execution, present: bool, first: u16, active: bool, tag: u64) {
    let returns = execution.returns_json();
    assert_eq!(returns.len(), 1);
    assert_eq!(returns["head"]["kind"], "struct");
    assert_eq!(
        returns["head"]["fields"],
        json!([
            {"name":"is_some", "value":{"kind":"bool", "value":present}},
            {"name":"value", "value":{
                "kind":"struct", "id":"NestedUInt16RecordList.Envelope",
                "fields":[
                    {"name":"memo", "value":{
                        "kind":"struct", "id":"NestedUInt16RecordList.Envelope.memo.Inner",
                        "fields":[
                            {"name":"first", "value":{"kind":"uint", "maximum":"65535", "value":first.to_string()}},
                            {"name":"active", "value":{"kind":"bool", "value":active}}
                        ]
                    }},
                    {"name":"tag", "value":{"kind":"native", "value":tag.to_string()}}
                ]
            }}
        ])
    );
}

fn assert_physical_uint16_record(state: &ChargedState<Db>, plan: &Plan, expected: [u64; 3]) {
    let StateValue::Array(root) = state.get_ref() else {
        panic!("expected contract state array")
    };
    let slot = plan
        .state
        .iter()
        .position(|declaration| declaration.name == "records")
        .expect("records state slot exists");
    let StateValue::Array(list) = root.get(slot).expect("records List exists") else {
        panic!("expected records List")
    };
    let StateValue::Cell(record) = list.get(0).expect("List head exists") else {
        panic!("expected flattened List head Cell")
    };
    let mut fields = Vec::new();
    record.value_only_field_repr(&mut fields);
    assert_eq!(fields.len(), 3, "nested record has three physical leaves");
    assert_eq!(
        fields
            .iter()
            .map(|field| field_decimal(*field))
            .collect::<Vec<_>>(),
        expected
            .into_iter()
            .map(|value| value.to_string())
            .collect::<Vec<_>>()
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

#[test]
#[ignore = "requires fresh NestedUInt16RecordList Plan and ZKIR artifacts in NOCTIUM_NESTED_RECORD_LIST_DIR"]
fn nested_record_list_uint16_leaves_match_fresh_artifacts_and_bounds() -> Result<()> {
    let directory = PathBuf::from(std::env::var("NOCTIUM_NESTED_RECORD_LIST_DIR")?);
    let push = fixture_named(&directory, "NestedUInt16RecordList", "push")?;
    let head = fixture_named(&directory, "NestedUInt16RecordList", "head")?;
    let pop = fixture_named(&directory, "NestedUInt16RecordList", "pop")?;
    let empty = create_state(&head.0, &BTreeMap::from([("records".into(), json!([]))]))?;
    let no_inputs = BTreeMap::new();

    let initial_head = run(&head, &no_inputs, &empty)?;
    assert_eq!(initial_head.after.state, empty);
    assert_uint16_head(&initial_head, false, 0, false, 0);

    let first = run(&push, &push_inputs(513, true, 17), &empty)?;
    assert_physical_uint16_record(&first.after.state, &push.0, [513, 1, 17]);
    let second = run(&push, &push_inputs(65_535, false, 23), &first.after.state)?;
    assert_physical_uint16_record(&second.after.state, &push.0, [65_535, 0, 23]);

    let newest_head = run(&head, &no_inputs, &second.after.state)?;
    assert_eq!(newest_head.after.state, second.after.state);
    assert_uint16_head(&newest_head, true, 65_535, false, 23);

    let after_first_pop = run(&pop, &no_inputs, &second.after.state)?;
    let older_head = run(&head, &no_inputs, &after_first_pop.after.state)?;
    assert_eq!(older_head.after.state, after_first_pop.after.state);
    assert_uint16_head(&older_head, true, 513, true, 17);

    assert!(prepare(
        &push.0,
        &push_inputs(65_536, true, 17),
        &empty,
        &INITIAL_PARAMETERS,
        ContractAddress::default(),
    )
    .is_err());
    Ok(())
}

fn fixture_named(directory: &PathBuf, contract: &str, entry: &str) -> Result<(Plan, IrSource)> {
    let stem = format!("{contract}.{entry}");
    let plan = serde_json::from_slice(&fs::read(
        directory.join(format!("{stem}.impact.json")),
    )?)?;
    let circuit = IrSource::load(fs::read(directory.join(format!("{stem}.zkir")))?.as_slice())?;
    Ok((plan, circuit))
}
