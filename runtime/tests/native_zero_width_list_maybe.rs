#![cfg(feature = "zkir-321")]

use anyhow::Result;
use base_crypto::fab::{AlignedValue, Alignment, AlignmentAtom, Value as FabValue, ValueAtom};
use coin_structure::contract::ContractAddress;
use ledger::structure::INITIAL_PARAMETERS;
use noctium_runtime::{check, create_state, prepare, zkir::IrSource, Db, Execution, Plan};
use onchain_runtime::{
    context::QueryContext,
    state::{ChargedState, StateValue},
};
use serde_json::{json, Value as Json};
use std::{collections::BTreeMap, fs, path::PathBuf};

fn artifact_directory() -> PathBuf {
    PathBuf::from(
        std::env::var_os("NOCTIUM_NATIVE_ZERO_WIDTH_LIST_MAYBE_DIR")
            .expect("set fresh outputs in NOCTIUM_NATIVE_ZERO_WIDTH_LIST_MAYBE_DIR"),
    )
}

fn compact_results() -> Result<Json> {
    let path = std::env::var_os("NOCTIUM_NATIVE_ZERO_WIDTH_LIST_MAYBE_COMPACT")
        .expect("set Compact output in NOCTIUM_NATIVE_ZERO_WIDTH_LIST_MAYBE_COMPACT");
    Ok(serde_json::from_slice(&fs::read(path)?)?)
}

fn fixture(directory: &std::path::Path, entry: &str) -> Result<(Plan, IrSource)> {
    let stem = format!("NativeZeroWidthListMaybe.{entry}");
    Ok((
        serde_json::from_slice(&fs::read(directory.join(format!("{stem}.impact.json")))?)?,
        IrSource::load(fs::File::open(directory.join(format!("{stem}.zkir")))?)?,
    ))
}

fn bytes_json(value: &[u8]) -> Json {
    json!({"kind":"bytes", "values":value})
}

fn compact_maybe(oracle: &Json, case: &str, id: &str) -> Json {
    let value = &oracle[case];
    json!({
        "kind":"struct",
        "id":id,
        "fields":[
            {"name":"is_some", "value":{"kind":"bool", "value":value["is_some"]}},
            {"name":"value", "value":bytes_json(
                &value["value"].as_array().unwrap().iter()
                    .map(|byte| byte.as_u64().unwrap() as u8).collect::<Vec<_>>()
            )}
        ]
    })
}

fn run(plan: &Plan, circuit: &IrSource, state: &ChargedState<Db>) -> Result<Execution> {
    let execution = prepare(
        plan,
        &BTreeMap::new(),
        state,
        &INITIAL_PARAMETERS,
        ContractAddress::default(),
    )?;
    check(&execution, circuit)?;
    Ok(execution)
}

fn empty_bytes_alignment() -> AlignedValue {
    AlignedValue::new(
        FabValue(vec![ValueAtom::from(&[][..])]),
        Alignment::singleton(AlignmentAtom::Bytes { length: 0 }),
    )
    .unwrap()
}

fn assert_list(node: &StateValue<Db>, expected_length: u64) {
    let StateValue::Array(node) = node else {
        panic!("expected native List array")
    };
    assert_eq!(node.len(), 3);
    let StateValue::Cell(length) = node.get(2).unwrap() else {
        panic!("expected List length Cell")
    };
    assert_eq!(**length, AlignedValue::from(expected_length));
    if expected_length == 0 {
        assert!(matches!(node.get(0), Some(StateValue::Null)));
        assert!(matches!(node.get(1), Some(StateValue::Null)));
    } else {
        assert_eq!(expected_length, 1);
        let StateValue::Cell(head) = node.get(0).unwrap() else {
            panic!("expected empty Bytes0 List head Cell")
        };
        assert_eq!(**head, empty_bytes_alignment());
        assert_list(node.get(1).expect("List tail"), expected_length - 1);
    }
}

fn query(state: &ChargedState<Db>, execution: &Execution) -> Result<ChargedState<Db>> {
    let result = QueryContext::new(state.clone(), ContractAddress::default()).query(
        &execution.program,
        None,
        &INITIAL_PARAMETERS.cost_model.runtime_cost_model,
    )?;
    Ok(result.context.state)
}

#[test]
#[ignore = "requires fresh outputs and Compact oracle for NativeZeroWidthListMaybe"]
fn native_zero_width_list_maybe_matches_compact_and_empty_pop_rejects_reads() -> Result<()> {
    let directory = artifact_directory();
    let oracle = compact_results()?;
    assert!(oracle["compact"]
        .as_str()
        .unwrap()
        .starts_with("0.36.1 (7fa3a117c"));
    assert_eq!(oracle["runtime"], "0.21.0");

    let (push, push_circuit) = fixture(&directory, "push")?;
    let (peek, peek_circuit) = fixture(&directory, "peek")?;
    let (pop, pop_circuit) = fixture(&directory, "pop")?;
    assert_eq!(peek.return_views.len(), 1);
    assert_eq!(peek.return_views[0].fields, ["item_is_some".to_string()]);
    assert_eq!(
        peek.returns
            .iter()
            .find(|output| output.name == "item_value")
            .map(|output| output.ty.as_str()),
        Some("Bytes<0>")
    );

    let base = create_state(&push, &BTreeMap::from([("inbox".into(), json!([]))]))?;
    let StateValue::Array(base_root) = base.get_ref() else {
        panic!("expected initial contract state array")
    };
    assert_list(base_root.get(0).expect("inbox List"), 0);

    let empty = run(&peek, &peek_circuit, &base)?;
    assert_eq!(
        empty.returns_json()["item"],
        compact_maybe(&oracle, "empty", "NativeZeroWidthListMaybe.MaybeBytes0",)
    );
    assert_eq!(empty.returns_json()["item_value"], bytes_json(&[]));
    assert_eq!(empty.returns().len(), 2);
    assert_eq!(empty.returns()[1].0, "item_value");

    let pushed = run(&push, &push_circuit, &base)?;
    let StateValue::Array(populated_root) = pushed.after.state.get_ref() else {
        panic!("expected state array after push")
    };
    assert_list(populated_root.get(0).unwrap(), 1);
    let populated = run(&peek, &peek_circuit, &pushed.after.state)?;
    assert_eq!(
        populated.returns_json()["item"],
        compact_maybe(&oracle, "populated", "NativeZeroWidthListMaybe.MaybeBytes0",)
    );

    let popped = run(&pop, &pop_circuit, &pushed.after.state)?;
    let StateValue::Array(empty_root) = popped.after.state.get_ref() else {
        panic!("expected state array after pop")
    };
    assert_list(empty_root.get(0).unwrap(), 0);
    let after_pop = run(&peek, &peek_circuit, &popped.after.state)?;
    assert_eq!(
        after_pop.returns_json()["item"],
        compact_maybe(&oracle, "afterPop", "NativeZeroWidthListMaybe.MaybeBytes0",)
    );

    let empty_pop = run(&pop, &pop_circuit, &popped.after.state)?;
    let ledger_after_empty_pop = query(&popped.after.state, &empty_pop)?;
    let StateValue::Array(root) = ledger_after_empty_pop.get_ref() else {
        panic!("expected state array after empty pop")
    };
    assert!(matches!(root.get(0), Some(StateValue::Null)));
    assert_eq!(oracle["emptyPopRead"], "rejected");
    assert!(prepare(
        &peek,
        &BTreeMap::new(),
        &ledger_after_empty_pop,
        &INITIAL_PARAMETERS,
        ContractAddress::default(),
    )
    .is_err());
    Ok(())
}
