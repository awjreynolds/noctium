#![cfg(feature = "zkir-321")]

use base_crypto::fab::AlignedValue;
use noctium_runtime::{Db, Plan, check, create_state, field_value, prepare, zkir::IrSource};
use onchain_runtime::state::{ChargedState, StateValue};
use serde_json::{Value as Json, json};
use std::collections::BTreeMap;
use transient_crypto::curve::Fr;

fn fixture(name: &str) -> (Plan, IrSource) {
    let (plan, circuit): (&str, &[u8]) = match name {
        "push" => (
            include_str!("fixtures/native-map-list/321/NativeMapList.push.impact.json"),
            include_bytes!("fixtures/native-map-list/321/NativeMapList.push.zkir"),
        ),
        "inspect" => (
            include_str!("fixtures/native-map-list/321/NativeMapList.inspect.impact.json"),
            include_bytes!("fixtures/native-map-list/321/NativeMapList.inspect.zkir"),
        ),
        "pop" => (
            include_str!("fixtures/native-map-list/321/NativeMapList.pop.impact.json"),
            include_bytes!("fixtures/native-map-list/321/NativeMapList.pop.zkir"),
        ),
        _ => unreachable!(),
    };
    (
        serde_json::from_str(plan).unwrap(),
        IrSource::load(circuit).unwrap(),
    )
}

fn inputs(plan: &Plan, owner: u64, value: u64) -> BTreeMap<String, Json> {
    plan.circuit
        .inputs
        .iter()
        .map(|input| {
            let value = match input.name.as_str() {
                "owner" => json!(owner.to_string()),
                "value" => json!(value.to_string()),
                other => panic!("unexpected input {other}"),
            };
            (input.name.clone(), value)
        })
        .collect()
}

fn run(
    plan: &Plan,
    circuit: &IrSource,
    owner: u64,
    value: u64,
    state: &ChargedState<Db>,
) -> noctium_runtime::Execution {
    let execution = prepare(
        plan,
        &inputs(plan, owner, value),
        state,
        &ledger::structure::INITIAL_PARAMETERS,
        coin_structure::contract::ContractAddress::default(),
    )
    .unwrap();
    check(&execution, circuit).unwrap();
    execution
}

fn assert_list(node: &StateValue<Db>, expected: &[u64]) {
    let StateValue::Array(node) = node else {
        panic!("expected native List array")
    };
    assert_eq!(node.len(), 3);
    let StateValue::Cell(length) = node.get(2).unwrap() else {
        panic!("expected List length Cell")
    };
    assert_eq!(**length, AlignedValue::from(expected.len() as u64));
    if let Some((head, tail)) = expected.split_first() {
        let StateValue::Cell(value) = node.get(0).unwrap() else {
            panic!("expected List head Cell")
        };
        assert_eq!(**value, field_value(Fr::from(*head)));
        assert_list(node.get(1).unwrap(), tail);
    } else {
        assert!(matches!(node.get(0), Some(StateValue::Null)));
        assert!(matches!(node.get(1), Some(StateValue::Null)));
    }
}

fn assert_buckets(state: &ChargedState<Db>, expected_a: &[u64], expected_b: &[u64]) {
    let StateValue::Array(root) = state.get_ref() else {
        panic!("expected contract state array")
    };
    let StateValue::Map(buckets) = root.get(0).unwrap() else {
        panic!("expected root Map")
    };
    assert_eq!(buckets.size(), 2);
    let bucket = |owner: u64| {
        buckets
            .get(&field_value(Fr::from(owner)))
            .expect("Map owner exists")
    };
    assert_list(&bucket(1), expected_a);
    assert_list(&bucket(2), expected_b);
}

fn assert_head(execution: &noctium_runtime::Execution, value: &str, length: &str) {
    assert_eq!(
        execution.returns_json(),
        BTreeMap::from([
            ("headPresent".into(), json!(true)),
            ("head".into(), json!(value)),
            ("length".into(), json!(length)),
        ])
    );
}

#[test]
fn native_map_of_list_chains_push_front_length_head_and_pop() {
    let (push, push_circuit) = fixture("push");
    let (inspect, inspect_circuit) = fixture("inspect");
    let (pop, pop_circuit) = fixture("pop");
    let mut state = create_state(&push, &BTreeMap::from([("buckets".into(), json!([]))])).unwrap();

    for (owner, value) in [(1, 5), (2, 99), (1, 11), (1, 22)] {
        let execution = run(&push, &push_circuit, owner, value, &state);
        state = execution.after.state;
    }
    assert_buckets(&state, &[22, 11, 5], &[99]);

    let view_a = run(&inspect, &inspect_circuit, 1, 0, &state);
    assert_head(&view_a, "22", "3");
    let view_b = run(&inspect, &inspect_circuit, 2, 0, &state);
    assert_head(&view_b, "99", "1");

    let popped = run(&pop, &pop_circuit, 1, 0, &state);
    state = popped.after.state;
    assert_buckets(&state, &[11, 5], &[99]);

    let view_a = run(&inspect, &inspect_circuit, 1, 0, &state);
    assert_head(&view_a, "11", "2");
    let view_b = run(&inspect, &inspect_circuit, 2, 0, &state);
    assert_head(&view_b, "99", "1");
}
