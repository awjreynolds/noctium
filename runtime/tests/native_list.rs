#![cfg(feature = "zkir-321")]

use base_crypto::fab::AlignedValue;
use noctium_runtime::{
    Db, Instruction, Plan, check, create_state, field_value, prepare, zkir::IrSource,
};
use onchain_runtime::{
    context::QueryContext,
    state::{ChargedState, StateValue},
};
use serde_json::{Value as Json, json};
use std::collections::BTreeMap;
use transient_crypto::curve::Fr;

fn fixture(operation: &str) -> (Plan, IrSource) {
    let (plan, circuit): (&str, &[u8]) = match operation {
        "append" => (
            include_str!("fixtures/native-list/321/NativeList.append.impact.json"),
            include_bytes!("fixtures/native-list/321/NativeList.append.zkir"),
        ),
        "pop" => (
            include_str!("fixtures/native-list/321/NativeList.pop.impact.json"),
            include_bytes!("fixtures/native-list/321/NativeList.pop.zkir"),
        ),
        "clear" => (
            include_str!("fixtures/native-list/321/NativeList.clear.impact.json"),
            include_bytes!("fixtures/native-list/321/NativeList.clear.zkir"),
        ),
        "guarded" => (
            include_str!("fixtures/native-list/321/NativeList.guarded.impact.json"),
            include_bytes!("fixtures/native-list/321/NativeList.guarded.zkir"),
        ),
        "inspect" => (
            include_str!("fixtures/native-list/321/NativeList.inspect.impact.json"),
            include_bytes!("fixtures/native-list/321/NativeList.inspect.zkir"),
        ),
        _ => unreachable!(),
    };
    (
        serde_json::from_str(plan).unwrap(),
        IrSource::load(circuit).unwrap(),
    )
}

fn inputs(
    plan: &Plan,
    owner: u8,
    spender: u8,
    x: u64,
    y: u64,
    enabled: bool,
) -> BTreeMap<String, Json> {
    plan.circuit
        .inputs
        .iter()
        .map(|input| {
            let value = match input.name.as_str() {
                "owner" => json!({"kind":"bytes", "values":vec![owner;32]}),
                "spender" => json!({"kind":"bytes", "values":vec![spender;32]}),
                "x" => json!(x.to_string()),
                "y" => json!(y.to_string()),
                "enabled" => json!(enabled),
                other => panic!("unexpected input {other}"),
            };
            (input.name.clone(), value)
        })
        .collect()
}

fn assert_list(value: &StateValue<Db>, expected: &[[u64; 2]]) {
    let StateValue::Array(node) = value else {
        panic!("expected native List array")
    };
    assert_eq!(node.len(), 3);
    let StateValue::Cell(length) = node.get(2).unwrap() else {
        panic!("expected List length Cell")
    };
    assert_eq!(**length, AlignedValue::from(expected.len() as u64));
    if let Some((head, tail)) = expected.split_first() {
        let StateValue::Cell(value) = node.get(0).unwrap() else {
            panic!("expected List record Cell")
        };
        let fields: Vec<_> = head
            .iter()
            .map(|value| field_value(Fr::from(*value)))
            .collect();
        assert_eq!(**value, AlignedValue::concat(&fields));
        assert_list(node.get(1).unwrap(), tail);
    } else {
        assert!(matches!(node.get(0), Some(StateValue::Null)));
        assert!(matches!(node.get(1), Some(StateValue::Null)));
    }
}

fn inbox(state: &ChargedState<Db>, expected: &[[u64; 2]]) {
    let StateValue::Array(root) = state.get_ref() else {
        panic!("expected root array")
    };
    assert_list(root.get(0).unwrap(), expected);
}

fn memos(state: &ChargedState<Db>, owner: u8, spender: u8, expected: &[[u64; 2]]) {
    let StateValue::Array(root) = state.get_ref() else {
        panic!("expected root array")
    };
    let StateValue::Map(owners) = root.get(1).unwrap() else {
        panic!("expected owner map")
    };
    let owner: AlignedValue = [owner; 32].into();
    let spender: AlignedValue = [spender; 32].into();
    let owner = owners.get(&owner).unwrap();
    let StateValue::Map(spenders) = &*owner else {
        panic!("expected spender map")
    };
    assert_list(&spenders.get(&spender).unwrap(), expected);
}

#[test]
fn native_list_records_preserve_order_paths_guards_and_empty_pop() {
    let (append, _) = fixture("append");
    let initial = create_state(
        &append,
        &BTreeMap::from([("inbox".into(), json!([])), ("memos".into(), json!([]))]),
    )
    .unwrap();
    inbox(&initial, &[]);
    let params = &ledger::structure::INITIAL_PARAMETERS;
    let address = coin_structure::contract::ContractAddress::default();
    let (guarded, circuit) = fixture("guarded");
    let inactive = prepare(
        &guarded,
        &inputs(&guarded, 0, 1, 1, 2, false),
        &initial,
        params,
        address,
    )
    .unwrap();
    check(&inactive, &circuit).unwrap();
    assert_eq!(inactive.after.state, initial);
    let mut state = initial.clone();
    for (owner, spender, x, y) in [(0, 1, 1, 2), (0, 1, 3, 4), (2, 3, 5, 6)] {
        let (plan, circuit) = fixture("append");
        let execution = prepare(
            &plan,
            &inputs(&plan, owner, spender, x, y, true),
            &state,
            params,
            address,
        )
        .unwrap();
        check(&execution, &circuit).unwrap();
        state = execution.after.state;
    }
    inbox(&state, &[[5, 6], [3, 4], [1, 2]]);
    memos(&state, 0, 1, &[[3, 4], [1, 2]]);
    memos(&state, 2, 3, &[[5, 6]]);
    let (inspect, circuit) = fixture("inspect");
    let view = prepare(
        &inspect,
        &inputs(&inspect, 0, 1, 0, 0, true),
        &state,
        params,
        address,
    )
    .unwrap();
    check(&view, &circuit).unwrap();
    let (pop, pop_circuit) = fixture("pop");
    let execution = prepare(
        &pop,
        &inputs(&pop, 0, 1, 0, 0, true),
        &state,
        params,
        address,
    )
    .unwrap();
    check(&execution, &pop_circuit).unwrap();
    // The selected nested path must exist even when the root List is empty.
    assert!(
        QueryContext::new(initial.clone(), address)
            .query(
                &execution.program,
                None,
                &params.cost_model.runtime_cost_model
            )
            .is_err()
    );
    state = execution.after.state;
    inbox(&state, &[[3, 4], [1, 2]]);
    memos(&state, 0, 1, &[[1, 2]]);
    memos(&state, 2, 3, &[[5, 6]]);
    let (clear, circuit) = fixture("clear");
    let execution = prepare(
        &clear,
        &inputs(&clear, 0, 1, 0, 0, true),
        &state,
        params,
        address,
    )
    .unwrap();
    check(&execution, &circuit).unwrap();
    state = execution.after.state;
    inbox(&state, &[]);
    memos(&state, 0, 1, &[]);
    memos(&state, 2, 3, &[[5, 6]]);
    let empty_pop = prepare(
        &pop,
        &inputs(&pop, 0, 1, 0, 0, true),
        &state,
        params,
        address,
    )
    .unwrap();
    check(&empty_pop, &pop_circuit).unwrap();
    let StateValue::Array(root) = empty_pop.after.state.get_ref() else {
        panic!("expected root array")
    };
    assert!(matches!(root.get(0), Some(StateValue::Null)));
    let StateValue::Map(owners) = root.get(1).unwrap() else {
        panic!("expected owner map")
    };
    let selected = owners.get(&AlignedValue::from([0u8; 32])).unwrap();
    let StateValue::Map(spenders) = &*selected else {
        panic!("expected spender map")
    };
    assert!(matches!(
        spenders.get(&AlignedValue::from([1u8; 32])),
        Some(value) if matches!(&*value, StateValue::Null)
    ));
    memos(&empty_pop.after.state, 2, 3, &[[5, 6]]);
    assert!(
        prepare(
            &inspect,
            &inputs(&inspect, 0, 1, 0, 0, true),
            &state,
            params,
            address
        )
        .is_err()
    );
    let mut malformed = append.clone();
    malformed
        .operations
        .iter_mut()
        .find_map(|op| match op {
            Instruction::ListPushFront { expressions, .. } => Some(expressions),
            _ => None,
        })
        .unwrap()
        .pop();
    assert!(
        prepare(
            &malformed,
            &inputs(&malformed, 0, 1, 1, 2, true),
            &initial,
            params,
            address
        )
        .is_err()
    );
}
