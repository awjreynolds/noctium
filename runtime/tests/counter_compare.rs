#![cfg(feature = "zkir-321")]

use base_crypto::fab::AlignedValue;
use noctium_runtime::{Db, Plan, check, create_state, prepare, zkir::IrSource};
use onchain_runtime::state::{ChargedState, StateValue};
use serde_json::{Value as Json, json};
use std::{
    collections::BTreeMap,
    env,
    path::{Path, PathBuf},
};
use storage::arena::Sp;

fn artifacts() -> PathBuf {
    env::var_os("NOCTIUM_COUNTER_COMPARE_DIR")
        .map(PathBuf::from)
        .expect("set fresh outputs in NOCTIUM_COUNTER_COMPARE_DIR")
}

fn fixture(directory: &Path, entry: &str) -> (Plan, IrSource) {
    let stem = format!("CounterCompare.{entry}");
    let plan = serde_json::from_slice(
        &std::fs::read(directory.join(format!("{stem}.impact.json"))).unwrap(),
    )
    .unwrap();
    let circuit = IrSource::load(
        std::fs::read(directory.join(format!("{stem}.zkir")))
            .unwrap()
            .as_slice(),
    )
    .unwrap();
    (plan, circuit)
}

fn inputs(enabled: bool, threshold: u64) -> BTreeMap<String, Json> {
    BTreeMap::from([
        (
            "owner".into(),
            json!({"kind":"bytes", "values":vec![1u8; 32]}),
        ),
        (
            "spender".into(),
            json!({"kind":"bytes", "values":vec![2u8; 32]}),
        ),
        ("threshold".into(), json!(threshold.to_string())),
        ("enabled".into(), json!(enabled)),
    ])
}

fn assert_below(execution: &noctium_runtime::Execution, expected: bool) {
    assert_eq!(
        execution.returns_json(),
        BTreeMap::from([("below".into(), json!(expected))])
    );
}

fn counter_at(state: &ChargedState<Db>, expected: u64) {
    let StateValue::Array(slots) = state.get_ref() else {
        panic!("expected contract state array")
    };
    let StateValue::Cell(value) = slots.get(0).unwrap() else {
        panic!("expected standalone counter cell")
    };
    assert_eq!(**value, AlignedValue::from(expected));
}

#[test]
#[ignore = "requires fresh CounterCompare ledger outputs in NOCTIUM_COUNTER_COMPARE_DIR"]
fn counter_comparison_checks_bounds_nested_guards_and_read_after_write() {
    let directory = artifacts();
    let (inspect, inspect_circuit) = fixture(&directory, "inspect");
    let (seed, seed_circuit) = fixture(&directory, "seedNested");
    let (inspect_nested, nested_circuit) = fixture(&directory, "inspectNested");
    let initial = create_state(
        &inspect,
        &BTreeMap::from([("total".into(), json!("0")), ("epochs".into(), json!([]))]),
    )
    .unwrap();
    let parameters = &ledger::structure::INITIAL_PARAMETERS;
    let address = coin_structure::contract::ContractAddress::default();

    for (threshold, expected) in [(301, true), (300, false), (299, false), (u64::MAX, true)] {
        let execution = prepare(
            &inspect,
            &inputs(true, threshold),
            &initial,
            parameters,
            address,
        )
        .unwrap();
        check(&execution, &inspect_circuit).unwrap();
        assert_below(&execution, expected);
        counter_at(&execution.after.state, 300);
    }

    let max_seed = create_state(
        &inspect,
        &BTreeMap::from([
            ("total".into(), json!((u64::MAX - 300).to_string())),
            ("epochs".into(), json!([])),
        ]),
    )
    .unwrap();
    let at_max = prepare(
        &inspect,
        &inputs(true, u64::MAX),
        &max_seed,
        parameters,
        address,
    )
    .unwrap();
    check(&at_max, &inspect_circuit).unwrap();
    assert_below(&at_max, false);
    counter_at(&at_max.after.state, u64::MAX);

    let seeded = prepare(&seed, &inputs(true, 301), &initial, parameters, address).unwrap();
    check(&seeded, &seed_circuit).unwrap();
    let seeded_state = seeded.after.state;
    for (threshold, expected) in [(301, true), (300, false), (299, false), (u64::MAX, true)] {
        let execution = prepare(
            &inspect_nested,
            &inputs(true, threshold),
            &seeded_state,
            parameters,
            address,
        )
        .unwrap();
        check(&execution, &nested_circuit).unwrap();
        assert_below(&execution, expected);
    }

    let inactive_missing = prepare(
        &inspect_nested,
        &inputs(false, 301),
        &initial,
        parameters,
        address,
    )
    .unwrap();
    check(&inactive_missing, &nested_circuit).unwrap();
    assert_below(&inactive_missing, false);
    assert!(
        prepare(
            &inspect_nested,
            &inputs(true, 301),
            &initial,
            parameters,
            address,
        )
        .is_err(),
        "active comparison of a missing nested counter must fail"
    );

    let StateValue::Array(slots) = initial.get_ref() else {
        panic!("expected contract state array")
    };
    let malformed_counter = StateValue::Cell(Sp::new(AlignedValue::from([0u8; 4])));
    let malformed = ChargedState::new(StateValue::Array(
        slots.insert(0, malformed_counter).unwrap(),
    ));
    assert!(
        prepare(
            &inspect,
            &inputs(true, 301),
            &malformed,
            parameters,
            address,
        )
        .is_err(),
        "a Counter value with non-Bytes8 alignment must fail"
    );
}
