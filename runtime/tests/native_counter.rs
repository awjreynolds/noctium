#![cfg(feature = "zkir-321")]

use base_crypto::fab::AlignedValue;
use noctium_runtime::{Db, Plan, check, create_state, prepare, zkir::IrSource};
use onchain_runtime::state::{ChargedState, StateValue};
use serde_json::{Value as Json, json};
use std::collections::BTreeMap;

fn fixture(operation: &str) -> (Plan, IrSource) {
    let (plan, circuit): (&str, &[u8]) = match operation {
        "bump" => (
            include_str!("fixtures/native-counter/321/NativeCounter.bump.impact.json"),
            include_bytes!("fixtures/native-counter/321/NativeCounter.bump.zkir"),
        ),
        "decrement" => (
            include_str!("fixtures/native-counter/321/NativeCounter.reduce.impact.json"),
            include_bytes!("fixtures/native-counter/321/NativeCounter.reduce.zkir"),
        ),
        "reset" => (
            include_str!("fixtures/native-counter/321/NativeCounter.resetCounters.impact.json"),
            include_bytes!("fixtures/native-counter/321/NativeCounter.resetCounters.zkir"),
        ),
        "read" => (
            include_str!("fixtures/native-counter/321/NativeCounter.readCounters.impact.json"),
            include_bytes!("fixtures/native-counter/321/NativeCounter.readCounters.zkir"),
        ),
        "guarded" => (
            include_str!("fixtures/native-counter/321/NativeCounter.guarded.impact.json"),
            include_bytes!("fixtures/native-counter/321/NativeCounter.guarded.zkir"),
        ),
        _ => unreachable!(),
    };
    (
        serde_json::from_str(plan).unwrap(),
        IrSource::load(circuit).unwrap(),
    )
}

fn inputs(plan: &Plan, enabled: bool) -> BTreeMap<String, Json> {
    plan.circuit
        .inputs
        .iter()
        .map(|input| {
            let value = match input.name.as_str() {
                "owner" => json!({"kind":"bytes", "values":vec![0u8; 32]}),
                "spender" => json!({"kind":"bytes", "values":vec![1u8; 32]}),
                "enabled" => json!(enabled),
                other => panic!("unexpected input {other}"),
            };
            (input.name.clone(), value)
        })
        .collect()
}

fn total(state: &ChargedState<Db>, expected: u64) {
    let StateValue::Array(state) = state.get_ref() else {
        panic!("expected state array")
    };
    let StateValue::Cell(value) = state.get(0).unwrap() else {
        panic!("expected counter Cell")
    };
    assert_eq!(**value, AlignedValue::from(expected));
}

fn epoch(state: &ChargedState<Db>, spender: u8, expected: u64) {
    let StateValue::Array(state) = state.get_ref() else {
        panic!("expected state array")
    };
    let StateValue::Map(owners) = state.get(1).unwrap() else {
        panic!("expected owners map")
    };
    let owner: AlignedValue = [0u8; 32].into();
    let spender: AlignedValue = [spender; 32].into();
    let StateValue::Map(spenders) = &*owners.get(&owner).unwrap() else {
        panic!("expected spender map")
    };
    let StateValue::Cell(value) = &*spenders.get(&spender).unwrap() else {
        panic!("expected nested counter Cell")
    };
    assert_eq!(**value, AlignedValue::from(expected));
}

#[test]
fn native_counter_codec_updates_reads_guards_and_checked_arithmetic() {
    let (bump, _) = fixture("bump");
    let initial = create_state(
        &bump,
        &BTreeMap::from([("total".into(), json!("0")), ("epochs".into(), json!([]))]),
    )
    .unwrap();
    total(&initial, 0);
    let params = &ledger::structure::INITIAL_PARAMETERS;
    let address = coin_structure::contract::ContractAddress::default();
    let (guarded, circuit) = fixture("guarded");
    let inactive = prepare(
        &guarded,
        &inputs(&guarded, false),
        &initial,
        params,
        address,
    )
    .unwrap();
    check(&inactive, &circuit).unwrap();
    assert_eq!(inactive.after.state, initial);
    let mut state = initial.clone();
    for (operation, expected_total, expected_epoch) in [
        ("bump", 3, 1),
        ("bump", 6, 2),
        ("decrement", 4, 1),
        ("reset", 0, 0),
    ] {
        let (plan, circuit) = fixture(operation);
        let execution = prepare(&plan, &inputs(&plan, true), &state, params, address).unwrap();
        check(&execution, &circuit).unwrap();
        state = execution.after.state;
        total(&state, expected_total);
        epoch(&state, 1, expected_epoch);
    }
    let (reset, reset_circuit) = fixture("reset");
    let mut missing_leaf = inputs(&reset, true);
    missing_leaf.insert(
        "spender".into(),
        json!({"kind":"bytes", "values":vec![2u8; 32]}),
    );
    assert!(prepare(&reset, &missing_leaf, &initial, params, address).is_err());

    let (seed, seed_circuit) = fixture("bump");
    let seeded = prepare(&seed, &inputs(&seed, true), &initial, params, address).unwrap();
    check(&seeded, &seed_circuit).unwrap();
    let (read, read_circuit) = fixture("read");
    let observed = prepare(
        &read,
        &inputs(&read, true),
        &seeded.after.state,
        params,
        address,
    )
    .unwrap();
    check(&observed, &read_circuit).unwrap();
    assert_eq!(
        observed.returns_json(),
        BTreeMap::from([
            ("totalValue".into(), json!("3")),
            ("epochValue".into(), json!("1")),
        ])
    );
    assert_eq!(observed.after.state, seeded.after.state);
    let reset_absent =
        prepare(&reset, &missing_leaf, &seeded.after.state, params, address).unwrap();
    check(&reset_absent, &reset_circuit).unwrap();
    total(&reset_absent.after.state, 0);
    epoch(&reset_absent.after.state, 1, 1);
    epoch(&reset_absent.after.state, 2, 0);
    let (decrement, _) = fixture("decrement");
    assert!(
        prepare(
            &decrement,
            &inputs(&decrement, true),
            &state,
            params,
            address
        )
        .is_err()
    );
    let overflow = create_state(
        &bump,
        &BTreeMap::from([
            ("total".into(), json!(u64::MAX.to_string())),
            ("epochs".into(), json!([])),
        ]),
    )
    .unwrap();
    assert!(prepare(&bump, &inputs(&bump, true), &overflow, params, address).is_err());
    let mut field_plan = bump.clone();
    field_plan.state[0].kind = json!({"tree":{"scalar":"UIntRange<18446744073709551616>"}});
    let wrong_codec = create_state(
        &field_plan,
        &BTreeMap::from([("total".into(), json!("0")), ("epochs".into(), json!([]))]),
    )
    .unwrap();
    assert!(prepare(&bump, &inputs(&bump, true), &wrong_codec, params, address).is_err());
}
