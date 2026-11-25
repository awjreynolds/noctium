#![cfg(feature = "zkir-321")]

use coin_structure::contract::ContractAddress;
use ledger::structure::INITIAL_PARAMETERS;
use noctium_runtime::{Db, Plan, check, create_state, field_value, prepare, zkir::IrSource};
use onchain_runtime::state::{ChargedState, StateValue};
use serde_json::{Value as Json, json};
use std::{collections::BTreeMap, fs, path::PathBuf};
use transient_crypto::curve::Fr;

fn fixture() -> (Plan, IrSource) {
    let directory = PathBuf::from(
        std::env::var_os("NOCTIUM_BOUNDED_SCALARS_REPLAY_DIR")
            .expect("set NOCTIUM_BOUNDED_SCALARS_REPLAY_DIR to fresh compiler outputs"),
    );
    let plan: Plan = serde_json::from_slice(
        &fs::read(directory.join("BoundedScalars.apply.impact.json")).unwrap(),
    )
    .unwrap();
    assert!(noctium_runtime::profile::validate_plan(
        plan.target.as_deref(),
        plan.target_profile.as_ref(),
    ));
    let circuit = IrSource::load(
        fs::read(directory.join("BoundedScalars.apply.zkir"))
            .unwrap()
            .as_slice(),
    )
    .unwrap();
    (plan, circuit)
}

fn inputs(expected: u64, left: u64, right: u64) -> BTreeMap<String, Json> {
    BTreeMap::from([
        ("expected".into(), json!(expected.to_string())),
        ("left".into(), json!(left.to_string())),
        ("right".into(), json!(right.to_string())),
    ])
}

fn total(state: &ChargedState<Db>, expected: u64) {
    let StateValue::Array(cells) = state.get_ref() else {
        panic!("expected contract state array")
    };
    let StateValue::Cell(value) = cells.get(0).unwrap() else {
        panic!("expected total Cell")
    };
    assert_eq!(**value, field_value(Fr::from(expected)));
}

fn checked_call(
    plan: &Plan,
    circuit: &IrSource,
    state: &ChargedState<Db>,
    expected: u64,
    left: u64,
    right: u64,
) -> noctium_runtime::Execution {
    let execution = prepare(
        plan,
        &inputs(expected, left, right),
        state,
        &INITIAL_PARAMETERS,
        ContractAddress::default(),
    )
    .unwrap();
    assert_eq!(
        check(&execution, circuit).unwrap(),
        execution.activity_schedule
    );
    assert!(
        execution.returns().is_empty(),
        "apply has no committed call returns"
    );
    assert!(execution.returns_json().is_empty());
    execution
}

#[test]
#[ignore = "requires freshly emitted BoundedScalars.apply Impact and ZKIR in NOCTIUM_BOUNDED_SCALARS_REPLAY_DIR"]
fn zero_sum_replay_then_positive_write_and_state_rejection_match_native_321() {
    let (plan, circuit) = fixture();
    let initial = create_state(&plan, &BTreeMap::from([("total".into(), json!("0"))])).unwrap();
    total(&initial, 0);

    let first_zero = checked_call(&plan, &circuit, &initial, 0, 0, 0);
    total(&first_zero.after.state, 0);
    let second_zero = checked_call(&plan, &circuit, &first_zero.after.state, 0, 0, 0);
    total(&second_zero.after.state, 0);

    let two = checked_call(&plan, &circuit, &second_zero.after.state, 2, 1, 1);
    total(&two.after.state, 2);

    // A sum of 3 satisfies the circuit in a fresh zero state. The same inputs
    // fail only after the prior accepted call writes 2 and the state guard runs.
    let valid_three = checked_call(&plan, &circuit, &initial, 3, 1, 2);
    total(&valid_three.after.state, 3);

    let state_before_rejection = two.after.state.clone();
    let rejection_boundary = match prepare(
        &plan,
        &inputs(3, 1, 2),
        &two.after.state,
        &INITIAL_PARAMETERS,
        ContractAddress::default(),
    ) {
        Err(_) => "prepare",
        Ok(execution) => {
            assert!(
                check(&execution, &circuit).is_err(),
                "native checker must reject the state guard"
            );
            "checker"
        }
    };
    assert_eq!(two.after.state, state_before_rejection);
    total(&two.after.state, 2);
    println!(
        "{}",
        json!({
            "nativeRelease": noctium_runtime::profile::RELEASE,
            "acceptedCalls": 3,
            "acceptedDecodedStateTotals": ["0", "0", "2"],
            "committedCallReturns": [],
            "sumThreeCircuitAcceptedFromZeroState": true,
            "sumThreeAfterStateTwoRejectedAt": rejection_boundary,
            "lastAcceptedTotalAfterRejection": "2",
            "privateInputObservations": false
        })
    );
}

#[test]
#[ignore = "requires freshly emitted BoundedScalars.apply Impact and ZKIR in NOCTIUM_BOUNDED_SCALARS_REPLAY_DIR"]
fn bounded_scalar_255_plus_255_is_checked_and_wrong_public_sum_is_rejected() {
    let (plan, circuit) = fixture();
    let initial = create_state(&plan, &BTreeMap::from([("total".into(), json!("0"))])).unwrap();
    total(&initial, 0);

    let accepted = checked_call(&plan, &circuit, &initial, 510, 255, 255);
    total(&accepted.after.state, 510);

    // Use the same fresh state so the state guard passes. Only the public sum
    // differs, and the native checker must reject the false value.
    let execution = prepare(
        &plan,
        &inputs(509, 255, 255),
        &initial,
        &INITIAL_PARAMETERS,
        ContractAddress::default(),
    )
    .expect("the mismatched public sum must reach the native checker");
    assert!(execution.returns().is_empty());
    assert!(execution.returns_json().is_empty());
    let error = check(&execution, &circuit)
        .expect_err("native checker must reject expected 509 for the sum 510");
    assert_eq!(
        error.to_string(),
        "native circuit assertion or preimage check failed"
    );
    total(&initial, 0);

    println!(
        "{}",
        json!({
            "nativeRelease": noctium_runtime::profile::RELEASE,
            "acceptedVector": {"expected": "510", "left": "255", "right": "255"},
            "acceptedDecodedStateTotal": "510",
            "committedCallReturns": [],
            "wrongExpectedVector": {"expected": "509", "left": "255", "right": "255"},
            "wrongExpectedRejectedAt": "checker",
            "wrongExpectedCheckerError": error.to_string(),
            "originalTotalAfterRejection": "0"
        })
    );
}
