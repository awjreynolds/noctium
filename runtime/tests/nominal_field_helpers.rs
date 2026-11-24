#![cfg(feature = "zkir-321")]

use coin_structure::contract::ContractAddress;
use noctium_runtime::{Plan, check, create_state, prepare, zkir::IrSource};
use serde_json::json;
use std::collections::BTreeMap;

fn fixture(name: &str) -> (Plan, IrSource) {
    let (plan, circuit): (&str, &[u8]) = match name {
        "direct" => (
            include_str!("fixtures/nominal-field-helpers/321/NominalField.NominalFieldHelperContract.identity.impact.json"),
            include_bytes!("fixtures/nominal-field-helpers/321/NominalField.NominalFieldHelperContract.identity.zkir"),
        ),
        "explicit-input" => (
            include_str!("fixtures/nominal-field-helpers/321/NominalField.NominalFieldHelperContract.explicitInput.impact.json"),
            include_bytes!("fixtures/nominal-field-helpers/321/NominalField.NominalFieldHelperContract.explicitInput.zkir"),
        ),
        "explicit-output" => (
            include_str!("fixtures/nominal-field-helpers/321/NominalField.NominalFieldHelperContract.explicitOutput.impact.json"),
            include_bytes!("fixtures/nominal-field-helpers/321/NominalField.NominalFieldHelperContract.explicitOutput.zkir"),
        ),
        "linked" => (
            include_str!("fixtures/nominal-field-helpers/321/NominalLinkedHelperContract.identity.impact.json"),
            include_bytes!("fixtures/nominal-field-helpers/321/NominalLinkedHelperContract.identity.zkir"),
        ),
        _ => unreachable!(),
    };
    (
        serde_json::from_str(plan).unwrap(),
        IrSource::load(circuit).unwrap(),
    )
}

fn check_helper(name: &str, input_name: &str, result_name: &str, value: &str) {
    let (plan, circuit) = fixture(name);
    assert_eq!(plan.target.as_deref(), Some("midnight-ledger-9-zkir-3.2.1"));
    assert_eq!(plan.circuit.inputs[0].ty, "Native");
    assert!(plan.circuit.outputs.iter().all(|output| output.ty == "Native"));
    let inputs = BTreeMap::from([(input_name.into(), json!(value))]);
    let state = create_state(&plan, &BTreeMap::new()).unwrap();
    let execution = prepare(
        &plan,
        &inputs,
        &state,
        &ledger::structure::INITIAL_PARAMETERS,
        ContractAddress::default(),
    )
    .unwrap();
    check(&execution, &circuit).unwrap();
    assert_eq!(
        execution.returns_json(),
        BTreeMap::from([(result_name.into(), json!(value))])
    );
}

#[test]
fn nominal_field_helper_arguments_and_results_stay_native_in_the_relation() {
    check_helper("direct", "amount", "result", "19");
    check_helper("explicit-input", "raw", "returned", "23");
    check_helper("explicit-output", "raw", "returned", "29");
    check_helper("linked", "amount", "returned", "37");
}
