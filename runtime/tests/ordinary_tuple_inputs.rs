#![cfg(feature = "zkir-321")]

use base_crypto::fab::AlignedValue;
use coin_structure::contract::ContractAddress;
use noctium_runtime::{Expr, Plan, check, create_state, field_value, prepare, zkir::IrSource};
use serde_json::{Value as Json, json};
use std::{
    collections::BTreeMap,
    env, fs,
    path::{Path, PathBuf},
};
use transient_crypto::curve::Fr;

fn artifact(directory: &Path, name: &str) -> Vec<u8> {
    fs::read(directory.join(name)).unwrap()
}

#[test]
#[ignore = "requires fresh OrdinaryTupleInputs Ledger 9/ZKIR 3.2.1 artifacts via NOCTIUM_ORDINARY_TUPLE_INPUTS_DIR"]
fn ordinary_tuple_call_inputs_keep_leaf_order_and_bind_both_results() {
    let directory = PathBuf::from(
        env::var_os("NOCTIUM_ORDINARY_TUPLE_INPUTS_DIR")
            .expect("NOCTIUM_ORDINARY_TUPLE_INPUTS_DIR"),
    );
    let plan: Plan = serde_json::from_slice(&artifact(
        &directory,
        "OrdinaryTupleInputs.project.impact.json",
    ))
    .unwrap();
    let circuit =
        IrSource::load(artifact(&directory, "OrdinaryTupleInputs.project.zkir").as_slice())
            .unwrap();
    let metadata: Json = serde_json::from_slice(&artifact(&directory, "noctium.json")).unwrap();
    let public_plan: Json = serde_json::from_slice(&artifact(
        &directory,
        "OrdinaryTupleInputs.publicProject.impact.json",
    ))
    .unwrap();

    assert_eq!(
        plan.call_inputs
            .iter()
            .map(String::as_str)
            .collect::<Vec<_>>(),
        ["pair.0", "pair.1"]
    );
    let entrypoint = metadata["contracts"][0]["entrypoints"]
        .as_array()
        .unwrap()
        .iter()
        .find(|entrypoint| entrypoint["name"] == "project")
        .unwrap();
    let expected_tuple = json!([{
        "name": "pair",
        "fields": [
            {"name": "pair.0", "type": "UIntRange<256>"},
            {"name": "pair.1", "type": "Bool"}
        ]
    }]);
    assert_eq!(entrypoint["callInputViews"], expected_tuple);
    let expected_public_inputs = json!([
        {"name": "pair.0", "type": "UIntRange<256>", "visibility": "public"},
        {"name": "pair.1", "type": "Bool", "visibility": "public"}
    ]);
    assert!(public_plan["circuit"].get("file").is_none());
    assert_eq!(public_plan["circuit"]["inputViews"], expected_tuple);
    assert_eq!(public_plan["circuit"]["inputs"], expected_public_inputs);

    let standalone_metadata: Json =
        serde_json::from_slice(&artifact(&directory, "standalone/noctium.json")).unwrap();
    let standalone = standalone_metadata["circuits"]
        .as_array()
        .unwrap()
        .iter()
        .find(|circuit| circuit["name"] == "ordinaryTupleProjection")
        .unwrap();
    assert_eq!(standalone["inputViews"], expected_tuple);
    assert_eq!(standalone["inputs"], expected_public_inputs);

    let inputs = BTreeMap::from([
        ("pair.0".into(), json!("173")),
        ("pair.1".into(), json!(true)),
    ]);
    let state = create_state(&plan, &BTreeMap::new()).unwrap();
    let mut execution = prepare(
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
        BTreeMap::from([
            ("firstResult".into(), json!("173")),
            ("flagResult".into(), json!(true)),
        ])
    );
    assert_eq!(
        execution.preimage.inputs,
        [Fr::from(173u64), Fr::from(1u64)]
    );

    let input_fields = [field_value(Fr::from(173u64)), field_value(Fr::from(1u64))];
    let output_fields = [field_value(Fr::from(173u64)), field_value(Fr::from(1u64))];
    let (commitment, randomness) = execution.preimage.communications_commitment.unwrap();
    assert_eq!(
        commitment,
        onchain_runtime::communication_commitment(
            AlignedValue::concat(&input_fields),
            AlignedValue::concat(&output_fields),
            randomness,
        )
    );

    let mut invalid_leaf = inputs.clone();
    invalid_leaf.insert("pair.0".into(), json!("256"));
    assert!(
        prepare(
            &plan,
            &invalid_leaf,
            &state,
            &ledger::structure::INITIAL_PARAMETERS,
            ContractAddress::default(),
        )
        .is_err()
    );

    let mut changed_result_plan = plan.clone();
    changed_result_plan.returns[0].expression = Expr::Uint {
        maximum: "255".into(),
        value: "174".into(),
    };
    let changed_result = prepare(
        &changed_result_plan,
        &inputs,
        &state,
        &ledger::structure::INITIAL_PARAMETERS,
        ContractAddress::default(),
    )
    .unwrap();
    assert!(check(&changed_result, &circuit).is_err());

    execution.preimage.inputs[0] = Fr::from(174u64);
    let altered_input = [field_value(Fr::from(174u64)), field_value(Fr::from(1u64))];
    execution.preimage.communications_commitment = Some((
        onchain_runtime::communication_commitment(
            AlignedValue::concat(&altered_input),
            AlignedValue::concat(&output_fields),
            randomness,
        ),
        randomness,
    ));
    assert!(check(&execution, &circuit).is_err());
}
