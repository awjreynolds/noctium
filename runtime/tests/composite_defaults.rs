#![cfg(feature = "zkir-321")]

use anyhow::Result;
use coin_structure::contract::ContractAddress;
use noctium_runtime::{Expr, Plan, check, create_state, prepare, zkir::IrSource};
use serde_json::json;
use std::{collections::BTreeMap, fs, path::PathBuf};

#[test]
#[ignore = "requires fresh artifacts in NOCTIUM_COMPOSITE_DEFAULTS_DIR"]
fn composite_defaults_decode_to_typed_zero_values_and_bind_them() -> Result<()> {
    let directory = PathBuf::from(
        std::env::var_os("NOCTIUM_COMPOSITE_DEFAULTS_DIR").expect("NOCTIUM_COMPOSITE_DEFAULTS_DIR"),
    );
    let mut plan: Plan = serde_json::from_slice(&fs::read(
        directory.join("CompositeDefaults.defaults.impact.json"),
    )?)?;
    let circuit = IrSource::load(fs::File::open(
        directory.join("CompositeDefaults.defaults.zkir"),
    )?)?;
    assert!(plan.circuit.inputs.is_empty());
    assert!(plan.call_inputs.is_empty());
    assert!(plan.state.is_empty());

    let record = json!({
        "kind":"struct",
        "id":"CompositeDefaults.Limits",
        "fields":[
            {"name":"count","value":{"kind":"uint","maximum":"255","value":"0"}},
            {"name":"enabled","value":{"kind":"bool","value":false}},
            {"name":"memo","value":{"kind":"bytes","values":[0,0,0,0]}}
        ]
    });
    let state = create_state(&plan, &BTreeMap::new())?;
    let execution = prepare(
        &plan,
        &BTreeMap::new(),
        &state,
        &ledger::structure::INITIAL_PARAMETERS,
        ContractAddress::default(),
    )?;
    assert_eq!(check(&execution, &circuit)?, execution.activity_schedule);
    assert_eq!(
        execution.returns_json(),
        BTreeMap::from([
            ("recordValue".into(), record.clone()),
            (
                "vectorValue".into(),
                json!({"kind":"vector","items":[record.clone(),record.clone()]}),
            ),
            (
                "maybeValue".into(),
                json!({
                    "kind":"struct",
                    "id":"CompositeDefaults.MaybeLimits",
                    "fields":[
                        {"name":"is_some","value":{"kind":"bool","value":false}},
                        {"name":"value","value":record}
                    ]
                }),
            ),
            (
                "eitherValue".into(),
                json!({
                    "kind":"struct",
                    "id":"CompositeDefaults.EitherLeftUInt8RightBool",
                    "fields":[
                        {"name":"is_left","value":{"kind":"bool","value":false}},
                        {"name":"left","value":{"kind":"uint","maximum":"255","value":"0"}},
                        {"name":"right","value":{"kind":"bool","value":false}}
                    ]
                }),
            ),
        ])
    );
    let (original_commitment, _) = execution.preimage.communications_commitment.unwrap();

    let count_name = plan
        .return_views
        .iter()
        .find(|view| view.name == "recordValue")
        .and_then(|view| view.fields.first())
        .expect("recordValue first physical field")
        .clone();
    let count_output = plan
        .returns
        .iter_mut()
        .find(|output| output.name == count_name)
        .expect("recordValue count output");
    count_output.expression = Expr::Constant { value: "1".into() };
    let changed = prepare(
        &plan,
        &BTreeMap::new(),
        &state,
        &ledger::structure::INITIAL_PARAMETERS,
        ContractAddress::default(),
    )?;
    let (changed_commitment, _) = changed.preimage.communications_commitment.unwrap();
    assert_ne!(changed_commitment, original_commitment);
    assert!(check(&changed, &circuit).is_err());
    Ok(())
}
