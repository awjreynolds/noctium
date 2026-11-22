#![cfg(feature = "zkir-321")]

use coin_structure::contract::ContractAddress;
use noctium_runtime::{Expr, Plan, check, create_state, prepare, zkir::IrSource};
use serde_json::json;
use std::{collections::BTreeMap, fs::File, path::PathBuf};

#[test]
#[ignore = "requires fresh artifacts in NOCTIUM_FIXED_BYTES_DEFAULTS_DIR"]
fn fixed_bytes_defaults_return_typed_zero_values_and_bind_them() -> anyhow::Result<()> {
    let directory = PathBuf::from(
        std::env::var_os("NOCTIUM_FIXED_BYTES_DEFAULTS_DIR")
            .expect("NOCTIUM_FIXED_BYTES_DEFAULTS_DIR"),
    );
    let mut plan: Plan = serde_json::from_reader(File::open(
        directory.join("FixedBytesDefaults.defaults.impact.json"),
    )?)?;
    let circuit = IrSource::load(File::open(
        directory.join("FixedBytesDefaults.defaults.zkir"),
    )?)?;
    assert!(plan.circuit.inputs.is_empty());
    assert!(plan.state.is_empty());

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
            ("emptyValue".into(), json!({"kind":"bytes","values":[]})),
            (
                "shortValue".into(),
                json!({"kind":"bytes","values":[0,0,0,0]}),
            ),
            (
                "wordValue".into(),
                json!({"kind":"bytes","values":vec![0u8; 32]}),
            ),
        ])
    );
    let (original_commitment, _) = execution.preimage.communications_commitment.unwrap();

    let short_value = plan
        .returns
        .iter_mut()
        .find(|output| output.name == "shortValue")
        .expect("shortValue return");
    short_value.expression = Expr::BytesLiteral {
        length: 4,
        values: vec![1, 0, 0, 0],
    };
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
