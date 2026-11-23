#![cfg(feature = "zkir-321")]

use anyhow::Result;
use coin_structure::contract::ContractAddress;
use noctium_runtime::{Plan, Value, check, create_state, prepare, zkir::IrSource};
use serde_json::json;
use std::{collections::BTreeMap, env, fs, path::PathBuf};

#[test]
#[ignore = "requires fresh ReadableNominalUInt artifacts in NOCTIUM_READABLE_NOMINAL_UINT_DIR"]
fn readable_nominal_uint_echo_keeps_legacy_uint_encoding() -> Result<()> {
    let directory = PathBuf::from(
        env::var_os("NOCTIUM_READABLE_NOMINAL_UINT_DIR")
            .expect("NOCTIUM_READABLE_NOMINAL_UINT_DIR must point to fresh compiler outputs"),
    );
    let stem = "ReadableNominalUInt.echo";
    let plan: Plan =
        serde_json::from_slice(&fs::read(directory.join(format!("{stem}.impact.json")))?)?;
    let circuit = IrSource::load(fs::read(directory.join(format!("{stem}.zkir")))?.as_slice())?;

    assert_eq!(plan.entrypoint, "echo");
    assert_eq!(plan.call_inputs, ["echoed"]);
    assert_eq!(plan.circuit.inputs.len(), 1);
    assert_eq!(plan.circuit.inputs[0].name, "echoed");
    assert_eq!(plan.circuit.inputs[0].ty, "UIntRange<256>");
    assert_eq!(plan.circuit.inputs[0].visibility, "private");
    assert_eq!(plan.circuit.outputs.len(), 1);
    assert_eq!(plan.circuit.outputs[0].ty, "UIntRange<256>");
    assert_eq!(plan.circuit.outputs[0].visibility, "public");
    assert_eq!(plan.returns.len(), 1);
    assert_eq!(plan.returns[0].name, "result");
    assert_eq!(plan.returns[0].ty, "UIntRange<256>");

    let initial = create_state(&plan, &BTreeMap::new())?;
    let execution = prepare(
        &plan,
        &BTreeMap::from([("echoed".into(), json!("7"))]),
        &initial,
        &ledger::structure::INITIAL_PARAMETERS,
        ContractAddress::default(),
    )?;
    assert_eq!(check(&execution, &circuit)?, execution.activity_schedule);
    assert_eq!(execution.returns_json()["result"], json!("7"));
    assert_eq!(
        execution.returns(),
        [(
            "result".into(),
            Value::UInt {
                number: 7u8.into(),
                maximum: 255u16.into(),
            },
        )]
    );
    Ok(())
}
